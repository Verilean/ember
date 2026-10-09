import Ember.Lang.Types
import Ember.Lang.Eval
import Ember.Lang.Profile
import Ember.C.Print

/-!
# Ember.C.Compile — `Lang → C` (M2.6)

Input: a checked program.  Output: a `CUnit` whose C has no undefined
behaviour on any input:

* every arithmetic operation is computed in the profile's `opType` and
  truncated with an explicit cast (`(uint8_t)((unsigned)a * (unsigned)b)`);
* shifts are guarded (`s >= w ? 0 : …`), divisions too (`b == 0 ? 0 : …`);
* array reads and writes are bounds-checked unless the index is provably
  in range (a literal, or a `u8` index into an array of ≥ 256 elements);
  the check is hoisted into a temporary before the statement, in the
  interpreter's evaluation order, and calls `ember_trap` with the
  interpreter's error location;
* `#line` directives map every statement back to its Ember source line.

Names: functions `e_f`, globals `g_x`, records `s_T`, locals and
parameters `v_x`, temporaries `t<n>`; `namePrefix` is prepended to the
global ones so that many programs can share one C file (the fuzzer).
-/

namespace Ember.C
open Ember.Lang

structure Opts where
  profile : Profile := .host64
  namePrefix : String := ""
  lines   : Bool := true
  /-- Planted bug for the fuzzer's self-test: drop the truncating cast of `+`. -/
  bugDropCast : Bool := false
  deriving Inhabited

structure VarInfo where
  ty  : Ty
  c   : CExpr
  /-- A by-reference record parameter: fields through `->`. -/
  ptr : Bool := false

structure Env where
  prog : Prog
  opts : Opts
  fn   : String := ""
  path : List Nat := []
  vars : List (String × VarInfo) := []

structure CS where
  out : Array CStmt := #[]
  tmp : Nat := 0

abbrev CM := ReaderT Env (StateT CS (Except String))

def Opts.fnName (o : Opts) (f : String) : String := s!"{o.namePrefix}e_{f}"
def Opts.globalName (o : Opts) (g : String) : String := s!"{o.namePrefix}g_{g}"
def Opts.structName (o : Opts) (s : String) : String := s!"{o.namePrefix}s_{s}"
def Opts.entryName (o : Opts) : String := s!"{o.namePrefix}entry"
def localName (x : String) : String := s!"v_{x}"

def emit (s : CStmt) : CM Unit := modify fun st => { st with out := st.out.push s }

def fresh : CM String := do
  let st ← get
  set { st with tmp := st.tmp + 1 }
  return s!"t{st.tmp}"

/-- Run `m`, returning the statements it emitted (not emitting them here). -/
def collect (m : CM Unit) : CM (List CStmt) := do
  let saved := (← get).out
  modify fun st => { st with out := #[] }
  m
  let ss := (← get).out
  modify fun st => { st with out := saved }
  return ss.toList

def cty (o : Opts) : Ty → CTy
  | .int w => .uint w.bits
  | .bool => .bool
  | .arr el n => .arr (cty o el) n
  | .record r => .strct (o.structName r)

def suffix (w : Width) : String :=
  match w with
  | .w8 | .w16 => "u"
  | .w32 => "UL"
  | .w64 => "ULL"

def litC (w : Width) (n : Nat) : CExpr := .cast (.uint w.bits) (.lit n (suffix w))

def opTy (o : Opts) (w : Width) : CTy :=
  if o.profile.promotes w then .unsigned else .uint w.bits

def err (msg : String) : CM α := do throw s!"{(← read).fn}: {msg}"

def varInfo (x : String) : CM VarInfo := do
  let e ← read
  if let some v := e.vars.lookup x then return v
  match e.prog.global? x with
  | some g => return { ty := g.ty, c := .var (e.opts.globalName x) }
  | none => err s!"unknown variable {x}"

def fieldTy (r f : String) : CM Ty := do
  let some sd := (← read).prog.struct? r | err s!"unknown record {r}"
  match sd.fields.lookup f with
  | some t => return t
  | none => err s!"no field {f}"

def trapMsg (msg : String) : CM String := do
  let e ← read
  return s!"fn={e.fn} at stmt {".".intercalate (e.path.map fun (n : Nat) => s!"{n}")}: {msg}"

/-! ## Comparisons and guards

GCC's `-Wtype-limits` and `-Wtautological-compare` fire on comparisons
the C front end can decide — after folding constants and looking through
casts, `&`, `|` and conditionals.  Ember allows such comparisons (and the
emitter's own guards `b == 0`, `s >= w` would trip them), so:

* a closed subexpression (no variables) is evaluated by the interpreter
  itself (`closedVal`) and emitted as a constant; closed expressions
  contain no array reads, so no bounds check is lost;
* every non-trivial operand of a comparison, every non-constant divisor
  and shift amount, is first stored in a temporary of its type
  (`hide`) — expressions are pure and strict, so this preserves the
  semantics — and the front end then knows only the operand's type;
* what the type alone decides (`x >= 0`, `x <= 2^w − 1`, …) is folded. -/

/-- The value of an expression without variables, by the interpreter. -/
def closedVal (e : Expr) : Option Val :=
  let m : Machine := { prog := { fns := [] }, world := { inputs := #[] }, fuel := 1000 }
  match (((eval [] e).run {}).run).run m with
  | (.ok v, _) => some v
  | (.error _, _) => none

/-- Decide `x op c` (or `c op x` when `flip`) from `x ∈ [0, hi]`. -/
def decide (op : BinOp) (hi c : Nat) (flip : Bool) : Option Bool :=
  let op := if !flip then op else match op with
    | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | o => o
  match op with
  | .lt => if hi < c then some true else if c == 0 then some false else none
  | .le => if hi ≤ c then some true else none
  | .gt => if hi ≤ c then some false else none
  | .ge => if c == 0 then some true else if hi < c then some false else none
  | .eq => if c > hi then some false else none
  | .ne => if c > hi then some true else none
  | _ => none

/-- The value of a compiled constant (`(T)42u`). -/
def CExpr.litVal? : CExpr → Option Nat
  | .lit n _ => some n
  | .cast _ (.lit n _) => some n
  | _ => none

/-- An lvalue or a literal: the front end knows nothing beyond its type. -/
def CExpr.isSimple : CExpr → Bool
  | .var _ | .dot _ _ | .arrow _ _ | .index _ _ | .lit _ _ | .blit _ => true
  | .cast _ (.lit _ _) => true
  | _ => false

/-- Store a non-simple operand in a temporary of type `t`. -/
def hide (t : CTy) (c : CExpr) : CM CExpr := do
  if c.isSimple then return c
  let x ← fresh
  emit (.decl t x (some c))
  -- an enclosing comparison may still be folded away
  emit (.expr (.cast .void (.var x)))
  return .var x

mutual

/-- Type of an expression of a checked program. -/
partial def tyOf (e : Expr) : CM Ty := do
  match e with
  | .lit _ (some w) => return .int w
  | .lit _ none => err "untyped literal (program not checked)"
  | .blit _ => return .bool
  | .var x => return (← varInfo x).ty
  | .field b f =>
    let .record r ← tyOf b | err "field of a non-record"
    fieldTy r f
  | .index b _ =>
    let .arr el _ ← tyOf b | err "index of a non-array"
    return el
  | .bin op a _ => if op.isCompare || op.isLogic then return .bool else tyOf a
  | .un _ a => tyOf a
  | .cast w _ => return .int w
  | .cond _ a _ => tyOf a

/-- A place: its C lvalue, type, and whether it is a record pointer. -/
partial def place (e : Expr) : CM (CExpr × Ty × Bool) := do
  match e with
  | .var x =>
    let v ← varInfo x
    return (v.c, v.ty, v.ptr)
  | .field b f =>
    let (c, t, ptr) ← place b
    let .record r := t | err "field of a non-record"
    return (if ptr then .arrow c f else .dot c f, ← fieldTy r f, false)
  | .index b i =>
    let (c, t, _) ← place b
    let .arr el n := t | err "index of a non-array"
    let iw ← match ← tyOf i with
      | .int w => pure w
      | _ => err "non-integer index"
    let ic ← expr i
    let safe := match i with
      | .lit v _ => v < n
      | _ => iw == .w8 && n ≥ 256
    if safe = true then return (.index c ic, el, false)
    let t ← fresh
    emit (.decl (.uint iw.bits) t (some ic))
    emit (.ite (.bin ">=" (.var t) (.lit n (suffix iw)))
      [.expr (.call "ember_trap" [.str (← trapMsg s!"index out of bounds [0, {n})")])] [])
    return (.index c (.var t), el, false)
  | _ => err "not a place"

partial def expr (e : Expr) : CM CExpr := do
  let o := (← read).opts
  match e with
  | .lit _ _ | .blit _ => pure ()
  | _ =>
    match closedVal e with
    | some (.int w v) => return litC w v.toNat
    | some (.bool b) => return .blit b
    | _ => pure ()
  match e with
  | .lit v (some w) => return litC w v
  | .lit _ none => err "untyped literal"
  | .blit b => return .blit b
  | .var _ | .field _ _ | .index _ _ => return (← place e).1
  | .bin op a b =>
    let ta ← tyOf a
    let ca ← expr a
    let cb ← expr b
    if op.isLogic then return .bin (if op == .land then "&&" else "||") ca cb
    if op.isCompare then
      let ct := cty o ta
      -- identical operands (`x == x`, -Wtautological-compare)
      if ca == cb then return .blit (op == .eq || op == .le || op == .ge)
      -- decided by the operand type's range (-Wtype-limits)
      if let .int w := ta then
        let hi := w.modulus - 1
        match ca.litVal?, cb.litVal? with
        | none, some c => if let some r := decide op hi c false then return .blit r
        | some c, none => if let some r := decide op hi c true then return .blit r
        | _, _ => pure ()
      let sym := match op with
        | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | _ => ">="
      return .bin sym (← hide ct ca) (← hide ct cb)
    match ta with
    | .int w =>
      let T : CTy := .uint w.bits
      let U := opTy o w
      let p (x : CExpr) := CExpr.cast U x
      let arith (sym : String) (y : CExpr) := CExpr.cast T (.bin sym (p ca) (p y))
      match op with
      | .add => return if o.bugDropCast then .bin "+" (p ca) (p cb) else arith "+" cb
      | .sub => return arith "-" cb
      | .mul => return arith "*" cb
      | .band => return arith "&" cb
      | .bor => return arith "|" cb
      | .bxor => return arith "^" cb
      | .div | .mod =>
        let sym := if op == .div then "/" else "%"
        match closedVal b with
        | some v => return if v.toNat == 0 then litC w 0 else arith sym cb
        | none =>
          let d ← hide T cb
          return .cast T (.cond (.bin "==" d (.lit 0 (suffix w))) (litC w 0) (arith sym d))
      | .shl | .shr =>
        let sw ← match ← tyOf b with
          | .int sw => pure sw
          | _ => err "shift amount"
        let sym := if op == .shl then "<<" else ">>"
        match closedVal b with
        | some v => return if v.toNat ≥ w.bits then litC w 0 else .cast T (.bin sym (p ca) cb)
        | none =>
          let s ← hide (.uint sw.bits) cb
          -- an amount type that cannot reach w needs no guard
          if sw.modulus ≤ w.bits then return .cast T (.bin sym (p ca) s)
          return .cast T (.cond (.bin ">=" s (.lit w.bits (suffix sw))) (litC w 0) (.cast T (.bin sym (p ca) s)))
      | _ => err "bad operator"
    | _ => err "bad operand type"
  | .un op a =>
    let ca ← expr a
    match op, ← tyOf a with
    | .lnot, _ => return .un "!" ca
    | .bnot, .int w => return .cast (.uint w.bits) (.un "~" (.cast (opTy o w) ca))
    | .neg, .int w => return .cast (.uint w.bits) (.bin "-" (.lit 0 "u") (.cast (opTy o w) ca))
    | _, _ => err "bad unary operand"
  | .cast w a =>
    let ca ← expr a
    match ← tyOf a with
    -- bool → int as a choice: casting a comparison and operating on it
    -- trips -Wbool-operation
    | .bool => return .cast (.uint w.bits) (.cond ca (.lit 1 (suffix w)) (.lit 0 (suffix w)))
    | _ => return .cast (.uint w.bits) ca
  | .cond c a b =>
    let cc ← expr c
    let ca ← expr a
    let cb ← expr b
    match ← tyOf a with
    | .int w => return .cast (.uint w.bits) (.cond cc ca cb)
    | _ => return .cond cc ca cb

end

/-- The C argument for a by-reference parameter. -/
def refArg (a : Expr) : CM CExpr := do
  let (c, t, ptr) ← place a
  match t with
  | .record _ => return if ptr then c else .addr c
  | _ => return c

def counterTy (n : Nat) : Width :=
  if n < 256 then .w8 else if n < 65536 then .w16 else .w32

def effectCall (e : Effect) : String :=
  match e with
  | .inputNext => "ember_input_next" | .outByte => "ember_out_byte" | .outEnd => "ember_out_end"
  | .drop => "ember_drop" | .note => "ember_note" | .mmioRead32 => "ember_mmio_read32"
  | .mmioWrite32 => "ember_mmio_write32" | .ringPop => "ember_ring_pop"

def withIdx (i : Nat) (m : CM α) : CM α :=
  withReader (fun e => { e with path := e.path ++ [i] }) m

/-- Store the result of a call.  The destination is evaluated *after*
the call, as the interpreter does: when its index is checked, the call
goes to a temporary first, so its effects precede a trap. -/
def assignResult (dst : Option Expr) (call : CExpr) (t : CTy) : CM Unit := do
  match dst with
  | none => emit (.expr call)
  | some d =>
    let mark := (← get).out.size
    let (cd, _, _) ← place d
    let checks := (← get).out.extract mark (← get).out.size
    if checks.isEmpty then
      emit (.assign cd call)
    else
      modify fun st => { st with out := st.out.extract 0 mark }
      let x ← fresh
      emit (.decl t x (some call))
      for c in checks do emit c
      emit (.assign cd (.var x))

mutual

/-- Compile a block; returns nothing, emits its statements. -/
partial def block (ss : List Stmt) : CM Unit := do
  let mut i := 1
  let mut env ← read
  let base := env.path
  for s in ss do
    let env' ← withReader (fun _ => { env with path := base ++ [i] }) (stmt s)
    env := { env' with path := base }
    i := i + 1

/-- Compile one statement; returns the environment for what follows. -/
partial def stmt (s : Stmt) : CM Env := do
  let env ← read
  let o := env.opts
  match s with
  | .at sp s =>
    if o.lines && sp.line > 0 then emit (.line sp.line sp.file)
    stmt s
  | .decl x ty init =>
    let v : VarInfo := { ty, c := .var (localName x) }
    match init, ty with
    | some e, _ => emit (.decl (cty o ty) (localName x) (some (← expr e)))
    | none, .int w => emit (.decl (cty o ty) (localName x) (some (litC w 0)))
    | none, .bool => emit (.decl .bool (localName x) (some (.blit false)))
    | none, _ => emit (.declZero (cty o ty) (localName x))
    return { env with vars := (x, v) :: env.vars }
  | .assign l r =>
    let cr ← expr r
    let (cl, _, _) ← place l
    emit (.assign cl cr)
    return env
  | .ite c t e =>
    let cc ← expr c
    let ct ← collect (block t)
    let ce ← collect (block e)
    emit (.ite cc ct ce)
    return env
  | .forRange x w lo hi body =>
    let w := w.getD .w32
    let T : CTy := .uint w.bits
    let clo ← expr lo
    let chi ← expr hi
    let tl ← fresh
    let th ← fresh
    let inner : Env := { env with vars := (x, { ty := .int w, c := .var (localName x) }) :: env.vars }
    let cb ← withReader (fun _ => inner) (collect (block body))
    emit (.block [.decl T tl (some clo), .decl T th (some chi), .forUp T (localName x) (.var tl) (.var th) cb])
    return env
  | .loop n body =>
    let w := counterTy n
    let k ← fresh
    let cb ← collect (block body)
    emit (.forUp (.uint w.bits) k (litC w 0) (.lit n (suffix w)) cb)
    return env
  | .brk => emit .brk; return env
  | .ret none => emit (.ret none); return env
  | .ret (some e) => emit (.ret (some (← expr e))); return env
  | .call dst f args =>
    let some fd := env.prog.fn? f | err s!"unknown function {f}"
    let mut cargs := #[]
    for (prm, a) in fd.params.zip args do
      cargs := cargs.push (← if prm.byRef then refArg a else expr a)
    let call := CExpr.call (o.fnName f) cargs.toList
    assignResult dst call ((fd.ret.map (cty o)).getD .void)
    return env
  | .eff dst e args =>
    let cargs ← args.mapM expr
    let call := CExpr.call (effectCall e) cargs
    assignResult dst call ((e.sig.2.map (cty o)).getD .void)
    return env

end

/-! ## Unused names

`-Wall -Wextra` warns about locals and parameters that are never read,
and `-Werror` turns that into an error.  Folding (below) can remove the
only read of a name, so every parameter and local gets a `(void)x;`. -/

partial def lhsReads : Expr → List String
  | .index b i => Check.exprVars i ++ lhsReads b
  | .field b _ => lhsReads b
  | _ => []

partial def readVars (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s.core with
    | .decl _ _ (some e) => Check.exprVars e
    | .assign l r => lhsReads l ++ Check.exprVars r
    | .ite c t e => Check.exprVars c ++ readVars t ++ readVars e
    | .forRange i _ lo hi b => i :: Check.exprVars lo ++ Check.exprVars hi ++ readVars b
    | .loop _ b => readVars b
    | .ret (some e) => Check.exprVars e
    | .call d _ as | .eff d _ as => (d.map lhsReads).getD [] ++ as.flatMap Check.exprVars
    | _ => []

partial def declared (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s.core with
    | .decl x _ _ => [x]
    | .ite _ t e => declared t ++ declared e
    | .forRange _ _ _ _ b | .loop _ b => declared b
    | _ => []

/-- Insert `(void)v_x;` after the declaration of each unread local. -/
partial def voidUnread (unread : List String) : List CStmt → List CStmt
  | [] => []
  | s :: rest =>
    let rest' := voidUnread unread rest
    match s with
    | .decl _ x _ | .declZero _ x =>
      if unread.contains (x.drop 2).toString then s :: .expr (.cast .void (.var x)) :: rest' else s :: rest'
    | .ite c t e => .ite c (voidUnread unread t) (voidUnread unread e) :: rest'
    | .forUp t i lo hi b => .forUp t i lo hi (voidUnread unread b) :: rest'
    | .block b => .block (voidUnread unread b) :: rest'
    | s => s :: rest'

def compileFn (p : Prog) (o : Opts) (f : Fn) : Except String CFn := do
  let mut vars := []
  let mut params := []
  for prm in f.params do
    let ct := cty o prm.ty
    match prm.ty, prm.byRef with
    | .arr el _, true =>
      params := params ++ [(CTy.ptr (cty o el), localName prm.name)]
      vars := (prm.name, { ty := prm.ty, c := .var (localName prm.name) : VarInfo }) :: vars
    | .record _, true =>
      params := params ++ [(CTy.ptr ct, localName prm.name)]
      vars := (prm.name, { ty := prm.ty, c := .var (localName prm.name), ptr := true : VarInfo }) :: vars
    | _, _ =>
      params := params ++ [(ct, localName prm.name)]
      vars := (prm.name, { ty := prm.ty, c := .var (localName prm.name) : VarInfo }) :: vars
  let env : Env := { prog := p, opts := o, fn := f.name, vars }
  let ((), st) ← ((block f.body).run env).run {}
  let lineDir := if o.lines && f.span.line > 0 then [CStmt.line f.span.line f.span.file] else []
  -- folding can remove the only read of a name, so every parameter and
  -- local is marked used
  let unreadParams := f.params.map (·.name)
  let unreadLocals := declared f.body
  let voids := unreadParams.map fun x => CStmt.expr (.cast .void (.var (localName x)))
  return { name := o.fnName f.name, ret := (f.ret.map (cty o)).getD .void, params, static := false,
           body := lineDir ++ voids ++ voidUnread unreadLocals st.out.toList }

/-- Compile a checked program. -/
def compile (p : Prog) (o : Opts := {}) : Except String CUnit := do
  let structs := p.structs.map fun sd => (o.structName sd.name, sd.fields.map fun (f, t) => (cty o t, f))
  let globals := p.globals.map fun g =>
    let init : Option (List CExpr) := match g.ty, g.init with
      | _, [] => none
      | .int w, [v] => some [litC w v]
      | .bool, [v] => some [.blit (v != 0)]
      | .arr (.int w) _, vs => some (vs.map (litC w))
      | .arr .bool _, vs => some (vs.map fun v => .blit (v != 0))
      | _, _ => none
    ({ ty := cty o g.ty, name := o.globalName g.name, const := g.const, static := false, init } : CGlobal)
  let fns ← p.fns.mapM (compileFn p o)
  let entry : CFn := { name := o.entryName, ret := .void, params := [], static := false,
                       body := [.expr (.call (o.fnName p.entry) [])] }
  let header := [s!"/* generated by Ember (Ember.C.Compile) for profile {o.profile.name}; do not edit */",
    "#include \"ember_rt.h\"", ""]
  return { header, structs, globals, fns := fns ++ [entry] }

/-- The names of a program's drop reasons and notes, as C tables. -/
def tables (p : Prog) (o : Opts) : String :=
  let tbl (n : String) (xs : List String) :=
    s!"const char *const {o.namePrefix}{n}[] = " ++ "{" ++ ", ".intercalate ((if xs.isEmpty then [""] else xs).map fun s => s!"\"{escape s}\"") ++ "};\n" ++
    s!"const unsigned {o.namePrefix}{n}_count = {xs.length}u;\n"
  s!"extern const char *const {o.namePrefix}drop_names[];\nextern const unsigned {o.namePrefix}drop_names_count;\n" ++
  s!"extern const char *const {o.namePrefix}note_names[];\nextern const unsigned {o.namePrefix}note_names_count;\n" ++
  tbl "drop_names" p.dropReasons ++ tbl "note_names" p.notes

/-- The program table the host harness runs (`harness -p K`): one entry
per program prefix. -/
def glue (prefixes : List String) : String :=
  let decls := prefixes.map fun p =>
    s!"extern void {p}entry(void);\nextern const char *const {p}drop_names[];\nextern const unsigned {p}drop_names_count;\n" ++
    s!"extern const char *const {p}note_names[];\nextern const unsigned {p}note_names_count;"
  let rows := prefixes.map fun p =>
    "  {" ++ s!"{p}entry, {p}drop_names, &{p}drop_names_count, {p}note_names, &{p}note_names_count" ++ "}"
  "/* generated by Ember: program table for the host harness */\n#include \"ember_rt.h\"\n" ++
  "typedef struct { void (*entry)(void); const char *const *drops; const unsigned *ndrops;\n" ++
  "                 const char *const *notes; const unsigned *nnotes; } ember_prog;\n" ++
  "\n".intercalate decls ++ "\nextern const ember_prog ember_progs[];\nextern const unsigned ember_nprogs;\n" ++
  "const ember_prog ember_progs[] = {\n" ++ ",\n".intercalate rows ++ "\n};\n" ++
  s!"const unsigned ember_nprogs = {prefixes.length}u;\n"

/-- Check, compile and print a program as one C translation unit. -/
def emitC (p : Prog) (o : Opts := {}) : Except String String := do
  let p ← match p.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let u ← compile p o
  return u.print ++ "\n" ++ tables p o

end Ember.C
