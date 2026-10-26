import Ember.Lang.Types
import Ember.Lang.Eval
import Ember.Lang.Sem
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

/-- The name of temporary number `k`. -/
def tmpName (k : Nat) : String := "t" ++ toString k

def fresh : CM String := do
  let st ← get
  set { st with tmp := st.tmp + 1 }
  return tmpName st.tmp

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

def opTy (o : Opts) (w : Width) : CTy :=
  if o.profile.promotes w then .unsigned else .uint w.bits

def err (msg : String) : CM α := do throw s!"{(← read).fn}: {msg}"

/-- What only reads the environment, as a compiler action. -/
def pureE (m : Env → Except String α) : CM α := fun e cs =>
  match m e with
  | .ok a => .ok (a, cs)
  | .error msg => .error msg

def Env.err (e : Env) (msg : String) : Except String α := .error s!"{e.fn}: {msg}"

def Env.varInfo (e : Env) (x : String) : Except String VarInfo :=
  match e.vars.lookup x with
  | some v => .ok v
  | none =>
    match e.prog.global? x with
    | some g => .ok { ty := g.ty, c := .var (e.opts.globalName x) }
    | none => e.err s!"unknown variable {x}"

def Env.fieldTy (e : Env) (r f : String) : Except String Ty :=
  match e.prog.struct? r with
  | some sd =>
    match sd.fields.lookup f with
    | some t => .ok t
    | none => e.err s!"no field {f}"
  | none => e.err s!"unknown record {r}"

def varInfo (x : String) : CM VarInfo := pureE (·.varInfo x)

def fieldTy (r f : String) : CM Ty := pureE (·.fieldTy r f)

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

/-- The value of an expression without variables, by the semantics
(`Ember.Lang.Sem.evalE` with no variable in scope). -/
def closedVal (e : Expr) : Option Val :=
  Sem.evalE { fns := [] } { globals := [], world := { inputs := #[] } } [] e

def suffix (w : Width) : String :=
  match w with
  | .w8 | .w16 => "u"
  | .w32 => "UL"
  | .w64 => "ULL"

def litC (w : Width) (n : Nat) : CExpr := .cast (.uint w.bits) (.lit n (suffix w))

/-- The constant a closed scalar expression (not itself a literal) is emitted as. -/
def closedConst (e : Expr) : Option CExpr :=
  match e with
  | .lit _ _ | .blit _ => none
  | _ =>
    match closedVal e with
    | some (.int w v) => some (litC w v.toNat)
    | some (.bool b) => some (.blit b)
    | _ => none

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

/-- Type of an expression of a checked program. -/
def Env.tyOf (g : Env) : Expr → Except String Ty
  | .lit _ (some w) => .ok (.int w)
  | .lit _ none => g.err "untyped literal (program not checked)"
  | .blit _ => .ok .bool
  | .var x =>
    match g.varInfo x with
    | .ok v => .ok v.ty
    | .error m => .error m
  | .field b f =>
    match g.tyOf b with
    | .ok (.record r) => g.fieldTy r f
    | .ok _ => g.err "field of a non-record"
    | .error m => .error m
  | .index b _ =>
    match g.tyOf b with
    | .ok (.arr el _) => .ok el
    | .ok _ => g.err "index of a non-array"
    | .error m => .error m
  | .bin op a _ => if op.isCompare || op.isLogic then .ok .bool else g.tyOf a
  | .un _ a => g.tyOf a
  | .cast w _ => .ok (.int w)
  | .cond _ a _ => g.tyOf a

def tyOf (e : Expr) : CM Ty := pureE (·.tyOf e)

/-- The place of a variable: its C lvalue, type, and whether it is a record pointer. -/
def placeVar (x : String) : CM (CExpr × Ty × Bool) := do
  let v ← varInfo x
  return (v.c, v.ty, v.ptr)

/-- The field `f` of the place `r`. -/
def placeField (r : CExpr × Ty × Bool) (f : String) : CM (CExpr × Ty × Bool) := do
  let (c, t, ptr) := r
  let .record rn := t | err "field of a non-record"
  return (if ptr then .arrow c f else .dot c f, ← fieldTy rn f, false)

/-- The index is in `[0, n)` by its form: a literal below `n`, or a `u8` into at least 256 elements. -/
def indexSafe (i : Expr) (iw : Width) (n : Nat) : Bool :=
  match i with
  | .lit v _ => v < n
  | _ => iw == .w8 && n ≥ 256

/-- The element of the place `r` at index `i` (of width `iw`, compiled to
`ic`): the bounds check is emitted unless the index is in range by its
form. -/
def placeIndex (r : CExpr × Ty × Bool) (i : Expr) (iw : Width) (ic : CExpr) : CM (CExpr × Ty × Bool) := do
  let (c, t, _) := r
  let .arr el n := t | err "index of a non-array"
  if indexSafe i iw n then return (.index c ic, el, false)
  let t ← fresh
  emit (.decl (.uint iw.bits) t (some ic))
  emit (.ite (.bin ">=" (.var t) (.lit n (suffix iw)))
    [.expr (.call "ember_trap" [.str (← trapMsg s!"index out of bounds [0, {n})")])] [])
  return (.index c (.var t), el, false)

/-- The width of an index expression. -/
def Env.indexWidth (g : Env) (i : Expr) : Except String Width :=
  match g.tyOf i with
  | .ok (.int w) => .ok w
  | .ok _ => g.err "non-integer index"
  | .error m => .error m

def indexWidth (i : Expr) : CM Width := pureE (·.indexWidth i)

/-! ### Operators, given the compiled operands -/

/-- A comparison that the C front end could decide: between identical
operands (-Wtautological-compare), or by the operand type's range
(-Wtype-limits). -/
def cmpFold (op : BinOp) (ta : Ty) (ca cb : CExpr) : Option Bool :=
  if ca.same cb then some (op == .eq || op == .le || op == .ge)
  else
    match ta with
    | .int w =>
      match ca.litVal?, cb.litVal? with
      | none, some c => decide op (w.modulus - 1) c false
      | some c, none => decide op (w.modulus - 1) c true
      | _, _ => none
    | _ => none

def cmpSym (op : BinOp) : String :=
  match op with
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | _ => ">="

def cmpC (o : Opts) (op : BinOp) (ta : Ty) (ca cb : CExpr) : CM CExpr :=
  match cmpFold op ta ca cb with
  | some r => pure (.blit r)
  | none => do
    let x ← hide (cty o ta) ca
    let y ← hide (cty o ta) cb
    pure (.bin (cmpSym op) x y)

/-- `(T)((U)a op (U)b)`: the operation in the profile's operation type, truncated. -/
def arithE (o : Opts) (w : Width) (sym : String) (ca cb : CExpr) : CExpr :=
  .cast (.uint w.bits) (.bin sym (.cast (opTy o w) ca) (.cast (opTy o w) cb))

def divC (o : Opts) (isDiv : Bool) (w : Width) (ca cb : CExpr) : CM CExpr :=
  let sym := if isDiv then "/" else "%"
  -- a divisor that came out as a literal (a closed expression, or
  -- one that folded on the way, like `x / 0`) needs no guard, and
  -- `… / 0` in the dead arm of a guard is an error to SDCC
  match cb.litVal? with
  | some v => pure (if v == 0 then litC w 0 else arithE o w sym ca cb)
  | none =>
    -- SDCC 4.6 moves a guarded `a / d` out of a loop, above its
    -- guard, and its `__divulong`/`__modulong` do not return for
    -- `d = 0`: there the guard lives in a helper (`C.Print`)
    if o.profile == .sdccZ80 then
      pure (.call s!"ember_{if isDiv then "div" else "mod"}{w.bits}" [ca, cb])
    else do
      let d ← hide (.uint w.bits) cb
      pure (.cast (.uint w.bits) (.cond (.bin "==" d (.lit 0 (suffix w))) (litC w 0) (arithE o w sym ca d)))

/-- `(T)((U)a << s)` -/
def shiftE (o : Opts) (w : Width) (sym : String) (ca s : CExpr) : CExpr :=
  .cast (.uint w.bits) (.bin sym (.cast (opTy o w) ca) s)

def shiftC (o : Opts) (isShl : Bool) (w sw : Width) (ca cb : CExpr) : CM CExpr :=
  let sym := if isShl then "<<" else ">>"
  match cb.litVal? with
  | some v => pure (if v ≥ w.bits then litC w 0 else shiftE o w sym ca cb)
  | none => do
    let s ← hide (.uint sw.bits) cb
    -- an amount type that cannot reach w needs no guard
    pure (if sw.modulus ≤ w.bits then shiftE o w sym ca s
      else .cast (.uint w.bits) (.cond (.bin ">=" s (.lit w.bits (suffix sw))) (litC w 0) (shiftE o w sym ca s)))

/-- A binary operator on the compiled operands `ca`, `cb` (`ta`: the type of the left one). -/
def binC (o : Opts) (op : BinOp) (ta : Ty) (b : Expr) (ca cb : CExpr) : CM CExpr :=
  if op.isLogic then pure (.bin (if op == .land then "&&" else "||") ca cb)
  else if op.isCompare then cmpC o op ta ca cb
  else
    match ta with
    | .int w =>
      match op with
      | .add =>
        pure (if o.bugDropCast then .bin "+" (.cast (opTy o w) ca) (.cast (opTy o w) cb) else arithE o w "+" ca cb)
      | .sub => pure (arithE o w "-" ca cb)
      | .mul => pure (arithE o w "*" ca cb)
      | .band => pure (arithE o w "&" ca cb)
      | .bor => pure (arithE o w "|" ca cb)
      | .bxor => pure (arithE o w "^" ca cb)
      | .div => divC o true w ca cb
      | .mod => divC o false w ca cb
      | .shl => do
        let tb ← tyOf b
        match tb with
        | .int sw => shiftC o true w sw ca cb
        | _ => err "shift amount"
      | .shr => do
        let tb ← tyOf b
        match tb with
        | .int sw => shiftC o false w sw ca cb
        | _ => err "shift amount"
      | _ => err "bad operator"
    | _ => err "bad operand type"

def unC (o : Opts) (op : UnOp) (ta : Ty) (ca : CExpr) : CM CExpr :=
  match op, ta with
  | .lnot, _ => pure (.un "!" ca)
  | .bnot, .int w => pure (.cast (.uint w.bits) (.un "~" (.cast (opTy o w) ca)))
  | .neg, .int w => pure (.cast (.uint w.bits) (.bin "-" (.lit 0 "u") (.cast (opTy o w) ca)))
  | _, _ => err "bad unary operand"

def castC (w : Width) (ta : Ty) (ca : CExpr) : CExpr :=
  match ta with
  -- bool → int as a choice: casting a comparison and operating on it
  -- trips -Wbool-operation
  | .bool => .cast (.uint w.bits) (.cond ca (.lit 1 (suffix w)) (.lit 0 (suffix w)))
  | _ => .cast (.uint w.bits) ca

def condC (ta : Ty) (cc ca cb : CExpr) : CExpr :=
  match ta with
  | .int w => .cast (.uint w.bits) (.cond cc ca cb)
  | _ => .cond cc ca cb

mutual

/-- A place: its C lvalue, type, and whether it is a record pointer. -/
def place (e : Expr) : CM (CExpr × Ty × Bool) := do
  match e with
  | .var x => placeVar x
  | .field b f => placeField (← place b) f
  | .index b i =>
    let r ← place b
    -- the type of `b` first: an index into a non-array is reported before anything is emitted
    let (_, t, _) := r
    let .arr _ _ := t | err "index of a non-array"
    let iw ← indexWidth i
    let ic ← expr i
    placeIndex r i iw ic
  | _ => err "not a place"

def expr (e : Expr) : CM CExpr := do
  let o := (← read).opts
  if let some c := closedConst e then return c
  match e with
  | .lit v (some w) => return litC w v
  | .lit _ none => err "untyped literal"
  | .blit b => return .blit b
  | .var x => return (← placeVar x).1
  | .field b f => return (← placeField (← place b) f).1
  | .index b i =>
    let r ← place b
    let (_, t, _) := r
    let .arr _ _ := t | err "index of a non-array"
    let iw ← indexWidth i
    let ic ← expr i
    return (← placeIndex r i iw ic).1
  | .bin op a b =>
    let ta ← tyOf a
    let ca ← expr a
    let cb ← expr b
    binC o op ta b ca cb
  | .un op a =>
    let ca ← expr a
    unC o op (← tyOf a) ca
  | .cast w a =>
    let ca ← expr a
    return castC w (← tyOf a) ca
  | .cond c a b =>
    let cc ← expr c
    let ca ← expr a
    let cb ← expr b
    return condC (← tyOf a) cc ca cb

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
  | .inputFrame => "ember_input_frame"

def withIdx (i : Nat) (m : CM α) : CM α :=
  withReader (fun e => { e with path := e.path ++ [i] }) m

/-- Does the place read a variable to find its storage (an index that is not a literal)? -/
def readsIndex : Expr → Bool
  | .index b i => (match i with | .lit _ _ => false | _ => true) || readsIndex b
  | .field b _ => readsIndex b
  | _ => false

/-- Store the result of a call.  The destination is evaluated *after*
the call, as the interpreter does: when its index is checked, the call
goes to a temporary first, so its effects precede a trap.  So it does
when the destination has an unchecked index that is not a literal and
the callee is an Ember function (`fnCall`): C does not order the
evaluation of `a[i]` against the call in `a[i] = f();`, and `f` may
change `i` (found by `Ember.C.Sem`). -/
def assignResult (dst : Option Expr) (call : CExpr) (t : CTy) (fnCall : Bool := false) : CM Unit := do
  match dst with
  | none => emit (.expr call)
  | some d =>
    let saved ← get
    let (cd, _, _) ← place d
    if (← get).out.size == saved.out.size && !(fnCall && readsIndex d) then
      emit (.assign cd call)
    else
      -- again, after the call: the checks of the destination follow the result
      set saved
      let x ← fresh
      emit (.decl t x (some call))
      let (cd, _, _) ← place d
      emit (.assign cd (.var x))

/-- The C arguments of a call, in order. -/
def callArgs : List Param → List Expr → CM (List CExpr)
  | prm :: ps, a :: as => do
    let c ← if prm.byRef then refArg a else expr a
    return c :: (← callArgs ps as)
  | _, _ => pure []

def exprs : List Expr → CM (List CExpr)
  | [] => pure []
  | e :: es => do
    let c ← expr e
    return c :: (← exprs es)

mutual

/-- Compile the statements of a block from number `i` on, in the
environment `env` (each statement yields the environment of the next). -/
def blockFrom (base : List Nat) (i : Nat) (env : Env) : List Stmt → CM Unit
  | [] => pure ()
  | s :: rest => do
    let env' ← withReader (fun _ => { env with path := base ++ [i] }) (stmt s)
    blockFrom base (i + 1) { env' with path := base } rest

/-- Compile one statement; returns the environment for what follows. -/
def stmt (s : Stmt) : CM Env := do
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
    let ct ← collect (blockFrom env.path 1 env t)
    let ce ← collect (blockFrom env.path 1 env e)
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
    let cb ← collect (blockFrom inner.path 1 inner body)
    emit (.block [.decl T tl (some clo), .decl T th (some chi), .forUp T (localName x) (.var tl) (.var th) cb])
    return env
  | .loop n body =>
    let w := counterTy n
    let k ← fresh
    let cb ← collect (blockFrom env.path 1 env body)
    emit (.forUp (.uint w.bits) k (litC w 0) (.lit n (suffix w)) cb)
    return env
  | .brk => emit .brk; return env
  | .ret none => emit (.ret none); return env
  | .ret (some e) => emit (.ret (some (← expr e))); return env
  | .call dst f args =>
    let some fd := env.prog.fn? f | err s!"unknown function {f}"
    let cargs ← callArgs fd.params args
    let call := CExpr.call (o.fnName f) cargs
    assignResult dst call ((fd.ret.map (cty o)).getD .void) (fnCall := true)
    return env
  | .eff dst e args =>
    let cargs ← exprs args
    let call := CExpr.call (effectCall e) cargs
    assignResult dst call ((e.sig.2.map (cty o)).getD .void)
    return env

end

/-- Compile a block (in the environment being read). -/
def block (ss : List Stmt) : CM Unit := do
  let env ← read
  blockFrom env.path 1 env ss

/-! ## Unused names

`-Wall -Wextra` warns about locals and parameters that are never read,
and `-Werror` turns that into an error.  Folding can remove the only
read of a name, so every parameter and local gets a `(void)x;`. -/

mutual
/-- The locals a statement declares, at any depth. -/
def declaredS : Stmt → List String
  | .at _ s => declaredS s
  | .decl x _ _ => [x]
  | .ite _ t e => declared t ++ declared e
  | .forRange _ _ _ _ b => declared b
  | .loop _ b => declared b
  | _ => []
def declared : List Stmt → List String
  | [] => []
  | s :: rest => declaredS s ++ declared rest
end

mutual
/-- Insert `(void)v_x;` after the declaration of each local in `unread`. -/
def voidUnreadS (unread : List String) : CStmt → List CStmt
  | .decl t x i =>
    if unread.contains (x.drop 2).toString then [.decl t x i, .expr (.cast .void (.var x))] else [.decl t x i]
  | .declZero t x =>
    if unread.contains (x.drop 2).toString then [.declZero t x, .expr (.cast .void (.var x))] else [.declZero t x]
  | .ite c t e => [.ite c (voidUnread unread t) (voidUnread unread e)]
  | .forUp t i lo hi b => [.forUp t i lo hi (voidUnread unread b)]
  | .block b => [.block (voidUnread unread b)]
  | s => [s]
def voidUnread (unread : List String) : List CStmt → List CStmt
  | [] => []
  | s :: rest => voidUnreadS unread s ++ voidUnread unread rest
end

/-- A parameter in C: a by-reference array or record is a pointer. -/
def paramC (o : Opts) (prm : Param) : CTy × String :=
  match prm.ty, prm.byRef with
  | .arr el _, true => (.ptr (cty o el), localName prm.name)
  | .record _, true => (.ptr (cty o prm.ty), localName prm.name)
  | _, _ => (cty o prm.ty, localName prm.name)

/-- A parameter as the emitter sees it in the body. -/
def paramVar (prm : Param) : String × VarInfo :=
  match prm.ty, prm.byRef with
  | .record _, true => (prm.name, { ty := prm.ty, c := .var (localName prm.name), ptr := true })
  | _, _ => (prm.name, { ty := prm.ty, c := .var (localName prm.name) })

/-- The environment a function's body is compiled in. -/
def fnEnv (p : Prog) (o : Opts) (f : Fn) : Env :=
  { prog := p, opts := o, fn := f.name, vars := f.params.map paramVar }

def compileFn (p : Prog) (o : Opts) (f : Fn) : Except String CFn :=
  match ((block f.body).run (fnEnv p o f)).run {} with
  | .error e => .error e
  | .ok ((), st) =>
    let lineDir := if o.lines && f.span.line > 0 then [CStmt.line f.span.line f.span.file] else []
    -- folding can remove the only read of a name, so every parameter and
    -- local is marked used
    let voids := f.params.map fun prm => CStmt.expr (.cast .void (.var (localName prm.name)))
    .ok { name := o.fnName f.name, ret := (f.ret.map (cty o)).getD .void, params := f.params.map (paramC o),
          static := false, body := lineDir ++ voids ++ voidUnread (declared f.body) st.out.toList }

/-- A record definition in C. -/
def structC (o : Opts) (sd : StructDef) : String × List (CTy × String) :=
  (o.structName sd.name, sd.fields.map fun (f, t) => (cty o t, f))

/-- The initialiser of a global, when it has one that is not all zeros by default. -/
def globalInit (g : Global) : Option (List CExpr) :=
  match g.ty, g.init with
  | _, [] => none
  | .int w, [v] => some [litC w v]
  | .bool, [v] => some [.blit (v != 0)]
  | .arr (.int w) _, vs => some (vs.map (litC w))
  | .arr .bool _, vs => some (vs.map fun v => .blit (v != 0))
  | _, _ => none

def globalC (o : Opts) (g : Global) : CGlobal :=
  { ty := cty o g.ty, name := o.globalName g.name, const := g.const, static := false, init := globalInit g }

/-- What the driver calls. -/
def entryFn (p : Prog) (o : Opts) : CFn :=
  { name := o.entryName, ret := .void, params := [], static := false,
    body := [.expr (.call (o.fnName p.entry) [])] }

/-- Compile a checked program. -/
def compile (p : Prog) (o : Opts := {}) : Except String CUnit :=
  match p.fns.mapM (compileFn p o) with
  | .error e => .error e
  | .ok fns =>
    .ok { header := [s!"/* generated by Ember (Ember.C.Compile) for profile {o.profile.name}; do not edit */",
            "#include \"ember_rt.h\"", ""],
          structs := p.structs.map (structC o), globals := p.globals.map (globalC o),
          fns := fns ++ [entryFn p o] }

/-- The names of a program's drop reasons and notes, as C tables. -/
def tables (p : Prog) (o : Opts) : String :=
  let tbl (n : String) (xs : List String) :=
    s!"const char *const {o.namePrefix}{n}[] = " ++ "{" ++ ", ".intercalate ((if xs.isEmpty then [""] else xs).map fun s => s!"\"{escape s}\"") ++ "};\n" ++
    s!"const unsigned {o.namePrefix}{n}_count = {xs.length}u;\n"
  -- a build that prints no names (a target without trace) leaves them out
  "#ifndef EMBER_NO_NAMES\n" ++
  s!"extern const char *const {o.namePrefix}drop_names[];\nextern const unsigned {o.namePrefix}drop_names_count;\n" ++
  s!"extern const char *const {o.namePrefix}note_names[];\nextern const unsigned {o.namePrefix}note_names_count;\n" ++
  tbl "drop_names" p.dropReasons ++ tbl "note_names" p.notes ++
  -- for the host harness: does the program read frame by frame?
  s!"extern const unsigned {o.namePrefix}framed;\nconst unsigned {o.namePrefix}framed = {if p.framed then 1 else 0}u;\n" ++
  "#endif\n"

/-- The program table the host harness runs (`harness -p K`): one entry
per program prefix. -/
def glue (prefixes : List String) : String :=
  let decls := prefixes.map fun p =>
    s!"extern void {p}entry(void);\nextern const char *const {p}drop_names[];\nextern const unsigned {p}drop_names_count;\n" ++
    s!"extern const char *const {p}note_names[];\nextern const unsigned {p}note_names_count;\n" ++
    s!"extern const unsigned {p}framed;"
  let rows := prefixes.map fun p =>
    "  {" ++ s!"{p}entry, {p}drop_names, &{p}drop_names_count, {p}note_names, &{p}note_names_count, &{p}framed" ++ "}"
  "/* generated by Ember: program table for the host harness */\n#include \"ember_rt.h\"\n" ++
  "typedef struct { void (*entry)(void); const char *const *drops; const unsigned *ndrops;\n" ++
  "                 const char *const *notes; const unsigned *nnotes; const unsigned *framed; } ember_prog;\n" ++
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
