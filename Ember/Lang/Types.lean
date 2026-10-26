import Ember.Lang.Syntax

/-!
# Ember.Lang.Types — the type checker (M2.2)

`check : Prog → Except Err Prog` validates a program and returns it
*elaborated*: every literal carries its width and every `for` loop its
counter width, so the interpreter and the emitter never guess.

Rules (each has a positive and a negative test in `Tests.Ember.LangTests`):

* operands of arithmetic, bitwise and comparison operators have the same
  width (a literal takes the width of the other operand; a shift amount
  may have any width); `&&`, `||`, `!` and conditions are `bool`;
* literals fit their width; a literal array index lies within the array;
* names are unique within a function and do not shadow globals;
* only scalar places are assigned; constants and `for` counters are
  read-only;
* arrays and records are passed only by reference, and the references of
  one call never overlap; a reference to a global is never passed to a
  function that (transitively) uses that global by name;
* the call graph is acyclic (no recursion), so stack depth is static;
* every path of a function with a result returns one;
* `break` only inside a loop; loop bounds are positive.
-/

namespace Ember.Lang

structure Err where
  span : Span
  fn   : String
  msg  : String
  deriving Inhabited, Repr

def Err.toString (e : Err) : String :=
  s!"{e.span.toString}: in {if e.fn.isEmpty then "program" else "fn " ++ e.fn}: {e.msg}"

instance : ToString Err := ⟨Err.toString⟩

namespace Check

structure Local where
  ty       : Ty
  readOnly : Bool := false
  byRef    : Bool := false

structure Ctx where
  prog   : Prog
  fn     : String := ""
  ret    : Option Ty := none
  inLoop : Bool := false
  span   : Span := {}

structure St where
  /-- Visible locals, innermost first. -/
  scope : List (String × Local) := []
  /-- Every name declared in the function so far (uniqueness). -/
  seen  : List String := []

abbrev M := ReaderT Ctx (StateT St (Except Err))

def err (msg : String) : M α := do
  let c ← read
  throw { span := c.span, fn := c.fn, msg }

def lookup (x : String) : M (Ty × Bool) := do
  if let some l := (← get).scope.lookup x then return (l.ty, l.readOnly)
  match (← read).prog.global? x with
  | some g => return (g.ty, g.const)
  | none => err s!"unknown variable '{x}'"

def fieldTy (r : String) (f : String) : M Ty := do
  let some sd := (← read).prog.struct? r | err s!"unknown record type '{r}'"
  match sd.fields.lookup f with
  | some t => return t
  | none => err s!"record '{r}' has no field '{f}'"

def isUntypedLit : Expr → Bool
  | .lit _ none => true
  | _ => false

def fits (v : Nat) (w : Width) : Bool := v < w.modulus

/-- Narrowest width holding `v`. -/
def widthFor (v : Nat) : Width :=
  if v < 256 then .w8 else if v < 65536 then .w16 else if v < 2^32 then .w32 else .w64

def wantInt (t : Ty) (what : String) : M Width := do
  match t with
  | .int w => return w
  | _ => err s!"{what} must be an integer, not {t}"

def wantScalar (t : Ty) (what : String) : M Unit := do
  unless t.isScalar do err s!"{what} must be a scalar, not {t} (arrays and records are passed by reference only)"

mutual

partial def infer (e : Expr) (expect : Option Ty) : M (Expr × Ty) := do
  match e with
  | .lit v (some w) =>
    unless fits v w do err s!"literal {v} does not fit {w.name}"
    return (e, .int w)
  | .lit v none =>
    match expect with
    | some (.int w) =>
      unless fits v w do err s!"literal {v} does not fit {w.name}"
      return (.lit v (some w), .int w)
    | some t => err s!"literal {v} where {t} is expected"
    | none => err s!"cannot infer the width of literal {v}; write ({v} : u8) or similar"
  | .blit _ => return (e, .bool)
  | .var x => return (e, (← lookup x).1)
  | .field b f =>
    let (b', bt) ← infer b none
    match bt with
    | .record r => return (.field b' f, ← fieldTy r f)
    | t => err s!"field '{f}' of a non-record ({t})"
  | .index b i =>
    let (b', bt) ← infer b none
    match bt with
    | .arr el n =>
      let (i', it) ← match i with
        | .lit v none => pure (Expr.lit v (some (widthFor (max v (n - 1)))), Ty.int (widthFor (max v (n - 1))))
        | _ => infer i none
      discard <| wantInt it "an array index"
      if let .lit v _ := i' then
        unless v < n do err s!"index {v} out of bounds [0, {n})"
      return (.index b' i', el)
    | t => err s!"indexing a non-array ({t})"
  | .bin op a b =>
    if op.isLogic then
      let a' ← checkAgainst a .bool
      let b' ← checkAgainst b .bool
      return (.bin op a' b', .bool)
    if op.isShift then
      let (a', aty) ← infer a expect
      let w ← wantInt aty s!"the left operand of {op.symbol}"
      let b' ← match b with
        | .lit v none => pure (Expr.lit v (some (widthFor v)))
        | _ => do
          let (b', bt) ← infer b none
          discard <| wantInt bt s!"a shift amount"
          pure b'
      return (.bin op a' b', .int w)
    let ex := if op.isCompare then none else expect
    let (a', b', t) ← unify a b ex op.symbol
    if op.isCompare then
      match t with
      | .bool => unless op == .eq || op == .ne do err s!"{op.symbol} on bool"
      | .int _ => pure ()
      | t => err s!"{op.symbol} on {t}"
      return (.bin op a' b', .bool)
    let _ ← wantInt t s!"operands of {op.symbol}"
    return (.bin op a' b', t)
  | .un op a =>
    match op with
    | .lnot => return (.un op (← checkAgainst a .bool), .bool)
    | _ =>
      let (a', t) ← infer a expect
      discard <| wantInt t s!"the operand of {if op == .neg then "-" else "~~~"}"
      return (.un op a', t)
  | .cast w a =>
    match a with
    | .lit v none =>
      unless fits v w do err s!"literal {v} does not fit {w.name}"
      return (.lit v (some w), .int w)
    | _ =>
      -- `(if c then 1 else 2 : u8)`: literals inside a cast that cannot
      -- be inferred otherwise take the cast's width
      let (a', t) ← tryCatch (infer a none) fun _ => infer a (some (.int w))
      match t with
      | .int _ | .bool => return (.cast w a', .int w)
      | t => err s!"cannot cast {t} to {w.name}"
  | .cond c a b =>
    let c' ← checkAgainst c .bool
    let (a', b', t) ← unify a b expect "if-then-else"
    wantScalar t "a branch of if-then-else"
    return (.cond c' a' b', t)

/-- Infer two operands that must have the same type; an untyped literal
takes the type of the other side. -/
partial def unify (a b : Expr) (expect : Option Ty) (what : String) : M (Expr × Expr × Ty) := do
  if isUntypedLit a && !isUntypedLit b then
    let (b', bt) ← infer b expect
    let a' ← checkAgainst a bt
    return (a', b', bt)
  let (a', aty) ← infer a expect
  let (b', bty) ← infer b (some aty)
  unless bty == aty do err s!"operands of {what} have different types ({aty} and {bty}); cast one"
  wantScalar aty s!"operands of {what}"
  return (a', b', aty)

partial def checkAgainst (e : Expr) (t : Ty) : M Expr := do
  let (e', t') ← infer e (some t)
  unless t' == t do err s!"expected {t}, got {t'}"
  return e'

end

partial def isPlace : Expr → Bool
  | .var _ => true
  | .field b _ => isPlace b
  | .index b _ => isPlace b
  | _ => false

/-- The variable a place is rooted at. -/
partial def root : Expr → Option String
  | .var x => some x
  | .field b _ => root b
  | .index b _ => root b
  | _ => none

/-- Path of a reference argument: root and fields (no indexing). -/
partial def refPath : Expr → Option (List String)
  | .var x => some [x]
  | .field b f => (refPath b).map (· ++ [f])
  | _ => none

def declare (x : String) (l : Local) : M Unit := do
  let s ← get
  if s.seen.contains x then err s!"'{x}' is declared twice in this function"
  if ((← read).prog.global? x).isSome then err s!"local '{x}' shadows a global"
  set { s with scope := (x, l) :: s.scope, seen := x :: s.seen }

def checkTy (t : Ty) : M Unit := do
  match t with
  | .int _ | .bool => pure ()
  | .arr el n =>
    unless el.isScalar do err s!"array elements must be scalars, not {el}"
    unless n > 0 do err "arrays have at least one element"
  | .record r => unless ((← read).prog.struct? r).isSome do err s!"unknown record type '{r}'"

/-- Run `m` in a nested scope: names declared inside are not visible after. -/
def inScope (m : M α) : M α := do
  let saved := (← get).scope
  let r ← m
  modify fun s => { s with scope := saved }
  return r

def checkDst (dst : Option Expr) (ret : Option Ty) (what : String) : M (Option Expr) := do
  match dst, ret with
  | none, _ => return none
  | some _, none => err s!"{what} returns nothing"
  | some d, some t =>
    unless isPlace d do err s!"the result of {what} must go to a variable, field or element"
    let (d', dt) ← infer d none
    unless dt == t do err s!"{what} returns {t}, assigned to {dt}"
    let some r := root d | err "bad destination"
    if (← lookup r).2 then err s!"'{r}' is read-only"
    return some d'

mutual

partial def stmt (s : Stmt) : M Stmt := do
  match s with
  | .at sp s => return .at sp (← withReader (fun c => { c with span := sp }) (stmt s))
  | .decl x ty init =>
    checkTy ty
    let init' ← match init with
      | none => pure none
      | some e =>
        wantScalar ty s!"an initialised local ('{x}')"
        pure (some (← checkAgainst e ty))
    declare x { ty }
    return .decl x ty init'
  | .assign lhs rhs =>
    unless isPlace lhs do err "the left side of := must be a variable, field or element"
    let (lhs', t) ← infer lhs none
    wantScalar t "an assigned value"
    let some r := root lhs | err "bad assignment"
    if (← lookup r).2 then err s!"'{r}' is read-only"
    return .assign lhs' (← checkAgainst rhs t)
  | .ite c t e =>
    let c' ← checkAgainst c .bool
    return .ite c' (← inScope (block t)) (← inScope (block e))
  | .forRange i w lo hi body =>
    let w' ← match w with
      | some w => pure w
      | none =>
        match lo, hi with
        | .lit a none, .lit b none => pure (widthFor (max a b))
        | _, _ =>
          let (_, _, t) ← unify lo hi none "for-loop bounds"
          wantInt t "for-loop bounds"
    let lo' ← checkAgainst lo (.int w')
    let hi' ← checkAgainst hi (.int w')
    inScope do
      declare i { ty := .int w', readOnly := true }
      let b ← withReader (fun c => { c with inLoop := true }) (block body)
      return .forRange i (some w') lo' hi' b
  | .loop n body =>
    unless n > 0 do err "loop (max := 0)"
    return .loop n (← inScope (withReader (fun c => { c with inLoop := true }) (block body)))
  | .brk =>
    unless (← read).inLoop do err "break outside a loop"
    return .brk
  | .ret e =>
    match e, (← read).ret with
    | none, none => return .ret none
    | some e, some t => return .ret (some (← checkAgainst e t))
    | none, some t => err s!"return without a value in a function returning {t}"
    | some _, none => err "return with a value in a function returning nothing"
  | .call dst f args =>
    let p := (← read).prog
    let some fd := p.fn? f | err s!"unknown function '{f}'"
    unless fd.params.length == args.length do
      err s!"{f} takes {fd.params.length} argument(s), {args.length} given"
    let mut args' := #[]
    let mut refs : Array (List String) := #[]
    for (prm, a) in fd.params.zip args do
      if prm.byRef then
        let some path := refPath a | err s!"argument '{prm.name}' of {f} is by reference: pass a variable or field"
        let (a', aty) ← infer a none
        unless aty == prm.ty do err s!"argument '{prm.name}' of {f}: expected {prm.ty}, got {aty}"
        if (← lookup path.head!).2 then err s!"'{path.head!}' is read-only and cannot be passed by reference"
        for q in refs do
          if q.isPrefixOf path || path.isPrefixOf q then
            err s!"references '{".".intercalate q}' and '{".".intercalate path}' overlap in the call to {f}"
        refs := refs.push path
        args' := args'.push a'
      else
        args' := args'.push (← checkAgainst a prm.ty)
    return .call (← checkDst dst fd.ret f) f args'.toList
  | .eff dst e args =>
    let (ps, ret) := e.sig
    unless ps.length == args.length do err s!"{e.name} takes {ps.length} argument(s)"
    let args' ← (ps.zip args).mapM fun (t, a) => checkAgainst a t
    return .eff (← checkDst dst ret e.name) e args'

partial def block (ss : List Stmt) : M (List Stmt) := ss.mapM stmt

end

/-- Definitely returns on every path. -/
partial def returns : List Stmt → Bool
  | [] => false
  | ss => ss.any fun s => match s.core with
    | .ret _ => true
    | .ite _ t e => returns t && returns e
    | _ => false

/-! ## Whole-program checks -/

/-- Functions called by a statement list. -/
partial def calls (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s.core with
    | .call _ f _ => [f]
    | .ite _ t e => calls t ++ calls e
    | .forRange _ _ _ _ b | .loop _ b => calls b
    | _ => []

partial def exprVars : Expr → List String
  | .var x => [x]
  | .field b _ => exprVars b
  | .index b i => exprVars b ++ exprVars i
  | .bin _ a b => exprVars a ++ exprVars b
  | .un _ a | .cast _ a => exprVars a
  | .cond c a b => exprVars c ++ exprVars a ++ exprVars b
  | _ => []

/-- Names used by a statement list (globals among them). -/
partial def stmtVars (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s.core with
    | .decl _ _ (some e) => exprVars e
    | .assign l r => exprVars l ++ exprVars r
    | .ite c t e => exprVars c ++ stmtVars t ++ stmtVars e
    | .forRange _ _ lo hi b => exprVars lo ++ exprVars hi ++ stmtVars b
    | .loop _ b => stmtVars b
    | .ret (some e) => exprVars e
    | .call d _ as | .eff d _ as => (d.map exprVars).getD [] ++ as.flatMap exprVars
    | _ => []

/-- Call sites: (dst, callee, args) of a statement list. -/
partial def callSites (ss : List Stmt) : List (String × List Expr) :=
  ss.flatMap fun s => match s.core with
    | .call _ f as => [(f, as)]
    | .ite _ t e => callSites t ++ callSites e
    | .forRange _ _ _ _ b | .loop _ b => callSites b
    | _ => []

def topErr (msg : String) (fn := "") (span : Span := {}) : Except Err α := throw { span, fn, msg }

/-- Topological order of the call graph (callees first); error on a cycle. -/
partial def callOrder (p : Prog) : Except Err (List String) := do
  let rec visit (f : String) (stack : List String) (done : List String) : Except Err (List String) := do
    if done.contains f then return done
    if stack.contains f then
      let cyc := (f :: stack).reverse.dropWhile (· != f)
      topErr s!"recursion: {" → ".intercalate cyc}" f (((p.fn? f).map (·.span)).getD {})
    let some fd := p.fn? f | return done
    let mut d := done
    for g in calls fd.body do d ← visit g (f :: stack) d
    return d ++ [f]
  let mut done := []
  for f in p.fns do done ← visit f.name [] done
  return done

def unique (what : String) (xs : List String) : Except Err Unit := do
  let mut seen : List String := []
  for x in xs do
    if seen.contains x then topErr s!"{what} '{x}' is defined twice"
    seen := x :: seen

def checkFn (p : Prog) (f : Fn) : Except Err Fn := do
  let ctx : Ctx := { prog := p, fn := f.name, ret := f.ret, span := f.span }
  let body : M (List Stmt) := do
    for prm in f.params do
      checkTy prm.ty
      if !prm.ty.isScalar && !prm.byRef then err s!"parameter '{prm.name}' of type {prm.ty} must be 'ref'"
      if prm.ty.isScalar && prm.byRef then err s!"parameter '{prm.name}': scalars are passed by value"
      declare prm.name { ty := prm.ty, byRef := prm.byRef }
    if let some t := f.ret then wantScalar t "a function result"
    block f.body
  let body' ← (body.run ctx).run' {}
  if f.ret.isSome && !returns body' then
    topErr "not every path returns a value" f.name f.span
  return { f with body := body' }

/-- Globals a function uses by name, directly or through its callees. -/
def globalUse (p : Prog) (order : List String) : List (String × List String) := Id.run do
  let gs := p.globals.map (·.name)
  let mut acc : List (String × List String) := []
  for f in order do
    let some fd := p.fn? f | continue
    let params := fd.params.map (·.name)
    let direct := (stmtVars fd.body).filter fun x => gs.contains x && !params.contains x
    let viaCallees := (calls fd.body).flatMap fun g => (acc.lookup g).getD []
    acc := (f, (direct ++ viaCallees).eraseDups) :: acc
  return acc

/-- Global roots that may be bound to each reference parameter. -/
def refRoots (p : Prog) (order : List String) : List ((String × String) × List String) := Id.run do
  let gs := p.globals.map (·.name)
  let mut acc : List ((String × String) × List String) := []
  -- callers before callees
  for f in order.reverse do
    let some fd := p.fn? f | continue
    for (g, args) in callSites fd.body do
      let some gd := p.fn? g | continue
      for (prm, a) in gd.params.zip args do
        if !prm.byRef then continue
        let some r := root a | continue
        let new := if gs.contains r then [r] else (acc.lookup (f, r)).getD []
        let old := (acc.lookup (g, prm.name)).getD []
        acc := ((g, prm.name), (old ++ new).eraseDups) :: acc.filter (·.1 != (g, prm.name))
  return acc

def check (p : Prog) : Except Err Prog := do
  unique "function" (p.fns.map (·.name))
  unique "global" (p.globals.map (·.name))
  unique "record type" (p.structs.map (·.name))
  for sd in p.structs do
    unique s!"field of {sd.name}" (sd.fields.map (·.1))
    for (fld, t) in sd.fields do
      match t with
      | .int _ | .bool => pure ()
      | .arr el n => unless el.isScalar && n > 0 do topErr s!"field {sd.name}.{fld}: arrays of scalars only"
      | .record _ => topErr s!"field {sd.name}.{fld}: records do not nest"
  for g in p.globals do
    match g.ty with
    | .int w => unless g.init.length ≤ 1 && g.init.all (fits · w) do topErr s!"initialiser of global {g.name}"
    | .bool => unless g.init.all (· ≤ 1) do topErr s!"initialiser of global {g.name}"
    | .arr (.int w) n => unless g.init.length ≤ n && g.init.all (fits · w) do topErr s!"initialiser of global {g.name}"
    | .arr .bool n => unless g.init.length ≤ n && g.init.all (· ≤ 1) do topErr s!"initialiser of global {g.name}"
    | .arr t _ => topErr s!"global {g.name}: arrays of {t} are not supported"
    | .record r =>
      unless (p.struct? r).isSome do topErr s!"global {g.name}: unknown record type '{r}'"
      unless g.init.isEmpty do topErr s!"global {g.name}: records start zeroed"
  let some e := p.fn? p.entry | topErr s!"entry function '{p.entry}' not defined"
  unless e.params.isEmpty && e.ret.isNone do topErr "the entry function takes no arguments and returns nothing" e.name
  let order ← callOrder p
  let fns ← p.fns.mapM (checkFn p)
  let p' := { p with fns }
  -- references to globals never reach a function that uses the global by name
  let uses := globalUse p' order
  for ((f, prm), roots) in refRoots p' order do
    let used := (uses.lookup f).getD []
    for r in roots do
      if used.contains r then
        topErr s!"global '{r}' is passed by reference as '{prm}' but {f} (or a function it calls) also uses it by name" f
          (((p'.fn? f).map (·.span)).getD {})
  return p'

end Check

/-- Type-check and elaborate a program. -/
def Prog.check (p : Prog) : Except Err Prog := Check.check p

end Ember.Lang
