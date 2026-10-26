import Ember.Lang.Eval

/-!
# Ember.Lang.Sem — the semantics as total functions (plan M5.4)

`Ember.Lang.Eval` is the interpreter: fast, with a store of cells and
`partial` loops, which the kernel cannot unfold.  This file gives the
same semantics in the form proofs need:

* `evalE`: an expression's value — a function by structural recursion,
  `none` when an index is out of range;
* `execS`/`execB`/`callF`: statements, blocks and calls by recursion on
  fuel (a loop iteration, a block and a call each take one unit), with a
  three-way result: finished, trapped, or out of fuel;
* variables are an association list, innermost first; a by-reference
  argument is copied in and copied back.  Ember's rules (two references
  of a call do not overlap, a function does not use a global it is
  handed) make that the same as passing the address.

Nothing here is proved equal to the interpreter: the two are run against
each other on the random programs of `Lang.Gen` and on the stack with
the corpus (`Tests/Ember/LangTests.lean`), which is the same kind of
evidence as for the emitted C.

`Ember/Proof/Refine.lean` executes Ember functions symbolically with
these definitions.
-/

namespace Ember.Lang.Sem
open Ember.Trace

abbrev Env := List (String × Val)

structure St where
  globals : Env
  world : World
  deriving Inhabited

def lookup (st : St) (env : Env) (x : String) : Option Val :=
  match env.lookup x with
  | some v => some v
  | none => st.globals.lookup x

/-- Replace the first binding of `x`. -/
def setFirst : Env → String → Val → Env
  | [], _, _ => []
  | (y, w) :: rest, x, v => if y == x then (y, v) :: rest else (y, w) :: setFirst rest x v

def fieldIndex (p : Prog) (r f : String) : Option Nat :=
  match p.struct? r with
  | some sd => sd.fields.findIdx? (·.1 == f)
  | none => none

def binop (op : BinOp) (a b : Val) : Option Val :=
  match op, a, b with
  | .land, .bool x, .bool y => some (.bool (x && y))
  | .lor, .bool x, .bool y => some (.bool (x || y))
  | .eq, .bool x, .bool y => some (.bool (x == y))
  | .ne, .bool x, .bool y => some (.bool (x != y))
  | .add, .int w x, .int _ y => some (.int w (mask w (x + y)))
  | .sub, .int w x, .int _ y => some (.int w (mask w (x - y)))
  | .mul, .int w x, .int _ y => some (.int w (mask w (x * y)))
  | .div, .int w x, .int _ y => some (.int w (mask w (if y == 0 then 0 else x / y)))
  | .mod, .int w x, .int _ y => some (.int w (mask w (if y == 0 then 0 else x % y)))
  | .band, .int w x, .int _ y => some (.int w (mask w (x &&& y)))
  | .bor, .int w x, .int _ y => some (.int w (mask w (x ||| y)))
  | .bxor, .int w x, .int _ y => some (.int w (mask w (x ^^^ y)))
  | .shl, .int w x, .int _ y => some (.int w (mask w (if y.toNat ≥ w.bits then 0 else x <<< y)))
  | .shr, .int w x, .int _ y => some (.int w (mask w (if y.toNat ≥ w.bits then 0 else x >>> y)))
  | .eq, .int _ x, .int _ y => some (.bool (x == y))
  | .ne, .int _ x, .int _ y => some (.bool (x != y))
  | .lt, .int _ x, .int _ y => some (.bool (x < y))
  | .le, .int _ x, .int _ y => some (.bool (x ≤ y))
  | .gt, .int _ x, .int _ y => some (.bool (x > y))
  | .ge, .int _ x, .int _ y => some (.bool (x ≥ y))
  | _, _, _ => none

/-- The value of an expression; `none` is a trap (an index out of range). -/
def evalE (p : Prog) (st : St) (env : Env) : Expr → Option Val
  | .lit v (some w) => some (.int w (mask w (UInt64.ofNat v)))
  | .lit _ none => none
  | .blit b => some (.bool b)
  | .var x => lookup st env x
  | .field e f =>
    match evalE p st env e with
    | some (.record r fs) =>
      match fieldIndex p r f with
      | some i => fs[i]?
      | none => none
    | _ => none
  | .index e i =>
    match evalE p st env e, evalE p st env i with
    | some (.arr xs), some iv => xs[iv.toNat]?
    | _, _ => none
  | .bin op a b =>
    match evalE p st env a, evalE p st env b with
    | some x, some y => binop op x y
    | _, _ => none
  | .un op a =>
    match op, evalE p st env a with
    | .lnot, some (.bool b) => some (.bool !b)
    | .bnot, some (.int w v) => some (.int w (mask w (~~~ v)))
    | .neg, some (.int w v) => some (.int w (mask w (0 - v)))
    | _, _ => none
  | .cast w a =>
    match evalE p st env a with
    | some (.int _ v) => some (.int w (mask w v))
    | some (.bool b) => some (.int w (if b then 1 else 0))
    | _ => none
  | .cond c a b =>
    match evalE p st env c, evalE p st env a, evalE p st env b with
    | some cv, some x, some y => some (if cv.toBool then x else y)
    | _, _, _ => none

/-- Change the value at a place: `f` maps the old value to the new one. -/
def update (p : Prog) (st : St) (env : Env) : Expr → (Val → Option Val) → Option (St × Env)
  | .var x, f =>
    match env.lookup x with
    | some old =>
      match f old with
      | some v => some (st, setFirst env x v)
      | none => none
    | none =>
      match st.globals.lookup x with
      | some old =>
        match f old with
        | some v => some ({ st with globals := setFirst st.globals x v }, env)
        | none => none
      | none => none
  | .field e fld, f =>
    update p st env e fun
      | .record r fs =>
        match fieldIndex p r fld with
        | some i =>
          match fs[i]? with
          | some old =>
            match f old with
            | some v => some (.record r (fs.set! i v))
            | none => none
          | none => none
        | none => none
      | _ => none
  | .index e i, f =>
    match evalE p st env i with
    | some iv =>
      update p st env e fun
        | .arr xs =>
          match xs[iv.toNat]? with
          | some old =>
            match f old with
            | some v => some (.arr (xs.set! iv.toNat v))
            | none => none
          | none => none
        | _ => none
    | none => none
  | _, _ => none

def assign (p : Prog) (st : St) (env : Env) (lhs : Expr) (v : Val) : Option (St × Env) :=
  update p st env lhs fun _ => some v

inductive Out where
  | normal | brk | ret (v : Option Val)
  deriving Inhabited

/-- How a statement ends: normally (with the state, the variables and
whether a `break` or `return` is under way), in a trap (the events so far
are in the state), or without an answer because the fuel ran out. -/
inductive Res where
  | ok (st : St) (env : Env) (o : Out)
  | trap (st : St)
  | fuel
  deriving Inhabited

def effect (p : Prog) (st : St) (e : Effect) (vs : List Val) : Option Val × St :=
  let w := st.world
  let set' (w : World) : St := { st with world := w }
  match e with
  | .inputNext | .ringPop =>
    let r := w.next
    (some (.int .w16 r.1.toUInt64), set' r.2)
  | .inputFrame =>
    let r := w.nextFramed
    (some (.int .w16 r.1.toUInt64), set' r.2)
  | .outByte => (none, set' { w with frame := w.frame.push ((vs.headD (.bool false)).toNat.toUInt8) })
  | .outEnd => (none, set' { (w.emit (.tx w.frame)) with frame := .empty })
  | .drop =>
    let k := (vs.headD (.bool false)).toNat
    (none, set' (w.emit (.drop (p.dropReasons.getD k s!"code-{k}"))))
  | .note =>
    let k := (vs.headD (.bool false)).toNat
    (none, set' (w.emit (.note s!"{p.notes.getD k s!"note-{k}"} {(vs.getD 1 (.bool false)).toNat}")))
  | .mmioRead32 =>
    (some (.int .w32 ((w.mmio.get? (vs.headD (.bool false)).toNat.toUInt32).getD 0).toUInt64), st)
  | .mmioWrite32 =>
    (none, set' { w with mmio := w.mmio.insert (vs.headD (.bool false)).toNat.toUInt32
                                                (vs.getD 1 (.bool false)).toNat.toUInt32 })

/-- Values of a list of expressions; `none` when one traps. -/
def evalArgs (p : Prog) (st : St) (env : Env) : List Expr → Option (List Val)
  | [] => some []
  | e :: es =>
    match evalE p st env e, evalArgs p st env es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Copy the final values of the by-reference parameters back to the
caller's places. -/
def copyBack (p : Prog) (callee : Env) : List Param → List Expr → St → Env → Option (St × Env)
  | prm :: ps, a :: as, st, env =>
    if prm.byRef then
      match callee.lookup prm.name with
      | some v =>
        match assign p st env a v with
        | some (st', env') => copyBack p callee ps as st' env'
        | none => none
      | none => none
    else copyBack p callee ps as st env
  | _, _, st, env => some (st, env)

/-- Store a call's or an effect's result. -/
def storeResult (p : Prog) (st : St) (env : Env) (dst : Option Expr) (r : Option Val) : Res :=
  match dst, r with
  | some d, some v =>
    match assign p st env d v with
    | some (st', env') => .ok st' env' .normal
    | none => .trap st
  | _, _ => .ok st env .normal

mutual

/-- A block: the variables it declares end with it. -/
def execB : Nat → Prog → St → Env → List Stmt → Res
  | 0, _, _, _, _ => .fuel
  | n + 1, p, st, env, ss =>
    match execL n p st env ss with
    | .ok st' env' o => .ok st' (env'.drop (env'.length - env.length)) o
    | r => r

/-- Statements in sequence, in one scope. -/
def execL : Nat → Prog → St → Env → List Stmt → Res
  | 0, _, _, _, _ => .fuel
  | _ + 1, _, st, env, [] => .ok st env .normal
  | n + 1, p, st, env, s :: rest =>
    match execS n p st env s with
    | .ok st' env' .normal => execL n p st' env' rest
    | r => r

def execS : Nat → Prog → St → Env → Stmt → Res
  | 0, _, _, _, _ => .fuel
  | n + 1, p, st, env, s =>
    match s with
    | .at _ s => execS n p st env s
    | .decl x ty init =>
      match init with
      | some e =>
        match evalE p st env e with
        | some v => .ok st ((x, v) :: env) .normal
        | none => .trap st
      | none => .ok st ((x, zeroOf p ty) :: env) .normal
    | .assign l r =>
      match evalE p st env r with
      | some v =>
        match assign p st env l v with
        | some (st', env') => .ok st' env' .normal
        | none => .trap st
      | none => .trap st
    | .ite c t e =>
      match evalE p st env c with
      | some cv => if cv.toBool then execB n p st env t else execB n p st env e
      | none => .trap st
    | .forRange x w lo hi body =>
      match evalE p st env lo, evalE p st env hi with
      | some a, some b =>
        match forLoop n p st ((x, .int (w.getD .w32) (UInt64.ofNat a.toNat)) :: env) x (w.getD .w32)
                a.toNat b.toNat body with
        | .ok st' env' o => .ok st' (env'.drop 1) o
        | r => r
      | _, _ => .trap st
    | .loop max body => loopN n p st env max body
    | .brk => .ok st env .brk
    | .ret none => .ok st env (.ret none)
    | .ret (some e) =>
      match evalE p st env e with
      | some v => .ok st env (.ret (some v))
      | none => .trap st
    | .call dst f args =>
      match p.fn? f with
      | some fd =>
        match evalArgs p st env args with
        | some vs =>
          match execB n p st ((fd.params.map (·.name)).zip vs) fd.body with
          | .ok st' cenv o =>
            match copyBack p cenv fd.params args st' env with
            | some (st'', env'') =>
              storeResult p st'' env'' dst (match o with | .ret v => v | _ => none)
            | none => .trap st'
          | r => r
        | none => .trap st
      | none => .trap st
    | .eff dst e args =>
      match evalArgs p st env args with
      | some vs =>
        let r := effect p st e vs
        storeResult p r.2 env dst r.1
      | none => .trap st

/-- `for`: the counter (the first variable) runs from `cur` to `hi`. -/
def forLoop : Nat → Prog → St → Env → String → Width → Nat → Nat → List Stmt → Res
  | 0, _, _, _, _, _, _, _, _ => .fuel
  | n + 1, p, st, env, x, w, cur, hi, body =>
    if cur < hi then
      match execB n p st (setFirst env x (.int w (UInt64.ofNat cur))) body with
      | .ok st' env' .normal => forLoop n p st' env' x w (cur + 1) hi body
      | .ok st' env' .brk => .ok st' env' .normal
      | r => r
    else .ok st env .normal

/-- `loop (max := k)`. -/
def loopN : Nat → Prog → St → Env → Nat → List Stmt → Res
  | 0, _, _, _, _, _ => .fuel
  | _ + 1, _, st, env, 0, _ => .ok st env .normal
  | n + 1, p, st, env, k + 1, body =>
    match execB n p st env body with
    | .ok st' env' .normal => loopN n p st' env' k body
    | .ok st' env' .brk => .ok st' env' .normal
    | r => r

end

/-- The result of calling a function with values (no by-reference
parameters): its result and the state after. -/
inductive CallRes where
  | ok (v : Option Val) (st : St)
  | trap (st : St)
  | fuel
  deriving Inhabited

def call (fuel : Nat) (p : Prog) (st : St) (f : String) (args : List Val) : CallRes :=
  match p.fn? f with
  | some fd =>
    match execB fuel p st ((fd.params.map (·.name)).zip args) fd.body with
    | .ok st' _ (.ret v) => .ok v st'
    | .ok st' _ _ => .ok none st'
    | .trap st' => .trap st'
    | .fuel => .fuel
  | none => .trap st

/-- The state a program starts in. -/
def initial (p : Prog) (inputs : Array Input) : St :=
  { globals := p.globals.map fun g => (g.name, initOf p g), world := { inputs, framed := p.framed } }

/-- The driver of `Lang.runMachine`, on this semantics: the trace. -/
def run (p : Prog) (inputs : Array Input) (header : Header := { impl := "sem" }) (fuel : Nat := 100000) :
    Trace := Id.run do
  let mut st := initial p inputs
  let mut idle := 0
  let mut trapped := false
  while !st.world.normalize.done && idle < 3 do
    let before := (st.world.pos, st.world.off)
    match call fuel p st p.entry [] with
    | .ok _ st' => st := st'
    | .trap st' => st := st'; trapped := true; break
    | .fuel => trapped := true; break
    idle := if (st.world.pos, st.world.off) == before then idle + 1 else 0
  let w := st.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    lines := lines.push ⟨i, match w.inputs[i]! with | .rx b => .rx b | .tick => .tick⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  if trapped then lines := lines.push ⟨w.cur, .note "trap (sem)"⟩
  return { header, lines }

end Ember.Lang.Sem
