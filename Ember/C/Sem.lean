import Ember.C.Ast
import Ember.Lang.Eval
import Ember.Lang.Profile

/-!
# Ember.C.Sem — a semantics for the C subset the emitter produces (plan M5.7)

Total functions, in the style of `Ember.Lang.Sem`: expressions by
structural recursion, statements by recursion on fuel.  A program has a
meaning here only where C gives it one and where that meaning does not
depend on a signed type:

* integers are unsigned values with a width; `unsigned` is as wide as
  the profile's `int`.  An arithmetic or bitwise operation whose
  converted operands are narrower than `int` would be done in *signed*
  `int` by C's integer promotions: it has no meaning here (`none`).
  Comparisons are of values, which is what C computes for non-negative
  operands whatever the promotion;
* a shift by the width of its (converted) left operand or more, a
  division by zero, an index outside its array, a read of something that
  is not there: no meaning.  `c ? a : b`, `&&` and `||` evaluate only
  what C evaluates;
* a by-reference argument is a pointer: a location (a global or a local
  of a suspended caller, and a path into it).  Reads and writes through
  it act on that storage, so aliasing is modelled, not assumed away;
* `l = f(…)`: C does not order the evaluation of `l` against the call.
  The statement has a meaning only if `l` names the same location before
  and after the call;
* an assignment converts to the type of the destination, which is read
  off the value stored there (declarations convert to their type, so
  stored values always have the width of their declaration);
* `ember_trap` ends the program (`Res.trap`); the other `ember_*`
  functions are the effects of `Ember.Lang`, on the same `World`.

So "the emitted C has no undefined behaviour" is the statement that
running it never yields `Res.undef`; `Tests/Ember/LangTests.lean` runs
the emitted C of the examples, of random programs and of the stack under
this semantics against `Ember.Lang.Sem`, for every profile.

Not modelled: the conditional's result type when its arms differ in
type (the emitter gives both arms one type), `const`, integer literals
that do not fit the type of their suffix, anything the emitter does not
produce.
-/

namespace Ember.C.Sem
open Ember.Lang (World)
open Ember.Trace

inductive Base where
  | global (g : String)
  /-- A local of the frame at `depth` (0: the entry function's). -/
  | frame (depth : Nat) (x : String)
  deriving Inhabited, DecidableEq, Repr

/-- A storage location: a variable and a path into it (array indices and field numbers). -/
structure Loc where
  base : Base
  path : List Nat := []
  deriving Inhabited, DecidableEq, Repr

inductive CVal where
  | int (bits : Nat) (v : Nat)
  | bool (b : Bool)
  | arr (xs : Array CVal)
  | strct (name : String) (fs : Array CVal)
  | ptr (l : Loc)
  deriving Inhabited, BEq, Repr

abbrev Env := List (String × CVal)

/-- A translation unit with what its meaning depends on. -/
structure CProg where
  unit : CUnit
  /-- Width of `int` and `unsigned`. -/
  intBits : Nat
  /-- Width of `unsigned long` (the type of a `UL` literal). -/
  longBits : Nat
  entry : String
  dropReasons : List String := []
  notes : List String := []
  deriving Inhabited

structure St where
  globals : Env
  /-- The frames of the suspended callers, innermost first. -/
  stack : List Env := []
  world : World
  deriving Inhabited

def setFirst : Env → String → CVal → Env
  | [], _, _ => []
  | (y, w) :: rest, x, v => if y == x then (y, v) :: rest else (y, w) :: setFirst rest x v

/-! ## Locations -/

def getPath : CVal → List Nat → Option CVal
  | v, [] => some v
  | .arr xs, i :: r =>
    match xs[i]? with
    | some x => getPath x r
    | none => none
  | .strct _ fs, i :: r =>
    match fs[i]? with
    | some x => getPath x r
    | none => none
  | _, _ :: _ => none

def setPath : CVal → List Nat → CVal → Option CVal
  | _, [], x => some x
  | .arr xs, i :: r, x =>
    match xs[i]? with
    | some old =>
      match setPath old r x with
      | some new => some (.arr (xs.set! i new))
      | none => none
    | none => none
  | .strct n fs, i :: r, x =>
    match fs[i]? with
    | some old =>
      match setPath old r x with
      | some new => some (.strct n (fs.set! i new))
      | none => none
    | none => none
  | _, _ :: _, _ => none

def readBase (st : St) (env : Env) : Base → Option CVal
  | .global g => st.globals.lookup g
  | .frame d x =>
    if d = st.stack.length then env.lookup x
    else
      match st.stack[st.stack.length - 1 - d]? with
      | some fr => fr.lookup x
      | none => none

def read (st : St) (env : Env) (l : Loc) : Option CVal :=
  match readBase st env l.base with
  | some v => getPath v l.path
  | none => none

def writeBase (st : St) (env : Env) (b : Base) (v : CVal) : St × Env :=
  match b with
  | .global g => ({ st with globals := setFirst st.globals g v }, env)
  | .frame d x =>
    if d = st.stack.length then (st, setFirst env x v)
    else
      let k := st.stack.length - 1 - d
      ({ st with stack := st.stack.modify k fun fr => setFirst fr x v }, env)

def write (st : St) (env : Env) (l : Loc) (v : CVal) : Option (St × Env) :=
  match readBase st env l.base with
  | some old =>
    match setPath old l.path v with
    | some new => some (writeBase st env l.base new)
    | none => none
  | none => none

/-! ## Types and conversions -/

def fieldIdx (cp : CProg) (s f : String) : Option Nat :=
  match cp.unit.structs.lookup s with
  | some fs => fs.findIdx? (·.2 == f)
  | none => none

/-- `(T)v` for a scalar type. -/
def castTo (cp : CProg) (t : CTy) (v : CVal) : Option CVal :=
  match t, v with
  | .uint n, .int _ x => some (.int n (x % 2 ^ n))
  | .uint n, .bool b => some (.int n (if b then 1 else 0))
  | .unsigned, .int _ x => some (.int cp.intBits (x % 2 ^ cp.intBits))
  | .unsigned, .bool b => some (.int cp.intBits (if b then 1 else 0))
  | .bool, .bool b => some (.bool b)
  | .bool, .int _ x => some (.bool (x != 0))
  | _, _ => none

/-- The conversion of an initialiser, an argument or a result to the declared type. -/
def convTo (cp : CProg) (t : CTy) (v : CVal) : Option CVal :=
  match t with
  | .uint _ | .unsigned | .bool => castTo cp t v
  | _ => some v

/-- The conversion of an assigned value to the type of what is stored. -/
def convLike (old v : CVal) : Option CVal :=
  match old, v with
  | .int n _, .int _ x => some (.int n (x % 2 ^ n))
  | .int n _, .bool b => some (.int n (if b then 1 else 0))
  | .bool _, .bool b => some (.bool b)
  | .bool _, .int _ x => some (.bool (x != 0))
  | .arr _, .arr xs => some (.arr xs)
  | .strct _ _, .strct n fs => some (.strct n fs)
  | _, _ => none

/-- `{0}` for a type without records. -/
def zero0 (cp : CProg) : CTy → CVal
  | .uint n => .int n 0
  | .unsigned => .int cp.intBits 0
  | .bool => .bool false
  | .arr t n => .arr (Array.replicate n (zero0 cp t))
  | _ => .bool false

def zero (cp : CProg) (t : CTy) : CVal :=
  match t with
  | .strct s => .strct s (((cp.unit.structs.lookup s).getD []).map fun (ft, _) => zero0 cp ft).toArray
  | t => zero0 cp t

def truthy : CVal → Option Bool
  | .bool b => some b
  | .int _ x => some (x != 0)
  | _ => none

def litBits (cp : CProg) (suffix : String) : Option Nat :=
  if suffix == "u" then some cp.intBits
  else if suffix == "UL" then some cp.longBits
  else if suffix == "ULL" then some 64
  else none

/-! ## Operators -/

def isCompare (op : String) : Bool :=
  op == "==" || op == "!=" || op == "<" || op == "<=" || op == ">" || op == ">="

def compare (op : String) (x y : Nat) : Bool :=
  if op == "==" then x == y
  else if op == "!=" then x != y
  else if op == "<" then x < y
  else if op == "<=" then x ≤ y
  else if op == ">" then x > y
  else x ≥ y

/-- `x op y` on unsigned values of `b` bits; `none`: no such operator, or a division by zero. -/
def arith (op : String) (b x y : Nat) : Option Nat :=
  if op == "+" then some ((x + y) % 2 ^ b)
  else if op == "-" then some ((2 ^ b + x - y) % 2 ^ b)
  else if op == "*" then some ((x * y) % 2 ^ b)
  else if op == "&" then some (x &&& y)
  else if op == "|" then some (x ||| y)
  else if op == "^" then some (x ^^^ y)
  else if op == "/" then (if y == 0 then none else some (x / y))
  else if op == "%" then (if y == 0 then none else some (x % y))
  else none

def binop (cp : CProg) (op : String) (a b : CVal) : Option CVal :=
  match a, b with
  | .int ba x, .int bb y =>
    if isCompare op then some (.bool (compare op x y))
    else if op == "<<" then
      if ba < cp.intBits || y ≥ ba then none else some (.int ba ((x <<< y) % 2 ^ ba))
    else if op == ">>" then
      if ba < cp.intBits || y ≥ ba then none else some (.int ba (x >>> y))
    else
      -- the usual arithmetic conversions: the wider of the two unsigned types
      let w := max ba bb
      if w < cp.intBits then none
      else
        match arith op w x y with
        | some r => some (.int w r)
        | none => none
  | .bool x, .bool y =>
    if op == "==" then some (.bool (x == y))
    else if op == "!=" then some (.bool (x != y))
    else none
  | _, _ => none

def unop (cp : CProg) (op : String) (a : CVal) : Option CVal :=
  if op == "!" then
    match truthy a with
    | some b => some (.bool !b)
    | none => none
  else if op == "~" then
    match a with
    | .int b x => if b < cp.intBits then none else some (.int b (2 ^ b - 1 - x))
    | _ => none
  else none

/-- The guarded division helpers of the SDCC profile (`Ember.C.Print`):
`(uintN_t)((d == 0) ? 0 : (a / d))` on `uintN_t` parameters. -/
def helper (f : String) : Option (Nat × Bool) :=
  if f == "ember_div8" then some (8, true) else if f == "ember_mod8" then some (8, false)
  else if f == "ember_div16" then some (16, true) else if f == "ember_mod16" then some (16, false)
  else if f == "ember_div32" then some (32, true) else if f == "ember_mod32" then some (32, false)
  else if f == "ember_div64" then some (64, true) else if f == "ember_mod64" then some (64, false)
  else none

def helperVal (bits : Nat) (div : Bool) (a d : CVal) : Option CVal :=
  match a, d with
  | .int _ x, .int _ y =>
    let x := x % 2 ^ bits
    let y := y % 2 ^ bits
    some (.int bits (if y == 0 then 0 else if div then x / y else x % y))
  | _, _ => none

/-! ## Expressions -/

def idxLoc (st : St) (env : Env) (la : Loc) (i : CVal) : Option Loc :=
  match i with
  | .int _ iv =>
    match read st env la with
    | some (.ptr l) => some { l with path := l.path ++ [iv] }
    | some (.arr _) => some { la with path := la.path ++ [iv] }
    | _ => none
  | _ => none

def dotLoc (cp : CProg) (st : St) (env : Env) (la : Loc) (f : String) : Option Loc :=
  match read st env la with
  | some (.strct s _) =>
    match fieldIdx cp s f with
    | some i => some { la with path := la.path ++ [i] }
    | none => none
  | _ => none

def arrowLoc (cp : CProg) (st : St) (env : Env) (la : Loc) (f : String) : Option Loc :=
  match read st env la with
  | some (.ptr l) => dotLoc cp st env l f
  | _ => none

def varLoc (st : St) (env : Env) (x : String) : Option Loc :=
  if (env.lookup x).isSome then some { base := .frame st.stack.length x }
  else if (st.globals.lookup x).isSome then some { base := .global x }
  else none

mutual

/-- The location an lvalue names. -/
def lval (cp : CProg) (st : St) (env : Env) : CExpr → Option Loc
  | .var x => varLoc st env x
  | .index a i =>
    match lval cp st env a, evalC cp st env i with
    | some la, some iv => idxLoc st env la iv
    | _, _ => none
  | .dot a f =>
    match lval cp st env a with
    | some la => dotLoc cp st env la f
    | none => none
  | .arrow a f =>
    match lval cp st env a with
    | some la => arrowLoc cp st env la f
    | none => none
  | _ => none

/-- The value of an expression; `none`: it has none (see the head of the file). -/
def evalC (cp : CProg) (st : St) (env : Env) : CExpr → Option CVal
  | .var x =>
    match varLoc st env x with
    | some l => read st env l
    | none => none
  | .index a i =>
    match lval cp st env a, evalC cp st env i with
    | some la, some iv =>
      match idxLoc st env la iv with
      | some l => read st env l
      | none => none
    | _, _ => none
  | .dot a f =>
    match lval cp st env a with
    | some la =>
      match dotLoc cp st env la f with
      | some l => read st env l
      | none => none
    | none => none
  | .arrow a f =>
    match lval cp st env a with
    | some la =>
      match arrowLoc cp st env la f with
      | some l => read st env l
      | none => none
    | none => none
  | .lit n s =>
    match litBits cp s with
    | some b => if n < 2 ^ b then some (.int b n) else none
    | none => none
  | .blit b => some (.bool b)
  | .cast t a =>
    match evalC cp st env a with
    | some v => castTo cp t v
    | none => none
  | .cond c a b =>
    match evalC cp st env c with
    | some cv =>
      match truthy cv with
      | some true => evalC cp st env a
      | some false => evalC cp st env b
      | none => none
    | none => none
  | .bin op a b =>
    if op == "&&" then
      match (evalC cp st env a).bind truthy with
      | some true => ((evalC cp st env b).bind truthy).map CVal.bool
      | some false => some (.bool false)
      | none => none
    else if op == "||" then
      match (evalC cp st env a).bind truthy with
      | some false => ((evalC cp st env b).bind truthy).map CVal.bool
      | some true => some (.bool true)
      | none => none
    else
      match evalC cp st env a, evalC cp st env b with
      | some x, some y => binop cp op x y
      | _, _ => none
  | .un op a =>
    match evalC cp st env a with
    | some v => unop cp op v
    | none => none
  | .call f args =>
    match helper f, evalCs cp st env args with
    | some (bits, div), some [x, y] => helperVal bits div x y
    | _, _ => none
  | .addr _ => none
  | .str _ => none

def evalCs (cp : CProg) (st : St) (env : Env) : List CExpr → Option (List CVal)
  | [] => some []
  | e :: es =>
    match evalC cp st env e, evalCs cp st env es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

end

/-! ## Calls -/

/-- The argument for a parameter of pointer type: `&place`, an array
(which decays to the address of its storage), or a pointer handed on. -/
def ptrArg (cp : CProg) (st : St) (env : Env) (a : CExpr) : Option CVal :=
  match a with
  | .addr c =>
    match lval cp st env c with
    | some l => some (.ptr l)
    | none => none
  | c =>
    match lval cp st env c with
    | some l =>
      match read st env l with
      | some (.ptr l') => some (.ptr l')
      | some _ => some (.ptr l)
      | none => none
    | none => none

def argVals (cp : CProg) (st : St) (env : Env) : List (CTy × String) → List CExpr → Option (List CVal)
  | [], [] => some []
  | (t, _) :: ps, a :: as =>
    let v := match t with
      | .ptr _ => ptrArg cp st env a
      | t =>
        match evalC cp st env a with
        | some v => convTo cp t v
        | none => none
    match v, argVals cp st env ps as with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _, _ => none

/-- The runtime's functions: the effects of `Ember.Lang`, on the same world. -/
def effect (cp : CProg) (st : St) (f : String) (vs : List CVal) : Option (Option CVal × St) :=
  let w := st.world
  let set' (w : World) : St := { st with world := w }
  let nat (i : Nat) : Nat := match vs[i]? with
    | some (.int _ x) => x
    | some (.bool b) => if b then 1 else 0
    | _ => 0
  if f == "ember_input_next" || f == "ember_ring_pop" then
    let r := w.next
    some (some (.int 16 r.1.toNat), set' r.2)
  else if f == "ember_input_frame" then
    let r := w.nextFramed
    some (some (.int 16 r.1.toNat), set' r.2)
  else if f == "ember_out_byte" then some (none, set' { w with frame := w.frame.push (nat 0 % 256).toUInt8 })
  else if f == "ember_out_end" then some (none, set' { (w.emit (.tx w.frame)) with frame := .empty })
  else if f == "ember_drop" then
    let k := nat 0 % 256
    some (none, set' (w.emit (.drop (cp.dropReasons.getD k s!"code-{k}"))))
  else if f == "ember_note" then
    let k := nat 0 % 256
    some (none, set' (w.emit (.note s!"{cp.notes.getD k s!"note-{k}"} {nat 1 % 2 ^ 32}")))
  else if f == "ember_mmio_read32" then
    some (some (.int 32 ((w.mmio.get? (nat 0 % 2 ^ 32).toUInt32).getD 0).toNat), st)
  else if f == "ember_mmio_write32" then
    some (none, set' { w with mmio := w.mmio.insert (nat 0 % 2 ^ 32).toUInt32 (nat 1 % 2 ^ 32).toUInt32 })
  else none

inductive Out where
  | normal | brk | ret (v : Option CVal)
  deriving Inhabited

/-- How a statement ends: normally; in `ember_trap`; without a meaning
(undefined behaviour, or outside the subset); out of fuel. -/
inductive Res where
  | ok (st : St) (env : Env) (o : Out)
  | trap (st : St)
  | undef
  | fuel
  deriving Inhabited

/-- A call that is a statement of its own (not a division helper). -/
def asCall : CExpr → Option (String × List CExpr)
  | .call f args => if (helper f).isSome then none else some (f, args)
  | _ => none

mutual

def execB : Nat → CProg → St → Env → List CStmt → Res
  | 0, _, _, _, _ => .fuel
  | n + 1, cp, st, env, ss =>
    match execL n cp st env ss with
    | .ok st' env' o => .ok st' (env'.drop (env'.length - env.length)) o
    | r => r

def execL : Nat → CProg → St → Env → List CStmt → Res
  | 0, _, _, _, _ => .fuel
  | _ + 1, _, st, env, [] => .ok st env .normal
  | n + 1, cp, st, env, s :: rest =>
    match execS n cp st env s with
    | .ok st' env' .normal => execL n cp st' env' rest
    | r => r

/-- `f(args)`: the result (as `Out.ret`) with the caller's frame as the callee left it. -/
def callC : Nat → CProg → St → Env → String → List CExpr → Res
  | 0, _, _, _, _, _ => .fuel
  | n + 1, cp, st, env, f, args =>
    if f == "ember_trap" then .trap st
    else
      match cp.unit.fns.find? (·.name == f) with
      | some fd =>
        match argVals cp st env fd.params args with
        | some vs =>
          match execB n cp { st with stack := env :: st.stack } ((fd.params.map (·.2)).zip vs) fd.body with
          | .ok st' _ o =>
            match st'.stack with
            | env' :: rest =>
              let st'' := { st' with stack := rest }
              match o with
              | .ret (some v) =>
                match convTo cp fd.ret v with
                | some v' => .ok st'' env' (.ret (some v'))
                | none => .undef
              | _ => .ok st'' env' (.ret none)
            | [] => .undef
          | r => r
        | none => .undef
      | none =>
        match evalCs cp st env args with
        | some vs =>
          match effect cp st f vs with
          | some (r, st') => .ok st' env (.ret r)
          | none => .undef
        | none => .undef

def execS : Nat → CProg → St → Env → CStmt → Res
  | 0, _, _, _, _ => .fuel
  | n + 1, cp, st, env, s =>
    match s with
    | .decl _ _ none => .undef
    | .decl t x (some e) =>
      match asCall e with
      | some (f, args) =>
        match callC n cp st env f args with
        | .ok st' env' (.ret (some v)) =>
          match convTo cp t v with
          | some v' => .ok st' ((x, v') :: env') .normal
          | none => .undef
        | .ok _ _ _ => .undef
        | r => r
      | none =>
        match evalC cp st env e with
        | some v =>
          match convTo cp t v with
          | some v' => .ok st ((x, v') :: env) .normal
          | none => .undef
        | none => .undef
    | .declZero t x => .ok st ((x, zero cp t) :: env) .normal
    | .assign l r =>
      match asCall r with
      | some (f, args) =>
        match lval cp st env l with
        | some loc =>
          match callC n cp st env f args with
          | .ok st' env' (.ret (some v)) =>
            -- `l` must name the same storage whether it is evaluated before or after the call
            if lval cp st' env' l = some loc then
              match read st' env' loc with
              | some old =>
                match convLike old v with
                | some v' =>
                  match write st' env' loc v' with
                  | some (st'', env'') => .ok st'' env'' .normal
                  | none => .undef
                | none => .undef
              | none => .undef
            else .undef
          | .ok _ _ _ => .undef
          | r => r
        | none => .undef
      | none =>
        match evalC cp st env r, lval cp st env l with
        | some v, some loc =>
          match read st env loc with
          | some old =>
            match convLike old v with
            | some v' =>
              match write st env loc v' with
              | some (st', env') => .ok st' env' .normal
              | none => .undef
            | none => .undef
          | none => .undef
        | _, _ => .undef
    | .expr e =>
      match asCall e with
      | some (f, args) =>
        match callC n cp st env f args with
        | .ok st' env' _ => .ok st' env' .normal
        | r => r
      | none =>
        match e with
        | .cast .void _ => .ok st env .normal
        | e =>
          match evalC cp st env e with
          | some _ => .ok st env .normal
          | none => .undef
    | .ite c t e =>
      match evalC cp st env c with
      | some cv =>
        match truthy cv with
        | some true => execB n cp st env t
        | some false => execB n cp st env e
        | none => .undef
      | none => .undef
    | .forUp t i lo hi body =>
      match evalC cp st env lo with
      | some v =>
        match convTo cp t v with
        | some v' =>
          match forC n cp st ((i, v') :: env) i hi body with
          | .ok st' env' o => .ok st' (env'.drop 1) o
          | r => r
        | none => .undef
      | none => .undef
    | .brk => .ok st env .brk
    | .ret none => .ok st env (.ret none)
    | .ret (some e) =>
      match evalC cp st env e with
      | some v => .ok st env (.ret (some v))
      | none => .undef
    | .block ss => execB n cp st env ss
    | .line _ _ => .ok st env .normal
    | .comment _ => .ok st env .normal

/-- `for (T i = …; i < hi; i = (T)(i + 1u))` once `i` is declared (the first variable). -/
def forC : Nat → CProg → St → Env → String → CExpr → List CStmt → Res
  | 0, _, _, _, _, _, _ => .fuel
  | n + 1, cp, st, env, i, hi, body =>
    match env.lookup i, evalC cp st env hi with
    | some (.int _ v), some (.int _ h) =>
      if v < h then
        match execB n cp st env body with
        | .ok st' env' .normal =>
          match env'.lookup i with
          | some (.int b v') => forC n cp st' (setFirst env' i (.int b ((v' + 1) % 2 ^ b))) i hi body
          | _ => .undef
        | .ok st' env' .brk => .ok st' env' .normal
        | r => r
      else .ok st env .normal
    | _, _ => .undef

end

/-! ## Programs -/

def initOf (cp : CProg) (g : CGlobal) : CVal :=
  let st0 : St := { globals := [], world := { inputs := #[] } }
  let val (e : CExpr) : Option CVal := evalC cp st0 [] e
  match g.init, g.ty with
  | none, t => zero cp t
  | some es, .arr el n =>
    .arr ((Array.range n).map fun i =>
      match es[i]? with
      | some e => ((val e).bind (convTo cp el)).getD (zero cp el)
      | none => zero cp el)
  | some es, t =>
    match es.head? with
    | some e => ((val e).bind (convTo cp t)).getD (zero cp t)
    | none => zero cp t

def initial (cp : CProg) (inputs : Array Input) (framed : Bool) : St :=
  { globals := cp.unit.globals.map fun g => (g.name, initOf cp g), world := { inputs, framed } }

/-- A unit emitted for `prof`, with the tables of the program it was compiled from. -/
def CProg.ofUnit (u : CUnit) (prof : Ember.Lang.Profile) (entry : String) (dropReasons notes : List String) : CProg :=
  { unit := u, intBits := prof.intBits, longBits := if prof.regBits == 64 then 64 else 32, entry, dropReasons, notes }

/-- The driver of `Ember.Lang.Sem.run`, on this semantics. -/
def run (cp : CProg) (inputs : Array Input) (framed : Bool) (header : Header := { impl := "csem" })
    (fuel : Nat := 100000) : Trace := Id.run do
  let mut st := initial cp inputs framed
  let mut idle := 0
  let mut bad : Option String := none
  while !st.world.normalize.done && idle < 3 do
    let before := (st.world.pos, st.world.off)
    match callC fuel cp st [] cp.entry [] with
    | .ok st' _ _ => st := st'
    | .trap st' => st := st'; bad := some "trap (sem)"; break
    | .undef => bad := some "undefined (C semantics)"; break
    | .fuel => bad := some "trap (sem)"; break
    idle := if (st.world.pos, st.world.off) == before then idle + 1 else 0
  let w := st.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    lines := lines.push ⟨i, match w.inputs[i]! with | .rx b => .rx b | .tick => .tick⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  if let some m := bad then lines := lines.push ⟨w.cur, .note m⟩
  return { header, lines }

end Ember.C.Sem
