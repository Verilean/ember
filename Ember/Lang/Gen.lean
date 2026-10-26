import Ember.Lang.Eval
import Ember.Util.Rand

/-!
# Ember.Lang.Gen — random well-typed programs, and a program shrinker (M2.8)

Programs exercise every construct the emitter handles, at every width:
all operators (shifts by amounts ≥ the width, division by zero), casts
both ways, `if-then-else` expressions, arrays (indices usually reduced
modulo the length, sometimes not, so traps are exercised too), a record
with an array field, by-reference parameters, nested `if`, `for` and
`loop` with `break`, calls between helpers (acyclic), and effects.

`main` reads one input item per call and transmits a frame of derived
bytes, so every computed value is observable in the trace.
-/

namespace Ember.Lang.Gen
open Ember

structure Var where
  name : String
  ty   : Ty
  writable : Bool := true

structure GState where
  rng    : Rng
  fresh  : Nat := 0
  /-- Helpers generated so far: name, scalar parameter types, result width. -/
  helpers : Array (String × List Width × Bool × Width) := #[]
  /-- Widths the generated code computes in.  (`u64` is left out for the
  Z80: SDCC 4.6 miscompiles 64-bit shifts and comparisons, see the
  decision log.) -/
  widths : Array Width := #[.w8, .w16, .w32, .w64]

abbrev GM := StateM GState

def liftR (m : RandM α) : GM α := do
  let s ← get
  let (a, r) := m.run s.rng
  set { s with rng := r }
  return a

def rn (n : Nat) : GM Nat := liftR (randNat n)
def chance (pct : Nat) : GM Bool := liftR (randBool pct)
def pick [Inhabited α] (xs : Array α) : GM α := liftR (randPick xs)

def freshName (base : String) : GM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{base}{s.fresh}"

def pickWidth : GM Width := do pick (← get).widths

def interesting (w : Width) : GM Nat := do
  let m := w.modulus
  match ← rn 8 with
  | 0 => return 0
  | 1 => return 1
  | 2 => return m - 1
  | 3 => return m / 2
  | 4 => return m / 2 - 1
  | 5 => return w.bits
  | _ => return (← liftR rand64).toNat % m

/-- The record type every program has. -/
def recDef : StructDef := { name := "R", fields := [("a", .u8), ("b", .u32), ("xs", .arr .u8 4)] }

/-- Scalar places of type `.int w` readable in scope (with array elements). -/
def intVars (vs : List Var) (w : Width) : List Expr :=
  vs.filterMap fun v => if v.ty == .int w then some (.var v.name) else none

def arrays (vs : List Var) : List (Expr × Width × Nat) :=
  vs.flatMap fun v => match v.ty with
    | .arr (.int w) n => [(.var v.name, w, n)]
    | .record "R" => [(.field (.var v.name) "xs", .w8, 4)]
    | _ => []

def recFields (vs : List Var) (w : Width) : List Expr :=
  vs.flatMap fun v => match v.ty with
    | .record "R" => (if w == .w8 then [.field (.var v.name) "a"] else []) ++
                     (if w == .w32 then [.field (.var v.name) "b"] else [])
    | _ => []

mutual

partial def genIndex (vs : List Var) (n : Nat) (d : Nat) : GM Expr := do
  let w ← pick #[Width.w8, .w16]
  let e ← genInt vs w (d + 1)
  if ← chance 97 then return .bin .mod e (.lit n (some w))
  -- unreduced (may trap at run time); a literal must still be in range
  match e with
  | .lit v w => return .lit (v % n) w
  | e => return e

partial def genInt (vs : List Var) (w : Width) (d : Nat) : GM Expr := do
  let leaf : GM Expr := do
    let vars := intVars vs w ++ recFields vs w
    match ← rn 4 with
    | 0 => return .lit (← interesting w) (some w)
    | 1 =>
      if vars.isEmpty then return .lit (← interesting w) (some w)
      return ← pick vars.toArray
    | 2 =>
      let arrs := (arrays vs).filter (·.2.1 == w)
      if arrs.isEmpty then return .lit (← interesting w) (some w)
      let (a, _, n) ← pick arrs.toArray
      return .index a (← genIndex vs n 3)
    | _ =>
      let w' ← pickWidth
      let vars' := intVars vs w'
      if vars'.isEmpty then return .lit (← interesting w) (some w)
      return .cast w (← pick vars'.toArray)
  if d ≥ 3 then return ← leaf
  match ← rn 12 with
  | 0 | 1 | 2 => leaf
  | 3 | 4 | 5 | 6 =>
    let op ← pick #[BinOp.add, .sub, .mul, .div, .mod, .band, .bor, .bxor]
    return .bin op (← genInt vs w (d+1)) (← genInt vs w (d+1))
  | 7 =>
    let op ← pick #[BinOp.shl, .shr]
    let sw ← pickWidth
    let amt ← if ← chance 50 then pure (.lit (← rn (w.bits + 8)) (some sw)) else genInt vs sw (d+1)
    return .bin op (← genInt vs w (d+1)) amt
  | 8 => return .un (← pick #[UnOp.bnot, .neg]) (← genInt vs w (d+1))
  | 9 =>
    let w' ← pickWidth
    return .cast w (← genInt vs w' (d+1))
  | 10 => return .cond (← genBool vs (d+1)) (← genInt vs w (d+1)) (← genInt vs w (d+1))
  | _ => return .cast w (← genBool vs (d+1))

partial def genBool (vs : List Var) (d : Nat) : GM Expr := do
  if d ≥ 3 then
    let bools := vs.filterMap fun v => if v.ty == .bool then some (Expr.var v.name) else none
    if !bools.isEmpty && (← chance 50) then return ← pick bools.toArray
    return .blit (← chance 50)
  match ← rn 5 with
  | 0 | 1 | 2 =>
    let w ← pickWidth
    let op ← pick #[BinOp.eq, .ne, .lt, .le, .gt, .ge]
    return .bin op (← genInt vs w (d+1)) (← genInt vs w (d+1))
  | 3 => return .bin (← pick #[BinOp.land, .lor]) (← genBool vs (d+1)) (← genBool vs (d+1))
  | _ => return .un .lnot (← genBool vs (d+1))

end

def genScalar (vs : List Var) (t : Ty) : GM Expr :=
  match t with
  | .int w => genInt vs w 0
  | _ => genBool vs 0

/-- Writable scalar places. -/
def targets (vs : List Var) : GM (List (Expr × Ty)) := do
  let mut out := []
  for v in vs do
    if !v.writable then continue
    match v.ty with
    | .int _ | .bool => out := out ++ [(Expr.var v.name, v.ty)]
    | .arr (.int w) n => out := out ++ [(.index (.var v.name) (← genIndex vs n 1), .int w)]
    | .record "R" => out := out ++ [(.field (.var v.name) "a", .u8), (.field (.var v.name) "b", .u32),
        (.index (.field (.var v.name) "xs") (← genIndex vs 4 1), .u8)]
    | _ => pure ()
  return out

partial def genStmts (vs : List Var) (depth : Nat) (n : Nat) (inLoop : Bool) : GM (List Stmt) := do
  let mut out : Array Stmt := #[]
  let mut vs := vs
  for _ in [0:n] do
    match ← rn (if depth ≥ 2 then 6 else 10) with
    | 0 | 1 =>
      let t ← pick #[Ty.u8, .u16, .u32, .u64, .bool]
      let x ← freshName "x"
      out := out.push (.decl x t (some (← genScalar vs t)))
      vs := { name := x, ty := t } :: vs
    | 2 | 3 | 4 =>
      let ts ← targets vs
      if ts.isEmpty then continue
      let (l, t) ← pick ts.toArray
      out := out.push (.assign l (← genScalar vs t))
    | 5 =>
      out := out.push (.eff none .outByte [.cast .w8 (← genInt vs (← pickWidth) 0)])
    | 6 =>
      out := out.push (.ite (← genBool vs 0) (← genStmts vs (depth+1) ((← rn 3) + 1) inLoop)
        (← if ← chance 50 then genStmts vs (depth+1) (← rn 3) inLoop else pure []))
    | 7 =>
      let i ← freshName "i"
      let w ← pick #[Width.w8, .w16, .w32]
      let hi : Expr ← if ← chance 50 then pure (.lit (← rn 6) (some w))
        else pure (.bin .mod (← genInt vs w 1) (.lit 6 (some w)))
      let body ← genStmts ({ name := i, ty := .int w, writable := false } :: vs) (depth+1) ((← rn 3) + 1) true
      out := out.push (.forRange i (some w) (.lit (← rn 2) (some w)) hi body)
    | 8 =>
      let stop : Stmt := .ite (← genBool vs 1) [.brk] []
      let body ← genStmts vs (depth+1) ((← rn 2) + 1) true
      out := out.push (.loop ((← rn 5) + 1) (body ++ [stop]))
    | _ =>
      let hs := (← get).helpers
      if hs.isEmpty then
        out := out.push (.eff none .drop [.lit (← rn 3) (some .w8)])
        continue
      let (h, ps, byRef, rw) ← pick hs
      let mut args := []
      for w in ps do args := args ++ [← genInt vs w 1]
      if byRef then
        let arrs := (arrays vs).filter fun (_, w, n) => w == .w8 && n == 8
        if arrs.isEmpty then continue
        args := args ++ [(← pick arrs.toArray).1]
      let ts := (← targets vs).filter (·.2 == .int rw)
      let dst ← if ts.isEmpty then pure none else some <$> (·.1) <$> pick ts.toArray
      out := out.push (.call dst h args)
  if inLoop && (← chance 20) then out := out.push .brk
  return out.toList

def globalsOf : List Global :=
  [{ name := "g8", ty := .u8, init := [7] }, { name := "g16", ty := .u16, init := [300] },
   { name := "g32", ty := .u32, init := [70000] }, { name := "g64", ty := .u64 },
   { name := "gb", ty := .bool }, { name := "ga", ty := .arr .u8 8, init := [1, 2, 3] },
   { name := "gw", ty := .arr .u16 5 }, { name := "gr", ty := .record "R" }]

def globalVars : List Var :=
  globalsOf.map fun g => { name := g.name, ty := g.ty }

/-- A helper: scalar parameters, maybe an array by reference, a result.
Helpers use only their parameters and locals (so passing a global by
reference to them is allowed). -/
def genHelper (k : Nat) : GM Fn := do
  let np ← rn 3
  let mut ps : List Param := []
  let mut pws : List Width := []
  for i in [0:np] do
    let w ← pickWidth
    ps := ps ++ [{ name := s!"p{i}", ty := .int w }]
    pws := pws ++ [w]
  let byRef ← chance 40
  if byRef then ps := ps ++ [{ name := "arr", ty := .arr .u8 8, byRef := true }]
  let rw ← pickWidth
  let vs : List Var := ps.map fun p => { name := p.name, ty := p.ty }
  let body ← genStmts vs 1 ((← rn 4) + 1) false
  let r ← genInt vs rw 0
  let name := s!"h{k}"
  modify fun s => { s with helpers := s.helpers.push (name, pws, byRef, rw) }
  return { name, params := ps, ret := some (.int rw), body := body ++ [.ret (some r)] }

def genProg : GM Prog := do
  let nh ← rn 3
  let mut fns := #[]
  for k in [0:nh] do fns := fns.push (← genHelper k)
  let kv : Var := { name := "k", ty := .u16 }
  -- without `u64` among the widths the program does not touch `g64` either
  let has64 := (← get).widths.contains .w64
  let vs := kv :: globalVars.filter fun v => has64 || v.name != "g64"
  let body ← genStmts vs 0 ((← rn 6) + 2) false
  let outs : List Stmt := [Expr.var "g8", .cast .w8 (.var "g16"), .cast .w8 (.var "g32"),
      .cast .w8 (.bin .shr (.var "g64") (.lit 56 (some .w64))), .cast .w8 (.var "gb"),
      .index (.var "ga") (.lit 0 (some .w8)), .field (.var "gr") "a"].filterMap fun e =>
        if !has64 && e == .cast .w8 (.bin .shr (.var "g64") (.lit 56 (some .w64))) then none
        else some (.eff none .outByte [e])
  let main : Fn := { name := "main", body :=
    [.decl "k" .u16 none, .eff (some (.var "k")) .inputNext [],
     .ite (.bin .eq (.var "k") (.lit 0xFFFF (some .w16))) [.ret none] []] ++ body ++ outs ++
    [.eff none .outEnd []] }
  return { structs := [recDef], globals := globalsOf, fns := (fns.push main).toList,
           dropReasons := ["d0", "d1", "d2"] }

def genInputs : GM (Array Trace.Input) := do
  let n ← rn 8
  let mut ins := #[]
  for _ in [0:n + 1] do
    if ← chance 20 then ins := ins.push .tick
    else ins := ins.push (.rx (← liftR (randBytes ((← rn 3) + 1))))
  return ins

/-- A random program and inputs from a seed. -/
def sample (seed : Nat) (widths : Array Width := #[.w8, .w16, .w32, .w64]) : Prog × Array Trace.Input :=
  let ((p, i), _) := (do return (← genProg, ← genInputs) : GM _).run { rng := Rng.ofSeed seed, widths }
  (p, i)

/-! ## Shrinking -/

/-- Number of statements (the size the shrinker minimises). -/
partial def stmtsSize (ss : List Stmt) : Nat :=
  ss.foldl (fun n s => n + match s.core with
    | .ite _ t e => 1 + stmtsSize t + stmtsSize e
    | .forRange _ _ _ _ b | .loop _ b => 1 + stmtsSize b
    | _ => 1) 0

def progSize (p : Prog) : Nat := p.fns.foldl (fun n f => n + stmtsSize f.body) 0

/-- Candidate programs one step smaller: a statement removed, a block
flattened, or an expression replaced by one of its operands or 0. -/
partial def shrinkStmts (ss : List Stmt) : List (List Stmt) :=
  let n := ss.length
  let removals := (List.range n).map fun i => ss.eraseIdx i
  let inner := (List.range n).flatMap fun i =>
    let s := ss[i]!
    let repl (s' : Stmt) := ss.set i s'
    match s.core with
    | .ite c t e =>
      [ss.eraseIdx i ++ t] ++ (shrinkStmts t).map (fun t' => repl (.ite c t' e)) ++
        (shrinkStmts e).map (fun e' => repl (.ite c t e'))
    | .forRange x w lo hi b => (shrinkStmts b).map fun b' => repl (.forRange x w lo hi b')
    | .loop m b => (shrinkStmts b).map fun b' => repl (.loop m b')
    | _ => []
  removals ++ inner

partial def shrinkExpr : Expr → List Expr
  | .bin op a b => [a, b] ++ (shrinkExpr a).map (.bin op · b) ++ (shrinkExpr b).map (.bin op a ·)
  | .un op a => [a] ++ (shrinkExpr a).map (.un op ·)
  | .cast w a => (shrinkExpr a).map (.cast w ·)
  | .cond c a b => [a, b] ++ (shrinkExpr a).map (.cond c · b) ++ (shrinkExpr b).map (.cond c a ·)
  | _ => []

partial def shrinkExprsIn (ss : List Stmt) : List (List Stmt) :=
  (List.range ss.length).flatMap fun i =>
    match ss[i]!.core with
    | .assign l r => (shrinkExpr r).map fun r' => ss.set i (.assign l r')
    | .decl x t (some e) => (shrinkExpr e).map fun e' => ss.set i (.decl x t (some e'))
    | .eff d e [a] => (shrinkExpr a).map fun a' => ss.set i (.eff d e [a'])
    | .ite c t e => (shrinkExprsIn t).map (fun t' => ss.set i (.ite c t' e)) ++
                    (shrinkExprsIn e).map (fun e' => ss.set i (.ite c t e'))
    | .forRange x w lo hi b => (shrinkExprsIn b).map fun b' => ss.set i (.forRange x w lo hi b')
    | _ => []

/-- Greedy shrinking: take the first smaller candidate that is still
well-typed and still `bad`, until none is. -/
partial def shrinkProg (bad : Prog → IO Bool) (p : Prog) (budget : Nat := 400) : IO Prog := do
  let mut cur := p
  let mut tries := 0
  let mut progress := true
  while progress && tries < budget do
    progress := false
    let candidates : List Prog :=
      -- drop a helper that is not called
      (cur.fns.filter (·.name != cur.entry)).map (fun f => { cur with fns := cur.fns.filter (·.name != f.name) }) ++
      cur.fns.flatMap (fun f => (shrinkStmts f.body ++ shrinkExprsIn f.body).map fun b =>
        { cur with fns := cur.fns.map fun g => if g.name == f.name then { g with body := b } else g })
    for c in candidates do
      tries := tries + 1
      if tries ≥ budget then break
      if (c.check).toOption.isNone then continue
      if ← bad c then
        cur := c
        progress := true
        break
  return cur

end Ember.Lang.Gen
