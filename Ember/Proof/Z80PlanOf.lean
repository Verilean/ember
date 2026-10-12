import Ember.Proof.Z80Check

/-!
# Ember.Proof.Z80PlanOf — the plan of a program (plan M7.3)

`mkPlan` makes a `Plan` of a program, its layout and the environments
its functions are generated in: the shared bytes are the globals in RAM
and the bytes of the frames but those whose stores the generator leaves
out; a function may write the globals, its frame and the frames of the
functions it can reach; it uses the slots it reads and writes.

Nothing is proved of `mkPlan`: what a plan must be is what `okB` and
`fnStaticB` decide of it.  `planCheck` runs them on every function.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

def opdS (n : Nat) : Opd → List (Slot × Nat)
  | .slot sl => [(sl, n)]
  | _ => []

def dstS (n : Nat) : Dst → List (Slot × Nat)
  | .slot sl => [(sl, n)]
  | _ => []

def addrS (p : IR.Addr) : List (Slot × Nat) :=
  match p.idx with
  | some x => opdS x.size x.opd
  | none => []

/-- The slots an instruction reads, with the sizes it reads them in. -/
def readsOf : IR.Instr → List (Slot × Nat)
  | .mov n _ s | .not n _ s | .neg n _ s => opdS n s
  | .bin _ n _ a b | .cmp _ n _ a b | .br _ n a b _ => opdS n a ++ opdS n b
  | .shift _ n _ a m amt => opdS n a ++ opdS m amt
  | .ext _ _ m s => opdS m s
  | .load _ _ p | .lea _ p => addrS p
  | .store n p s => addrS p ++ opdS n s
  | .call _ _ reg => (reg.map fun a => opdS a.1 a.2).getD []
  | .eff _ args _ => args.flatMap fun a => opdS a.1 a.2
  | .ret v => (v.map fun a => opdS a.1 a.2).getD []
  | _ => []

/-- The slots an instruction writes. -/
def writesOf : IR.Instr → List (Slot × Nat)
  | .mov n d _ | .bin _ n d _ _ | .shift _ n d _ _ _ | .not n d _ | .neg n d _ | .ext n d _ _
  | .load n d _ => dstS n d
  | .cmp _ _ d _ _ => dstS 1 d
  | .lea d _ => dstS 2 d
  | .call _ ret _ | .eff _ _ ret => (ret.map fun a => dstS a.1 a.2).getD []
  | _ => []

def fnWrites (f : IR.Fn) : List (Slot × Nat) :=
  (f.regParam.map fun p => [(p.2, p.1)]).getD [] ++ f.body.toList.flatMap writesOf

def fnReads (f : IR.Fn) : List (Slot × Nat) := f.body.toList.flatMap readsOf

/-- Offsets in the function's own frame the stores to which are left out. -/
def deadBytes (E : GEnv) : List Nat :=
  (fnWrites E.fn).flatMap fun p => if deadB E p.1 p.2 then (List.range p.2).map (p.1.off + ·) else []

/-- The bytes `base + k`, `k < n`, but those of `dead`, as intervals. -/
def runs (base n : Nat) (dead : List Nat) : Ivs :=
  (List.range n).foldl (fun acc k =>
    if dead.contains k then acc
    else
      match acc with
      | (lo, hi) :: r => if hi == base + k then (lo, base + k + 1) :: r else (base + k, base + k + 1) :: acc
      | [] => [(base + k, base + k + 1)]) []

structure PlanIn where
  c : IR.Ctx
  /-- The functions with code, and the environment of each (`progEnvs`). -/
  envs : List (IR.Fn × Array Bool × Option (Array Bool))
  ramStart : Nat
  stackLo : Nat
  stackHi : Nat
  acc : Nat
  rtK : Nat
  rt : Ivs
  /-- Labels of the runtime. -/
  labels : List String

/-- The stack every function needs: a routine of the runtime, or a call more than a function it calls. -/
def depths (p : IR.Prog) (rtK : Nat) : Nat → List (String × Nat)
  | 0 => p.fns.map fun f => (f.name, rtK + 2)
  | k + 1 =>
    let d := depths p rtK k
    p.fns.map fun f => (f.name, f.callees.foldl (fun m g => Nat.max m ((d.lookup g).getD 0 + 2)) (rtK + 2))

def mkPlan (I : PlanIn) : Plan :=
  let L := I.c.layout
  let globals : Ivs := I.c.prog.globals.filterMap fun g => (L.globals.lookup g.name).map fun a => (a, a + g.size)
  let frameOf (f : String) : Ivs :=
    match L.frames.lookup f, I.envs.find? (·.1.name == f) with
    | some a, some e => [(a, a + (tmpLayout e.1 e.2.1).2)]
    | some a, none => [(a, a + ((I.c.prog.fn? f).map (·.frame)).getD 0)]
    | none, _ => []
  { c := I.c, ramStart := I.ramStart, stackLo := I.stackLo, stackHi := I.stackHi, acc := I.acc, rtK := I.rtK,
    depth := depths I.c.prog I.rtK I.c.prog.fns.length,
    data := globals ++ I.envs.flatMap fun e =>
      let E := genEnv e.1 e.2.1 e.2.2
      runs (L.addr { area := .frame e.1.name, off := 0 }) e.1.frame (deadBytes E),
    rt := I.rt,
    wr := I.envs.map fun e => (e.1.name, globals ++ (e.1.name :: IR.reach I.c.prog e.1.name).flatMap frameOf),
    use := I.envs.map fun e =>
      let E := genEnv e.1 e.2.1 e.2.2
      (e.1.name, fnReads e.1 ++ (fnWrites e.1).filter fun p => ownB E p.1),
    dst := I.envs.map fun e => (e.1.name, fnWrites e.1),
    labels := I.labels ++ I.envs.flatMap fun e =>
      let E := genEnv e.1 e.2.1 e.2.2
      fnLabel e.1.name :: e.1.body.toList.filterMap fun i =>
        match i with
        | .label l => some (lname E l)
        | _ => none }

/-- The plan passes: `okB`, and `fnStaticB` of every function in its environment. -/
def planCheck (I : PlanIn) : Bool :=
  okB (mkPlan I) && I.envs.all fun e => fnStaticB (mkPlan I) (genEnv e.1 e.2.1 e.2.2)

theorem planCheck_static {I : PlanIn} (h : planCheck I = true) (M : Around) (hlab : Labels (mkPlan I) M) :
    ∀ e, e ∈ I.envs → FnStatic ((mkPlan I).toZ M) (genEnv e.1 e.2.1 e.2.2) := by
  simp only [planCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact fun e he => fnStaticB_sound hlab (h.2 e he)

theorem planCheck_ok {I : PlanIn} (h : planCheck I = true) : okB (mkPlan I) = true := by
  simp only [planCheck, Bool.and_eq_true] at h
  exact h.1

end Ember.Proof.Z80Gen
