import Ember.Proof.Z80CallFn

/-!
# Ember.Proof.Z80After — what follows an instruction (plan M7.3)

`After`: what the code of an instruction does from a state, for each
thing `IR.Sem.step` can say the instruction does.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The temporaries assigned after an instruction.  After a label none
is taken to be: a temporary is not read across a label. -/
def dtNext (dt : Nat → Prop) : IR.Instr → Nat → Prop
  | .label _ => fun _ => False
  | .mov _ d _ | .bin _ _ d _ _ | .shift _ _ d _ _ _ | .not _ d _ | .neg _ d _ | .ext _ d _ _
  | .cmp _ _ d _ _ | .load _ d _ | .lea d _ => dtAfter dt d
  | .call _ ret _ | .eff _ _ ret => dtRet dt ret
  | _ => dt

/-- What the code does from `s`, for what the IR's instruction does. -/
def After (Z : ZCtx) (E : GEnv) (base : Nat) (fr : Fr) (dt : Nat → Prop) (i : IR.Instr) (s1 : GS)
    (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) : IR.Sem.Step → Prop
  | .next ist' tmps' => ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr (dtNext dt i) s1.regs ist' tmps' s'
  | .goto l => ∀ j : Nat, Z.items[j]? = some (Item.label (lname E l)) →
      ∃ s' r, Steps s s' ∧ At Z.addrs j s' ∧ (l, r) ∈ s1.jumps ∧ Rel Z E fr dt r ist tmps s'
  | .call g st1 ret => ∀ res, Callee Z g st1 res →
      AfterCall Z E fr (dtNext dt i) s1.regs (base + s1.out.size) tmps ret s res
  | .stop (.ok r st') => ∃ s' v, Steps s s' ∧ i = .ret v ∧ RetSt Z E.fn fr st' (v.map (·.1)) r s'
  | .stop (.trap st') => ∃ s', Steps s s' ∧ Trapped Z st' s'
  | .stop _ => True

end Ember.Proof.Z80Gen
