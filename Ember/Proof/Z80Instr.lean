import Ember.Proof.Z80Store

/-!
# Ember.Proof.Z80Instr — the code of an IR instruction does what the instruction does (plan M7.3)

`InsPost`: what the generator promises for an instruction that goes on
to the next — from states that agree, the code reaches states that agree
after `IR.Sem.step`.  Proved here: `mov` of one and two bytes.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area)

/-- What the generator promises for the instruction `i`, given `H` of its operands. -/
def InsPost (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt dt' : Nat → Prop) (i : IR.Instr) (H : Prop)
    (s0 : GS) (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
      match IR.Sem.step Z.c ist tmps i with
      | .next ist' tmps' =>
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt' s1.regs ist' tmps' s'
      | _ => True)

theorem opd_lt (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (n : Nat) (o : Opd) :
    IR.Sem.opd c ist tmps n o < 2 ^ (8 * n) := by
  cases o with
  | const v => exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | slot sl => exact rd_lt _ _ _
  | tmp t => exact Nat.mod_lt _ (Nat.two_pow_pos _)

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem mov1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.mov 1 d src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.mov 1 d src) (Rd Z E dt 1 src ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, Codegen.load, store, wpg_bind, beq_self_eq_true, if_true]
  refine wpg_mono (loadA_ok (dt := dt) ok F src s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  refine wpg_mono (storeA_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hA⟩ := hl (hx2.trans hxF) fr ist tmps s hrd R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' (IR.Sem.opd Z.c ist tmps 1 src) hwr R1 at1 (by
    rw [hA, Nat.mod_eq_of_lt (opd_lt _ _ _ 1 _)])
  exact ⟨s'', st1.trans st2, at2, R2⟩

theorem mov2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.mov 2 d src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.mov 2 d src) (Rd Z E dt 2 src ∧ Wr Z E 2 d) s0) s0 := by
  simp only [genInstr, Codegen.load, store, wpg_bind, beq_self_eq_true, if_true,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (loadHL_ok (dt := dt) ok F src s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl (hx2.trans hxF) fr ist tmps s hrd R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' (IR.Sem.opd Z.c ist tmps 2 src) hwr R1 at1 (by
    rw [hHL, Nat.mod_eq_of_lt (opd_lt _ _ _ 2 _)])
  exact ⟨s'', st1.trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
