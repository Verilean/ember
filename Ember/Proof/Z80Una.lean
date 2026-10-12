import Ember.Proof.Z80Bin16

/-!
# Ember.Proof.Z80Una — `not` and `neg` of one and two bytes (plan M7.3)
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin)

/-- `cpl` and `neg` as the model runs them. -/
def cplA (s : Cpu) : Cpu :=
  ({ (op1 s) with a := ~~~(op1 s).a,
                  f := ((op1 s).f &&& (FS ||| FZ ||| FPV ||| FC)) ||| FH ||| FN ||| (~~~(op1 s).a &&& FXY) } : Cpu).tick 4

def negA (s : Cpu) : Cpu :=
  ({ (op2 s) with a := (sub8 0 (op2 s).a false).1, f := (sub8 0 (op2 s).a false).2 } : Cpu).tick 8

theorem does_cpl : Does ⟨.cpl, []⟩ cplA := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, cplA, zsim, and_self]⟩
theorem does_neg : Does ⟨.neg, []⟩ negA := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, negA, zsim, and_self]⟩

theorem cplA_a (s : Cpu) : (cplA s).a.toNat = 255 - s.a.toNat := by
  simp only [cplA, zsim]
  rw [UInt8.toNat_not]
  rfl

theorem negA_a (s : Cpu) : (negA s).a.toNat = (256 - s.a.toNat) % 256 := by
  simp only [negA, zsim]
  show ((((0 : UInt8).toUInt16 - s.a.toUInt16 - 0).toUInt8)).toNat = _
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16]
  have := s.a.toNat_lt
  show (2 ^ 16 - 0 + (2 ^ 16 - s.a.toNat + 0) % 2 ^ 16) % 2 ^ 16 % 256 = _
  omega

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- A one-byte operation on `A` alone, from its operand to its destination. -/
theorem unA_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {op : Op} (f : Cpu → Cpu) (hd : Does ⟨op, []⟩ f)
    (hhl : ∀ s, (f s).hl = s.hl) (g : Nat → Nat) (hg : ∀ s, (f s).a.toNat = g s.a.toNat) (hlt : ∀ x, g x < 256)
    (d : Dst) (a : Opd)
    (s0 : GS) :
    wpg (do loadA a; ins op; setRegs fun r => { r with a := [] }; storeA d) E
      (fun _ s1 => GExt s0 s1 ∧
        (GExt s1 sF → Rd Z E dt 1 a ∧ Wr Z E 1 d → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
          At Z.addrs (base + s0.out.size) s →
          ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
            Rel Z E fr (dtAfter dt d) s1.regs
              (IR.Sem.setDst Z.c ist tmps 1 d (g (IR.Sem.opd Z.c ist tmps 1 a))).1
              (IR.Sem.setDst Z.c ist tmps 1 d (g (IR.Sem.opd Z.c ist tmps 1 a))).2 s')) s0 := by
  simp only [wpg_bind]
  refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  simp only [wpg_ins, wpg_setRegs]
  refine wpg_mono (storeA_ok (dt := dt) ok hT F d _) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans (((GExt.push _ _).trans (GExt.regs _ _)).trans hx2), fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hA⟩ := hl (((GExt.push _ _).trans (GExt.regs _ _)).trans (hx2.trans hxF)) fr ist tmps s hrd R hat
  obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1) (s1 := { s1 with out := s1.out.push (.ins ⟨op, []⟩) })
    ((GExt.regs _ _).trans (hx2.trans hxF)) rfl R1.mach at1 (f s') (fun ad _ => hd.exec _ _ _) hd.falls (hd.sys s')
  have R2 : Rel Z E fr dt { s1.regs with a := [] } ist tmps (f s') :=
    R1.of_sys (hd.sys s') rfl (fun o ho => ho) (fun o ho hown => by rw [hhl]; exact R1.rhl o ho hown) (fun n o h => h)
  obtain ⟨s'', st3, at3, R3, _⟩ := hs hxF fr ist tmps (f s') (g (IR.Sem.opd Z.c ist tmps 1 a)) hwr R2 at2 (by
    rw [hg, hA]
    exact (Nat.mod_eq_of_lt (hlt _)).symm)
  exact ⟨s'', (st1.trans st2).trans st3, at3, R3⟩

theorem not1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (a : Opd) (s0 : GS) :
    wpg (genInstr (.not 1 d a)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.not 1 d a) (Rd Z E dt 1 a ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, Codegen.load, store, beq_self_eq_true, if_true]
  refine wpg_mono (unA_ok (dt := dt) ok hT F cplA does_cpl (fun s => by simp only [cplA, zsim, Cpu.hl]) (fun x => 255 - x)
    cplA_a (fun x => by omega) d a s0) ?_
  intro _ s1 ⟨hx, h⟩
  exact ⟨hx, fun hxF hH fr ist tmps s R hat => h hxF hH fr ist tmps s R hat⟩

theorem neg1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (a : Opd) (s0 : GS) :
    wpg (genInstr (.neg 1 d a)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.neg 1 d a) (Rd Z E dt 1 a ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, Codegen.load, store, beq_self_eq_true, if_true]
  refine wpg_mono (unA_ok (dt := dt) ok hT F negA does_neg (fun s => by simp only [negA, zsim, Cpu.hl])
    (fun x => (256 - x) % 256) negA_a (fun x => Nat.mod_lt _ (by decide)) d a s0) ?_
  intro _ s1 ⟨hx, h⟩
  exact ⟨hx, fun hxF hH fr ist tmps s R hat => h hxF hH fr ist tmps s R hat⟩

/-- A two-byte operation on `HL` by a routine of the runtime, from its operand to its destination. -/
theorem unHL_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (name : String) (g : Nat → Nat)
    (hlt : ∀ x, g x < 65536) (d : Dst) (a : Opd) (s0 : GS) :
    wpg (do loadHL a; call name; setRegs fun r => { r with a := [], hl := [] }; storeHL d) E
      (fun _ s1 => GExt s0 s1 ∧
        (GExt s1 sF → Rd Z E dt 2 a ∧ Wr Z E 2 d ∧ RtPure Z name (fun s s' => s'.hl.toNat = g s.hl.toNat) ∧
            Z.rtK + 2 ≤ Z.depth E.fn.name →
          ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
          ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
            Rel Z E fr (dtAfter dt d) s1.regs
              (IR.Sem.setDst Z.c ist tmps 2 d (g (IR.Sem.opd Z.c ist tmps 2 a))).1
              (IR.Sem.setDst Z.c ist tmps 2 d (g (IR.Sem.opd Z.c ist tmps 2 a))).2 s')) s0 := by
  simp only [wpg_bind]
  refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  simp only [wpg_call, wpg_setRegs]
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d _) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans (((GExt.push _ _).trans (GExt.regs _ _)).trans hx2),
    fun hxF ⟨hrd, hwr, hrt, hdep⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl (((GExt.push _ _).trans (GExt.regs _ _)).trans (hx2.trans hxF)) fr ist tmps s hrd R hat
  obtain ⟨c1, s'', cs, st2, at2, hval, hRel⟩ := rt_call ok hT F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym name)]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hxF)) rfl hrt hdep R1 at1
  have R2 := hRel { s1.regs with a := [], hl := [] } (fun o ho => by cases ho) (fun o ho => by cases ho)
    (fun sl hsl => by cases hsl) (fun sl hsl => by cases hsl) (fun n o h => h)
  obtain ⟨s3, st3, at3, R3, _⟩ := hs hxF fr ist tmps s'' (g (IR.Sem.opd Z.c ist tmps 2 a)) hwr R2 at2 (by
    rw [hval, hl_congr cs.h cs.l, hHL]
    exact (Nat.mod_eq_of_lt (hlt _)).symm)
  exact ⟨s3, (st1.trans st2).trans st3, at3, R3⟩

theorem not2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (a : Opd) (s0 : GS) :
    wpg (genInstr (.not 2 d a)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.not 2 d a)
        (Rd Z E dt 2 a ∧ Wr Z E 2 d ∧ RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s0 := by
  simp only [genInstr, Codegen.load, store, beq_self_eq_true, if_true,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (unHL_ok (dt := dt) ok hT F "rt_not16" (fun x => 65535 - x) (fun x => by omega) d a s0) ?_
  intro _ s1 ⟨hx, h⟩
  exact ⟨hx, fun hxF ⟨h1, h2, hrt, hdep⟩ fr ist tmps s R hat => h hxF ⟨h1, h2, hrt.not16, hdep⟩ fr ist tmps s R hat⟩

theorem neg2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (a : Opd) (s0 : GS) :
    wpg (genInstr (.neg 2 d a)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.neg 2 d a)
        (Rd Z E dt 2 a ∧ Wr Z E 2 d ∧ RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s0 := by
  simp only [genInstr, Codegen.load, store, beq_self_eq_true, if_true,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (unHL_ok (dt := dt) ok hT F "rt_neg16" (fun x => (65536 - x) % 65536)
    (fun x => Nat.mod_lt _ (by decide)) d a s0) ?_
  intro _ s1 ⟨hx, h⟩
  exact ⟨hx, fun hxF ⟨h1, h2, hrt, hdep⟩ fr ist tmps s R hat => h hxF ⟨h1, h2, hrt.neg16, hdep⟩ fr ist tmps s R hat⟩

end

end Ember.Proof.Z80Gen
