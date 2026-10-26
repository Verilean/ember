import Ember.Proof.Z80Acc
import Ember.Proof.Z80Ctl

/-!
# Ember.Proof.Z80AccOps — operations on the accumulator (plan M7.3)

`bin`, `cmp` and `br` of values wider than two bytes: the first operand
in the accumulator, the second pointed to by `HL`, a routine of the
runtime (`RtW`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- `a` in the accumulator and `HL` at `b`: where a wide operation starts. -/
theorem accHL_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 0 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (a b : Opd) (s0 : GS) :
    wpg (do
      let pb ← ptrOf n b
      loadAcc n a
      ins .ld [.hl, .imm pb]) E (fun _ s1 => GExt s0 s1 ∧ s1.regs.acc = some (n, a) ∧
      (GExt s1 sF → ∀ fr ist tmps s, RdW Z E dt n a → RdW Z E dt n b → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
          Rel Z E fr dt { s1.regs with a := [], hl := [] } ist tmps s' ∧
          IR.Sem.rd s'.mem Z.acc n = IR.Sem.opd Z.c ist tmps n a ∧
          (∀ c : Cpu, c.h = s'.h → c.l = s'.l →
            (∀ x, x < s'.sp.toNat - 2 ∨ s'.sp.toNat ≤ x → c.mem.get! x = s'.mem.get! x) →
            IR.Sem.rd c.mem Z.acc n = IR.Sem.opd Z.c ist tmps n a ∧
            IR.Sem.rd c.mem c.hl.toNat n = IR.Sem.opd Z.c ist tmps n b ∧ HLApart Z n c))) s0 := by
  simp only [wpg_bind]
  refine wpg_mono (ptrOf_ok n b s0) ?_
  intro pb s1 ⟨ho1, hr1, hp, hsp, hj1, hl1, hlv⟩
  subst hp
  have hx01 : GExt s0 s1 := ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩
  refine wpg_mono (loadAcc_ok (dt := dt) ok hT F hn hrt hdep a s1) ?_
  intro _ s2 ⟨hx2, hacc2, hl⟩
  rw [wpg_ins]
  refine ⟨hx01.trans (hx2.trans (GExt.push _ _)), hacc2, fun hx fr ist tmps s hra hrb R hat => ?_⟩
  obtain ⟨s', st1, at1, R1⟩ := hl ((GExt.push _ _).trans hx) fr ist tmps s hra
    (by rw [hr1]; exact R) (by rw [ho1]; exact hat)
  obtain ⟨ad, had, hpc⟩ := at1
  obtain ⟨B, hv, hb, hns, hna, hmem⟩ := ptr_ok (fr := fr) ok hT hn.1 hrb hsp hlv ad
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n b)]⟩).toNat = B :=
    immW_toNat _ _ _ _ rfl hv (by omega)
  have hS : Sys s' (((skip (op1 s') 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n b)]⟩)).tick 10) := by
    simp only [Sys, zsim, and_self]
  obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s2) hx rfl R1.mach ⟨ad, had, hpc⟩ _ (fun ad' had' => by
    rw [had] at had'
    cases had'
    intro _
    rfl) rfl hS
  have hroom := R1.room
  have hstk := ok.stack
  have hacr := ok.accRam
  have hacs := ok.accStack
  have hspv : s'.sp.toNat = fr.sp.toNat := by rw [R1.sp]
  have hacc := R1.racc n a hacc2 (Rd.own_w hra)
  refine ⟨_, st1.trans st2, at2, R1.regs_only hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 (fun o ho => by cases ho)
    (fun o ho => by cases ho) (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => h),
    by rw [hS.1]; exact hacc, fun c hch hcl hcm => ?_⟩
  simp only [zsim] at hch hcl hcm
  constructor
  · rw [← hacc]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hcm x (by omega))
  · have hchl : c.hl.toNat = B := by
      rw [hl_toNat, hch, hcl, ← hnn, ← mk16_toNat, mk16_hi_lo]
    refine ⟨?_, by rw [hchl]; exact hb, fun j hj => by rw [hchl]; exact ⟨hna j hj, hns j hj⟩⟩
    rw [hchl, ← hmem _ ist tmps _ R1]
    refine rd_congr _ _ _ _ hb (fun x h1 h2 => hcm x ?_)
    have := hns (x - B) (by omega)
    rw [show B + (x - B) = x by omega] at this
    omega

/-- **`bin` of a wide value.** -/
theorem binW_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 2 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (op : Bin) (d : Dst) (a b : Opd) (s0 : GS) :
    wpg (genInstr (.bin op n d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.bin op n d a b)
        (RdW Z E dt n a ∧ RdW Z E dt n b ∧ Wr Z E n d) s0) s0 := by
  have h1 : (n == 1) = false := by simp; omega
  have h2 : (n == 2) = false := by simp; omega
  simp only [genInstr, genBin, binW, store, h1, h2, Bool.false_eq_true, if_false]
  have hacc := accHL_ok (dt := dt) ok hT F ⟨by omega, hn.2⟩ hrt hdep a b s0
  simp only [wpg_bind] at hacc ⊢
  refine wpg_mono hacc ?_
  intro pb sa h1'
  refine wpg_mono h1' ?_
  intro _ sb h2'
  refine wpg_mono h2' ?_
  intro _ s1 ⟨hx1, _, hl⟩
  simp only [wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F ⟨by omega, hn.2⟩ hrt hdep d _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (routineW op n))]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hx1.trans (hmid.trans hx2), fun hxF ⟨hra, hrb, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hop⟩ := hl (hmid.trans (hx2.trans hxF)) fr ist tmps s hra hrb R hat
  obtain ⟨c1, s'', cs, st2, at2, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (routineW op n))]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hxF)) rfl (hrt.bin op) hdep R1 at1
    (fun c1 cs => (hop c1 cs.h cs.l cs.mem).2.2)
  obtain ⟨ha, hb, _⟩ := hop c1 cs.h cs.l cs.mem
  have R2 : Rel Z E fr dt {} ist tmps s'' :=
    R1.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho) (fun o ho => by cases ho)
      (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h) (fun k sl h => by cases h)
      (fun k o h => by cases h)
  obtain ⟨s3, st3, at3, R3⟩ := hs hxF fr ist tmps s'' _ hwr R2 at2 (by rw [hrel, ha, hb])
  exact ⟨s3, (st1.trans st2).trans st3, at3, R3⟩

/-- **`not` of four bytes**, an operand that is not a constant: the accumulator complemented by
`rt_not32` (`RtOK.not32`). -/
theorem notW_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (a : Opd) (hc : ∀ v, a ≠ .const v) (s0 : GS) :
    wpg (genInstr (.not 4 d a)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.not 4 d a) (Rd Z E dt 4 a ∧ Wr Z E 4 d) s0) s0 := by
  have hname : s!"rt_not{bits 4}" = "rt_not32" := rfl
  simp only [genInstr, store, Codegen.load, show ((4 : Nat) == 1) = false from rfl,
    show ((4 : Nat) == 2) = false from rfl, Bool.false_eq_true, if_false, hname, wpg_bind]
  refine wpg_mono (loadAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep a s0) ?_
  intro _ s1 ⟨hx1, hacc1, hl⟩
  simp only [wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep d _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym "rt_not32")]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hx1.trans (hmid.trans hx2), fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  have hrw : RdW Z E dt 4 a := by
    cases a with
    | const v => exact absurd rfl (hc v)
    | slot sl => exact hrd
    | tmp t => exact hrd
  obtain ⟨s', st1, at1, R1⟩ := hl (hmid.trans (hx2.trans hxF)) fr ist tmps s hrw R hat
  have hv := R1.racc 4 a hacc1 (Rd.own_w hrw)
  obtain ⟨c1, s'', cs, st2, at2, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym "rt_not32")]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hxF)) rfl hrt.not32 hdep R1 at1 (fun _ _ => trivial)
  have hroom := R1.room
  have hstk := ok.stack
  have hacr := ok.accRam
  have hacs := ok.accStack
  have hspv : s'.sp.toNat = fr.sp.toNat := by rw [R1.sp]
  have hc1 : IR.Sem.rd c1.mem Z.acc 4 = IR.Sem.rd s'.mem Z.acc 4 :=
    rd_congr _ _ _ _ (by omega) (fun x h1 h2 => cs.mem x (by omega))
  have R2 : Rel Z E fr dt {} ist tmps s'' :=
    R1.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho) (fun o ho => by cases ho)
      (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h) (fun k sl h => by cases h)
      (fun k o h => by cases h)
  obtain ⟨s3, st3, at3, R3⟩ := hs hxF fr ist tmps s'' _ hwr R2 at2 (by rw [hrel, hc1, hv])
  exact ⟨s3, (st1.trans st2).trans st3, at3, R3⟩

/-- **A comparison of wide values leaves its result in the flags.** -/
theorem flagsW_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 2 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (op : Cmp) (a b : Opd) (s0 : GS) :
    wpg (genFlags op n a b) E
      (FlagsG Z E base sF dt op n a b (RdW Z E dt n a) (RdW Z E dt n b) s0) s0 := by
  have h1 : (n == 1) = false := by simp; omega
  have h2 : (n == 2) = false := by simp; omega
  simp only [genFlags, flagsW, h1, h2, Bool.false_eq_true, if_false]
  have hacc := accHL_ok (dt := dt) ok hT F ⟨by omega, hn.2⟩ hrt hdep a b s0
  simp only [wpg_bind] at hacc ⊢
  refine wpg_mono hacc ?_
  intro pb sa h1'
  refine wpg_mono h1' ?_
  intro _ sb h2'
  refine wpg_mono h2' ?_
  intro _ s1 ⟨hx1, hacc1, hl⟩
  simp only [wpg_call, wpg_setRegs]
  refine ⟨hx1.trans ((GExt.push _ _).trans (GExt.regs _ _)), fun hxF fr ist tmps s hra hrb R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, hav, hop⟩ :=
    hl ((GExt.push _ _).trans ((GExt.regs _ _).trans hxF)) fr ist tmps s hra hrb R hat
  obtain ⟨c1, s'', cs, st2, at2, ⟨hz, hc⟩, hRel⟩ := rt_call_pre ok hT F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym s!"rt_cmp{bits n}")]⟩) })
    ((GExt.regs _ _).trans hxF) rfl hrt.cmp hdep R1 at1 (fun c1 cs => (hop c1 cs.h cs.l cs.mem).2.2)
  obtain ⟨ha, hb, _⟩ := hop c1 cs.h cs.l cs.mem
  rw [ha, hb] at hz hc
  exact ⟨s'', st1.trans st2, at2, hRel _ (fun o ho => by cases ho) (fun o ho => by cases ho)
    (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => h), FlagsOf.both hz hc⟩

end

end Ember.Proof.Z80Gen
