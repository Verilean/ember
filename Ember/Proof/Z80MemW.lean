import Ember.Proof.Z80Acc
import Ember.Proof.Z80Mem

/-!
# Ember.Proof.Z80MemW — a `load` of four bytes through an address (plan M7.3)

The address into `HL` (`genAddr_ok`), `call rt_ld32` (`RtW.ld`: the four
bytes at `HL` into the accumulator), then `storeAcc`.  What `rt_ld32`
asks of the bytes at `HL` (`HLApart`: no wrap, apart from the
accumulator and the stack) follows from their being shared bytes
(`AddrData`) and `ZCtx.OK` (`accData`, `nostack`).

A `store` of four bytes through an address is not covered: its code
keeps the address on the stack (`push hl`) while `loadAcc` runs.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- **`load` of four bytes.** -/
theorem load4_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.load 4 d p)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrData Z p 4 ∧ Wr Z E 4 d → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.load 4 d p) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.load 4 d p)))) s0 := by
  simp only [genInstr, store, wpg_bind, show ((4 : Nat) == 1) = false from rfl,
    show ((4 : Nat) == 2) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
  intro _ s1 ⟨hx1, _, _, ha⟩
  simp only [wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep d _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym "rt_ld32")]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hx1.trans (hmid.trans hx2), fun hxF ⟨hN, hD, hwr⟩ fr ist tmps s R hat => ?_⟩
  have h1 := ha (hmid.trans (hx2.trans hxF)) hN fr ist tmps s R hat
  simp only [IR.Sem.step]
  cases haddr : IR.Sem.addr Z.c ist tmps p with
  | none =>
    rw [haddr] at h1
    exact h1
  | some a =>
    rw [haddr] at h1
    by_cases hb : IR.Sem.inBound Z.c ist tmps p = true
    · simp only [hb, if_true]
      obtain ⟨s', st, at', R', _, _, hv⟩ := h1
      obtain ⟨hbd, hdat⟩ := hD ist tmps a haddr hb
      have hhl : s'.hl.toNat = a := by rw [hv, Nat.mod_eq_of_lt (by omega)]
      have hroom := R'.room
      have hspv : s'.sp.toNat = fr.sp.toNat := by rw [R'.sp]
      have hstk := ok.stack
      obtain ⟨c1, s'', cs, st2, at2, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F (s0 := s1)
        (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym "rt_ld32")]⟩) })
        ((GExt.regs _ _).trans (hx2.trans hxF)) rfl hrt.wide.ld hdep R' at' (fun c1 cs => by
          have hc1 : c1.hl.toNat = a := by rw [hl_congr cs.h cs.l]; exact hhl
          exact ⟨by rw [hc1]; exact hbd, fun j hj => by
            rw [hc1]
            exact ⟨ok.accData _ (hdat j hj), ok.nostack _ (hdat j hj)⟩⟩)
      have R2 : Rel Z E fr dt {} ist tmps s'' :=
        R'.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho) (fun o ho => by cases ho)
          (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h) (fun k sl h => by cases h)
          (fun k o h => by cases h)
      obtain ⟨s3, st3, at3, R3⟩ := hs hxF fr ist tmps s'' (IR.Sem.rd ist.mem a 4) hwr R2 at2 (by
        rw [hrel, hl_congr cs.h cs.l, hhl]
        refine rd_congr _ _ _ _ hbd (fun x hx1 hx2 => ?_)
        have hdx := hdat (x - a) (by omega)
        rw [show a + (x - a) = x by omega] at hdx
        have hns := ok.nostack _ hdx
        rw [cs.mem x (by omega), R'.mem x hdx])
      exact ⟨s3, (st.trans st2).trans st3, at3, R3⟩
    · simp only [hb, Bool.false_eq_true, if_false]
      trivial

end

/-- info: 'Ember.Proof.Z80Gen.load4_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms load4_ok

end Ember.Proof.Z80Gen
