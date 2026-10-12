import Ember.Proof.Z80Ext

/-!
# Ember.Proof.Z80Acc — values wider than two bytes: the accumulator (plan M7.3)

A value of four bytes lives in the runtime's `rt_acc`: `loadAcc` brings
an operand there (a constant from the literal pool), `storeAcc` stores
it — both by routines of the runtime taken with specifications (`RtW`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The constant `v` of `n` bytes is in the literal pool of the image. -/
def LitOK (Z : ZCtx) (n v : Nat) : Prop :=
  ∃ ad, Z.sym s!"lit{bits n}_{v % 2 ^ bits n}" ad ∧ ad + n ≤ Z.ramStart ∧
    ∀ s : Cpu, Img Z.a 0 s → IR.Sem.rd s.mem ad n = v % 2 ^ (8 * n)

/-- A wide operand can be read: a constant from the pool, the others where they are. -/
def RdW (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (n : Nat) : Opd → Prop
  | .const v => LitOK Z n v
  | o => Rd Z E dt n o

/-- Where a wide operand is, as the generator names it. -/
def ptrVal (E : GEnv) (n : Nat) : Opd → Val
  | .const v => .sym s!"lit{bits n}_{v % 2 ^ bits n}"
  | o => opdVal E o

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem ptrOf_ok (n : Nat) (o : Opd) (s : GS) :
    wpg (ptrOf n o) E (fun p s1 => s1.out = s.out ∧ s1.regs = s.regs ∧ p = ptrVal E n o ∧
      (∀ t, o = .tmp t → E.spilled[t]! = true) ∧ s1.jumps = s.jumps ∧ s1.labelRegs = s.labelRegs) s := by
  unfold ptrOf
  cases o with
  | const v =>
    simp only [wpg_bind, wpg_modify, wpg_pure]
    refine ⟨?_, ?_, rfl, fun t h => (by cases h), ?_, ?_⟩ <;> split <;> rfl
  | slot sl =>
    refine wpg_mono (addrOf_ok (.slot sl) s) ?_
    intro p s1 ⟨h1, h2, h3, h4, _, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h6, h7⟩
  | tmp t =>
    refine wpg_mono (addrOf_ok (.tmp t) s) ?_
    intro p s1 ⟨h1, h2, h3, h4, _, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h6, h7⟩

theorem Rd.own_w {n : Nat} {o : Opd} (h : RdW Z E dt n o) : Own E o := by
  cases o with
  | const v => trivial
  | tmp t => trivial
  | slot sl => exact Rd.own (dt := dt) (n := n) h

/-- **The address of a wide operand**, what is there, and that it is not in the stack. -/
theorem ptr_ok (ok : Z.OK) (hT : FnLay Z E) {n : Nat} (hn : 0 < n) {o : Opd} (hrd : RdW Z E dt n o)
    (hsp : ∀ t, o = .tmp t → E.spilled[t]! = true) (pc : Nat) :
    ∃ A, (Z.a.env pc).val (ptrVal E n o) = Int.ofNat A ∧ A + n ≤ 65536 ∧
      (∀ j, j < n → A + j < Z.stackLo ∨ Z.stackHi ≤ A + j) ∧
      ∀ regs ist tmps (s : Cpu), Rel Z E fr dt regs ist tmps s →
        IR.Sem.rd s.mem A n = IR.Sem.opd Z.c ist tmps n o := by
  have hstk := ok.stack
  have hacr := ok.accRam
  cases o with
  | const v =>
    obtain ⟨ad, hsym, hb, hval⟩ := hrd
    refine ⟨ad, sym_val pc hsym, by omega, fun j hj => Or.inl (by omega), fun regs ist tmps s R => ?_⟩
    rw [hval s R.img]
    rfl
  | slot sl =>
    obtain ⟨hv, hb⟩ := opd_val (dt := dt) ok (o := .slot sl) hrd hsp (fun v h => by cases h) pc
    refine ⟨_, hv, hb, fun j hj => ok.nostack _ (hrd.2.2.1 j hj), fun regs ist tmps s R => ?_⟩
    exact opd_mem (dt := dt) (o := .slot sl) hrd hsp (fun v h => by cases h) R
  | tmp t =>
    obtain ⟨hv, hb⟩ := opd_val (dt := dt) ok (o := .tmp t) hrd hsp (fun v h => by cases h) pc
    have hns := hT.nostack t (hsp t rfl)
    have hsz := (hrd (hsp t rfl)).2.2.2
    refine ⟨_, hv, hb, fun j hj => ?_, fun regs ist tmps s R => ?_⟩
    · show tmpAddr Z E t + j < Z.stackLo ∨ Z.stackHi ≤ tmpAddr Z E t + j
      omega
    · exact opd_mem (dt := dt) (o := .tmp t) hrd hsp (fun v h => by cases h) R

/-- What `loadAcc n o` promises: the operand in the accumulator. -/
def LoadAcc (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (n : Nat) (o : Opd) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.acc = some (n, o) ∧
    (GExt s1 sF → ∀ fr ist tmps s, RdW Z E dt n o → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s')

theorem loadAcc_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 0 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (o : Opd) (s0 : GS) :
    wpg (loadAcc n o) E (LoadAcc Z E base sF dt n o s0) s0 := by
  unfold loadAcc
  simp only [wpg_bind, wpg_get]
  by_cases h1 : (s0.regs.acc == some (n, o)) = true
  · simp only [h1, if_true, wpg_pure]
    have hacc : s0.regs.acc = some (n, o) := by simpa using h1
    exact ⟨GExt.refl _, hacc, fun _ fr ist tmps s _ R hat => ⟨s, Steps.refl _, hat, R⟩⟩
  · simp only [h1, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (ptrOf_ok n o s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, hj1, hl1⟩
    subst hp
    simp only [wpg_ins, wpg_call, wpg_setRegs]
    have hx01 : GExt s0 s1 := ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩
    have hxp : GExt s1 (pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1) :=
      pushL_ext _ _
    refine ⟨hx01.trans (hxp.trans (GExt.regs _ _)), rfl, fun hx fr ist tmps s hrd R hat => ?_⟩
    have hxm : GExt (pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1) sF :=
      (GExt.regs _ _).trans hx
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨A, hv, hb, hns, hmem⟩ := ptr_ok (fr := fr) ok hT hn.1 hrd hsp ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩).toNat = A :=
      immW_toNat _ _ _ _ rfl hv (by omega)
    have hS : Sys s (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩)).tick 10) := by
      simp only [Sys, zsim, and_self]
    obtain ⟨st1, at1, _⟩ := run_reg ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩) })
      ((GExt.push _ _).trans hxm) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩) _
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        intro _
        rfl) rfl hS
    have R1 : Rel Z E fr dt { s0.regs with hl := [] } ist tmps
        (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩)).tick 10) :=
      R.hl_gone hS rfl (Or.inr ⟨rfl, by simp only [zsim]⟩) (fun n o h => h)
    obtain ⟨c1, s', cs, st2, at2, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F
      (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩) })
      (s1 := pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1)
      hxm rfl hrt.ld hdep R1 at1 (fun _ _ => trivial)
    refine ⟨s', st1.trans st2, at2, R1.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o' ho' => by cases ho')
      (fun o' ho' => by cases ho') (fun sl h => by cases h) (fun sl h => by cases h) (fun m o' h hown => ?_)
      (fun m sl h hown => ?_) (fun m o' h => ?_)⟩
    · cases h
      rw [hrel, hl_congr cs.h cs.l]
      simp only [zsim]
      rw [hnn, ← hmem _ ist tmps _ R]
      have hroom := R.room
      have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
      have hstk := ok.stack
      refine rd_congr _ _ _ _ hb (fun x hx1 hx2 => ?_)
      have := hns (x - A) (by omega)
      rw [show A + (x - A) = x by omega] at this
      rw [cs.mem x (by simp only [zsim]; omega)]
      simp only [zsim]
    · cases h
      exact Rd.use (dt := dt) (n := n) hrd
    · cases h
      exact hn.2

end

end Ember.Proof.Z80Gen
