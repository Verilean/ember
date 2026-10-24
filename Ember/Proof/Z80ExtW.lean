import Ember.Proof.Z80Acc
import Ember.Proof.Z80Mul

/-!
# Ember.Proof.Z80ExtW — `ext` to and from four bytes (plan M7.3)

Zero-extension of `A` or `HL` into the accumulator by a routine of the
runtime; the low two bytes (`ext24_ok`) and the low byte (`ext14_ok`) of
a four-byte value from the accumulator or from memory.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- A value in the accumulator after a routine, then stored: the tail of the extensions to four bytes. -/
theorem accThenStore (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (name : String) (val : Cpu → Nat)
    (hr : RtAcc Z name (fun _ => True) (fun s s' => IR.Sem.rd s'.mem Z.acc 8 = val s))
    (hval : ∀ s c : Cpu, c.a = s.a → c.h = s.h → c.l = s.l → val c = val s) (d : Dst) (s1 : GS) :
    wpg (do call name; killAll; storeAcc 4 d) E (fun _ s2 => GExt s1 s2 ∧
      (GExt s2 sF → ∀ fr ist tmps s, Wr Z E 4 d → Rel Z E fr dt s1.regs ist tmps s →
        At Z.addrs (base + s1.out.size) s → val s < 2 ^ 32 →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
          Rel Z E fr (dtAfter dt d) s2.regs (IR.Sem.setDst Z.c ist tmps 4 d (val s)).1
            (IR.Sem.setDst Z.c ist tmps 4 d (val s)).2 s')) s1 := by
  simp only [wpg_bind, wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep d _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym name)]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hmid.trans hx2, fun hxF fr ist tmps s hwr R hat hlt => ?_⟩
  obtain ⟨c1, s', cs, st, at', hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym name)]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hxF)) rfl hr hdep R hat (fun _ _ => trivial)
  have R2 : Rel Z E fr dt {} ist tmps s' :=
    R.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho) (fun o ho => by cases ho)
      (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h) (fun k sl h => by cases h)
      (fun k o h => by cases h)
  obtain ⟨s'', st2, at2, R3⟩ := hs hxF fr ist tmps s' (val s) hwr R2 at' (by
    have h8 := rd_low s'.mem Z.acc 4 4
    rw [h8, hrel, hval s c1 cs.a cs.h cs.l]
    exact Nat.mod_eq_of_lt hlt)
  exact ⟨s'', st.trans st2, at2, R3⟩

/-- **`ext` to four bytes from two.** -/
theorem ext42_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 4 d 2 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 4 d 2 src) (Rd Z E dt 2 src ∧ Wr Z E 4 d) s0) s0 := by
  simp only [genInstr, store, wpg_bind, wpg_get, show ¬ ((4 : Nat) < 2) from by decide, if_false,
    show ((4 : Nat) == 2) = false from rfl, show ((4 : Nat) == 1) = false from rfl,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, beq_self_eq_true, if_true]
  refine wpg_mono (loadHL_ok (dt := dt) ok F src s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  have tail := accThenStore (dt := dt) ok hT F hrt hdep "rt_acc_hl" (fun s => s.hl.toNat) hrt.accHL
    (fun s c _ hh hl => by rw [hl_congr hh hl]) d s1
  simp only [wpg_bind] at tail
  refine wpg_mono tail ?_
  intro _ sa t1
  refine wpg_mono t1 ?_
  intro _ sb t2
  refine wpg_mono t2 ?_
  intro _ s2 ⟨hx2, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl (hx2.trans hxF) fr ist tmps s hrd R hat
  have hlt := opd_lt Z.c ist tmps 2 src
  obtain ⟨s'', st2, at2, R2⟩ := hs hxF fr ist tmps s' hwr R1 at1 (by
    have := s'.hl.toNat_lt
    omega)
  refine ⟨s'', st1.trans st2, at2, ?_⟩
  have hv : IR.modN 4 (IR.Sem.opd Z.c ist tmps 2 src) = s'.hl.toNat := by
    rw [hHL]
    exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ (8 * 2) ≤ 2 ^ (8 * 4) := by decide
                               omega)
  show Rel Z E fr (dtAfter dt d) s2.regs (IR.Sem.setDst Z.c ist tmps 4 d (IR.modN 4 (IR.Sem.opd Z.c ist tmps 2 src))).1
    (IR.Sem.setDst Z.c ist tmps 4 d (IR.modN 4 (IR.Sem.opd Z.c ist tmps 2 src))).2 s''
  rw [hv]
  exact R2

/-- **`ext` to four bytes from one.** -/
theorem ext41_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 4 d 1 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 4 d 1 src) (Rd Z E dt 1 src ∧ Wr Z E 4 d) s0) s0 := by
  simp only [genInstr, store, wpg_bind, wpg_get, show ¬ ((4 : Nat) < 1) from by decide, if_false,
    show ((4 : Nat) == 2) = false from rfl, show ((4 : Nat) == 1) = false from rfl,
    Bool.false_eq_true, beq_self_eq_true, if_true]
  refine wpg_mono (loadA_ok (dt := dt) ok F src s0) ?_
  intro _ s1 ⟨hx1, _, _, hl⟩
  have tail := accThenStore (dt := dt) ok hT F hrt hdep "rt_acc_a" (fun s => s.a.toNat) hrt.accA
    (fun s c ha _ _ => by rw [ha]) d s1
  simp only [wpg_bind] at tail
  refine wpg_mono tail ?_
  intro _ sa t1
  refine wpg_mono t1 ?_
  intro _ sb t2
  refine wpg_mono t2 ?_
  intro _ s2 ⟨hx2, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, _, hA⟩ := hl (hx2.trans hxF) fr ist tmps s hrd R hat
  have hlt := opd_lt Z.c ist tmps 1 src
  obtain ⟨s'', st2, at2, R2⟩ := hs hxF fr ist tmps s' hwr R1 at1 (by
    have := s'.a.toNat_lt
    omega)
  refine ⟨s'', st1.trans st2, at2, ?_⟩
  have hv : IR.modN 4 (IR.Sem.opd Z.c ist tmps 1 src) = s'.a.toNat := by
    rw [hA]
    exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ (8 * 1) ≤ 2 ^ (8 * 4) := by decide
                               omega)
  show Rel Z E fr (dtAfter dt d) s2.regs (IR.Sem.setDst Z.c ist tmps 4 d (IR.modN 4 (IR.Sem.opd Z.c ist tmps 1 src))).1
    (IR.Sem.setDst Z.c ist tmps 4 d (IR.modN 4 (IR.Sem.opd Z.c ist tmps 1 src))).2 s''
  rw [hv]
  exact R2

/-- **`ext` to two bytes from four**: the low two. -/
theorem ext24_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 2 d 4 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 2 d 4 src)
        ((∀ v, src ≠ .const v → Rd Z E dt 4 src) ∧ Wr Z E 2 d) s0) s0 := by
  simp only [genInstr, store, Codegen.load, wpg_bind, wpg_get, show (2 : Nat) < 4 from by decide, if_true,
    show ((4 : Nat) == 2) = false from rfl, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
    beq_self_eq_true]
  have low4 : ∀ x, x < 2 ^ (8 * 4) → IR.modN 2 x % 65536 = x % 65536 := by
    intro x _
    show x % 65536 % 65536 = _
    omega
  have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
      wpg (do
        let p ← addrOf o
        ins .ld [.hl, .mem p]
        setRegs fun r => { r with hl := [] }
        storeHL d) E
        (InsPost Z E base sF dt (dtAfter dt d) (.ext 2 d 4 o)
          ((∀ v, o ≠ .const v → Rd Z E dt 4 o) ∧ Wr Z E 2 d) s0) s0 := by
    intro o hc
    simp only [wpg_bind]
    refine wpg_mono (addrOf_ok o s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1, hlv⟩
    subst hp
    simp only [wpg_ins, wpg_setRegs]
    refine wpg_mono (thenStoreHL (dt := dt) ok hT F d s0 _ (∀ v, o ≠ .const v → Rd Z E dt 4 o)
      (fun ist tmps => IR.modN 2 (IR.Sem.opd Z.c ist tmps 4 o))
      ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩ (fun hx hrd' fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    have hrd : Rd Z E dt 4 o := hrd' 0 (hc 0)
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨hv, hb⟩ := opd_val (n := 4) ok hrd hsp hc ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o :=
      immW_toNat _ _ _ _ rfl hv (by omega)
    have hS : Sys s (((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16) := by
      simp only [Sys, zsim, and_self]
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem (opdVal E o)]⟩) })
      (i := ⟨.ld, [.hl, .mem (opdVal E o)]⟩) ((GExt.regs _ _).trans hx) rfl R.img R.run
      (by rw [ho1]; exact ⟨ad, had, hpc⟩)
      (s' := ((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16)
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        intro _
        rfl) rfl
    refine ⟨_, hst, hat', R.hl_gone hS rfl (Or.inr ⟨by rw [hr1], by simp only [zsim]⟩)
      (fun n o h => by rw [← hr1]; exact h), ?_⟩
    simp only [zsim]
    rw [cpu_rd16 _ _ (by rw [hnn]; omega), hnn, low4 _ (opd_lt Z.c ist tmps 4 o), ← opd_mem hrd hsp hc hlv R,
      rd_low s.mem _ 2 2]
  by_cases hacc : (s0.regs.acc == some (4, src)) = true
  · simp only [hacc, if_true, wpg_bind, wpg_ins, wpg_setRegs]
    have hacc' : s0.regs.acc = some (4, src) := by simpa using hacc
    refine wpg_mono (thenStoreHL (dt := dt) ok hT F d s0 _ (∀ v, src ≠ .const v → Rd Z E dt 4 src)
      (fun ist tmps => IR.modN 2 (IR.Sem.opd Z.c ist tmps 4 src))
      ((GExt.push _ _).trans (GExt.regs _ _)) (fun hx hrd fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    obtain ⟨ad, had, hpc⟩ := hat
    have hacr := ok.accRam
    have href : AccRef Z := ⟨_, ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩, 0,
      F.emitted (s := { s0 with out := s0.out.push (.ins ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩) })
        ((GExt.regs _ _).trans hx) rfl, rfl⟩
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩).toNat = Z.acc :=
      immW_toNat _ _ _ _ rfl (sym_val ad (ok.accSym href)) (by omega)
    have hS : Sys s (((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩))).tick 16) := by
      simp only [Sys, zsim, and_self]
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩) })
      (i := ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩) ((GExt.regs _ _).trans hx) rfl R.img R.run ⟨ad, had, hpc⟩
      (s' := ((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (.sym "rt_acc")]⟩))).tick 16)
      (fun ad' had' => by
        rw [had] at had'
        cases had'
        intro _
        rfl) rfl
    have hown : Own E src := by
      cases src with
      | const v => trivial
      | tmp t => trivial
      | slot sl => exact Rd.own (dt := dt) (n := 4) (hrd 0 (by intro h; cases h))
    refine ⟨_, hst, hat', R.hl_gone hS rfl (Or.inr ⟨rfl, by simp only [zsim]⟩) (fun n o h => h), ?_⟩
    simp only [zsim]
    rw [cpu_rd16 _ _ (by rw [hnn]; omega), hnn, low4 _ (opd_lt Z.c ist tmps 4 src), ← R.racc 4 src hacc' hown,
      rd_low s.mem _ 2 2]
  · simp only [hacc, Bool.false_eq_true, if_false]
    cases src with
    | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
    | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
    | const v =>
      simp only [wpg_bind]
      refine wpg_mono (loadHL_ok (dt := dt) ok F (.const (v % 2 ^ bits 2)) s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine wpg_mono (thenStoreHL (dt := dt) ok hT F d s0 s1 (∀ w, Opd.const v ≠ .const w → Rd Z E dt 4 (.const v))
        (fun ist tmps => IR.modN 2 (IR.Sem.opd Z.c ist tmps 4 (.const v))) hx1
        (fun hx _ fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
      obtain ⟨s', st, at', R', _, hHL⟩ := hl hx fr ist tmps s trivial R hat
      refine ⟨s', st, at', R', ?_⟩
      rw [hHL, low4 _ (opd_lt Z.c ist tmps 4 (.const v))]
      show v % 2 ^ (8 * 2) % 2 ^ (8 * 2) = v % 2 ^ (8 * 4) % 65536
      have : (2 : Nat) ^ (8 * 2) = 65536 := by decide
      have : (2 : Nat) ^ (8 * 4) = 65536 * 65536 := by decide
      omega

/-- **`ext` to one byte from four**: the low byte. -/
theorem ext14_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 1 d 4 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 1 d 4 src)
        ((∀ v, src ≠ .const v → Rd Z E dt 4 src) ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, store, Codegen.load, wpg_bind, wpg_get, show (1 : Nat) < 4 from by decide, if_true,
    show ((4 : Nat) == 2) = false from rfl, Bool.false_eq_true, if_false, beq_self_eq_true]
  have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
      wpg (do
        let p ← addrOf o
        ins .ld [.a, .mem p]
        setRegs fun r => { r with a := [] }
        storeA d) E
        (InsPost Z E base sF dt (dtAfter dt d) (.ext 1 d 4 o)
          ((∀ v, o ≠ .const v → Rd Z E dt 4 o) ∧ Wr Z E 1 d) s0) s0 := by
    intro o hc
    simp only [wpg_bind]
    refine wpg_mono (addrOf_ok o s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1, hlv⟩
    subst hp
    simp only [wpg_ins, wpg_setRegs]
    refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 _ (∀ v, o ≠ .const v → Rd Z E dt 4 o)
      (fun ist tmps => IR.modN 1 (IR.Sem.opd Z.c ist tmps 4 o))
      ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩ (fun hx hrd' fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    have hrd : Rd Z E dt 4 o := hrd' 0 (hc 0)
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨hv, hb⟩ := opd_val (n := 4) ok hrd hsp hc ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o :=
      immW_toNat _ _ _ _ rfl hv (by omega)
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.a, .mem (opdVal E o)]⟩) })
      (i := ⟨.ld, [.a, .mem (opdVal E o)]⟩) ((GExt.regs _ _).trans hx) rfl R.img R.run
      (by rw [ho1]; exact ⟨ad, had, hpc⟩)
      (s' := ({ (skip (op1 s) 2) with
        a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩) }).tick 13)
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        intro _
        rfl) rfl
    refine ⟨_, hst, hat', R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o h => by rw [← hr1]; exact h)
      (fun o ho hown => R.rhl o (by rw [← hr1]; exact ho) hown) (fun n o h => by rw [← hr1]; exact h), ?_⟩
    simp only [zsim]
    show (s.mem.get! _).toNat = _
    rw [hnn, ← rd_one _ _ (by omega), modN1_mod, ← opd_mem hrd hsp hc hlv R, rd_low s.mem _ 1 3]
  by_cases hacc : (s0.regs.acc == some (4, src)) = true
  · simp only [hacc, if_true, wpg_bind, wpg_ins, wpg_setRegs]
    have hacc' : s0.regs.acc = some (4, src) := by simpa using hacc
    refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 _ (∀ v, src ≠ .const v → Rd Z E dt 4 src)
      (fun ist tmps => IR.modN 1 (IR.Sem.opd Z.c ist tmps 4 src))
      ((GExt.push _ _).trans (GExt.regs _ _)) (fun hx hrd fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    obtain ⟨ad, had, hpc⟩ := hat
    have hacr := ok.accRam
    have href : AccRef Z := ⟨_, ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩, 0,
      F.emitted (s := { s0 with out := s0.out.push (.ins ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩) })
        ((GExt.regs _ _).trans hx) rfl, rfl⟩
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩).toNat = Z.acc :=
      immW_toNat _ _ _ _ rfl (sym_val ad (ok.accSym href)) (by omega)
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩) })
      (i := ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩) ((GExt.regs _ _).trans hx) rfl R.img R.run ⟨ad, had, hpc⟩
      (s' := ({ (skip (op1 s) 2) with
        a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym "rt_acc")]⟩) }).tick 13)
      (fun ad' had' => by
        rw [had] at had'
        cases had'
        intro _
        rfl) rfl
    have hown : Own E src := by
      cases src with
      | const v => trivial
      | tmp t => trivial
      | slot sl => exact Rd.own (dt := dt) (n := 4) (hrd 0 (by intro h; cases h))
    refine ⟨_, hst, hat', R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o h => h)
      (fun o ho hown => R.rhl o ho hown) (fun n o h => h), ?_⟩
    simp only [zsim]
    show (s.mem.get! _).toNat = _
    rw [hnn, ← rd_one _ _ (by omega), modN1_mod, ← R.racc 4 src hacc' hown, rd_low s.mem _ 1 3]
  · simp only [hacc, Bool.false_eq_true, if_false]
    cases src with
    | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
    | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
    | const v =>
      simp only [wpg_bind]
      refine wpg_mono (loadA_ok (dt := dt) ok F (.const (v % 2 ^ bits 1)) s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 s1 (∀ w, Opd.const v ≠ .const w → Rd Z E dt 4 (.const v))
        (fun ist tmps => IR.modN 1 (IR.Sem.opd Z.c ist tmps 4 (.const v))) hx1
        (fun hx _ fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
      obtain ⟨s', st, at', R', _, hA⟩ := hl hx fr ist tmps s trivial R hat
      refine ⟨s', st, at', R', ?_⟩
      rw [hA, modN1_mod]
      show v % 2 ^ (8 * 1) % 2 ^ (8 * 1) = v % 2 ^ (8 * 4) % 256
      have : (2 : Nat) ^ (8 * 1) = 256 := by decide
      have : (2 : Nat) ^ (8 * 4) = 256 * 16777216 := by decide
      omega

end

end Ember.Proof.Z80Gen
