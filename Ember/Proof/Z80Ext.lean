import Ember.Proof.Z80Una

/-!
# Ember.Proof.Z80Ext — `ext` between one and two bytes (plan M7.3)

`thenStoreA`, `thenStoreHL`: a value computed into `A` or `HL`, then
stored — the shape of most instructions.  `ext12_ok`: the low byte of
two; `ext21_ok`: a byte as two.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

theorem modN1_mod (x : Nat) : IR.modN 1 x % 256 = x % 256 := by
  show x % 256 % 256 = x % 256
  exact Nat.mod_mod _ _

theorem modN2_byte (x : Nat) (h : x < 256) : IR.modN 2 x % 65536 = x := by
  show x % 65536 % 65536 = x
  omega

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- A value computed into `A`, then stored. -/
theorem thenStoreA (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (s0 s1 : GS) (H : Prop)
    (val : IR.Sem.St → Array Nat → Nat) (hx1 : GExt s0 s1)
    (run : GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.a.toNat = val ist tmps % 256) :
    wpg (storeA d) E (fun _ s2 => GExt s0 s2 ∧
      (GExt s2 sF → H ∧ Wr Z E 1 d → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
          Rel Z E fr (dtAfter dt d) s2.regs (IR.Sem.setDst Z.c ist tmps 1 d (val ist tmps)).1
            (IR.Sem.setDst Z.c ist tmps 1 d (val ist tmps)).2 s')) s1 := by
  refine wpg_mono (storeA_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hH, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, hA⟩ := run (hx2.trans hxF) hH fr ist tmps s R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' (val ist tmps) hwr R1 at1 hA
  exact ⟨s'', st1.trans st2, at2, R2⟩

/-- A value computed into `HL`, then stored. -/
theorem thenStoreHL (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (s0 s1 : GS) (H : Prop)
    (val : IR.Sem.St → Array Nat → Nat) (hx1 : GExt s0 s1)
    (run : GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.hl.toNat = val ist tmps % 65536) :
    wpg (storeHL d) E (fun _ s2 => GExt s0 s2 ∧
      (GExt s2 sF → H ∧ Wr Z E 2 d → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
          Rel Z E fr (dtAfter dt d) s2.regs (IR.Sem.setDst Z.c ist tmps 2 d (val ist tmps)).1
            (IR.Sem.setDst Z.c ist tmps 2 d (val ist tmps)).2 s')) s1 := by
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hH, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, hHL⟩ := run (hx2.trans hxF) hH fr ist tmps s R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' (val ist tmps) hwr R1 at1 hHL
  exact ⟨s'', st1.trans st2, at2, R2⟩

/-- **`ext` to one byte from two**: the low byte. -/
theorem ext12_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 1 d 2 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 1 d 2 src) (Rd Z E dt 2 src ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, store, wpg_bind, wpg_get, show (1 : Nat) < 2 from by decide, if_true, beq_self_eq_true]
  by_cases h1 : s0.regs.hl.contains src = true
  · simp only [h1, if_true, wpg_ins, wpg_setRegs]
    have hmem : src ∈ s0.regs.hl := by simpa using h1
    refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 _ (Rd Z E dt 2 src)
      (fun ist tmps => IR.modN 1 (IR.Sem.opd Z.c ist tmps 2 src))
      ((GExt.push _ _).trans (GExt.regs _ _)) (fun hx hrd fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.a, .l]⟩) })
      ((GExt.regs _ _).trans hx) rfl R.mach hat (ldAR 5 s) (fun _ _ => rfl) rfl (does_ld_a_l.sys s)
    refine ⟨_, st, at', R.of_sys (does_ld_a_l.sys s) rfl (fun o h => h) (fun o ho hown => R.rhl o ho hown)
      (fun n o h => h), ?_⟩
    rw [modN1_mod, ← R.rhl src hmem hrd.own, hl_toNat]
    simp only [ldAR, zsim]
    have := s.l.toNat_lt
    omega
  · simp only [h1, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (addrOf_ok src s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, hc, hj1, hl1⟩
    subst hp
    simp only [wpg_ins, wpg_setRegs]
    refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 _ (Rd Z E dt 2 src)
      (fun ist tmps => IR.modN 1 (IR.Sem.opd Z.c ist tmps 2 src))
      ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩ (fun hx hrd fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E src)]⟩).toNat = opdAddr Z E src := by
      show (w16 (byteOf ((Z.a.env ad).val (opdVal E src))) (byteOf ((Z.a.env ad).val (opdVal E src) / 256))).toNat = _
      rw [hv]
      exact w16_val _ (by omega)
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.a, .mem (opdVal E src)]⟩) })
      (i := ⟨.ld, [.a, .mem (opdVal E src)]⟩) ((GExt.regs _ _).trans hx) rfl R.img R.run
      (by rw [ho1]; exact ⟨ad, had, hpc⟩)
      (s' := ({ (skip (op1 s) 2) with
        a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E src)]⟩) }).tick 13)
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        rfl) rfl
    refine ⟨_, hst, hat', R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o h => by rw [← hr1]; exact h)
      (fun o ho hown => R.rhl o (by rw [← hr1]; exact ho) hown) (fun n o h => by rw [← hr1]; exact h), ?_⟩
    simp only [zsim]
    show (s.mem.get! _).toNat = _
    rw [hnn, ← rd_one _ _ (by omega), modN1_mod, ← opd_mem hrd hsp hc R, rd_low s.mem _ 1 1]

theorem byte0 : (byteOf (Int.ofNat (0 % 256))).toNat = 0 := by decide

def ldH0 (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 4 (byteOf (Int.ofNat (0 % 256)))).tick 7

theorem does_ld_h_0 : Does ⟨.ld, [.h, n8 0]⟩ ldH0 :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldH0, zsim, and_self]⟩

/-- **A byte into `HL`**, the upper byte zero; `A` and `DE` are as they were. -/
theorem loadHLByte_ok (ok : Z.OK) (F : GFinal Z base sF) (o : Opd) (s0 : GS) :
    wpg (loadHLByte o) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 o → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ KeepADE s s' ∧
          s'.hl.toNat = IR.Sem.opd Z.c ist tmps 1 o)) s0 := by
  unfold loadHLByte
  simp only [wpg_bind, wpg_get]
  have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
      wpg (do
        let p ← addrOf o
        ins .ld [.hl, .mem p]
        ins .ld [.h, n8 0]) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 o → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ KeepADE s s' ∧
          s'.hl.toNat = IR.Sem.opd Z.c ist tmps 1 o)) s0 := by
    intro o hc
    simp only [wpg_bind]
    refine wpg_mono (addrOf_ok o s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1⟩
    subst hp
    simp only [wpg_ins]
    refine ⟨⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩, hr1, fun hx fr ist tmps s hrd R hat => ?_⟩
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o :=
      immW_toNat _ _ _ _ rfl hv (by omega)
    have hxa : GExt (pushL [⟨.ld, [.hl, .mem (opdVal E o)]⟩, ⟨.ld, [.h, n8 0]⟩] s1) sF := hx
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem (opdVal E o)]⟩) })
      (i := ⟨.ld, [.hl, .mem (opdVal E o)]⟩) ((GExt.push _ _).trans hxa) rfl R.img R.run
      (by rw [ho1]; exact ⟨ad, had, hpc⟩)
      (s' := ((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16)
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        rfl) rfl
    have hS1 : Sys s (((skip (op1 s) 2).setHL
        ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16) := by
      simp only [Sys, zsim, and_self]
    obtain ⟨st2, at2, _⟩ := run_reg ok F
      (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem (opdVal E o)]⟩) })
      (s1 := pushL [⟨.ld, [.hl, .mem (opdVal E o)]⟩, ⟨.ld, [.h, n8 0]⟩] s1)
      hxa rfl (R.mach.sys hS1) hat' (ldH0 _) (fun _ _ => rfl) rfl (does_ld_h_0.sys _)
    refine ⟨_, hst.trans st2, at2, ⟨hS1.trans (does_ld_h_0.sys _), by simp only [ldH0, zsim],
      by simp only [ldH0, zsim]⟩, ?_⟩
    rw [← opd_mem hrd hsp hc R, rd_one _ _ (by omega), hl_toNat]
    simp only [ldH0, zsim]
    rw [← hnn]
    show (byteOf (Int.ofNat (0 % 256))).toNat * 256 +
      (lo (w16 (s.mem.get! _) (s.mem.get! _))).toNat = _
    rw [w16_eq, lo_mk16, byte0, Nat.zero_mul, Nat.zero_add]
  by_cases ha : s0.regs.a.contains o = true
  · simp only [ha, if_true, wpg_bind, wpg_ins]
    have hmem : o ∈ s0.regs.a := by simpa using ha
    refine ⟨pushL_ext [⟨.ld, [.l, .a]⟩, ⟨.ld, [.h, n8 0]⟩] s0, trivial, fun hx fr ist tmps s hrd R hat => ?_⟩
    obtain ⟨st, at', _, hS⟩ := run_list ok F [(⟨.ld, [.l, .a]⟩, ldRA 5), (⟨.ld, [.h, n8 0]⟩, ldH0)]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact does_ld_l_a
        · exact does_ld_h_0) s0 s hx R.mach hat
    refine ⟨_, st, at', ⟨hS, by simp only [List.map, runL, ldRA, ldH0, zsim],
      by simp only [List.map, runL, ldRA, ldH0, zsim]⟩, ?_⟩
    rw [← R.ra o hmem hrd.own, hl_toNat]
    simp only [List.map, runL, ldRA, ldH0, zsim]
    rw [byte0, Nat.zero_mul, Nat.zero_add]
  · simp only [ha, Bool.false_eq_true, if_false]
    cases o with
    | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
    | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
    | const v =>
      simp only [wpg_ins]
      refine ⟨GExt.push _ _, trivial, fun hx fr ist tmps s hrd R hat => ?_⟩
      have hS : Sys s (((skip (op1 s) 2).setHL (w16 (byteOf (Int.ofNat (v % 256 % 65536)))
          (byteOf (Int.ofNat (v % 256 % 65536) / 256)))).tick 10) := by simp only [Sys, zsim, and_self]
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0)
        (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.hl, n16 (v % 256)]⟩) })
        hx rfl R.mach hat _ (fun _ _ => rfl) rfl hS
      refine ⟨_, st, at', ⟨hS, by simp only [zsim], by simp only [zsim]⟩, ?_⟩
      simp only [zsim]
      rw [w16_val _ (Nat.mod_lt _ (by decide))]
      show v % 256 % 65536 = v % 256
      omega

/-- **`ext` to two bytes from one.** -/
theorem ext21_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.ext 2 d 1 src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.ext 2 d 1 src) (Rd Z E dt 1 src ∧ Wr Z E 2 d) s0) s0 := by
  simp only [genInstr, store, wpg_bind, wpg_get, show ¬ ((2 : Nat) < 1) from by decide, if_false,
    beq_self_eq_true, if_true, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true]
  refine wpg_mono (loadHLByte_ok (dt := dt) ok F src s0) ?_
  intro _ s1 ⟨hx1, hr1, h⟩
  rw [wpg_setRegs]
  refine wpg_mono (thenStoreHL (dt := dt) ok hT F d s0 _ (Rd Z E dt 1 src)
    (fun ist tmps => IR.modN 2 (IR.Sem.opd Z.c ist tmps 1 src))
    (hx1.trans (GExt.regs _ _)) (fun hx hrd fr ist tmps s R hat => ?_)) (fun _ s2 h => h)
  obtain ⟨s', st, at', hk, hv⟩ := h ((GExt.regs _ _).trans hx) fr ist tmps s hrd R hat
  refine ⟨s', st, at', R.hl_gone hk.1 rfl (Or.inr ⟨by rw [hr1], hk.2.1⟩) (fun n o h => by rw [← hr1]; exact h), ?_⟩
  rw [modN2_byte _ (opd_lt _ _ _ 1 _)]
  exact hv

end

end Ember.Proof.Z80Gen
