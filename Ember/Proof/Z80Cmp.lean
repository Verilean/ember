import Ember.Proof.Z80Una
import Ember.Proof.Z80Flags

/-!
# Ember.Proof.Z80Cmp — comparisons (plan M7.3)

`Codegen.genFlags` leaves the comparison of its operands in the flags:
`Z` when they are equal, `C` when the first is below — for `eq` and `ne`
only `Z` is promised (`FlagsOf`).  So the condition `condOf op` holds
exactly when `IR.cmpOp op` does (`cond_of`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The flags hold the comparison of `x` and `y`, as far as `op` needs. -/
def FlagsOf (op : Cmp) (x y : Nat) (s : Cpu) : Prop :=
  match op with
  | .eq | .ne => s.flag FZ = (x == y)
  | .lt | .ge => s.flag FC = decide (x < y)

theorem FlagsOf.both {op : Cmp} {x y : Nat} {s : Cpu} (hz : s.flag FZ = (x == y)) (hc : s.flag FC = decide (x < y)) :
    FlagsOf op x y s := by
  cases op <;> first | exact hz | exact hc

/-- The code of a condition. -/
def ccOf : Cmp → UInt8
  | .eq => 1 | .ne => 0 | .lt => 3 | .ge => 2

theorem cond_ccOf (op : Cmp) : cc? (condOf op) = some (ccOf op) := by cases op <;> rfl

/-- **The condition of the jump is the comparison of the IR.** -/
theorem cond_of {op : Cmp} {x y : Nat} {s : Cpu} (h : FlagsOf op x y s) : s.cond (ccOf op) = IR.cmpOp op x y := by
  cases op
  · show s.flag FZ = (x == y)
    exact h
  · show (!s.flag FZ) = (x != y)
    rw [show s.flag FZ = (x == y) from h]
    rfl
  · show s.flag FC = decide (x < y)
    exact h
  · show (!s.flag FC) = decide (x ≥ y)
    rw [show s.flag FC = decide (x < y) from h]
    by_cases hxy : x < y <;> simp [hxy] <;> omega

theorem u8_beq (a b : UInt8) : (a == b) = (a.toNat == b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact ⟨fun h => by rw [h], fun h => UInt8.toNat_inj.mp h⟩

/-- `cp x` as the model runs it, `x` a register, a byte or `(hl)`. -/
def cpR (z : UInt8) (s : Cpu) : Cpu := ((op1 s).alu 7 ((op1 s).reg .hl z)).tick 4
def cpN (v : Nat) (s : Cpu) : Cpu := ((skip (op1 s) 1).alu 7 (byteOf (Int.ofNat (v % 256)))).tick 7
def cpM (s : Cpu) : Cpu := ((op1 s).alu 7 ((op1 s).rd (op1 s).hl)).tick 7

theorem does_cp_c : Does ⟨.cp, [.c]⟩ (cpR 1) := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, cpR, zsim, and_self]⟩
theorem does_cp_a : Does ⟨.cp, [.a]⟩ (cpR 7) := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, cpR, zsim, and_self]⟩
theorem does_cp_n (v : Nat) : Does ⟨.cp, [n8 v]⟩ (cpN v) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, cpN, zsim, and_self]⟩
theorem does_cp_m : Does ⟨.cp, [.mhl]⟩ cpM := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, cpM, zsim, and_self]⟩

/-- After `cp v` the flags compare `A` and `v`. -/
theorem cp_flags (op : Cmp) (s : Cpu) (v : UInt8) (n : UInt64) :
    FlagsOf op s.a.toNat v.toNat ((s.alu 7 v).tick n) := by
  refine FlagsOf.both ?_ ?_
  · rw [flag_tick, cp_z, u8_beq]
  · rw [flag_tick, cp_c]

theorem cpR7_flags (op : Cmp) (s : Cpu) : FlagsOf op s.a.toNat s.a.toNat (cpR 7 s) := by
  have := cp_flags op (op1 s) ((op1 s).reg .hl 7) 4
  simp only [zsim] at this
  exact this

theorem cpR1_flags (op : Cmp) (s : Cpu) : FlagsOf op s.a.toNat s.c.toNat (cpR 1 s) := by
  have := cp_flags op (op1 s) ((op1 s).reg .hl 1) 4
  simp only [zsim] at this
  exact this

theorem cpN_flags (op : Cmp) (v : Nat) (s : Cpu) : FlagsOf op s.a.toNat (v % 256) (cpN v s) := by
  have := cp_flags op (skip (op1 s) 1) (byteOf (Int.ofNat (v % 256))) 7
  simp only [zsim] at this
  rw [byteOf_toNat] at this
  have e : (Int.ofNat (v % 256) % 256).toNat = v % 256 := by
    show (((v % 256 : Nat) : Int) % 256).toNat = v % 256
    omega
  rw [e] at this
  exact this

theorem cpM_flags (op : Cmp) (s : Cpu) : FlagsOf op s.a.toNat (s.rd s.hl).toNat (cpM s) := by
  have := cp_flags op (op1 s) ((op1 s).rd (op1 s).hl) 7
  simp only [zsim] at this
  exact this

/-! ## `HL` against zero and against a constant, in `A` -/

/-- `inc a` as the model runs it. -/
def incA (s : Cpu) : Cpu :=
  (((op1 s).inc8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).inc8 ((op1 s).reg .hl 7)).1).tick 4

theorem does_inc_a : Does ⟨.inc, [.a]⟩ incA := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, incA, zsim, and_self]⟩

theorem byte_val (v : Nat) (hv : v < 256) : (byteOf (Int.ofNat (v % 256))).toNat = v := by
  rw [byteOf_toNat]
  show (((v % 256 : Nat) : Int) % 256).toNat = v
  omega

/-- `ld a,h; or l`: `Z` when `HL` is 0. -/
theorem zt16 (s : Cpu) : (aluR 6 5 (ldAR 4 s)).flag FZ = (s.hl.toNat == 0) := by
  simp only [aluR, ldAR, zsim]
  rw [or_z]
  simp only [zsim]
  rw [u8_beq, UInt8.toNat_or, hl_toNat, Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  show s.h.toNat ||| s.l.toNat = 0 ↔ _
  rw [or_eq_zero]
  omega

/-- `ld a,h; and l; inc a`: `Z` when `HL` is 65535. -/
theorem eqFFFF (s : Cpu) : (incA (aluR 4 5 (ldAR 4 s))).flag FZ = (s.hl.toNat == 65535) := by
  simp only [incA, aluR, ldAR, zsim]
  rw [inc8_z]
  rw [u8_beq, UInt8.toNat_add, UInt8.toNat_and, hl_toNat, Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  have hh := s.h.toNat_lt
  have hl := s.l.toNat_lt
  have ha : s.h.toNat &&& s.l.toNat < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hh
  have key := and_eq_255 hh hl
  show ((s.h.toNat &&& s.l.toNat) + 1) % 256 = 0 ↔ _
  omega

/-- `ld a,l; xor v; or h`: `Z` when `HL` is `v`, a byte. -/
theorem eqLow (v : Nat) (hv : v < 256) (s : Cpu) : (aluR 6 4 (aluN 5 v (ldAR 5 s))).flag FZ = (s.hl.toNat == v) := by
  simp only [aluR, aluN, ldAR, zsim]
  rw [or_z]
  simp only [zsim]
  rw [u8_beq, UInt8.toNat_or, UInt8.toNat_xor, byte_val v hv, hl_toNat, Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  show (s.l.toNat ^^^ v) ||| s.h.toNat = 0 ↔ _
  rw [or_eq_zero, xor_eq_zero]
  have hl := s.l.toNat_lt
  omega

/-- `ld a,h; xor v; or l`: `Z` when `HL` is `v·256`. -/
theorem eqHigh (v : Nat) (hv : v < 256) (s : Cpu) :
    (aluR 6 5 (aluN 5 v (ldAR 4 s))).flag FZ = (s.hl.toNat == v * 256) := by
  simp only [aluR, aluN, ldAR, zsim]
  rw [or_z]
  simp only [zsim]
  rw [u8_beq, UInt8.toNat_or, UInt8.toNat_xor, byte_val v hv, hl_toNat, Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  show (s.h.toNat ^^^ v) ||| s.l.toNat = 0 ↔ _
  rw [or_eq_zero, xor_eq_zero]
  have hl := s.l.toNat_lt
  omega

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- What a comparison promises: the flags, the states agreeing as before. -/
def Flags (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (op : Cmp) (n : Nat) (a b : Opd) (H : Prop)
    (s0 : GS) (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → H → ∀ fr ist tmps s, Rd Z E dt n a → Rd Z E dt n b → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        FlagsOf op (IR.Sem.opd Z.c ist tmps n a) (IR.Sem.opd Z.c ist tmps n b) s')

/-- `cp` with the second operand, `A` holding the first. -/
theorem cp8Opd_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (a b : Opd) (s0 : GS) :
    wpg (cp8Opd a b) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s → s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          FlagsOf op (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b) s')) s0 := by
  unfold cp8Opd
  have mem_case : ∀ b : Opd, (∀ v, b ≠ .const v) →
      wpg (if (a == b) = true then ins .cp [.a]
        else do
          let p ← addrOf b
          ins .ld [.hl, .imm p]
          ins .cp [.mhl]
          setRegs fun r => { r with hl := [] }) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s → s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          FlagsOf op (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b) s')) s0 := by
    intro b hc
    by_cases hab : (a == b) = true
    · rw [if_pos hab, wpg_ins]
      have hab' : a = b := by simpa using hab
      subst hab'
      refine ⟨GExt.of_out (by simp) rfl rfl, fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (cpR 7 s) (fun ad _ => does_cp_a.exec _ _ _)
        rfl (does_cp_a.sys s)
      refine ⟨_, st, at', R.keep (does_cp_a.sys s) (by simp only [cpR, zsim]) (by simp only [cpR, zsim]), ?_⟩
      have := cpR7_flags op s
      rw [hA] at this
      exact this
    · rw [if_neg hab]
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok b s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1⟩
      subst hp
      simp only [wpg_ins, wpg_setRegs]
      refine ⟨GExt.of_out (by simp [ho1]) hj1 hl1, fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩).toNat = opdAddr Z E b :=
        immW_toNat _ _ _ _ rfl hv (by omega)
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1)
        (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (((GExt.push _ _).trans (GExt.regs _ _)).trans hx) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩)
        (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          rfl) rfl (by simp only [Sys, zsim, and_self])
      obtain ⟨st2, at2, _⟩ := run_reg ok F
        (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (s1 := { s1 with out := (s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).push (.ins ⟨.cp, [.mhl]⟩) })
        ((GExt.regs _ _).trans hx) rfl M1 at1 _ (fun ad' _ => does_cp_m.exec _ _ _) rfl (does_cp_m.sys _)
      refine ⟨_, st1.trans st2, at2, R.hl_gone (by simp only [Sys, cpM, zsim, and_self]) rfl
        (Or.inr ⟨by show s1.regs.a = s0.regs.a; rw [hr1], by simp only [cpM, zsim]⟩)
        (fun n o h => by rw [← hr1]; exact h), ?_⟩
      have := cpM_flags op (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)
      have e1 : (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10).a = s.a := by
        simp only [zsim]
      have e2 : ((((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10).rd
          (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10).hl).toNat =
          IR.Sem.opd Z.c ist tmps 1 b := by
        simp only [zsim]
        show (s.mem.get! _).toNat = _
        rw [hnn, ← rd_one _ _ (by omega)]
        exact opd_mem hrd hsp hc R
      rw [e1, e2, hA] at this
      exact this
  cases b with
  | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
  | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
  | const v =>
    simp only [wpg_ins]
    refine ⟨GExt.of_out (by simp) rfl rfl, fun hx fr ist tmps s hrd R hat hA => ?_⟩
    obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (cpN v s) (fun ad _ => (does_cp_n v).exec _ _ _)
      rfl ((does_cp_n v).sys s)
    refine ⟨_, st, at', R.keep ((does_cp_n v).sys s) (by simp only [cpN, zsim]) (by simp only [cpN, zsim]), ?_⟩
    have := cpN_flags op v s
    rw [hA] at this
    exact this

theorem cmp_beq {x y : Cmp} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

/-- A test for zero: the second operand is the constant 0 and only `Z` is asked. -/
theorem zeroTest_spec {op : Cmp} {b : Opd} (h : zeroTest op b = true) : b = .const 0 ∧ (op = .eq ∨ op = .ne) := by
  simp only [zeroTest, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2.imp cmp_beq cmp_beq⟩

/-- `or a` as the model runs it. -/
def orA (s : Cpu) : Cpu := ((op1 s).alu 6 ((op1 s).reg .hl 7)).tick 4

theorem does_or_a : Does ⟨.or, [.a]⟩ orA := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, orA, zsim, and_self]⟩

theorem orA_a (s : Cpu) : (orA s).a = s.a := by
  simp only [orA, zsim]
  exact UInt8.or_self

theorem orA_z (s : Cpu) : (orA s).flag FZ = (s.a.toNat == 0) := by
  simp only [orA, zsim]
  rw [or_z]
  simp only [zsim]
  rw [UInt8.or_self, u8_beq]
  rfl

theorem flags8_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (a b : Opd) (s0 : GS) :
    wpg (flags8 op a b) E (Flags Z E base sF dt op 1 a b True s0) s0 := by
  unfold flags8
  simp only [wpg_bind, wpg_get]
  by_cases hz : zeroTest op b = true
  · simp only [hz, if_true, wpg_bind]
    obtain ⟨rfl, hop⟩ := zeroTest_spec hz
    refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    rw [wpg_ins]
    refine ⟨hx1.trans (GExt.push _ _), fun hx _ fr ist tmps s hra _ R hat => ?_⟩
    obtain ⟨s', st1, at1, R1, _, hA⟩ := hl ((GExt.push _ _).trans hx) fr ist tmps s hra R hat
    obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1) hx rfl R1.mach at1 (orA s') (fun ad _ => does_or_a.exec _ _ _)
      rfl (does_or_a.sys s')
    refine ⟨_, st1.trans st2, at2, R1.keep (does_or_a.sys s') (orA_a s') (by simp only [orA, zsim]), ?_⟩
    have hf : (orA s').flag FZ = (IR.Sem.opd Z.c ist tmps 1 a == IR.Sem.opd Z.c ist tmps 1 (.const 0)) := by
      rw [orA_z, hA]
      rfl
    rcases hop with rfl | rfl <;> exact hf
  · simp only [hz, Bool.false_eq_true, if_false]
    by_cases hat : (s0.regs.a.contains b && a != b) = true
    · simp only [hat, if_true, wpg_bind, wpg_ins, wpg_setRegs]
      have hbmem : b ∈ s0.regs.a := by
        simp only [Bool.and_eq_true] at hat
        simpa using hat.1
      refine wpg_mono (loadA_ok (dt := dt) ok F a _) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine ⟨((GExt.push _ _).trans (GExt.regs _ _)).trans (hx1.trans (GExt.push _ _)),
        fun hx _ fr ist tmps s hra hrb R hat0 => ?_⟩
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0)
        (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.c, .a]⟩) })
        (((GExt.regs _ _).trans (hx1.trans (GExt.push _ _))).trans hx) rfl R.mach hat0
        (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4) (fun ad _ => rfl) rfl (by simp only [Sys, zsim, and_self])
      have hc : (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4).c.toNat = IR.Sem.opd Z.c ist tmps 1 b := by
        simp only [zsim]
        exact R.ra b hbmem hrb.own
      have R1 : Rel Z E fr dt { s0.regs with a := [] } ist tmps (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4) :=
        R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o ho => ho)
          (fun o ho hown => by simp only [zsim]; exact R.rhl o ho hown) (fun n o h => h)
      obtain ⟨s2, st2, at2, R2, hk2, hA2⟩ := hl ((GExt.push _ _).trans hx) fr ist tmps _ hra R1 at1
      obtain ⟨st3, at3, _⟩ := run_reg ok F (s0 := s1) hx rfl R2.mach at2 (cpR 1 s2)
        (fun ad _ => does_cp_c.exec _ _ _) rfl (does_cp_c.sys s2)
      refine ⟨_, (st1.trans st2).trans st3, at3,
        R2.keep (does_cp_c.sys s2) (by simp only [cpR, zsim]) (by simp only [cpR, zsim]), ?_⟩
      have := cpR1_flags op s2
      rw [hA2, hk2.2.1, hc] at this
      exact this
    · simp only [hat, Bool.false_eq_true, if_false, wpg_bind]
      refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine wpg_mono (cp8Opd_ok (dt := dt) ok F op a b s1) ?_
      intro _ s2 ⟨hx2, hcp⟩
      refine ⟨hx1.trans hx2, fun hx _ fr ist tmps s hra hrb R hat0 => ?_⟩
      obtain ⟨s1', st1, at1, R1, _, hA1⟩ := hl (hx2.trans hx) fr ist tmps s hra R hat0
      obtain ⟨s2', st2, at2, R2, hf⟩ := hcp hx fr ist tmps s1' hrb R1 at1 hA1
      exact ⟨s2', st1.trans st2, at2, R2, hf⟩

/-! ## Two bytes -/

theorem eqConst_spec {op : Cmp} {b : Opd} {v : Nat} (h : eqConst op b = some v) :
    ∃ v0, b = .const v0 ∧ v = v0 % 65536 ∧ (op = .eq ∨ op = .ne) ∧ (v = 65535 ∨ v % 256 = 0 ∨ v / 256 = 0) := by
  cases b with
  | slot sl => cases h
  | tmp t => cases h
  | const v0 =>
    simp only [eqConst] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      exact ⟨v0, rfl, rfl, hc.1.imp cmp_beq cmp_beq, by rcases hc.2 with (h | h) | h <;> simp [h]⟩
    · cases h

/-- `Z` exactly when `HL` is the constant; `HL` is kept. -/
theorem eqHL_ok (ok : Z.OK) (F : GFinal Z base sF) (v : Nat) (hv : v < 65536)
    (hk : v = 65535 ∨ v % 256 = 0 ∨ v / 256 = 0) (s0 : GS) :
    wpg (eqHL v) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → ∀ s, Mach Z s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Sys s s' ∧ s'.hl = s.hl ∧
          s'.flag FZ = (s.hl.toNat == v))) s0 := by
  unfold eqHL
  by_cases h1 : (v == 65535) = true
  · simp only [h1, if_true, wpg_bind, wpg_ins]
    have hv1 : v = 65535 := by simpa using h1
    subst hv1
    refine ⟨pushL_ext [⟨.ld, [.a, .h]⟩, ⟨.and, [.l]⟩, ⟨.inc, [.a]⟩] s0, trivial, fun hx s M hat => ?_⟩
    obtain ⟨st, at', _, hS⟩ := run_list ok F
      [(⟨.ld, [.a, .h]⟩, ldAR 4), (⟨.and, [.l]⟩, aluR 4 5), (⟨.inc, [.a]⟩, incA)]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact does_ld_a_h
        · exact does_alu_reg (op := .and) rfl rfl
        · exact does_inc_a) s0 s hx M hat
    exact ⟨_, st, at', hS, by simp only [List.map, runL, incA, aluR, ldAR, zsim], eqFFFF s⟩
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : (v / 256 == 0) = true
    · simp only [h2, if_true, wpg_bind, wpg_ins]
      have hv2 : v < 256 := by
        have : v / 256 = 0 := by simpa using h2
        omega
      refine ⟨pushL_ext [⟨.ld, [.a, .l]⟩, ⟨.xor, [n8 v]⟩, ⟨.or, [.h]⟩] s0, trivial, fun hx s M hat => ?_⟩
      obtain ⟨st, at', _, hS⟩ := run_list ok F
        [(⟨.ld, [.a, .l]⟩, ldAR 5), (⟨.xor, [n8 v]⟩, aluN 5 v), (⟨.or, [.h]⟩, aluR 6 4)]
        (by
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact does_ld_a_l
          · exact does_alu_imm (op := .xor) rfl v
          · exact does_alu_reg (op := .or) rfl rfl) s0 s hx M hat
      exact ⟨_, st, at', hS, by simp only [List.map, runL, aluN, aluR, ldAR, zsim], eqLow v hv2 s⟩
    · simp only [h2, Bool.false_eq_true, if_false, wpg_bind, wpg_ins]
      have hv3 : v % 256 = 0 := by
        have n1 : v ≠ 65535 := by simpa using h1
        have n2 : v / 256 ≠ 0 := by simpa using h2
        rcases hk with h | h | h
        · exact absurd h n1
        · exact h
        · exact absurd h n2
      refine ⟨pushL_ext [⟨.ld, [.a, .h]⟩, ⟨.xor, [n8 (v / 256)]⟩, ⟨.or, [.l]⟩] s0, trivial, fun hx s M hat => ?_⟩
      obtain ⟨st, at', _, hS⟩ := run_list ok F
        [(⟨.ld, [.a, .h]⟩, ldAR 4), (⟨.xor, [n8 (v / 256)]⟩, aluN 5 (v / 256)), (⟨.or, [.l]⟩, aluR 6 5)]
        (by
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact does_ld_a_h
          · exact does_alu_imm (op := .xor) rfl (v / 256)
          · exact does_alu_reg (op := .or) rfl rfl) s0 s hx M hat
      refine ⟨_, st, at', hS, by simp only [List.map, runL, aluN, aluR, ldAR, zsim], ?_⟩
      have := eqHigh (v / 256) (by omega) s
      rw [show v / 256 * 256 = v by omega] at this
      exact this

theorem u16_beq (a b : UInt16) : (a == b) = (a.toNat == b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact ⟨fun h => by rw [h], fun h => UInt16.toNat_inj.mp h⟩

/-- `sbc hl,de` as the model runs it. -/
def sbcDE (s : Cpu) : Cpu := ((op2 s).sbc16 ((op2 s).rp .hl 1)).tick 15

theorem does_sbc_de : Does ⟨.sbc, [.hl, .de]⟩ sbcDE :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, sbcDE, zsim, and_self]⟩

theorem does_add_de : Does ⟨.add, [.hl, .de]⟩ addHLDE :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, addHLDE, zsim, and_self]⟩

/-- `or a; sbc hl,de`: the flags compare `HL` and `DE`. -/
theorem sub_flags (s : Cpu) :
    (sbcDE (orA s)).flag FZ = (s.hl.toNat == s.de.toNat) ∧
      (sbcDE (orA s)).flag FC = decide (s.hl.toNat < s.de.toNat) ∧
      (sbcDE (orA s)).hl.toNat = (s.hl.toNat + 65536 - s.de.toNat) % 65536 ∧
      (sbcDE (orA s)).de = s.de ∧ (sbcDE (orA s)).a = s.a := by
  have hc : (op2 (orA s)).flag FC = false := by
    simp only [orA, zsim]
    exact alu6_flag _ _
  have hhl : (op2 (orA s)).hl = s.hl := by simp only [orA, zsim]
  have hde : (orA s).de = s.de := by simp only [orA, zsim]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [sbcDE, zsim]
    rw [sbc16_fz _ _ hc, hhl, hde, u16_beq]
  · simp only [sbcDE, zsim]
    rw [sbc16_fc _ _ hc, hhl, hde]
  · simp only [sbcDE, zsim]
    rw [sbc16_val _ _ hc, hhl, hde]
  · simp only [sbcDE, orA, zsim]
  · simp only [sbcDE, zsim]
    exact orA_a s

/-- Adding the subtrahend back restores `HL` and leaves `Z` and `C`. -/
theorem addback (s : Cpu) (x y : Nat) (hx : x < 65536) (hy : y < 65536)
    (hhl : s.hl.toNat = (x + 65536 - y) % 65536) (hde : s.de.toNat = y) :
    (addHLDE s).flag FZ = s.flag FZ ∧ (addHLDE s).flag FC = decide (x < y) ∧ (addHLDE s).hl.toNat = x := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [addHLDE, zsim]
    exact add16_fz _ _ _
  · simp only [addHLDE, zsim]
    rw [add16_fc, hhl, hde]
    by_cases h : x < y <;> simp [h] <;> omega
  · rw [addHLDE_hl, hhl, hde]
    omega

theorem sub16_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (a b : Opd) (s0 : GS) :
    wpg (sub16 a b) E (Flags Z E base sF dt op 2 a b True s0) s0 := by
  -- the subtraction, from `HL` and `DE` holding the operands
  have fin : ∀ (s1 : GS), GExt s0 s1 →
      (∀ s2, GExt s1 s2 → GExt s2 sF → ∀ fr ist tmps s, Rd Z E dt 2 a → Rd Z E dt 2 b →
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 a ∧ s'.de.toNat = IR.Sem.opd Z.c ist tmps 2 b) →
      wpg (do
        ins .or [.a]
        ins .sbc [.hl, .de]
        let e ← read
        if readAgain e a then ins .add [.hl, .de] else setRegs fun r => { r with hl := [] }) E
        (Flags Z E base sF dt op 2 a b True s0) s1 := by
    intro s1 hx1 hpre
    simp only [wpg_bind, wpg_ins, wpg_read]
    by_cases hag : readAgain E a = true
    · simp only [hag, if_true, wpg_ins]
      refine ⟨hx1.trans (pushL_ext [⟨.or, [.a]⟩, ⟨.sbc, [.hl, .de]⟩, ⟨.add, [.hl, .de]⟩] s1),
        fun hx _ fr ist tmps s hra hrb R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, hHL, hDE⟩ := hpre _ (pushL_ext [⟨.or, [.a]⟩, ⟨.sbc, [.hl, .de]⟩, ⟨.add, [.hl, .de]⟩] s1)
        hx fr ist tmps s hra hrb R hat
      obtain ⟨st2, at2, _, hS⟩ := run_list ok F
        [(⟨.or, [.a]⟩, orA), (⟨.sbc, [.hl, .de]⟩, sbcDE), (⟨.add, [.hl, .de]⟩, addHLDE)]
        (by
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact does_or_a
          · exact does_sbc_de
          · exact does_add_de) s1 s' hx R1.mach at1
      obtain ⟨fz, fc, hv, hde, ha⟩ := sub_flags s'
      obtain ⟨bz, bc, bhl⟩ := addback (sbcDE (orA s')) s'.hl.toNat s'.de.toNat s'.hl.toNat_lt s'.de.toNat_lt hv
        (by rw [hde])
      have hhl' : (addHLDE (sbcDE (orA s'))).hl = s'.hl := UInt16.toNat_inj.mp bhl
      have ha' : (addHLDE (sbcDE (orA s'))).a = s'.a := by
        rw [← ha]
        simp only [addHLDE, zsim]
      refine ⟨_, st1.trans st2, at2, R1.keep hS ha' hhl', FlagsOf.both ?_ ?_⟩
      · show (addHLDE (sbcDE (orA s'))).flag FZ = _
        rw [bz, fz, hHL, hDE]
      · show (addHLDE (sbcDE (orA s'))).flag FC = _
        rw [bc, hHL, hDE]
    · simp only [hag, Bool.false_eq_true, if_false, wpg_setRegs]
      refine ⟨hx1.trans ((pushL_ext [⟨.or, [.a]⟩, ⟨.sbc, [.hl, .de]⟩] s1).trans (GExt.regs _ _)),
        fun hx _ fr ist tmps s hra hrb R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, hHL, hDE⟩ := hpre _
        ((pushL_ext [⟨.or, [.a]⟩, ⟨.sbc, [.hl, .de]⟩] s1).trans (GExt.regs _ _)) hx fr ist tmps s hra hrb R hat
      obtain ⟨st2, at2, _, hS⟩ := run_list ok F
        [(⟨.or, [.a]⟩, orA), (⟨.sbc, [.hl, .de]⟩, sbcDE)]
        (by
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact does_or_a
          · exact does_sbc_de) s1 s' ((GExt.regs _ _).trans hx) R1.mach at1
      obtain ⟨fz, fc, _, _, ha⟩ := sub_flags s'
      refine ⟨_, st1.trans st2, at2, R1.hl_gone hS rfl (Or.inr ⟨rfl, ha⟩) (fun n o h => h), FlagsOf.both ?_ ?_⟩
      · show (sbcDE (orA s')).flag FZ = _
        rw [fz, hHL, hDE]
      · show (sbcDE (orA s')).flag FC = _
        rw [fc, hHL, hDE]
  unfold sub16
  simp only [wpg_bind, wpg_get]
  by_cases hat : (s0.regs.hl.contains b && a != b) = true
  · simp only [hat, if_true, wpg_bind, wpg_ins, wpg_setRegs]
    have hbmem : b ∈ s0.regs.hl := by
      simp only [Bool.and_eq_true] at hat
      simpa using hat.1
    refine wpg_mono (loadHL_ok (dt := dt) ok F a _) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine fin s1 (((GExt.push _ _).trans (GExt.regs _ _)).trans hx1) (fun s2 hx2 hxF fr ist tmps s hra hrb R hat0 => ?_)
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.ex, [.de, .hl]⟩) })
      (((GExt.regs _ _).trans hx1).trans (hx2.trans hxF)) rfl R.mach hat0 (exDEHL s) (fun ad _ => rfl) rfl
      (by simp only [Sys, exDEHL, zsim, and_self])
    have R1 : Rel Z E fr dt { s0.regs with hl := [] } ist tmps (exDEHL s) :=
      R.hl_gone (by simp only [Sys, exDEHL, zsim, and_self]) rfl (Or.inr ⟨rfl, by simp only [exDEHL, zsim]⟩)
        (fun n o h => h)
    obtain ⟨s2', st2, at2, R2, hk2, hHL⟩ := hl (hx2.trans hxF) fr ist tmps _ hra R1 at1
    refine ⟨s2', st1.trans st2, at2, R2, hHL, ?_⟩
    rw [de_congr hk2.2.2.2.2.1 hk2.2.2.2.2.2.1, ← R.rhl b hbmem hrb.own, de_toNat, hl_toNat]
    simp only [exDEHL, zsim]
  · simp only [hat, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine wpg_mono (loadDE_ok (dt := dt) ok F b s1) ?_
    intro _ s2 ⟨hx2, hr2, hd⟩
    refine fin s2 (hx1.trans hx2) (fun s3 hx3 hxF fr ist tmps s hra hrb R hat0 => ?_)
    obtain ⟨s1', st1, at1, R1, _, hHL⟩ := hl (hx2.trans (hx3.trans hxF)) fr ist tmps s hra R hat0
    obtain ⟨s2', st2, at2, R2, hhl, _, hDE⟩ := hd (hx3.trans hxF) fr ist tmps s1' hrb R1 at1
    exact ⟨s2', st1.trans st2, at2, R2, by rw [hhl, hHL], hDE⟩

theorem flags16_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (a b : Opd) (s0 : GS) :
    wpg (flags16 op a b) E (Flags Z E base sF dt op 2 a b True s0) s0 := by
  unfold flags16
  by_cases hz : zeroTest op b = true
  · simp only [hz, if_true, wpg_bind]
    obtain ⟨rfl, hop⟩ := zeroTest_spec hz
    refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    simp only [wpg_ins, wpg_setRegs]
    refine ⟨hx1.trans ((pushL_ext [⟨.ld, [.a, .h]⟩, ⟨.or, [.l]⟩] s1).trans (GExt.regs _ _)),
      fun hx _ fr ist tmps s hra _ R hat => ?_⟩
    obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl ((pushL_ext [⟨.ld, [.a, .h]⟩, ⟨.or, [.l]⟩] s1).trans ((GExt.regs _ _).trans hx))
      fr ist tmps s hra R hat
    obtain ⟨st2, at2, _, hS⟩ := run_list ok F [(⟨.ld, [.a, .h]⟩, ldAR 4), (⟨.or, [.l]⟩, aluR 6 5)]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact does_ld_a_h
        · exact does_alu_reg (op := .or) rfl rfl) s1 s' ((GExt.regs _ _).trans hx) R1.mach at1
    refine ⟨_, st1.trans st2, at2, R1.of_sys hS rfl (fun o ho => ho) (fun o ho hown => ?_) (fun n o h => h), ?_⟩
    · have : (runL (List.map (·.2) [((⟨.ld, [.a, .h]⟩ : Instr), ldAR 4), (⟨.or, [.l]⟩, aluR 6 5)]) s').hl = s'.hl := by
        simp only [List.map, runL, aluR, ldAR, zsim]
      rw [this]
      exact R1.rhl o ho hown
    · have hf : (aluR 6 5 (ldAR 4 s')).flag FZ =
          (IR.Sem.opd Z.c ist tmps 2 a == IR.Sem.opd Z.c ist tmps 2 (.const 0)) := by
        rw [zt16, hHL]
        rfl
      rcases hop with rfl | rfl <;> exact hf
  · simp only [hz, Bool.false_eq_true, if_false]
    cases he : eqConst op b with
    | none => exact sub16_ok ok F op a b s0
    | some v =>
      obtain ⟨v0, rfl, rfl, hop, hk⟩ := eqConst_spec he
      simp only [wpg_bind]
      refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine wpg_mono (eqHL_ok ok F (v0 % 65536) (Nat.mod_lt _ (by decide)) hk s1) ?_
      intro _ s2 ⟨hx2, hr2, hq⟩
      rw [wpg_setRegs]
      refine ⟨hx1.trans (hx2.trans (GExt.regs _ _)), fun hx _ fr ist tmps s hra _ R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl (hx2.trans ((GExt.regs _ _).trans hx)) fr ist tmps s hra R hat
      obtain ⟨s'', st2, at2, hS, hhl, hf⟩ := hq ((GExt.regs _ _).trans hx) s' R1.mach at1
      refine ⟨s'', st1.trans st2, at2, R1.of_sys hS rfl (fun o ho => by rw [← hr2]; exact ho)
        (fun o ho hown => by rw [hhl]; exact R1.rhl o (by rw [← hr2]; exact ho) hown)
        (fun n o h => by rw [← hr2]; exact h), ?_⟩
      have hf' : s''.flag FZ = (IR.Sem.opd Z.c ist tmps 2 a == IR.Sem.opd Z.c ist tmps 2 (.const v0)) := by
        rw [hf, hHL]
        rfl
      rcases hop with rfl | rfl <;> exact hf'

/-- **A comparison of one or two bytes leaves its result in the flags.** -/
theorem genFlags_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (n : Nat) (hn : n = 1 ∨ n = 2) (a b : Opd)
    (s0 : GS) : wpg (genFlags op n a b) E (Flags Z E base sF dt op n a b True s0) s0 := by
  rcases hn with rfl | rfl
  · exact flags8_ok ok F op a b s0
  · exact flags16_ok ok F op a b s0

end

end Ember.Proof.Z80Gen
