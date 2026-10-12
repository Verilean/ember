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
      refine ⟨GExt.push _ _, fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (cpR 7 s) (fun ad _ => does_cp_a.exec _ _ _)
        rfl (does_cp_a.sys s)
      refine ⟨_, st, at', R.keep (does_cp_a.sys s) (by simp only [cpR, zsim]) (by simp only [cpR, zsim]), ?_⟩
      have := cpR7_flags op s
      rw [hA] at this
      exact this
    · rw [if_neg hab]
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok b s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _⟩
      subst hp
      simp only [wpg_ins, wpg_setRegs]
      refine ⟨by simp [GExt, ho1], fun hx fr ist tmps s hrd R hat hA => ?_⟩
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
    refine ⟨GExt.push _ _, fun hx fr ist tmps s hrd R hat hA => ?_⟩
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

end

end Ember.Proof.Z80Gen
