import Ember.Proof.Z80Fields

/-!
# Ember.Proof.Z80Bits — what the 16-bit instructions compute (plan M7.3)

`add hl,rr`, `sbc hl,rr` after a cleared carry, and the byte-wise logic
operations, as the IR's operations on numbers.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm

set_option maxRecDepth 100000 in
/-- `S`, `Z`, `P/V` and the copies of bits 5 and 3 leave the carry clear. -/
theorem szxyp_fc (r : UInt8) : (szxyp r &&& FC) = 0 := by
  have h : ∀ n : Fin 256, (szxyp (UInt8.ofNat n.val) &&& FC) = 0 := by decide
  have := h ⟨r.toNat, r.toNat_lt⟩
  simpa using this

/-- `or` clears the carry. -/
theorem alu6_flag (s : Cpu) (v : UInt8) : (s.alu 6 v).flag FC = false := by
  show ((szxyp (s.a ||| v)) &&& FC != 0) = false
  rw [szxyp_fc]
  rfl

theorem add16_val (s : Cpu) (a b : UInt16) : (s.add16 a b).1.toNat = (a.toNat + b.toNat) % 65536 := by
  show ((a.toUInt32 + b.toUInt32).toUInt16).toNat = _
  simp only [UInt32.toNat_toUInt16, UInt32.toNat_add, UInt16.toNat_toUInt32]
  have := a.toNat_lt
  have := b.toNat_lt
  omega

/-- `sbc hl,rr` with the carry clear. -/
theorem sbc16_val (s : Cpu) (b : UInt16) (hc : s.flag FC = false) :
    (s.sbc16 b).hl.toNat = (s.hl.toNat + 65536 - b.toNat) % 65536 := by
  show (mk16 (hi _) (lo _)).toNat = _
  rw [mk16_hi_lo]
  show ((s.hl.toUInt32 - b.toUInt32 - (if s.flag FC = true then 1 else 0)).toUInt16).toNat = _
  rw [hc]
  simp only [Bool.false_eq_true, if_false, UInt32.toNat_toUInt16, UInt32.toNat_sub, UInt16.toNat_toUInt32]
  have := s.hl.toNat_lt
  have := b.toNat_lt
  show (2 ^ 32 - 0 + (2 ^ 32 - b.toNat + s.hl.toNat) % 2 ^ 32) % 2 ^ 32 % 65536 = _
  omega

theorem testBit_split (x y i : Nat) (hy : y < 256) :
    (x * 256 + y).testBit i = if i < 8 then y.testBit i else x.testBit (i - 8) := by
  rw [show x * 256 + y = 2 ^ 8 * x + y by omega, Nat.testBit_two_pow_mul_add _ hy]

theorem and_split (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (a * 256 + b) &&& (c * 256 + d) = (a &&& c) * 256 + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  rw [testBit_split _ _ _ hb, testBit_split _ _ _ hd, testBit_split _ _ _ (Nat.lt_of_le_of_lt Nat.and_le_left hb)]
  split <;> simp [Nat.testBit_and]

theorem or_split (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (a * 256 + b) ||| (c * 256 + d) = (a ||| c) * 256 + (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or]
  rw [testBit_split _ _ _ hb, testBit_split _ _ _ hd,
    testBit_split _ _ _ (Nat.or_lt_two_pow (n := 8) hb hd)]
  split <;> simp [Nat.testBit_or]

theorem xor_split (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (a * 256 + b) ^^^ (c * 256 + d) = (a ^^^ c) * 256 + (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  rw [testBit_split _ _ _ hb, testBit_split _ _ _ hd,
    testBit_split _ _ _ (Nat.xor_lt_two_pow (n := 8) hb hd)]
  split <;> simp [Nat.testBit_xor]

theorem or_eq_zero {a b : Nat} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h1 : a ≤ a ||| b := Nat.left_le_or
    have h2 : b ≤ a ||| b := Nat.right_le_or
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem xor_eq_zero {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (·.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp [ha, hb] at this ⊢
  · rintro rfl
    exact Nat.xor_self _

theorem and_eq_255 {h l : Nat} (hh : h < 256) (hl : l < 256) : h &&& l = 255 ↔ h = 255 ∧ l = 255 := by
  constructor
  · intro e
    have h1 : h &&& l ≤ h := Nat.and_le_left
    have h2 : h &&& l ≤ l := Nat.and_le_right
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

section
variable (s : Cpu) (w x : UInt16)

@[zsim] theorem flag_setReg7 (v m : UInt8) : (s.setReg .hl 7 v).flag m = s.flag m := rfl
@[zsim] theorem flag_setHL (w : UInt16) (m : UInt8) : (s.setHL w).flag m = s.flag m := rfl
@[zsim] theorem flag_tick (n : UInt64) (m : UInt8) : (s.tick n).flag m = s.flag m := rfl
@[zsim] theorem flag_op1 (m : UInt8) : (op1 s).flag m = s.flag m := rfl
@[zsim] theorem flag_op2 (m : UInt8) : (op2 s).flag m = s.flag m := rfl
@[zsim] theorem flag_skip (k : UInt16) (m : UInt8) : (skip s k).flag m = s.flag m := rfl
@[zsim] theorem setRp0 : s.setRp .hl 0 w = s.setBC w := rfl
@[zsim] theorem setRp1 : s.setRp .hl 1 w = s.setDE w := rfl
@[zsim] theorem setRp2 : s.setRp .hl 2 w = s.setHL w := rfl
@[zsim] theorem rp0 : s.rp .hl 0 = s.bc := rfl
@[zsim] theorem rp1 : s.rp .hl 1 = s.de := rfl
@[zsim] theorem rp2 : s.rp .hl 2 = s.hl := rfl
@[zsim] theorem add16_a : (s.add16 w x).2.a = s.a := rfl
@[zsim] theorem add16_b : (s.add16 w x).2.b = s.b := rfl
@[zsim] theorem add16_c : (s.add16 w x).2.c = s.c := rfl
@[zsim] theorem add16_d : (s.add16 w x).2.d = s.d := rfl
@[zsim] theorem add16_e : (s.add16 w x).2.e = s.e := rfl
@[zsim] theorem add16_h : (s.add16 w x).2.h = s.h := rfl
@[zsim] theorem add16_l : (s.add16 w x).2.l = s.l := rfl
@[zsim] theorem add16_sp : (s.add16 w x).2.sp = s.sp := rfl
@[zsim] theorem add16_pc : (s.add16 w x).2.pc = s.pc := rfl
@[zsim] theorem add16_mem : (s.add16 w x).2.mem = s.mem := rfl
@[zsim] theorem add16_halted : (s.add16 w x).2.halted = s.halted := rfl
@[zsim] theorem add16_ramStart : (s.add16 w x).2.ramStart = s.ramStart := rfl
@[zsim] theorem add16_io : (s.add16 w x).2.io = s.io := rfl
@[zsim] theorem add16_hl : (s.add16 w x).2.hl = s.hl := rfl
@[zsim] theorem add16_de : (s.add16 w x).2.de = s.de := rfl
@[zsim] theorem add16_bc : (s.add16 w x).2.bc = s.bc := rfl
@[zsim] theorem sbc16_a : (s.sbc16 w).a = s.a := rfl
@[zsim] theorem sbc16_b : (s.sbc16 w).b = s.b := rfl
@[zsim] theorem sbc16_c : (s.sbc16 w).c = s.c := rfl
@[zsim] theorem sbc16_d : (s.sbc16 w).d = s.d := rfl
@[zsim] theorem sbc16_e : (s.sbc16 w).e = s.e := rfl
@[zsim] theorem sbc16_sp : (s.sbc16 w).sp = s.sp := rfl
@[zsim] theorem sbc16_pc : (s.sbc16 w).pc = s.pc := rfl
@[zsim] theorem sbc16_mem : (s.sbc16 w).mem = s.mem := rfl
@[zsim] theorem sbc16_halted : (s.sbc16 w).halted = s.halted := rfl
@[zsim] theorem sbc16_ramStart : (s.sbc16 w).ramStart = s.ramStart := rfl
@[zsim] theorem sbc16_io : (s.sbc16 w).io = s.io := rfl
@[zsim] theorem sbc16_de : (s.sbc16 w).de = s.de := rfl
@[zsim] theorem sbc16_bc : (s.sbc16 w).bc = s.bc := rfl

end

end Ember.Proof.Z80Gen
