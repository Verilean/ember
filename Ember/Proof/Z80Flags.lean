import Ember.Proof.Z80Bits

/-!
# Ember.Proof.Z80Flags — the zero and carry flags (plan M7.3)

What a comparison leaves in `Z` and `C`: `cp`, `or`, `inc`, `sbc hl,rr`
and `add hl,rr`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm

set_option maxRecDepth 100000 in
theorem flagZ_bit (f : UInt8) : (f &&& FZ != 0) = f.toNat.testBit 6 := by
  have h : ∀ n : Fin 256, ((UInt8.ofNat n.val) &&& FZ != 0) = (UInt8.ofNat n.val).toNat.testBit 6 := by decide
  have := h ⟨f.toNat, f.toNat_lt⟩
  simpa using this

set_option maxRecDepth 100000 in
theorem flagC_bit (f : UInt8) : (f &&& FC != 0) = f.toNat.testBit 0 := by
  have h : ∀ n : Fin 256, ((UInt8.ofNat n.val) &&& FC != 0) = (UInt8.ofNat n.val).toNat.testBit 0 := by decide
  have := h ⟨f.toNat, f.toNat_lt⟩
  simpa using this

theorem bit_testBit (c : Bool) (m : UInt8) (i : Nat) :
    (Cpu.bit c m).toNat.testBit i = (c && m.toNat.testBit i) := by
  cases c <;> simp [Cpu.bit]

theorem sub8_z (a b : UInt8) : ((sub8 a b false).2 &&& FZ != 0) = (a == b) := by
  rw [flagZ_bit]
  simp only [sub8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FH, FPV, FN, FC, Nat.testBit]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h' := congrArg UInt8.toNat h
    rw [UInt8.toNat_sub] at h'
    apply UInt8.toNat_inj.mp
    have h'' : (2 ^ 8 - b.toNat + a.toNat) % 2 ^ 8 = 0 := h'
    omega
  · rintro rfl
    simp

theorem sub8_c (a b : UInt8) : ((sub8 a b false).2 &&& FC != 0) = decide (a.toNat < b.toNat) := by
  rw [flagC_bit]
  simp only [sub8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FH, FPV, FN, FC, Nat.testBit]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_sub]
  simp only [UInt8.toNat_toUInt16]
  show 255 < (2 ^ 16 - b.toNat + a.toNat) % 2 ^ 16 ↔ _
  omega

section
variable (s : Cpu) (v : UInt8)

/-- `cp v`: `Z` when `A = v`, `C` when `A < v`. -/
theorem cp_z : (s.alu 7 v).flag FZ = (s.a == v) := by
  show ((((sub8 s.a v false).2 &&& ~~~FXY) ||| (v &&& FXY)) &&& FZ != 0) = _
  rw [← sub8_z, flagZ_bit, flagZ_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and]
  simp [FXY, Nat.testBit]

theorem cp_c : (s.alu 7 v).flag FC = decide (s.a.toNat < v.toNat) := by
  show ((((sub8 s.a v false).2 &&& ~~~FXY) ||| (v &&& FXY)) &&& FC != 0) = _
  rw [← sub8_c, flagC_bit, flagC_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and]
  simp [FXY, Nat.testBit]

/-- `or v`: `Z` when the result is 0. -/
theorem or_z : (s.alu 6 v).flag FZ = (s.a ||| v == 0) := by
  show ((szxyp (s.a ||| v)) &&& FZ != 0) = _
  rw [flagZ_bit]
  simp only [szxyp, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, Nat.testBit]

/-- `xor v`: `Z` when the result is 0. -/
theorem xor_z : (s.alu 5 v).flag FZ = (s.a ^^^ v == 0) := by
  show ((szxyp (s.a ^^^ v)) &&& FZ != 0) = _
  rw [flagZ_bit]
  simp only [szxyp, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, Nat.testBit]

/-- `and v`: `Z` when the result is 0. -/
theorem and_z : (s.alu 4 v).flag FZ = (s.a &&& v == 0) := by
  show ((szxyp (s.a &&& v) ||| FH) &&& FZ != 0) = _
  rw [flagZ_bit]
  simp only [szxyp, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, Nat.testBit]

/-- `inc`: `Z` when the result is 0. -/
theorem inc8_z : (s.inc8 v).2.flag FZ = (v + 1 == 0) := by
  show (((s.f &&& FC) ||| szxy (v + 1) ||| Cpu.bit (v &&& 0x0F == 0x0F) FH ||| Cpu.bit (v == 0x7F) FPV) &&& FZ != 0) = _
  rw [flagZ_bit]
  simp only [szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, FC, Nat.testBit]

end

section
variable (s : Cpu) (b x y : UInt16)

/-- `sbc hl,rr` with the carry clear: `Z` when equal, `C` when `HL` is below. -/
theorem sbc16_fz (hc : s.flag FC = false) : (s.sbc16 b).flag FZ = (s.hl == b) := by
  unfold Cpu.sbc16
  simp only [hc, Bool.false_eq_true, if_false]
  show ((_ : UInt8) &&& FZ != 0) = _
  rw [flagZ_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, FC, FN, FS, FXY, Nat.testBit]
  have ha := s.hl.toNat_lt
  have hb := b.toNat_lt
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h' := congrArg UInt16.toNat h
    rw [UInt16.toNat_sub] at h'
    apply UInt16.toNat_inj.mp
    have h'' : (2 ^ 16 - b.toNat + s.hl.toNat) % 2 ^ 16 = 0 := h'
    omega
  · intro h
    rw [h]
    first | exact UInt32.sub_self _ | exact UInt16.sub_self _

theorem sbc16_fc (hc : s.flag FC = false) : (s.sbc16 b).flag FC = decide (s.hl.toNat < b.toNat) := by
  unfold Cpu.sbc16
  simp only [hc, Bool.false_eq_true, if_false]
  show ((_ : UInt8) &&& FC != 0) = _
  rw [flagC_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, FC, FN, FS, FXY, Nat.testBit]
  have ha := s.hl.toNat_lt
  have hb := b.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub]
  simp only [UInt16.toNat_toUInt32]
  show 65535 < (2 ^ 32 - b.toNat + s.hl.toNat) % 2 ^ 32 ↔ _
  omega

/-- `add hl,rr` leaves `Z`, and carries when the sum does. -/
theorem add16_fz : (s.add16 x y).2.flag FZ = s.flag FZ := by
  simp only [Cpu.add16, Cpu.flag]
  rw [flagZ_bit, flagZ_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, FC, FS, FXY, Nat.testBit]

theorem add16_fc : (s.add16 x y).2.flag FC = decide (65536 ≤ x.toNat + y.toNat) := by
  simp only [Cpu.add16, Cpu.flag]
  rw [flagC_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FH, FC, FS, FXY, Nat.testBit]
  have ha := x.toNat_lt
  have hb := y.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  simp only [UInt16.toNat_toUInt32]
  show 65535 < (x.toNat + y.toNat) % 2 ^ 32 ↔ _
  omega

end

end Ember.Proof.Z80Gen
