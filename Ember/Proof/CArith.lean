import Ember.Proof.CTypes

/-!
# Ember.Proof.CArith — the operators, as functions on natural numbers (plan M5.8)

`natOp` is what an Ember operator computes on values below `2^n`;
`binop_nat` says so for `Lang.Sem.binop` (which works on `UInt64` with
`mask`).  The C side (`Ember.C.Sem.binop` on the emitted casts) is
compared with `natOp` in `CExpr.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C

theorem mask_toNat (w : Width) (v : UInt64) : (mask w v).toNat = v.toNat % 2 ^ w.bits := by
  cases w with
  | w64 => exact (Nat.mod_eq_of_lt v.toNat_lt).symm
  | w8 =>
    change (v &&& 255).toNat = v.toNat % 2 ^ 8
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 8
  | w16 =>
    change (v &&& 65535).toNat = v.toNat % 2 ^ 16
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 16
  | w32 =>
    change (v &&& 4294967295).toNat = v.toNat % 2 ^ 32
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 32

theorem bits_le (w : Width) : w.bits ≤ 64 := by cases w <;> decide

theorem bits_pos (w : Width) : 8 ≤ w.bits := by cases w <;> decide

theorem pow_bits_dvd (w : Width) : 2 ^ w.bits ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (bits_le w)

/-- An arithmetic operator on values below `2^n`. -/
def natOp (op : BinOp) (n a b : Nat) : Nat :=
  match op with
  | .add => (a + b) % 2 ^ n
  | .sub => (2 ^ n + a - b) % 2 ^ n
  | .mul => (a * b) % 2 ^ n
  | .div => if b = 0 then 0 else a / b
  | .mod => if b = 0 then 0 else a % b
  | .band => a &&& b
  | .bor => a ||| b
  | .bxor => a ^^^ b
  | .shl => if b ≥ n then 0 else (a <<< b) % 2 ^ n
  | .shr => if b ≥ n then 0 else a >>> b
  | _ => 0

/-- A comparison of numbers. -/
def natCmp (op : BinOp) (a b : Nat) : Bool :=
  match op with
  | .eq => a == b
  | .ne => a != b
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .gt => decide (a > b)
  | .ge => decide (a ≥ b)
  | _ => false

theorem binop_cmp (op : BinOp) (hc : op.isCompare = true) (w w' : Width) (x y : UInt64) :
    Lang.Sem.binop op (.int w x) (.int w' y) = some (.bool (natCmp op x.toNat y.toNat)) := by
  cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;>
    simp only [Lang.Sem.binop, natCmp, Option.some.injEq, Val.bool.injEq]
  · rw [Bool.eq_iff_iff]; simp [UInt64.toNat_inj]
  · rw [Bool.eq_iff_iff]; simp [UInt64.toNat_inj]
  · simp [UInt64.lt_iff_toNat_lt]
  · simp [UInt64.le_iff_toNat_le]
  · simp [UInt64.lt_iff_toNat_lt]
  · simp [UInt64.le_iff_toNat_le]

theorem mod_pow_bits (w : Width) (a : Nat) : a % 2 ^ 64 % 2 ^ w.bits = a % 2 ^ w.bits :=
  Nat.mod_mod_of_dvd a (pow_bits_dvd w)

theorem beq_zero_iff (y : UInt64) : (y == 0) = (y.toNat == 0) := by
  rw [Bool.eq_iff_iff]
  simp [← UInt64.toNat_inj]

theorem binop_arith (op : BinOp) (hc : op.isCompare = false) (hl : op.isLogic = false) (w w' : Width)
    (x y : UInt64) (hx : x.toNat < 2 ^ w.bits) (hy : op.isShift = false → y.toNat < 2 ^ w.bits) :
    ∃ r, Lang.Sem.binop op (.int w x) (.int w' y) = some (.int w r) ∧
      r.toNat = natOp op w.bits x.toNat y.toNat := by
  have h64 := bits_le w
  cases op <;> simp only [BinOp.isCompare, BinOp.isLogic, BinOp.isShift, Bool.true_eq_false, forall_const] at hc hl hy <;>
    refine ⟨_, rfl, ?_⟩ <;> simp only [natOp, mask_toNat]
  · rw [UInt64.toNat_add, mod_pow_bits]
  · rw [UInt64.toNat_sub, mod_pow_bits]
    cases w <;> simp only [Width.bits, Nat.reducePow] at hx hy ⊢ <;> omega
  · rw [UInt64.toNat_mul, mod_pow_bits]
  · rw [beq_zero_iff]
    by_cases h0 : y.toNat = 0
    · simp [h0]
    · simp only [h0, beq_iff_eq, if_false, UInt64.toNat_div]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)
  · rw [beq_zero_iff]
    by_cases h0 : y.toNat = 0
    · simp [h0]
    · simp only [h0, beq_iff_eq, if_false, UInt64.toNat_mod]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx)
  · rw [UInt64.toNat_and]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)
  · rw [UInt64.toNat_or]
    exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hx hy)
  · rw [UInt64.toNat_xor]
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy)
  · by_cases hs : y.toNat ≥ w.bits
    · simp [hs]
    · simp only [hs, decide_false, Bool.false_eq_true, if_false, UInt64.toNat_shiftLeft]
      rw [Nat.mod_eq_of_lt (show y.toNat < 64 by omega), mod_pow_bits]
  · by_cases hs : y.toNat ≥ w.bits
    · simp [hs]
    · simp only [hs, decide_false, Bool.false_eq_true, if_false, UInt64.toNat_shiftRight]
      rw [Nat.mod_eq_of_lt (show y.toNat < 64 by omega)]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)

end Ember.Proof.CSim
