import Ember.Z80.IRSem

/-!
# Ember.Proof.IRMem — the IR's memory (plan M7.1)

`rd` and `wr` are little-endian reads and writes of `n` bytes.  Away
from the top of the 64 KB (which the frame validator guarantees):

* `wr_get`: the bytes of a write, and that it touches no others;
* `rd_wr`: reading back what was written;
* `rd_congr`: a read depends on its bytes only;
* `rd_add`: a read of `n + k` bytes is two reads (so the low bytes of a
  variable are a variable, as the lowering uses).
-/

namespace Ember.Proof.IRSim
open Ember Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run

theorem pow256 (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem get_set (m : ByteArray) (i : Nat) (b : UInt8) (x : Nat) :
    (m.set! i b).get! x = if i = x ∧ i < m.size then b else m.get! x := by
  obtain ⟨bs⟩ := m
  simp only [ByteArray.set!, ByteArray.get!, ByteArray.size]
  by_cases hx : i = x
  · subst hx
    by_cases hi : i < bs.size
    · simp [hi]
    · simp [hi, Array.setIfInBounds]
  · simp [hx, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hx]

@[simp] theorem size_set (m : ByteArray) (i : Nat) (b : UInt8) : (m.set! i b).size = m.size := by
  obtain ⟨bs⟩ := m
  simp [ByteArray.set!, ByteArray.size]

@[simp] theorem wr_size (m : ByteArray) (a n v : Nat) : (wr m a n v).size = m.size := by
  induction n generalizing m a v with
  | zero => rfl
  | succ n ih => rw [wr, ih, size_set]

/-- The bytes of a write. -/
theorem wr_get (m : ByteArray) (a n v x : Nat) (ha : a + n ≤ m.size) (hm : m.size ≤ 65536) :
    (wr m a n v).get! x =
      if a ≤ x ∧ x < a + n then UInt8.ofNat (v / 256 ^ (x - a) % 256) else m.get! x := by
  induction n generalizing m a v with
  | zero =>
    rw [wr]
    simp
    omega
  | succ n ih =>
    rw [wr, ih _ _ _ (by rw [size_set]; omega) (by rw [size_set]; exact hm), get_set]
    have ha' : a % 65536 = a := Nat.mod_eq_of_lt (by omega)
    rw [ha']
    by_cases h1 : a + 1 ≤ x ∧ x < a + 1 + n
    · rw [if_pos h1, if_pos (by omega)]
      congr 2
      rw [show x - a = (x - (a + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    · rw [if_neg h1]
      by_cases h2 : a = x
      · subst h2
        rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
        simp
      · rw [if_neg (by omega), if_neg (by omega)]

/-- A write does not touch the bytes outside it. -/
theorem wr_get_out (m : ByteArray) (a n v x : Nat) (ha : a + n ≤ m.size) (hm : m.size ≤ 65536)
    (hx : x < a ∨ a + n ≤ x) : (wr m a n v).get! x = m.get! x := by
  rw [wr_get m a n v x ha hm, if_neg (by omega)]

/-- A read depends on its bytes only. -/
theorem rd_congr (m m' : ByteArray) (a n : Nat) (ha : a + n ≤ 65536)
    (h : ∀ x, a ≤ x → x < a + n → m'.get! x = m.get! x) : rd m' a n = rd m a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [rd, rd, ih (a + 1) (by omega) (fun x h1 h2 => h x (by omega) (by omega))]
    rw [Nat.mod_eq_of_lt (by omega), h a (Nat.le_refl _) (by omega)]

theorem rd_lt (m : ByteArray) (a n : Nat) : rd m a n < 2 ^ (8 * n) := by
  induction n generalizing a with
  | zero => simp [rd]
  | succ n ih =>
    rw [rd]
    have h1 := ih (a + 1)
    have h2 := (m.get! (a % 65536)).toNat_lt
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
    omega

/-- Reading back what was written. -/
theorem rd_wr (m : ByteArray) (a n v : Nat) (ha : a + n ≤ m.size) (hm : m.size ≤ 65536) :
    rd (wr m a n v) a n = v % 2 ^ (8 * n) := by
  induction n generalizing m a v with
  | zero => simp [rd, Nat.mod_one]
  | succ n ih =>
    rw [rd, Nat.mod_eq_of_lt (by omega), wr_get m a (n + 1) v a ha hm, if_pos (by omega)]
    rw [wr, Nat.mod_eq_of_lt (show a < 65536 by omega), ih _ _ _ (by rw [size_set]; omega) (by rw [size_set]; exact hm)]
    rw [← pow256, ← pow256, Nat.pow_succ', Nat.mod_mul]
    simp

/-- A read away from a write. -/
theorem rd_wr_out (m : ByteArray) (a n b k v : Nat) (ha : a + n ≤ m.size) (hb : b + k ≤ m.size)
    (hm : m.size ≤ 65536) (hd : a + n ≤ b ∨ b + k ≤ a) : rd (wr m b k v) a n = rd m a n :=
  rd_congr _ _ _ _ (by omega) fun x h1 h2 => wr_get_out m b k v x hb hm (by omega)

/-- A read of `n + k` bytes is two reads. -/
theorem rd_add (m : ByteArray) (a n k : Nat) : rd m a (n + k) = rd m a n + 2 ^ (8 * n) * rd m (a + n) k := by
  induction n generalizing a with
  | zero => simp [rd]
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega, rd, rd, ih (a + 1)]
    rw [show a + 1 + n = a + (n + 1) by omega, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add]
    simp only [Nat.reducePow]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- The low bytes of what is at `a`. -/
theorem rd_low (m : ByteArray) (a n k : Nat) : rd m a n = rd m a (n + k) % 2 ^ (8 * n) := by
  rw [rd_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (rd_lt m a n)]

/-- The bytes from `n` on of what is at `a`. -/
theorem rd_high (m : ByteArray) (a n k : Nat) : rd m (a + n) k = rd m a (n + k) / 2 ^ (8 * n) := by
  rw [rd_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (rd_lt m a n), Nat.zero_add]

end Ember.Proof.IRSim
