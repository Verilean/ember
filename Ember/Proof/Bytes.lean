import Ember.Util.Bytes

/-!
# Ember.Proof.Bytes — lemmas about `Ember.Bytes`

The byte-buffer facts the header proofs need: what `get`/`get16`/`get32`
read back after `set`/`set16`, from `ofList` and across `++`, and that
splitting a word into big-endian bytes and joining them again is the
identity.
-/

namespace Ember.Bytes

/-! ## Words and their bytes -/

private theorem mul_two_pow_or (k : Nat) {y : Nat} (h : y < 2 ^ k) (x : Nat) :
    x * 2 ^ k ||| y = x * 2 ^ k + y := by
  rw [Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt h]

/-- Joining the two big-endian bytes of a 16-bit word gives the word. -/
theorem join16 (v : UInt16) : ((v >>> 8).toUInt8.toUInt16 <<< 8) ||| v.toUInt8.toUInt16 = v := by
  apply UInt16.toNat_inj.mp
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt16.toNat_toUInt8,
    UInt16.toNat_shiftRight]
  have := v.toNat_lt
  generalize v.toNat = n at *
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, UInt16.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega), mul_two_pow_or 8 (by omega)]
  omega

/-- Joining the four big-endian bytes of a 32-bit word gives the word. -/
theorem join32 (v : UInt32) :
    ((v >>> 24).toUInt8.toUInt32 <<< 24) ||| ((v >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((v >>> 8).toUInt8.toUInt32 <<< 8) ||| v.toUInt8.toUInt32 = v := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight]
  have := v.toNat_lt
  generalize v.toNat = n at *
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := _ * 2 ^ 24) (by omega), Nat.mod_eq_of_lt (a := _ * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := _ * 2 ^ 8) (by omega)]
  rw [mul_two_pow_or 24 (by omega)]
  rw [show n / 2 ^ 24 % 256 * 2 ^ 24 + n / 2 ^ 16 % 256 * 2 ^ 16
        = (n / 2 ^ 24 % 256 * 2 ^ 8 + n / 2 ^ 16 % 256) * 2 ^ 16 by omega,
    mul_two_pow_or 16 (by omega)]
  rw [show (n / 2 ^ 24 % 256 * 2 ^ 8 + n / 2 ^ 16 % 256) * 2 ^ 16 + n / 2 ^ 8 % 256 * 2 ^ 8
        = ((n / 2 ^ 24 % 256 * 2 ^ 8 + n / 2 ^ 16 % 256) * 2 ^ 8 + n / 2 ^ 8 % 256) * 2 ^ 8 by omega,
    mul_two_pow_or 8 (by omega)]
  omega

/-! ## `get` and `set` -/

theorem get_of_lt {b : ByteArray} {i : Nat} (h : i < b.size) : get b i = b[i] := by
  simp [get, h]

theorem get_of_ge {b : ByteArray} {i : Nat} (h : b.size ≤ i) : get b i = 0 := by
  simp [get, Nat.not_lt.mpr h]

@[simp] theorem size_set (b : ByteArray) (i : Nat) (v : UInt8) : (set b i v).size = b.size := by
  unfold set; split <;> simp

theorem get_set (b : ByteArray) (i j : Nat) (v : UInt8) :
    get (set b i v) j = if i = j ∧ i < b.size then v else get b j := by
  unfold set
  by_cases hi : i < b.size
  · by_cases hj : j < b.size
    · rw [if_pos hi, get_of_lt (by simpa using hj), get_of_lt hj, ByteArray.getElem_set! _ _ _ _ hi]
      by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
      · exact hj
    · have hj' : b.size ≤ j := Nat.not_lt.mp hj
      rw [if_pos hi, get_of_ge (by simpa using hj'), get_of_ge hj']
      have : i ≠ j := by omega
      simp [this]
  · simp [hi]

@[simp] theorem size_set16 (b : ByteArray) (i : Nat) (v : UInt16) : (set16 b i v).size = b.size := by
  simp [set16]

theorem get_set16 (b : ByteArray) (i j : Nat) (v : UInt16) :
    get (set16 b i v) j =
      if i + 1 = j ∧ i + 1 < b.size then v.toUInt8
      else if i = j ∧ i < b.size then (v >>> 8).toUInt8 else get b j := by
  simp [set16, get_set]

/-- A 16-bit field reads back what was written, when it lies in the buffer. -/
theorem get16_set16_self {b : ByteArray} {i : Nat} (h : i + 1 < b.size) (v : UInt16) :
    get16 (set16 b i v) i = v := by
  have h0 : i < b.size := by omega
  have e1 : get (set16 b i v) i = (v >>> 8).toUInt8 := by simp [get_set16, h0]
  have e2 : get (set16 b i v) (i + 1) = v.toUInt8 := by simp [get_set16, h]
  rw [get16, e1, e2, join16]

/-- Writing a 16-bit field leaves every disjoint 16-bit field alone. -/
theorem get16_set16_ne {b : ByteArray} {i j : Nat} (h : j + 1 < i ∨ i + 1 < j) (v : UInt16) :
    get16 (set16 b i v) j = get16 b j := by
  have h1 : i + 1 ≠ j := by omega
  have h2 : i ≠ j := by omega
  have h3 : i + 1 ≠ j + 1 := by omega
  have h4 : i ≠ j + 1 := by omega
  simp [get16, get_set16, h1, h2, h4]

/-- Bytes outside a written 16-bit field are unchanged. -/
theorem get_set16_ne {b : ByteArray} {i j : Nat} (h : j < i ∨ i + 1 < j) (v : UInt16) :
    get (set16 b i v) j = get b j := by
  have h1 : i + 1 ≠ j := by omega
  have h2 : i ≠ j := by omega
  simp [get_set16, h1, h2]

/-! ## `ofList` and `++` -/

@[simp] theorem size_ofList (l : List UInt8) : (ofList l).size = l.length := by
  simp [ofList, ByteArray.size]

theorem get_ofList (l : List UInt8) (i : Nat) : get (ofList l) i = l.getD i 0 := by
  by_cases h : i < l.length
  · rw [get_of_lt (by simpa using h)]
    simp [ofList, ByteArray.getElem_eq_getElem_data, h]
  · rw [get_of_ge (by simpa using Nat.not_lt.mp h)]
    simp [List.getD, List.getElem?_eq_none (Nat.not_lt.mp h)]

theorem get_append (a b : ByteArray) (i : Nat) :
    get (a ++ b) i = if i < a.size then get a i else get b (i - a.size) := by
  by_cases h : i < a.size
  · rw [if_pos h, get_of_lt (by simp [ByteArray.size_append]; omega), get_of_lt h,
      ByteArray.getElem_append_left h]
  · rw [if_neg h]
    by_cases h' : i < (a ++ b).size
    · have hb : i - a.size < b.size := by simp [ByteArray.size_append] at h'; omega
      rw [get_of_lt h', get_of_lt hb, ByteArray.getElem_append_right (Nat.not_lt.mp h)]
    · have hb : b.size ≤ i - a.size := by simp [ByteArray.size_append] at h'; omega
      rw [get_of_ge (Nat.not_lt.mp h'), get_of_ge hb]

theorem get16_append_left {a b : ByteArray} {i : Nat} (h : i + 1 < a.size) :
    get16 (a ++ b) i = get16 a i := by
  have h0 : i < a.size := by omega
  simp [get16, get_append, h, h0]

/-- Two buffers with the same bytes are equal. -/
theorem ext_get {a b : ByteArray} (hs : a.size = b.size) (h : ∀ i, i < a.size → get a i = get b i) :
    a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  have := h i hi
  rwa [get_of_lt hi, get_of_lt hi'] at this

/-- A write inside the first part of a concatenation stays there. -/
theorem set_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) (v : UInt8) :
    set (a ++ b) i v = set a i v ++ b := by
  apply ext_get (by simp [ByteArray.size_append])
  intro j _
  simp only [get_set, get_append, size_set, ByteArray.size_append]
  by_cases hij : i = j
  · subst hij; simp [h]; omega
  · simp [hij]

theorem set16_append_left {a b : ByteArray} {i : Nat} (h : i + 1 < a.size) (v : UInt16) :
    set16 (a ++ b) i v = set16 a i v ++ b := by
  have h0 : i < a.size := by omega
  simp only [set16]
  rw [set_append_left h0, set_append_left (by simpa using h)]

/-- `slice` of the second part of a concatenation. -/
theorem slice_append_right (a b : ByteArray) : slice (a ++ b) a.size b.size = b := by
  simp [slice, ByteArray.extract_append_eq_right rfl rfl]

end Ember.Bytes
