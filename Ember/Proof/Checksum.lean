import Ember.Spec.Checksum
import Ember.Proof.Bytes

/-!
# Ember.Proof.Checksum — the checksum algebra (plan M5.1)

`Checksum.add` is addition modulo 0xFFFF on the representatives
`0 … 0xFFFF`, where `0` only arises as `0 + 0`: a commutative monoid
with unit `0` in which `0xFFFF` is a second zero for every non-zero
word.  From that:

* `sum` is a left fold of `add` over the 16-bit words of the range
  (`sum_eq_foldl`), so it does not depend on the order of the words
  (`sum_perm`, `sum_append_comm`);
* filling a zeroed checksum field with `checksum` makes the range sum to
  `0xFFFF` (`sum_set16_checksum`, `verifies_set16_checksum`);
* the RFC 1624 update `incremental` equals recomputation after one word
  changes — except that when the new data sums to `0` (all words zero)
  recomputation gives `0xFFFF` and the update gives `0x0000`, the other
  representation of zero (`incremental_eq_recompute`,
  `incremental_eq_checksum`).
-/

namespace Ember.Spec.Checksum
open Ember

/-! ## `add` -/

/-- `add` on the values: the sum, minus 0xFFFF when it carries out of 16 bits. -/
theorem toNat_add (a b : UInt16) :
    (add a b).toNat =
      if a.toNat + b.toNat < 65536 then a.toNat + b.toNat else a.toNat + b.toNat - 65535 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [add, UInt32.toNat_toUInt16, UInt32.toNat_add, UInt32.toNat_and, UInt32.toNat_shiftRight,
    UInt16.toNat_toUInt32]
  have h1 : (0xFFFF : UInt32).toNat = 2 ^ 16 - 1 := rfl
  have h2 : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem add_comm (a b : UInt16) : add a b = add b a := by
  apply UInt16.toNat_inj.mp
  simp only [toNat_add]
  split <;> split <;> omega

theorem add_assoc (a b c : UInt16) : add (add a b) c = add a (add b c) := by
  apply UInt16.toNat_inj.mp
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  simp only [toNat_add]
  repeat' split
  all_goals omega

@[simp] theorem add_zero (a : UInt16) : add a 0 = a := by
  apply UInt16.toNat_inj.mp
  have ha := a.toNat_lt
  simp only [toNat_add, UInt16.toNat_zero]
  split <;> omega

@[simp] theorem zero_add (a : UInt16) : add 0 a = a := by rw [add_comm, add_zero]

/-- The form `List.Perm.foldl_eq'` asks for. -/
theorem add_right_comm (z x y : UInt16) : add (add z x) y = add (add z y) x := by
  rw [add_assoc, add_comm x y, ← add_assoc]

/-- A sum is `0` only when both words are (`0xFFFF` is the zero that sums produce). -/
theorem add_eq_zero_iff (a b : UInt16) : add a b = 0 ↔ a = 0 ∧ b = 0 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  constructor
  · intro h
    have h' := congrArg UInt16.toNat h
    simp only [toNat_add, UInt16.toNat_zero] at h'
    constructor <;> apply UInt16.toNat_inj.mp <;> simp only [UInt16.toNat_zero] <;>
      (split at h' <;> omega)
  · rintro ⟨rfl, rfl⟩; simp

theorem toNat_not (a : UInt16) : (~~~ a).toNat = 65535 - a.toNat := by
  simp [UInt16.toNat_not]

/-- A word plus its complement is `0xFFFF`. -/
theorem add_not_self (a : UInt16) : add a (~~~ a) = 0xFFFF := by
  apply UInt16.toNat_inj.mp
  have ha := a.toNat_lt
  simp only [toNat_add, toNat_not]
  split <;> simp <;> omega

/-- `0xFFFF` is neutral for every word except `0`. -/
theorem add_ffff (a : UInt16) : add a 0xFFFF = if a = 0 then 0xFFFF else a := by
  have ha := a.toNat_lt
  by_cases h : a = 0
  · subst h; simp
  · rw [if_neg h]
    have h' : a.toNat ≠ 0 := fun e => h (UInt16.toNat_inj.mp (by simpa using e))
    apply UInt16.toNat_inj.mp
    simp only [toNat_add]
    have : (0xFFFF : UInt16).toNat = 65535 := rfl
    split <;> omega

/-! ## Folds of `add` -/

theorem foldl_add_init (l : List UInt16) (i x : UInt16) :
    l.foldl add (add i x) = add (l.foldl add i) x := by
  induction l generalizing i with
  | nil => rfl
  | cons y t ih => simp only [List.foldl_cons]; rw [add_right_comm, ih]

/-- The one's-complement sum of a list of words does not depend on their order. -/
theorem foldl_add_perm {l₁ l₂ : List UInt16} (h : l₁.Perm l₂) (i : UInt16) :
    l₁.foldl add i = l₂.foldl add i :=
  h.foldl_eq' (fun x _ y _ z => add_right_comm z x y) i

theorem foldl_add_eq_zero_iff (l : List UInt16) (i : UInt16) :
    l.foldl add i = 0 ↔ i = 0 ∧ ∀ w ∈ l, w = 0 := by
  induction l generalizing i with
  | nil => simp
  | cons y t ih =>
    simp only [List.foldl_cons, ih, add_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- Taking one word out of a fold: the rest `r` does not depend on that word. -/
theorem foldl_add_set (l : List UInt16) (k : Nat) (i : UInt16) (hk : k < l.length) :
    ∃ r, l.foldl add i = add r l[k] ∧ ∀ v, (l.set k v).foldl add i = add r v := by
  induction l generalizing k i with
  | nil => simp at hk
  | cons x t ih =>
    cases k with
    | zero =>
      refine ⟨t.foldl add i, ?_, fun v => ?_⟩ <;> simp [foldl_add_init]
    | succ k =>
      obtain ⟨r, h1, h2⟩ := ih k (add i x) (by simpa using hk)
      exact ⟨r, by simpa using h1, fun v => by simpa using h2 v⟩

/-! ## `sum` as a fold over words -/

/-- The words `sum` adds up: `b[off, off+len)` in big-endian pairs, an odd
last byte padded with zero. -/
def words (b : ByteArray) (off len : Nat) : List UInt16 :=
  (List.range (len / 2)).map (fun j => Bytes.get16 b (off + 2 * j)) ++
    if len % 2 = 1 then [(Bytes.get b (off + (len - 1))).toUInt16 <<< 8] else []

/-- The `while` loop of `sum`, run from index `i` with `n` whole words left. -/
private theorem sum_loop (b : ByteArray) (off len : Nat) :
    ∀ (n i : Nat) (s : UInt16), i + 2 * n ≤ len → len < i + 2 * n + 2 →
      (forIn (m := Id) Lean.Loop.mk (s, i) fun _ r =>
          if r.snd + 1 < len then
            pure (ForInStep.yield (add r.fst (Bytes.get16 b (off + r.snd)), r.snd + 2))
          else pure (ForInStep.done (r.fst, r.snd)))
        = pure (((List.range n).map (fun j => Bytes.get16 b (off + i + 2 * j))).foldl add s, i + 2 * n) := by
  intro n
  induction n with
  | zero =>
    intro i s h1 h2
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have : ¬ (i + 1 < len) := by omega
    simp [this]
  | succ n ih =>
    intro i s h1 h2
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have : i + 1 < len := by omega
    simp only [this, if_true, pure_bind]
    have ih' := ih (i + 2) (add s (Bytes.get16 b (off + i))) (by omega) (by omega)
    simp only [forIn] at ih'
    have e : (List.range n).map (fun j => Bytes.get16 b (off + (i + 2) + 2 * j))
        = (List.range n).map ((fun j => Bytes.get16 b (off + i + 2 * j)) ∘ Nat.succ) :=
      List.map_congr_left fun j _ => by
        show Bytes.get16 b _ = Bytes.get16 b _
        congr 1; omega
    have e2 : i + 2 + 2 * n = i + 2 * (n + 1) := by omega
    rw [ih', e, e2, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.foldl_cons, Nat.mul_zero, Nat.add_zero]

/-- `sum` is the left fold of `add` over the words of the range. -/
theorem sum_eq_foldl (b : ByteArray) (off len : Nat) (init : UInt16) :
    sum b off len init = (words b off len).foldl add init := by
  have h := sum_loop b off len (len / 2) 0 init (by omega) (by omega)
  simp only [Nat.add_zero, Nat.zero_add] at h
  unfold sum
  simp only [h, words, List.foldl_append, pure_bind]
  by_cases hodd : len % 2 = 1
  · have h1 : 2 * (len / 2) = len - 1 := by omega
    have h2 : len - 1 < len := by omega
    simp [hodd, h1, h2]
  · have h1 : ¬ 2 * (len / 2) < len := by omega
    simp [hodd, h1]

/-! ## The word list -/

private theorem append_congr {α : Type} {a a' b b' : List α} (h1 : a = a') (h2 : b = b') :
    a ++ b = a' ++ b' := by rw [h1, h2]

/-- The words depend only on the bytes of the range. -/
theorem words_congr {b b' : ByteArray} {off off' len : Nat}
    (h : ∀ i, i < len → Bytes.get b (off + i) = Bytes.get b' (off' + i)) :
    words b off len = words b' off' len := by
  unfold words
  refine append_congr ?_ ?_
  · apply List.map_congr_left
    intro j hj
    have hj' : j < len / 2 := List.mem_range.mp hj
    have h1 := h (2 * j) (by omega)
    have h2 := h (2 * j + 1) (by omega)
    simp only [Bytes.get16, ← Nat.add_assoc] at *
    rw [h1, h2]
  · split
    · rw [h (len - 1) (by omega)]
    · rfl

theorem length_words (b : ByteArray) (off len : Nat) : (words b off len).length = (len + 1) / 2 := by
  unfold words
  split <;> simp <;> omega

theorem getElem_words {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len) :
    (words b off len)[k]'(by rw [length_words]; omega) = Bytes.get16 b (off + 2 * k) := by
  unfold words
  rw [List.getElem_append_left (by simp; omega)]
  simp

/-- Overwriting the `k`-th word of the range overwrites the `k`-th element of `words`. -/
theorem words_set16 {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (v : UInt16) :
    words (Bytes.set16 b (off + 2 * k) v) off len = (words b off len).set k v := by
  unfold words
  rw [List.set_append_left _ _ (by simp; omega)]
  refine append_congr ?_ ?_
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_set]
    by_cases hjk : k = j
    · subst hjk; simp [Bytes.get16_set16_self hb]
    · rw [if_neg hjk, Bytes.get16_set16_ne (by omega)]
  · split
    · rw [Bytes.get_set16_ne (by omega)]
    · rfl

theorem words_append {a b : ByteArray} (ha : a.size % 2 = 0) :
    words (a ++ b) 0 (a.size + b.size) = words a 0 a.size ++ words b 0 b.size := by
  have e1 : (a.size + b.size) / 2 = a.size / 2 + b.size / 2 := by omega
  have e2 : (a.size + b.size) % 2 = b.size % 2 := by omega
  unfold words
  rw [e1, e2, List.range_add, List.map_append, List.map_map, if_neg (by omega : ¬ a.size % 2 = 1),
    List.append_nil, List.append_assoc]
  refine append_congr ?_ ?_
  · apply List.map_congr_left
    intro j hj
    have hj' : j < a.size / 2 := List.mem_range.mp hj
    simp only [Nat.zero_add]
    exact Bytes.get16_append_left (by omega)
  · refine append_congr ?_ ?_
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp, Nat.zero_add, Bytes.get16, Bytes.get_append]
      rw [if_neg (by omega), if_neg (by omega)]
      congr 3 <;> congr 1 <;> omega
    · split
      · simp only [Nat.zero_add, Bytes.get_append]
        rw [if_neg (by omega)]
        congr 4; omega
      · rfl

/-! ## Order independence -/

/-- The sum over a range depends only on its words as a multiset: any
reordering of the 16-bit words gives the same sum. -/
theorem sum_perm {b b' : ByteArray} {off off' len len' : Nat}
    (h : (words b off len).Perm (words b' off' len')) (init : UInt16) :
    sum b off len init = sum b' off' len' init := by
  rw [sum_eq_foldl, sum_eq_foldl, foldl_add_perm h]

/-- The start value is just one more word. -/
theorem sum_init (b : ByteArray) (off len : Nat) (init : UInt16) :
    sum b off len init = add init (sum b off len 0) := by
  rw [sum_eq_foldl, sum_eq_foldl, add_comm, ← foldl_add_init, zero_add]

/-- The sum over a concatenation continues the sum of the first part,
when that part has an even number of bytes. -/
theorem sum_append {a b : ByteArray} (ha : a.size % 2 = 0) (init : UInt16) :
    sum (a ++ b) 0 (a.size + b.size) init = sum b 0 b.size (sum a 0 a.size init) := by
  simp only [sum_eq_foldl, words_append ha, List.foldl_append]

/-- Two blocks of whole words may be swapped. -/
theorem sum_append_comm {a b : ByteArray} (ha : a.size % 2 = 0) (hb : b.size % 2 = 0)
    (init : UInt16) :
    sum (a ++ b) 0 (a.size + b.size) init = sum (b ++ a) 0 (b.size + a.size) init := by
  apply sum_perm
  rw [words_append ha, words_append hb]
  exact List.perm_append_comm

/-- The sum is `0` only for all-zero data with a zero start value. -/
theorem sum_eq_zero_iff (b : ByteArray) (off len : Nat) (init : UInt16) :
    sum b off len init = 0 ↔ init = 0 ∧ ∀ w ∈ words b off len, w = 0 := by
  rw [sum_eq_foldl, foldl_add_eq_zero_iff]

/-- The sum over a range sees only the bytes of the range. -/
theorem sum_congr {b b' : ByteArray} {off off' len : Nat}
    (h : ∀ i, i < len → Bytes.get b (off + i) = Bytes.get b' (off' + i)) (init : UInt16) :
    sum b off len init = sum b' off' len init := by
  rw [sum_eq_foldl, sum_eq_foldl, words_congr h]

/-! ## Filling in and verifying a checksum field -/

/-- Writing `v` into a word of the range that was zero adds `v` to the sum. -/
theorem sum_set16_of_zero {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (hz : Bytes.get16 b (off + 2 * k) = 0) (v init : UInt16) :
    sum (Bytes.set16 b (off + 2 * k) v) off len init = add (sum b off len init) v := by
  have hlen : k < (words b off len).length := by rw [length_words]; omega
  obtain ⟨r, h1, h2⟩ := foldl_add_set (words b off len) k init hlen
  rw [getElem_words hk, hz, add_zero] at h1
  rw [sum_eq_foldl, sum_eq_foldl, words_set16 hk hb, h2, h1]

/-- A range whose (zeroed) checksum field is filled with `checksum` sums to `0xFFFF`. -/
theorem sum_set16_checksum {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (hz : Bytes.get16 b (off + 2 * k) = 0) (init : UInt16) :
    sum (Bytes.set16 b (off + 2 * k) (checksum b off len init)) off len init = 0xFFFF := by
  rw [sum_set16_of_zero hk hb hz, checksum, add_not_self]

/-- The same when a computed `0` is sent as `0xFFFF` (UDP, RFC 768). -/
theorem sum_set16_checksum_nonzero {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (hz : Bytes.get16 b (off + 2 * k) = 0) (init : UInt16) :
    sum (Bytes.set16 b (off + 2 * k)
        (if checksum b off len init == 0 then 0xFFFF else checksum b off len init)) off len init
      = 0xFFFF := by
  rw [sum_set16_of_zero hk hb hz]
  split
  · rename_i h
    have h' : sum b off len init = 0xFFFF := by
      have h0 : ~~~ sum b off len init = 0 := by simpa [checksum] using h
      rw [← UInt16.not_not (a := sum b off len init), h0]; rfl
    rw [h']; rfl
  · rw [checksum, add_not_self]

/-- What a receiver checks: the filled-in range `verifies`. -/
theorem verifies_set16_checksum {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (hz : Bytes.get16 b (off + 2 * k) = 0) (init : UInt16) :
    verifies (sum (Bytes.set16 b (off + 2 * k) (checksum b off len init)) off len init) = true := by
  rw [sum_set16_checksum hk hb hz]; rfl

/-! ## RFC 1624: incremental update -/

/-- The algebra of RFC 1624 eqn. 3 on a sum `add r m` whose word `m`
becomes `m'`: the update yields the new sum `add r m'`, with `0xFFFF`
in place of `0`. -/
theorem add_not_add (r m m' : UInt16) :
    add (add (add r m) (~~~ m)) m' = if add r m' = 0 then 0xFFFF else add r m' := by
  rw [add_assoc r, add_not_self, add_ffff]
  by_cases hr : r = 0
  · subst hr
    simp only [if_true, zero_add]
    rw [add_comm, add_ffff]
  · have : ¬ (add r m' = 0) := fun h => hr ((add_eq_zero_iff _ _).mp h).1
    rw [if_neg hr, if_neg this]

/-- RFC 1624 against recomputation, exactly: after the `k`-th word of the
range changes to `m'`, `incremental` on the old checksum gives the
recomputed checksum — unless the new range sums to `0` (all-zero data and
start value), where recomputation gives `0xFFFF` and the update `0`. -/
theorem incremental_eq_checksum {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (m' init : UInt16) :
    incremental (checksum b off len init) (Bytes.get16 b (off + 2 * k)) m' =
      if sum (Bytes.set16 b (off + 2 * k) m') off len init = 0 then 0
      else checksum (Bytes.set16 b (off + 2 * k) m') off len init := by
  have hlen : k < (words b off len).length := by rw [length_words]; omega
  obtain ⟨r, h1, h2⟩ := foldl_add_set (words b off len) k init hlen
  rw [getElem_words hk] at h1
  have e1 : sum b off len init = add r (Bytes.get16 b (off + 2 * k)) := by rw [sum_eq_foldl, h1]
  have e2 : sum (Bytes.set16 b (off + 2 * k) m') off len init = add r m' := by
    rw [sum_eq_foldl, words_set16 hk hb, h2]
  simp only [incremental, checksum, e1, e2, UInt16.not_not, add_not_add]
  split <;> rfl

/-- M5.1 (a): the RFC 1624 incremental update equals recomputation of
the checksum after one 16-bit word of the range changes, whenever the
new range does not sum to `0`. -/
theorem incremental_eq_recompute {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (m' init : UInt16)
    (hnz : sum (Bytes.set16 b (off + 2 * k) m') off len init ≠ 0) :
    incremental (checksum b off len init) (Bytes.get16 b (off + 2 * k)) m' =
      checksum (Bytes.set16 b (off + 2 * k) m') off len init := by
  rw [incremental_eq_checksum hk hb, if_neg hnz]

/-- In particular the update is exact as soon as the new word is not zero. -/
theorem incremental_eq_recompute_of_ne_zero {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (m' init : UInt16) (hm : m' ≠ 0) :
    incremental (checksum b off len init) (Bytes.get16 b (off + 2 * k)) m' =
      checksum (Bytes.set16 b (off + 2 * k) m') off len init := by
  apply incremental_eq_recompute hk hb
  intro h
  have hlen : k < (words b off len).length := by rw [length_words]; omega
  have := ((sum_eq_zero_iff _ _ _ _).mp h).2 m' (by
    rw [words_set16 hk hb]; exact List.mem_set hlen m')
  exact hm this

/-! ## Axioms -/

/-- info: 'Ember.Spec.Checksum.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_comm

/-- info: 'Ember.Spec.Checksum.add_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_assoc

/-- info: 'Ember.Spec.Checksum.sum_eq_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_eq_foldl

/-- info: 'Ember.Spec.Checksum.sum_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_perm

/-- info: 'Ember.Spec.Checksum.sum_append_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_append_comm

/-- info: 'Ember.Spec.Checksum.sum_set16_checksum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_set16_checksum

/-- info: 'Ember.Spec.Checksum.incremental_eq_checksum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms incremental_eq_checksum

/-- info: 'Ember.Spec.Checksum.incremental_eq_recompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms incremental_eq_recompute

end Ember.Spec.Checksum
