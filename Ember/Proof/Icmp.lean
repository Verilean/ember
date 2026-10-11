import Ember.Spec.Icmp
import Ember.Proof.Checksum

/-!
# Ember.Proof.Icmp — the echo reply's checksum (plan M5.1)

`Icmp.reply` is where the Spec uses the RFC 1624 update: it changes the
type byte of a verified echo request and patches the checksum with
`Checksum.incremental` instead of summing the message again.  The reply
it builds verifies (`reply_verifies`).  The statement is about
`verifies` rather than about equality with a recomputed checksum because
the request's checksum may be either representation of zero.
-/

namespace Ember.Spec.Checksum

/-- `add` is addition modulo 0xFFFF. -/
theorem toNat_add_mod (a b : UInt16) : (add a b).toNat % 65535 = (a.toNat + b.toNat) % 65535 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [toNat_add]
  split <;> omega

/-- A sum verifies when it is zero modulo 0xFFFF. -/
theorem verifies_iff (s : UInt16) : verifies s = true ↔ s.toNat % 65535 = 0 := by
  have hs := s.toNat_lt
  simp only [verifies, Bool.or_eq_true, beq_iff_eq, ← UInt16.toNat_inj]
  have : (0xFFFF : UInt16).toNat = 65535 := rfl
  have : (0 : UInt16).toNat = 0 := rfl
  omega

/-- The RFC 1624 update keeps a sum verifying: if the data with word
`m` (rest `r₀`) verifies, and after `m` becomes `m'` the rest around the
checksum field `hc` is `r₁`, then the data with the updated checksum
verifies. -/
theorem verifies_incremental (r₀ r₁ m m' hc : UInt16) (h1 : verifies (add r₀ m) = true)
    (h2 : add r₀ m' = add r₁ hc) : verifies (add r₁ (incremental hc m m')) = true := by
  rw [verifies_iff] at h1 ⊢
  have e2 := congrArg (fun x : UInt16 => x.toNat % 65535) h2
  simp only [toNat_add_mod] at h1 e2 ⊢
  have e3 := toNat_add_mod (add (~~~ hc) (~~~ m)) m'
  have e4 := toNat_add_mod (~~~ hc) (~~~ m)
  have b1 := (add (add (~~~ hc) (~~~ m)) m').toNat_lt
  have b2 := (add (~~~ hc) (~~~ m)).toNat_lt
  have b3 := hc.toNat_lt
  have b4 := m.toNat_lt
  simp only [incremental, toNat_not] at *
  omega

end Ember.Spec.Checksum

namespace Ember.Spec.Icmp
open Ember

/-- M5.1, as the Spec uses it: the echo reply, whose checksum is patched
with the RFC 1624 update, verifies. -/
theorem reply_verifies {msg r : ByteArray} (h : reply msg = .ok r) :
    Checksum.verifies (Checksum.sum r 0 r.size) = true := by
  have ex : ∀ (e : String) (f : Unit → Except String ByteArray),
      (throw e >>= f) ≠ Except.ok r := fun e f hc => by cases hc
  by_cases h1 : msg.size < 8
  · simp only [reply, h1, if_true] at h
    exact absurd h (ex _ _)
  by_cases h2 : Checksum.verifies (Checksum.sum msg 0 msg.size) = true
  · by_cases h3 : Bytes.get msg 0 = typeEchoRequest
    · simp [reply, h1, h2, h3] at h
      cases h
      -- the two words involved: the type/code word and the checksum
      have hsz : 8 ≤ msg.size := by omega
      generalize hnew : (typeEchoReply.toUInt16 <<< 8 ||| Bytes.get16 msg 0 &&& 255) = new
      have l0 : 0 < (Checksum.words msg 0 msg.size).length := by rw [Checksum.length_words]; omega
      obtain ⟨r₀, a1, a2⟩ := Checksum.foldl_add_set (Checksum.words msg 0 msg.size) 0 0 l0
      rw [Checksum.getElem_words (k := 0) (by omega)] at a1
      have hm : Checksum.words (Bytes.set16 msg 0 new) 0 msg.size = (Checksum.words msg 0 msg.size).set 0 new :=
        Checksum.words_set16 (off := 0) (k := 0) (by omega) (by omega) new
      have l1 : 1 < (Checksum.words (Bytes.set16 msg 0 new) 0 msg.size).length := by
        rw [Checksum.length_words]; omega
      obtain ⟨r₁, c1, c2⟩ := Checksum.foldl_add_set (Checksum.words (Bytes.set16 msg 0 new) 0 msg.size) 1 0 l1
      rw [Checksum.getElem_words (k := 1) (by omega), show 0 + 2 * 1 = 2 from rfl,
        Bytes.get16_set16_ne (by omega), hm, a2] at c1
      have hr : Checksum.words (Bytes.set16 (Bytes.set16 msg 0 new) 2
            (Checksum.incremental (Bytes.get16 msg 2) (Bytes.get16 msg 0) new)) 0 msg.size
          = (Checksum.words (Bytes.set16 msg 0 new) 0 msg.size).set 1
              (Checksum.incremental (Bytes.get16 msg 2) (Bytes.get16 msg 0) new) :=
        Checksum.words_set16 (off := 0) (k := 1) (by omega) (by simp; omega) _
      rw [Checksum.sum_eq_foldl, a1] at h2
      rw [Bytes.size_set16, Bytes.size_set16, Checksum.sum_eq_foldl, hr, c2]
      exact Checksum.verifies_incremental r₀ r₁ _ _ _ h2 c1
    · simp [reply, h1, h2, h3] at h
      exact absurd h (by intro hc; cases hc)
  · simp [reply, h1, h2] at h
    exact absurd h (ex _ _)

/-- info: 'Ember.Spec.Icmp.reply_verifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reply_verifies

end Ember.Spec.Icmp
