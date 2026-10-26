import Ember.Z80.Asm

/-!
# Ember.Proof.Z80Asm — where the assembler puts what it encodes (plan M7.4)

`Asm.assemble` is two passes: `place` gives every item its address and
collects the labels, `emit` encodes every item at its address with the
labels resolved.  `assemble_ok`: in what it returns,

* every item has an address, the next item's is that plus the length of
  its encoding, the first is the origin and the last ends within 64 KB;
* the bytes at an item's address are its encoding in the environment
  `Assembled.env` (the labels, the item's address as `pc`);
* a label resolves to the address of its item.

That an item has in the second pass the size the first pass gave it is
checked by `emit`, so nothing is assumed of the encoder here.
-/

namespace Ember.Proof.Z80Enc
open Ember.Z80.Asm

theorem lookup_any {α : Type} : ∀ (L : List (String × α)) (m : String) (a : α), L.lookup m = some a →
    L.any (·.1 == m) = true
  | [], _, _, h => by simp at h
  | (k, v) :: t, m, a, h => by
    simp only [List.lookup] at h
    simp only [List.any_cons, Bool.or_eq_true]
    cases hk : m == k with
    | true =>
      left
      rw [beq_iff_eq] at hk
      simp [hk]
    | false =>
      simp only [hk] at h
      exact Or.inr (lookup_any t m a h)

/-- A new name leaves what the others resolve to. -/
theorem lookup_fresh {α : Type} {L : List (String × α)} {n m : String} {v a : α} (hn : L.any (·.1 == n) = false)
    (h : L.lookup m = some a) : ((n, v) :: L).lookup m = some a := by
  have hne : (m == n) = false := by
    cases hmn : m == n with
    | false => rfl
    | true =>
      rw [beq_iff_eq] at hmn
      subst hmn
      rw [lookup_any L m a h] at hn
      cases hn
  simp only [List.lookup, hne]
  exact h

theorem map_ok {α β : Type} {x : Except String α} {f : α → β} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a =>
    cases h
    exact ⟨a, rfl, rfl⟩

/-- **The first pass.** -/
theorem place_spec : ∀ (items : List Item) (pc : Nat) (L : List (String × Nat)) (as : List Nat)
    (L' : List (String × Nat)), place items pc L = .ok (as, L') →
    as[0]? = some pc ∧ (∀ n a, L.lookup n = some a → L'.lookup n = some a) ∧
      ∀ (k : Nat) (n : String), items[k]? = some (Item.label n) → ∃ a, as[k]? = some a ∧ L'.lookup n = some a
  | [], pc, L, as, L', h => by
    simp only [place, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ _ h => h, fun k n hk => by simp at hk⟩
  | it :: r, pc, L, as, L', h => by
    have other : ∀ pc', (place r pc' L).map (fun x => (pc :: x.1, x.2)) = .ok (as, L') →
        (∀ n, it ≠ Item.label n) →
        as[0]? = some pc ∧ (∀ n a, L.lookup n = some a → L'.lookup n = some a) ∧
          ∀ (k : Nat) (n : String), (it :: r)[k]? = some (Item.label n) → ∃ a, as[k]? = some a ∧ L'.lookup n = some a := by
      intro pc' hm hne
      obtain ⟨x, hx, hxe⟩ := map_ok hm
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      obtain ⟨_, hmono, hlab⟩ := place_spec r pc' L x.1 x.2 hx
      refine ⟨rfl, hmono, fun k n hk => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        exact absurd hk (hne n)
      | succ k => simpa using hlab k n (by simpa using hk)
    cases it with
    | label n =>
      simp only [place] at h
      split at h
      · cases h
      · rename_i hany
        have hany' : L.any (·.1 == n) = false := Bool.not_eq_true _ ▸ hany
        obtain ⟨x, hx, hxe⟩ := map_ok h
        simp only [Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl⟩ := hxe
        obtain ⟨_, hmono, hlab⟩ := place_spec r pc ((n, pc) :: L) x.1 x.2 hx
        refine ⟨rfl, fun m a hm => hmono m a (lookup_fresh hany' hm), fun k m hk => ?_⟩
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Item.label.injEq] at hk
          subst hk
          exact ⟨pc, rfl, hmono n pc (by simp [List.lookup])⟩
        | succ k => simpa using hlab k m (by simpa using hk)
    | equ n v =>
      simp only [place] at h
      split at h
      · cases h
      · rename_i hany
        have hany' : L.any (·.1 == n) = false := Bool.not_eq_true _ ▸ hany
        obtain ⟨x, hx, hxe⟩ := map_ok h
        simp only [Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl⟩ := hxe
        obtain ⟨_, hmono, hlab⟩ := place_spec r pc ((n, v) :: L) x.1 x.2 hx
        refine ⟨rfl, fun m a hm => hmono m a (lookup_fresh hany' hm), fun k m hk => ?_⟩
        cases k with
        | zero => simp at hk
        | succ k => simpa using hlab k m (by simpa using hk)
    | ins i =>
      simp only [place] at h
      split at h
      · exact other _ h (fun n hn => by cases hn)
      · cases h
    | db vs =>
      simp only [place] at h
      split at h
      · exact other _ h (fun n hn => by cases hn)
      · cases h
    | dw vs =>
      simp only [place] at h
      split at h
      · exact other _ h (fun n hn => by cases hn)
      · cases h
    | ds m =>
      simp only [place] at h
      split at h
      · exact other _ h (fun n hn => by cases hn)
      · cases h
    | comment c =>
      simp only [place] at h
      split at h
      · exact other _ h (fun n hn => by cases hn)
      · cases h

/-- **The second pass.** -/
theorem emit_spec (res : String → Option Int) : ∀ (items : List Item) (as : List Nat) (out : List UInt8),
    emit res items as = .ok out → ∀ k it, items[k]? = some it →
    ∃ ad bs a0, as[k]? = some ad ∧ it.encode { resolve := res, pc := (ad : Int) } = .ok bs ∧
      as[k + 1]? = some (ad + bs.length) ∧ as[0]? = some a0 ∧ a0 ≤ ad ∧
      (∀ j b, bs[j]? = some b → out[ad - a0 + j]? = some b) ∧ ad - a0 + bs.length ≤ out.length
  | [], _, _, _, k, it, hk => by simp at hk
  | it0 :: r, as, out, h, k, it, hk => by
    rcases as with _ | ⟨a, _ | ⟨a', rest⟩⟩
    · simp [emit] at h
    · simp [emit] at h
    · simp only [emit] at h
      split at h
      · rename_i bs0 he
        split at h
        · cases h
        · rename_i hne
          have ha' : a' = a + bs0.length := by simpa using hne
          obtain ⟨out', hr, rfl⟩ := map_ok h
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            refine ⟨a, bs0, a, rfl, by simpa using he, by simp [ha'], rfl, Nat.le_refl _, fun j b hj => ?_, by simp⟩
            have hj' : j < bs0.length := by
              rcases Nat.lt_or_ge j bs0.length with h' | h'
              · exact h'
              · rw [List.getElem?_eq_none h'] at hj; cases hj
            rw [Nat.sub_self, Nat.zero_add, List.getElem?_append_left hj']
            exact hj
          | succ k =>
            obtain ⟨ad, bs, a0, h1, h2, h3, h4, h5, h6, h7⟩ := emit_spec res r (a' :: rest) out' hr k it (by simpa using hk)
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h4
            subst h4
            refine ⟨ad, bs, a, by simpa using h1, h2, by simpa using h3, rfl, by omega, fun j b hj => ?_, by
              rw [List.length_append]; omega⟩
            rw [List.getElem?_append_right (by omega), show ad - a + j - bs0.length = ad - a' + j by omega]
            exact h6 j b hj
      · cases h

/-- **What the assembler returns.** -/
theorem assemble_ok {items : List Item} {origin : Nat} {a : Assembled} (h : assemble items origin = .ok a) :
    ∃ addrs : List Nat, addrs[0]? = some origin ∧
      ∀ k it, items[k]? = some it →
        ∃ ad bs, addrs[k]? = some ad ∧ it.encode (a.env ad) = .ok bs ∧ addrs[k + 1]? = some (ad + bs.length) ∧
          origin ≤ ad ∧ (∀ j b, bs[j]? = some b → a.bytes.data[ad - origin + j]? = some b) ∧
          ad + bs.length ≤ origin + a.bytes.size ∧
          ∀ n, it = Item.label n → a.labels.reverse.lookup n = some ad := by
  unfold assemble at h
  split at h
  · cases h
  · rename_i addrs labels hp
    split at h
    · cases h
    · split at h
      · rename_i bytes hem
        cases h
        obtain ⟨h0, _, hlab⟩ := place_spec items origin [] addrs labels hp
        refine ⟨addrs, h0, fun k it hk => ?_⟩
        obtain ⟨ad, bs, a0, h1, h2, h3, h4, h5, h6, h7⟩ := emit_spec _ items addrs bytes hem k it hk
        rw [h0] at h4
        cases h4
        refine ⟨ad, bs, h1, by simpa [Assembled.env] using h2, h3, h5, fun j b hj => by simpa using h6 j b hj,
          by simp [ByteArray.size]; omega, fun n hn => ?_⟩
        subst hn
        obtain ⟨a1, ha1, hl⟩ := hlab k n hk
        rw [h1] at ha1
        cases ha1
        simpa using hl
      · cases h

/-- info: 'Ember.Proof.Z80Enc.assemble_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assemble_ok

end Ember.Proof.Z80Enc
