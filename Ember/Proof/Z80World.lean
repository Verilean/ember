import Ember.Lang.Eval

/-!
# Ember.Proof.Z80World — the input of the world, by position (plan M7.3)

`World.next` skips exhausted chunks by a recursion of its own
(`World.normalize`).  `normPos` is that skipping as a function of the
position alone; with it: what `next` returns (`next_eq`), and that
taking an item moves the position (`next_moves`).
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember
open Ember.Lang (World)
open Ember.Trace (Input)

/-- Where the next item of input is: exhausted chunks skipped. -/
def normPos (inputs : Array Input) (pos off : Nat) : Nat × Nat :=
  if h : pos < inputs.size then
    match inputs[pos] with
    | .rx b => if off ≥ b.size then normPos inputs (pos + 1) 0 else (pos, off)
    | .tick => (pos, off)
  else (pos, off)
termination_by inputs.size - pos

theorem wnorm : ∀ (n : Nat) (w : World), n = w.inputs.size - w.pos → w.framed = false →
    w.normalize = { w with pos := (normPos w.inputs w.pos w.off).1, off := (normPos w.inputs w.pos w.off).2 } := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hn hf
    obtain ⟨inputs, pos, off, cur, events, frame, mmio, framed⟩ := w
    simp only at hf hn
    subst hf
    rw [World.normalize, normPos]
    simp only [Bool.false_eq_true, if_false]
    by_cases h : pos < inputs.size
    · simp only [h, dite_true]
      cases hx : inputs[pos] with
      | tick => rfl
      | rx b =>
        simp only
        by_cases ho : off ≥ b.size
        · simp only [ho, if_true]
          rw [ih (inputs.size - (pos + 1)) (by omega) _ rfl rfl]
        · simp only [ho, if_false]
    · simp only [h, dite_false]

/-- The world with its position moved, an item taken. -/
def wTook (w : World) (x : Nat) (p : Nat × Nat) : World := { w with cur := x, pos := p.1, off := p.2 }
def wAt (w : World) (p : Nat × Nat) : World := { w with pos := p.1, off := p.2 }

/-- `World.next`, by where the next item is. -/
theorem next_eq (w : World) (hf : w.framed = false) :
    w.next =
      (if h : (normPos w.inputs w.pos w.off).1 < w.inputs.size then
        match w.inputs[(normPos w.inputs w.pos w.off).1] with
        | .tick => (0x0100, wTook w (normPos w.inputs w.pos w.off).1
            (normPos w.inputs ((normPos w.inputs w.pos w.off).1 + 1) 0))
        | .rx b => ((b.get! (normPos w.inputs w.pos w.off).2).toUInt16, wTook w (normPos w.inputs w.pos w.off).1
            (normPos w.inputs (normPos w.inputs w.pos w.off).1 ((normPos w.inputs w.pos w.off).2 + 1)))
      else (0xFFFF, wAt w (normPos w.inputs w.pos w.off))) := by
  unfold World.next wTook wAt
  simp only
  rw [wnorm _ w rfl hf]
  simp only
  by_cases h : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [h, dite_true]
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] with
    | tick =>
      simp only
      congr 1
      exact wnorm _ _ rfl hf
    | rx b =>
      simp only
      congr 1
      exact wnorm _ _ rfl hf
  · simp only [h, dite_false]

theorem np_ge (inputs : Array Input) : ∀ (n pos off : Nat), n = inputs.size - pos →
    pos ≤ (normPos inputs pos off).1 ∧ ((normPos inputs pos off).1 = pos → (normPos inputs pos off).2 = off) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro pos off hn
    rw [normPos]
    by_cases h : pos < inputs.size
    · simp only [h, dite_true]
      cases hx : inputs[pos] with
      | tick => exact ⟨Nat.le_refl _, fun _ => rfl⟩
      | rx b =>
        simp only
        by_cases ho : off ≥ b.size
        · simp only [ho, if_true]
          have := (ih (inputs.size - (pos + 1)) (by omega) (pos + 1) 0 rfl).1
          exact ⟨by omega, fun e => by omega⟩
        · simp [ho]
    · simp [h]

/-- **Taking an item moves the position in the input.** -/
theorem next_moves (w : World) (hf : w.framed = false) (h : w.next.1 ≠ 0xFFFF) :
    (w.next.2.pos, w.next.2.off) ≠ (w.pos, w.off) := by
  rw [next_eq w hf] at h ⊢
  obtain ⟨hge, heq⟩ := np_ge w.inputs _ w.pos w.off rfl
  by_cases hlt : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [hlt, dite_true] at h ⊢
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] with
    | tick =>
      simp only [wTook]
      have := (np_ge w.inputs _ ((normPos w.inputs w.pos w.off).1 + 1) 0 rfl).1
      intro e
      have := congrArg Prod.fst e
      simp only at this
      omega
    | rx b =>
      simp only [wTook]
      obtain ⟨h1, h2⟩ := np_ge w.inputs _ (normPos w.inputs w.pos w.off).1 ((normPos w.inputs w.pos w.off).2 + 1) rfl
      intro e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only at e1 e2
      have hp : (normPos w.inputs w.pos w.off).1 = w.pos := by omega
      have := heq hp
      have := h2 (by omega)
      omega
  · simp only [hlt, dite_false] at h
    exact absurd rfl h

/-- `next` leaves the world unframed. -/
theorem next_framed (w : World) (hf : w.framed = false) : w.next.2.framed = false := by
  rw [next_eq w hf]
  by_cases hlt : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [hlt, dite_true]
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] <;> exact hf
  · simp only [hlt, dite_false]
    exact hf

/-! ## How much input is left -/

/-- The items of input from a position on: the bytes of the chunks, the ticks. -/
def remFrom (inputs : Array Input) (pos off : Nat) : Nat :=
  if h : pos < inputs.size then
    (match inputs[pos] with
     | .rx b => b.size - off
     | .tick => 1) + remFrom inputs (pos + 1) 0
  else 0
termination_by inputs.size - pos

theorem rem_tick (inputs : Array Input) (pos off : Nat) (h : pos < inputs.size) (hx : inputs[pos] = .tick) :
    remFrom inputs pos off = 1 + remFrom inputs (pos + 1) 0 := by
  rw [remFrom]
  simp only [h, dite_true, hx]

theorem rem_rx (inputs : Array Input) (pos off : Nat) (h : pos < inputs.size) (b : ByteArray)
    (hx : inputs[pos] = .rx b) : remFrom inputs pos off = (b.size - off) + remFrom inputs (pos + 1) 0 := by
  rw [remFrom]
  simp only [h, dite_true, hx]

theorem rem_end (inputs : Array Input) (pos off : Nat) (h : ¬ pos < inputs.size) : remFrom inputs pos off = 0 := by
  rw [remFrom]
  simp only [h, dite_false]

/-- Skipping exhausted chunks skips no item. -/
theorem rem_norm (inputs : Array Input) : ∀ (n pos off : Nat), n = inputs.size - pos →
    remFrom inputs (normPos inputs pos off).1 (normPos inputs pos off).2 = remFrom inputs pos off := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro pos off hn
    rw [normPos]
    by_cases h : pos < inputs.size
    · simp only [h, dite_true]
      cases hx : inputs[pos] with
      | tick => rfl
      | rx b =>
        simp only
        by_cases ho : off ≥ b.size
        · simp only [ho, if_true]
          rw [ih (inputs.size - (pos + 1)) (by omega) (pos + 1) 0 rfl, rem_rx inputs pos off h b hx,
            Nat.sub_eq_zero_of_le ho, Nat.zero_add]
        · simp only [ho, if_false]
    · simp only [h, dite_false]

/-- After skipping, the position is at an item (not past the end of a chunk) or at the end. -/
theorem np_item (inputs : Array Input) : ∀ (n pos off : Nat), n = inputs.size - pos →
    ∀ b, inputs[(normPos inputs pos off).1]? = some (.rx b) → (normPos inputs pos off).2 < b.size := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro pos off hn b
    rw [normPos]
    by_cases h : pos < inputs.size
    · simp only [h, dite_true]
      cases hx : inputs[pos] with
      | tick =>
        simp only
        intro hb
        rw [Array.getElem?_eq_getElem h, hx] at hb
        cases hb
      | rx b' =>
        simp only
        by_cases ho : off ≥ b'.size
        · simp only [ho, if_true]
          exact ih (inputs.size - (pos + 1)) (by omega) (pos + 1) 0 rfl b
        · simp only [ho, if_false]
          intro hb
          rw [Array.getElem?_eq_getElem h, hx] at hb
          cases hb
          omega
    · simp only [h, dite_false]
      intro hb
      rw [Array.getElem?_eq_none (by omega)] at hb
      cases hb

/-- What is left of the world's input. -/
def World.rem (w : World) : Nat := remFrom w.inputs w.pos w.off

/-- **Nothing is left exactly when `next` says so.** -/
theorem rem_zero (w : World) (hf : w.framed = false) : w.next.1 = 0xFFFF ↔ World.rem w = 0 := by
  unfold World.rem
  rw [next_eq w hf, ← rem_norm w.inputs _ w.pos w.off rfl]
  by_cases hlt : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [hlt, dite_true]
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] with
    | tick =>
      simp only
      rw [rem_tick _ _ _ hlt hx]
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; omega
    | rx b =>
      simp only
      have hit := np_item w.inputs _ w.pos w.off rfl b (by rw [Array.getElem?_eq_getElem hlt, hx])
      rw [rem_rx _ _ _ hlt b hx]
      constructor
      · intro h
        have hl : (b.get! (normPos w.inputs w.pos w.off).2).toUInt16.toNat < 256 := by
          rw [UInt8.toNat_toUInt16]
          exact UInt8.toNat_lt _
        rw [h] at hl
        exact absurd hl (by decide)
      · intro h; omega
  · simp only [hlt, dite_false]
    rw [rem_end _ _ _ hlt]
    simp

/-- **Taking an item leaves one less.** -/
theorem rem_next (w : World) (hf : w.framed = false) (h : w.next.1 ≠ 0xFFFF) :
    World.rem w.next.2 + 1 = World.rem w := by
  unfold World.rem
  rw [next_eq w hf] at h ⊢
  rw [← rem_norm w.inputs _ w.pos w.off rfl]
  by_cases hlt : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [hlt, dite_true] at h ⊢
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] with
    | tick =>
      simp only [wTook]
      rw [rem_norm w.inputs _ _ 0 rfl, rem_tick _ _ (normPos w.inputs w.pos w.off).2 hlt hx]
      omega
    | rx b =>
      have hit := np_item w.inputs _ w.pos w.off rfl b (by rw [Array.getElem?_eq_getElem hlt, hx])
      simp only [wTook]
      rw [rem_norm w.inputs _ _ _ rfl, rem_rx _ _ _ hlt b hx, rem_rx _ _ _ hlt b hx]
      omega
  · simp only [hlt, dite_false] at h
    exact absurd rfl h

theorem next_inputs (w : World) (hf : w.framed = false) : w.next.2.inputs = w.inputs := by
  rw [next_eq w hf]
  by_cases hlt : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [hlt, dite_true]
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] <;> rfl
  · simp only [hlt, dite_false]
    rfl

end Ember.Proof.Z80Gen.LoopH
