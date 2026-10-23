import Ember.Proof.Z80PassMaster

/-!
# Ember.Proof.Z80PassMeet — where the two runs meet, every time `A`'s stack is empty (plan M7.3)

`passes_halt` keeps the relation of the two runs (`Inv`) at the ends of
the segments only.  Here those ends are made a sequence (`seq`: the
steps of `A` and of `B` at the `i`-th), each segment of at least one step
of each, and inside a segment `A`'s stack is never empty (`NZ`, which
every segment gives).  So **every step of `A` at which it is not halted
and its stack is empty is the end of a segment** (`meet`): there the two
machines are related by `Sync` with no frames, `B` at the step of the
sequence; and those steps of `B` go up with those of `A` (`seq_lt`).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu
open Classical

section
variable {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)} {acl : List AS}
  {lv : List (Nat × Nat)} {x0 y0 : Cpu × D.W}

/-- The ends of the segments, one after another: from related states with `A` not halted, the
segment `step_inv` gives; otherwise where it is. -/
noncomputable def nxt (Gl : Glob D A B lo hi cert tr acl lv x0) (y0 : Cpu × D.W) (p : Nat × Nat) : Nat × Nat :=
  if h : Inv D A B lo hi cert tr acl lv x0 (mrun D p.1 x0) (mrun D p.2 y0) ∧ (mrun D p.1 x0).1.halted = false then
    (p.1 + Classical.choose (step_inv Gl _ _ h.1 h.2),
      p.2 + Classical.choose (Classical.choose_spec (step_inv Gl _ _ h.1 h.2)))
  else p

noncomputable def seq (Gl : Glob D A B lo hi cert tr acl lv x0) (y0 : Cpu × D.W) : Nat → Nat × Nat
  | 0 => (0, 0)
  | i + 1 => nxt Gl y0 (seq Gl y0 i)

variable (Gl : Glob D A B lo hi cert tr acl lv x0)

theorem nxt_spec {p : Nat × Nat} (hI : Inv D A B lo hi cert tr acl lv x0 (mrun D p.1 x0) (mrun D p.2 y0))
    (hx : (mrun D p.1 x0).1.halted = false) :
    p.1 < (nxt Gl y0 p).1 ∧ p.2 < (nxt Gl y0 p).2 ∧ NZ D (mrun D p.1 x0) ((nxt Gl y0 p).1 - p.1) ∧
      Inv D A B lo hi cert tr acl lv x0 (mrun D (nxt Gl y0 p).1 x0) (mrun D (nxt Gl y0 p).2 y0) := by
  have h : Inv D A B lo hi cert tr acl lv x0 (mrun D p.1 x0) (mrun D p.2 y0) ∧ (mrun D p.1 x0).1.halted = false :=
    ⟨hI, hx⟩
  have e : nxt Gl y0 p = (p.1 + Classical.choose (step_inv Gl _ _ h.1 h.2),
      p.2 + Classical.choose (Classical.choose_spec (step_inv Gl _ _ h.1 h.2))) := by
    unfold nxt; rw [dif_pos h]
  rw [e]
  obtain ⟨ha, hb, nz, hI'⟩ := Classical.choose_spec (Classical.choose_spec (step_inv Gl _ _ h.1 h.2))
  refine ⟨by simp only; omega, by simp only; omega, by simpa using nz, ?_⟩
  simp only
  rw [mrun_add, mrun_add]
  exact hI'

theorem nxt_stay {p : Nat × Nat}
    (h : ¬ (Inv D A B lo hi cert tr acl lv x0 (mrun D p.1 x0) (mrun D p.2 y0) ∧ (mrun D p.1 x0).1.halted = false)) :
    nxt Gl y0 p = p := by
  unfold nxt; rw [dif_neg h]

/-- **The relation at every end of a segment.** -/
theorem seq_inv (hI0 : Inv D A B lo hi cert tr acl lv x0 x0 y0) :
    ∀ i, Inv D A B lo hi cert tr acl lv x0 (mrun D (seq Gl y0 i).1 x0) (mrun D (seq Gl y0 i).2 y0)
  | 0 => hI0
  | i + 1 => by
    have ih := seq_inv hI0 i
    show Inv D A B lo hi cert tr acl lv x0 (mrun D (nxt Gl y0 (seq Gl y0 i)).1 x0) (mrun D (nxt Gl y0 (seq Gl y0 i)).2 y0)
    cases hx : (mrun D (seq Gl y0 i).1 x0).1.halted with
    | false => exact (nxt_spec Gl ih hx).2.2.2
    | true => rw [nxt_stay Gl (fun h => by rw [h.2] at hx; cases hx)]; exact ih

theorem seq_succ_le (i : Nat) : (seq Gl y0 i).1 ≤ (seq Gl y0 (i + 1)).1 ∧ (seq Gl y0 i).2 ≤ (seq Gl y0 (i + 1)).2 := by
  show (seq Gl y0 i).1 ≤ (nxt Gl y0 (seq Gl y0 i)).1 ∧ (seq Gl y0 i).2 ≤ (nxt Gl y0 (seq Gl y0 i)).2
  by_cases h : Inv D A B lo hi cert tr acl lv x0 (mrun D (seq Gl y0 i).1 x0) (mrun D (seq Gl y0 i).2 y0) ∧
      (mrun D (seq Gl y0 i).1 x0).1.halted = false
  · have := nxt_spec Gl h.1 h.2; omega
  · rw [nxt_stay Gl h]; omega

theorem seq_mono {i j : Nat} (h : i ≤ j) : (seq Gl y0 i).1 ≤ (seq Gl y0 j).1 ∧ (seq Gl y0 i).2 ≤ (seq Gl y0 j).2 := by
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · subst e; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · have := ih (by omega); have := seq_succ_le Gl (y0 := y0) j; omega

/-- A CPU not halted at a step was not halted before. -/
theorem not_halted_before {n t : Nat} (ht : t ≤ n) (h : (mrun D n x0).1.halted = false) :
    (mrun D t x0).1.halted = false := by
  cases e : (mrun D t x0).1.halted with
  | false => rfl
  | true =>
    have := (mrun_halted D (n - t) (mrun D t x0) e).1
    rw [← mrun_add, show t + (n - t) = n by omega, h] at this
    cases this

/-- Not halted at the `i`-th end: the next is further on, in both runs. -/
theorem seq_lt_succ (hI0 : Inv D A B lo hi cert tr acl lv x0 x0 y0) {i : Nat}
    (hx : (mrun D (seq Gl y0 i).1 x0).1.halted = false) :
    (seq Gl y0 i).1 < (seq Gl y0 (i + 1)).1 ∧ (seq Gl y0 i).2 < (seq Gl y0 (i + 1)).2 ∧
      NZ D (mrun D (seq Gl y0 i).1 x0) ((seq Gl y0 (i + 1)).1 - (seq Gl y0 i).1) := by
  have := nxt_spec Gl (seq_inv Gl hI0 i) hx
  exact ⟨this.1, this.2.1, this.2.2.1⟩

/-- **Every step of `A` at which it is not halted and its stack is empty is the end of a segment.** -/
theorem cover (hI0 : Inv D A B lo hi cert tr acl lv x0 x0 y0) {n : Nat} (hn : (mrun D n x0).1.halted = false)
    (hsp : (mrun D n x0).1.sp = 0) : ∃ i, (seq Gl y0 i).1 = n := by
  refine Classical.byContradiction fun hne => ?_
  have hne' : ∀ i, (seq Gl y0 i).1 ≠ n := fun i h => hne ⟨i, h⟩
  -- every end before `n`, and each further on than the one before
  have hlt : ∀ i, (seq Gl y0 i).1 < n ∧ i ≤ (seq Gl y0 i).1 := by
    intro i
    induction i with
    | zero => exact ⟨Nat.lt_of_le_of_ne (Nat.zero_le _) (fun h => hne' 0 h), Nat.le_refl _⟩
    | succ i ih =>
      have hx := not_halted_before (Nat.le_of_lt ih.1) hn
      obtain ⟨h1, _, nz⟩ := seq_lt_succ Gl hI0 hx
      have hle : (seq Gl y0 (i + 1)).1 ≤ n := by
        refine Nat.le_of_not_lt fun hgt => ?_
        have := nz (n - (seq Gl y0 i).1) (by omega) (by omega)
        rw [← mrun_add, show (seq Gl y0 i).1 + (n - (seq Gl y0 i).1) = n by omega] at this
        exact this hsp
      exact ⟨Nat.lt_of_le_of_ne hle (hne' _), by omega⟩
  have := hlt n
  omega

/-- The ends at two steps of `A` not halted: in the same order in `B`'s run. -/
theorem seq_lt (hI0 : Inv D A B lo hi cert tr acl lv x0 x0 y0) {i j : Nat}
    (hij : (seq Gl y0 i).1 < (seq Gl y0 j).1) (hx : (mrun D (seq Gl y0 j).1 x0).1.halted = false) :
    (seq Gl y0 i).2 < (seq Gl y0 j).2 := by
  have hij' : i < j := by
    refine Nat.lt_of_not_le fun h => ?_
    have := (seq_mono Gl (y0 := y0) h).1; omega
  -- from `i` to `j`, each end further on in `B`'s run
  have key : ∀ d, i + d + 1 ≤ j → (seq Gl y0 i).2 < (seq Gl y0 (i + d + 1)).2 := by
    intro d
    induction d with
    | zero =>
      intro h
      have hx' := not_halted_before (seq_mono Gl (y0 := y0) (show i ≤ j by omega)).1 hx
      exact (seq_lt_succ Gl hI0 hx').2.1
    | succ d ih =>
      intro h
      have h1 := ih (by omega)
      have hx' := not_halted_before (seq_mono Gl (y0 := y0) (show i + d + 1 ≤ j by omega)).1 hx
      have h2 := (seq_lt_succ Gl hI0 hx').2.1
      rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]
      omega
  have := key (j - i - 1) (by omega)
  rwa [show i + (j - i - 1) + 1 = j by omega] at this

include Gl in
/-- The relation at the start: both machines at their first items, empty stacks. -/
theorem inv0 (S0 : Sync D A B lo hi [] 0 0 false false x0 y0) : Inv D A B lo hi cert tr acl lv x0 x0 y0 := by
  obtain ⟨_, ⟨r, rs, hc, ht, hkb, hth, htl, htop⟩, _⟩ := Gl.chk
  have hr0 : rowAt cert 0 = r := by simp [rowAt, hc]
  refine Or.inr ⟨[], 0, by rw [hr0]; exact ht, ?_, by rw [hr0]; exact htop, trivial, ⟨0, rfl⟩,
    by rw [Gl.ab.first]; trivial, trivial⟩
  rw [hr0, hkb, hth, htl]; exact S0

/-- **Where the two runs meet with empty stacks**: at an end of a segment where `A` is not halted and its
stack is empty, the machines are related at a row of the certificate with no frames. -/
theorem meet (hI0 : Inv D A B lo hi cert tr acl lv x0 x0 y0) {i : Nat}
    (hn : (mrun D (seq Gl y0 i).1 x0).1.halted = false) (hsp : (mrun D (seq Gl y0 i).1 x0).1.sp = 0) :
    ∃ k, (rowAt cert k).tag ≠ .none ∧
      Sync D A B lo hi [] k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl
        (mrun D (seq Gl y0 i).1 x0) (mrun D (seq Gl y0 i).2 y0) := by
  rcases seq_inv Gl hI0 i with hd | ⟨G, k, ht, S, _⟩
  · rw [hd.1] at hn; cases hn
  · cases G with
    | nil => exact ⟨k, ht, S⟩
    | cons f G => exact absurd hsp (S.sp_ne (List.cons_ne_nil _ _))

end

end Ember.Proof.PassSim
