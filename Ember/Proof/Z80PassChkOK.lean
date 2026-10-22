import Ember.Proof.Z80PassChk

/-!
# Ember.Proof.Z80PassChkOK — what the checker's walk and tables say (plan M7.3)

* `labTbl_lookup`: a label in the table of all labels is at its index, the items from there on;
* `mkTbl_lookup`: a label in the table of meeting points: its row, its index;
* `walk_rows`, `check_rows`: a walk that holds checks every row of a meeting point, with each
  image's items from the row on.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm

theorem lookup_cons {α β : Type} [BEq α] (a k : α) (v : β) (l : List (α × β)) :
    ((k, v) :: l).lookup a = if a == k then some v else l.lookup a := by
  simp only [List.lookup]
  split <;> simp_all

theorem labTbl_lookup : ∀ (xs : List Item) (k : Nat) (l : String) (i : Nat) (suf : List Item),
    (labTbl xs k).lookup l = some (i, suf) → k ≤ i ∧ xs[i - k]? = some (.label l) ∧ suf = xs.drop (i - k)
  | [], _, _, _, _, h => by simp [labTbl] at h
  | it :: r, k, l, i, suf, h => by
    cases it with
    | label l' =>
      simp only [labTbl] at h
      rw [lookup_cons] at h
      by_cases e : l = l'
      · subst e
        simp only [beq_self_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · have hne : (l == l') = false := by simpa using e
        rw [hne] at h
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨h1, h2, h3⟩ := labTbl_lookup r (k + 1) l i suf h
        refine ⟨by omega, ?_, ?_⟩
        · rw [show i - k = (i - (k + 1)) + 1 by omega]; simpa using h2
        · rw [show i - k = (i - (k + 1)) + 1 by omega]; simpa using h3
    | _ =>
      simp only [labTbl] at h
      obtain ⟨h1, h2, h3⟩ := labTbl_lookup r (k + 1) l i suf h
      refine ⟨by omega, ?_, ?_⟩
      · rw [show i - k = (i - (k + 1)) + 1 by omega]; simpa using h2
      · rw [show i - k = (i - (k + 1)) + 1 by omega]; simpa using h3

/-- The items of an image from a label on, as the table says. -/
theorem sufOf_label {xs : List Item} {l : String} {suf : List Item} (h : sufOf (labTbl xs 0) l = some suf) :
    ∃ i, xs[i]? = some (.label l) ∧ suf = xs.drop i := by
  simp only [sufOf, Option.map_eq_some_iff] at h
  obtain ⟨⟨i, suf'⟩, h1, rfl⟩ := h
  obtain ⟨_, h2, h3⟩ := labTbl_lookup xs 0 l i suf' h1
  exact ⟨i, by simpa using h2, by simpa using h3⟩

theorem mkTbl_lookup : ∀ (xs : List Item) (rs : List Row) (k : Nat) (l : String) (li : LInfo),
    (mkTbl xs rs k).lookup l = some li →
      k ≤ li.ia ∧ xs[li.ia - k]? = some (.label l) ∧ rs[li.ia - k]? = some li.row ∧ li.row.tag = .skipBoth ∧
        li.ib = li.row.kb ∧ li.sufA = xs.drop (li.ia - k)
  | [], _, _, _, _, h => by simp [mkTbl] at h
  | _ :: _, [], _, _, _, h => by simp [mkTbl] at h
  | it :: r, row :: rs, k, l, li, h => by
    have step : (mkTbl r rs (k + 1)).lookup l = some li →
        k ≤ li.ia ∧ (it :: r)[li.ia - k]? = some (.label l) ∧ (row :: rs)[li.ia - k]? = some li.row ∧
          li.row.tag = .skipBoth ∧ li.ib = li.row.kb ∧ li.sufA = (it :: r).drop (li.ia - k) := by
      intro h'
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mkTbl_lookup r rs (k + 1) l li h'
      refine ⟨by omega, ?_, ?_, h4, h5, ?_⟩
      · rw [show li.ia - k = (li.ia - (k + 1)) + 1 by omega]; simpa using h2
      · rw [show li.ia - k = (li.ia - (k + 1)) + 1 by omega]; simpa using h3
      · rw [show li.ia - k = (li.ia - (k + 1)) + 1 by omega]; simpa using h6
    cases it with
    | label l' =>
      simp only [mkTbl] at h
      by_cases ht : row.tag = .skipBoth
      · rw [if_pos ht, lookup_cons] at h
        by_cases e : l = l'
        · subst e
          simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
          subst h
          simp [ht]
        · have hne : (l == l') = false := by simpa using e
          rw [hne] at h
          simp only [Bool.false_eq_true, if_false] at h
          exact step h
      · rw [if_neg ht] at h
        exact step h
    | _ => simp only [mkTbl] at h; exact step h

/-- `A`'s item before an index (none at the start). -/
def prevOf (xs : List Item) (k : Nat) : Option Item := if k = 0 then none else xs[k - 1]?

/-- **A walk that holds checks every row of a meeting point**: at each, `B`'s index not before the
previous one, the check of the row with each image's items from the row on. -/
theorem walk_rows (c : Ctx) (xs ys : List Item) (cert : List Row) :
    ∀ (n k kb : Nat), walk c n (prevOf xs k) (xs.drop k) (cert.drop k) (ys.drop kb) kb = true →
      ∀ j r, j < n → k + j < xs.length → cert[k + j]? = some r → r.tag ≠ .none →
        rowOK c (prevOf xs (k + j)) (xs.drop (k + j)) (ys.drop r.kb) r (cert.drop (k + j + 1)) = true
  | 0, _, _, _, j, _, hj, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, k, kb, h, j, r, hj, hk, hr, ht => by
    have hxs : xs.drop k = xs[k]'(by omega) :: xs.drop (k + 1) := by simp
    have hc : k < cert.length := by
      have := (List.getElem?_eq_some_iff.mp (show cert[k + j]? = some r from hr)).1; omega
    have hcs : cert.drop k = cert[k] :: cert.drop (k + 1) := by simp
    rw [hxs, hcs] at h
    simp only [walk] at h
    have hpre : prevOf xs (k + 1) = some (xs[k]'(by omega)) := by simp [prevOf]
    by_cases ht0 : cert[k].tag = .none
    · rw [if_pos ht0, ← hpre] at h
      cases j with
      | zero =>
        simp only [Nat.add_zero] at hr
        rw [List.getElem?_eq_getElem hc] at hr
        cases hr; exact absurd ht0 ht
      | succ j =>
        have := walk_rows c xs ys cert n (k + 1) kb h j r (by omega) (by omega)
          (by rw [show k + 1 + j = k + (j + 1) by omega]; exact hr) ht
        rw [show k + 1 + j = k + (j + 1) by omega] at this
        exact this
    · rw [if_neg ht0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hle, hrow⟩, hrest⟩ := h
      have hd : (ys.drop kb).drop (cert[k].kb - kb) = ys.drop cert[k].kb := by
        rw [List.drop_drop]; congr 1; omega
      rw [hd] at hrow hrest
      cases j with
      | zero =>
        simp only [Nat.add_zero] at hr ⊢
        rw [List.getElem?_eq_getElem hc] at hr
        cases hr
        rw [hxs]
        exact hrow
      | succ j =>
        rw [← hpre] at hrest
        have := walk_rows c xs ys cert n (k + 1) cert[k].kb hrest j r (by omega) (by omega)
          (by rw [show k + 1 + j = k + (j + 1) by omega]; exact hr) ht
        rw [show k + 1 + j = k + (j + 1) by omega] at this
        exact this

/-- **A certificate's rows checked**: as many rows as items, the first a meeting point at `B`'s first
item in the activation of no function, every row of a meeting point checked. -/
def RowsOK (xs ys : List Item) (a b : Assembled) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool)) :
    Prop :=
  cert.length = xs.length ∧
    (∃ r rs, cert = r :: rs ∧ r.tag ≠ .none ∧ r.kb = 0 ∧ r.th = false ∧ r.tl = false ∧ topE ∈ r.act) ∧
    ∀ k r, cert[k]? = some r → r.tag ≠ .none →
      rowOK (mkCtx xs ys a b lo hi cert tr) (prevOf xs k) (xs.drop k) (ys.drop r.kb) r (cert.drop (k + 1)) = true

/-- **The check of a certificate**: as many rows as items, the first a meeting point at `B`'s first
item in the activation of no function, every row of a meeting point checked. -/
theorem check_rows {xs ys : List Item} {a b : Assembled} {lo hi : Nat} {cert : List Row}
    {tr : List (Nat × Bool × Bool)} (h : check xs ys a b lo hi cert tr = true) :
    RowsOK xs ys a b lo hi cert tr := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hlen, hfirst⟩, hw⟩ := h
  refine ⟨hlen, ?_, ?_⟩
  · cases cert with
    | nil => simp at hfirst
    | cons r rs =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
        List.contains_iff_mem] at hfirst
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hfirst
      exact ⟨r, rs, rfl, h1, h2, h3, h4, h5⟩
  · intro k r hr ht
    have hk : k < xs.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
    have := walk_rows (mkCtx xs ys a b lo hi cert tr) xs ys cert xs.length 0 0 (by simpa [prevOf] using hw) k r hk
      (by omega) (by simpa using hr) ht
    simpa using this

/-- **Rows checked in parts**: walks of `n` items from starts that cover every index (each start with
`B`'s index there). -/
theorem rows_of_walks (c : Ctx) (xs ys : List Item) (cert : List Row) (n : Nat) (starts : List (Nat × Nat))
    (hw : ∀ p, p ∈ starts → walk c n (prevOf xs p.1) (xs.drop p.1) (cert.drop p.1) (ys.drop p.2) p.2 = true)
    (hcov : ∀ k, k < xs.length → ∃ p, p ∈ starts ∧ p.1 ≤ k ∧ k < p.1 + n) (hlen : cert.length = xs.length) :
    ∀ k r, cert[k]? = some r → r.tag ≠ .none →
      rowOK c (prevOf xs k) (xs.drop k) (ys.drop r.kb) r (cert.drop (k + 1)) = true := by
  intro k r hr ht
  have hk : k < xs.length := by have := (List.getElem?_eq_some_iff.mp hr).1; omega
  obtain ⟨p, hp, h1, h2⟩ := hcov k hk
  have := walk_rows c xs ys cert n p.1 p.2 (hw p hp) (k - p.1) r (by omega) (by omega)
    (by rw [show p.1 + (k - p.1) = k by omega]; exact hr) ht
  rw [show p.1 + (k - p.1) = k by omega] at this
  exact this

/-- info: 'Ember.Proof.PassSim.check_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_rows

end Ember.Proof.PassSim
