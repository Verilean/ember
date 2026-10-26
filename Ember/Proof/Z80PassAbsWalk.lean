import Ember.Proof.Z80PassAbsOK

/-!
# Ember.Proof.Z80PassAbsWalk — the list of what is known, checked by a walk (plan M7.3)

`absWalk`: one walk over `A`'s items, the certificate's rows and the
list of what is known (one `AS` per item), checking at each item
`absOK`, `tgtOK` and the levels of the functions at the rows of calls
(`lvRowOK`).  `AbsGlob`: what the master theorem takes of it — every
item checked, nothing known at the first, and the stack's room for the
frames of the levels.  The facts the segments use: where a segment ends,
what is known there (`land_none`, `land_after`, `land_label`).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Gen

/-- The row of the certificate at `k`. -/
def rowAt (cert : List Row) (k : Nat) : Row := cert[k]?.getD default

/-- What is known at an item. -/
def acAt (acl : List AS) (k : Nat) : AS := (acl[k]?).getD none

/-- The level of a function, by its entry (`topE`: the activation of no function). -/
def lvOf (lv : List (Nat × Nat)) (e : Nat) : Nat := (lv.lookup e).getD 0

/-- **At a row of a call** (of both, or of `A` only): the function called below every activation the
row may be in. -/
def lvRowOK (t : List (String × LInfo)) (lv : List (Nat × Nat)) (it : Item) (r : Row) : Bool :=
  match r.tag, it with
  | .call, .ins ⟨.call, [.imm (.sym l 0)]⟩ | .tail, .ins ⟨.call, [.imm (.sym l 0)]⟩ =>
    match lookupL t l with
    | some li => r.act.all fun e => decide (lvOf lv li.ia + 1 ≤ lvOf lv e)
    | none => false
  | _, _ => true

/-- **The walk** over `n` items: each checked, with the item, row and what is known before. -/
def absWalk (la : List (String × Nat)) (tA : List (String × Nat × List Item)) (lo hi : Nat)
    (lt : List (String × AS)) (t : List (String × LInfo)) (lv : List (Nat × Nat)) :
    Nat → Option (Item × Row × AS) → List Item → List Row → List AS → Bool
  | 0, _, _, _, _ => true
  | _ + 1, _, [], _, _ => true
  | n + 1, prev, it :: xs, r :: rs, a :: as =>
    absOK la tA lo hi prev it r a as && tgtOK lt it r a && lvRowOK t lv it r &&
      absWalk la tA lo hi lt t lv n (some (it, r, a)) xs rs as
  | _ + 1, _, _ :: _, _, _ => false

/-- The item, row and what is known before an index. -/
def prevA (xs : List Item) (cert : List Row) (acl : List AS) (k : Nat) : Option (Item × Row × AS) :=
  if k = 0 then none else (xs[k - 1]?).map fun it => (it, rowAt cert (k - 1), acAt acl (k - 1))

/-- The context of the walk for an image `A`, its certificate and list. -/
structure ACtx where
  la : List (String × Nat)
  tA : List (String × Nat × List Item)
  lt : List (String × AS)
  t : List (String × LInfo)

def mkACtx (xs : List Item) (a : Assembled) (cert : List Row) (acl : List AS) : ACtx :=
  ⟨a.labels.reverse, labTbl xs 0, acTbl xs cert acl, mkTbl xs cert 0⟩

/-- Every item checked, as a fact about the indices. -/
def AbsRows (c : ACtx) (lo hi : Nat) (lv : List (Nat × Nat)) (xs : List Item) (cert : List Row) (acl : List AS) :
    Prop :=
  ∀ k it, xs[k]? = some it →
    absOK c.la c.tA lo hi (prevA xs cert acl k) it (rowAt cert k) (acAt acl k) (acl.drop (k + 1)) = true ∧
      tgtOK c.lt it (rowAt cert k) (acAt acl k) = true ∧ lvRowOK c.t lv it (rowAt cert k) = true

theorem rowAt_eq {cert : List Row} {k : Nat} (h : k < cert.length) : rowAt cert k = cert[k] := by
  simp [rowAt, List.getElem?_eq_getElem h]

theorem acAt_eq {acl : List AS} {k : Nat} (h : k < acl.length) : acAt acl k = acl[k] := by
  simp [acAt, List.getElem?_eq_getElem h]

/-- **A walk that holds checks every item it goes over.** -/
theorem absWalk_rows (c : ACtx) (lo hi : Nat) (lv : List (Nat × Nat)) (xs : List Item) (cert : List Row)
    (acl : List AS) (hc : cert.length = xs.length) (ha : acl.length = xs.length) :
    ∀ (n k : Nat), absWalk c.la c.tA lo hi c.lt c.t lv n (prevA xs cert acl k) (xs.drop k) (cert.drop k) (acl.drop k) = true →
      ∀ j it, j < n → xs[k + j]? = some it →
        absOK c.la c.tA lo hi (prevA xs cert acl (k + j)) it (rowAt cert (k + j)) (acAt acl (k + j))
            (acl.drop (k + j + 1)) = true ∧
          tgtOK c.lt it (rowAt cert (k + j)) (acAt acl (k + j)) = true ∧ lvRowOK c.t lv it (rowAt cert (k + j)) = true
  | 0, _, _, j, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, k, h, j, it, hj, hit => by
    have hk : k < xs.length := by have := (List.getElem?_eq_some_iff.mp hit).1; omega
    have hxs : xs.drop k = xs[k] :: xs.drop (k + 1) := by simp
    have hcs : cert.drop k = cert[k]'(by omega) :: cert.drop (k + 1) := by simp
    have has : acl.drop k = acl[k]'(by omega) :: acl.drop (k + 1) := by simp
    rw [hxs, hcs, has] at h
    simp only [absWalk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hpre : prevA xs cert acl (k + 1) = some (xs[k], cert[k]'(by omega), acl[k]'(by omega)) := by
      simp [prevA, rowAt_eq (show k < cert.length by omega), acAt_eq (show k < acl.length by omega)]
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hit ⊢
      rw [List.getElem?_eq_getElem hk] at hit
      cases hit
      rw [rowAt_eq (show k < cert.length by omega), acAt_eq (show k < acl.length by omega)]
      exact ⟨h1, h2, h3⟩
    | succ j =>
      rw [← hpre] at h4
      have := absWalk_rows c lo hi lv xs cert acl hc ha n (k + 1) h4 j it (by omega)
        (by rw [show k + 1 + j = k + (j + 1) by omega]; exact hit)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      exact this

/-- **Walks in parts of `n` items one after another**: the `i`-th from `n * i`, past the last item. -/
theorem absRows_of_walks (c : ACtx) (lo hi : Nat) (lv : List (Nat × Nat)) (xs : List Item) (cert : List Row)
    (acl : List AS) (hc : cert.length = xs.length) (ha : acl.length = xs.length) (n : Nat) (starts : List Nat)
    (hw : ∀ p, p ∈ starts →
      absWalk c.la c.tA lo hi c.lt c.t lv n (prevA xs cert acl p) (xs.drop p) (cert.drop p) (acl.drop p) = true)
    (hst : ∀ i (h : i < starts.length), starts[i]'h = n * i) (hn : 0 < n) (hreach : xs.length ≤ n * starts.length) :
    AbsRows c lo hi lv xs cert acl := by
  intro k it hit
  have hk : k < xs.length := by have := (List.getElem?_eq_some_iff.mp hit).1; omega
  have hkn : k / n < starts.length := by
    have := Nat.div_lt_iff_lt_mul hn |>.mpr (show k < starts.length * n by rw [Nat.mul_comm]; omega)
    exact this
  have h1 := Nat.div_add_mod k n
  have h2 := Nat.mod_lt k hn
  have e := hst _ hkn
  have := absWalk_rows c lo hi lv xs cert acl hc ha n starts[k / n] (hw _ (List.getElem_mem hkn)) (k - starts[k / n])
    it (by rw [e]; omega) (by rw [show starts[k / n] + (k - starts[k / n]) = k by rw [e]; omega]; exact hit)
  rw [show starts[k / n] + (k - starts[k / n]) = k by rw [e]; omega] at this
  exact this

/-! ## The tables -/

theorem acTbl_lookup : ∀ (xs : List Item) (rs : List Row) (as : List AS) (k : Nat) (l : String) (li : LInfo),
    as.length = xs.length → (mkTbl xs rs k).lookup l = some li → (acTbl xs rs as).lookup l = as[li.ia - k]?
  | [], _, _, _, _, _, _, h => by simp [mkTbl] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [mkTbl] at h
  | _ :: _, _ :: _, [], _, _, _, hl, _ => by simp at hl
  | it :: r, row :: rs, a :: as, k, l, li, hl, h => by
    have hl' : as.length = r.length := by simpa using hl
    have step : (mkTbl r rs (k + 1)).lookup l = some li → (acTbl r rs as).lookup l = (a :: as)[li.ia - k]? := by
      intro h'
      have e := acTbl_lookup r rs as (k + 1) l li hl' h'
      obtain ⟨h1, _⟩ := mkTbl_lookup r rs (k + 1) l li h'
      rw [e, show li.ia - k = (li.ia - (k + 1)) + 1 by omega]; simp
    cases it with
    | label l' =>
      simp only [mkTbl] at h
      simp only [acTbl]
      by_cases ht : row.tag = .skipBoth
      · rw [if_pos ht, lookup_cons] at h
        rw [if_pos ht, lookup_cons]
        by_cases e : l = l'
        · subst e
          simp only [beq_self_eq_true, if_true, Option.some.injEq] at h ⊢
          subst h
          simp
        · have hne : (l == l') = false := by simpa using e
          rw [hne] at h ⊢
          simp only [Bool.false_eq_true, if_false] at h ⊢
          exact step h
      · rw [if_neg ht] at h
        rw [if_neg ht]
        exact step h
    | _ => simp only [mkTbl] at h; simp only [acTbl]; exact step h

/-- What is known at a label where the runs meet, from the table. -/
theorem acOf_label {xs : List Item} {cert : List Row} {acl : List AS} (ha : acl.length = xs.length) {l : String}
    {li : LInfo} (h : lookupL (mkTbl xs cert 0) l = some li) : acOf (acTbl xs cert acl) l = acAt acl li.ia := by
  have e := acTbl_lookup xs cert acl 0 l li ha h
  simp only [Nat.sub_zero] at e
  simp only [acOf, acAt, e]

/-! ## Where a segment ends -/

/-- **What the master theorem takes of the list**: walked, as long as the items, nothing known at the
first item; the frames of the levels leave the stack above `hi + 4`. -/
structure AbsGlob (xs : List Item) (a : Assembled) (lo hi : Nat) (cert : List Row) (acl : List AS)
    (lv : List (Nat × Nat)) : Prop where
  rows : AbsRows (mkACtx xs a cert acl) lo hi lv xs cert acl
  len : acl.length = xs.length
  clen : cert.length = xs.length
  first : acAt acl 0 = none
  top : hi + 4 + 2 * lvOf lv topE ≤ 65536

theorem absAfter_ret (la : List (String × Nat)) (pr : Row) (pa : AS) : absAfter la (.ins ⟨.ret, []⟩) pr pa = none := by
  obtain ⟨tag, kb, fi, th, tl, act⟩ := pr
  cases tag <;> simp only [absAfter, isZero, Bool.false_eq_true, if_false]
  split
  · rename_i f _
    split
    · rename_i e; exfalso; revert e; cases f <;> simp [Form.instr]
    · rfl
  · rfl

/-- **Nothing known after a segment of a kind `absAfter` has nothing for.** -/
theorem land_none {xs : List Item} {a : Assembled} {lo hi : Nat} {cert : List Row} {acl : List AS}
    {lv : List (Nat × Nat)} (Ag : AbsGlob xs a lo hi cert acl lv) {k : Nat} {it : Item}
    (hit : xs[k]? = some it)
    (hn : absAfter a.labels.reverse it (rowAt cert k) (acAt acl k) = none) (hr : it ≠ .ins ⟨.ret, []⟩) :
    acAt acl (k + 1) = none := by
  cases hit' : xs[k + 1]? with
  | none =>
    have : acl[k + 1]? = none := by
      rw [List.getElem?_eq_none]; have := List.getElem?_eq_none_iff.mp hit'; rw [Ag.len]; exact this
    simp [acAt, this]
  | some it' =>
    have h := (Ag.rows (k + 1) it' hit').1
    have hp : prevA xs cert acl (k + 1) = some (it, rowAt cert k, acAt acl k) := by simp [prevA, hit]
    rw [hp] at h
    simp only [absOK, mkACtx, hn, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩ := h
    rcases h1 with e | (⟨_, e⟩ | ⟨_, e⟩)
    · exact e
    · cases e
    · simp only [decide_eq_true_eq] at e; exact absurd e hr

theorem asat_none {s : Cpu} : ASat none s := trivial

/-- **What is known after a segment `absAfter` has something for**, of the state there. -/
theorem land_after {xs : List Item} {a : Assembled} {lo hi : Nat} {cert : List Row} {acl : List AS}
    {lv : List (Nat × Nat)} (Ag : AbsGlob xs a lo hi cert acl lv) {k : Nat} {it : Item} {b : AS} {s : Cpu}
    (hit : xs[k]? = some it) (hn : absAfter a.labels.reverse it (rowAt cert k) (acAt acl k) = some b)
    (hs : ASat b s) : ASat (acAt acl (k + 1)) s := by
  cases hit' : xs[k + 1]? with
  | none =>
    have : acl[k + 1]? = none := by
      rw [List.getElem?_eq_none]; have := List.getElem?_eq_none_iff.mp hit'; rw [Ag.len]; exact this
    simp [acAt, this]; trivial
  | some it' =>
    have h := (Ag.rows (k + 1) it' hit').1
    have hp : prevA xs cert acl (k + 1) = some (it, rowAt cert k, acAt acl k) := by simp [prevA, hit]
    rw [hp] at h
    simp only [absOK, mkACtx, hn, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩ := h
    rcases h1 with e | (⟨_, e⟩ | ⟨_, e⟩)
    · rw [e]; trivial
    · exact AS.le_sat e hs
    · simp only [decide_eq_true_eq] at e
      subst e
      rw [absAfter_ret] at hn; cases hn

/-- Nothing known two items after a row of `blkR`, four after one of `pack` or `copyR`. -/
theorem land_skip {xs : List Item} {a : Assembled} {lo hi : Nat} {cert : List Row} {acl : List AS}
    {lv : List (Nat × Nat)} (Ag : AbsGlob xs a lo hi cert acl lv) {k : Nat} {it : Item} (hit : xs[k]? = some it) :
    ((rowAt cert k).tag = .blkR → acAt acl (k + 2) = none) ∧
      ((rowAt cert k).tag = .pack ∨ (rowAt cert k).tag = .copyR → acAt acl (k + 4) = none) := by
  have h := (Ag.rows k it hit).1
  simp only [absOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, _⟩ := h
  have e2 : (acl.drop (k + 1)).drop 1 = acl.drop (k + 2) := by rw [List.drop_drop]
  have e4 : (acl.drop (k + 1)).drop 3 = acl.drop (k + 4) := by rw [List.drop_drop]
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rw [ht] at h3
    simp only [bne_self_eq_false, Bool.false_or, e2, List.head?_drop, Option.isNone_iff_eq_none] at h3
    simp only [acAt]
    cases e : acl[k + 2]? with
    | none => rfl
    | some v => rw [e] at h3; simpa using h3
  · have h4' : ((acl.drop (k + 1)).drop 3).head?.join.isNone = true := by
      rcases ht with ht | ht <;> rw [ht] at h4 <;> simpa using h4
    simp only [e4, List.head?_drop, Option.isNone_iff_eq_none] at h4'
    simp only [acAt]
    cases e : acl[k + 4]? with
    | none => rfl
    | some v => rw [e] at h4'; simpa using h4'

/-- **At a label where the runs meet**, from a row that goes there: what the row checks. -/
theorem land_label {xs : List Item} {a : Assembled} {lo hi : Nat} {cert : List Row} {acl : List AS}
    {lv : List (Nat × Nat)} (Ag : AbsGlob xs a lo hi cert acl lv) {l : String} {li : LInfo}
    (hli : lookupL (mkTbl xs cert 0) l = some li) : acOf (acTbl xs cert acl) l = acAt acl li.ia :=
  acOf_label Ag.len hli

end Ember.Proof.PassSim
