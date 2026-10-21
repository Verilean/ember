import Ember.Z80.Asm

/-!
# Ember.Proof.Z80AsmChunks — the assembler, a stretch of items at a time (plan M7.3)

`assemble` looks labels up by name: each label placed is compared with
every label before it (`place`), each symbol of an instruction with the
labels in turn (`emit`).  Run by the kernel over the stack's 2924 items
in one evaluation, that is about 8 GB kept at once.  Both passes go
item by item, so they can be cut: `place_step` (the addresses and labels
of a stretch, then of the rest from the address and the labels it ends
with) and `emit_step` (the bytes of a stretch, then of the rest), each
stretch a theorem of its own.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Asm

/-- So that the kernel can decide what a pass gives (`decide +kernel`). -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

theorem place_ne : ∀ (r : List Item) (pc : Nat) (ls : List (String × Nat)) (X : List Nat) (L : List (String × Nat)),
    place r pc ls = .ok (X, L) → X ≠ []
  | [], pc, ls, X, L, h => by
    simp only [place, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact List.cons_ne_nil _ _
  | it :: r, pc, ls, X, L, h => by
    unfold place at h
    split at h
    · split at h
      · cases h
      · cases hp : place r pc (_ :: ls) with
        | error e => rw [hp] at h; cases h
        | ok x => rw [hp] at h; simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; simp
    · split at h
      · cases h
      · cases hp : place r pc (_ :: ls) with
        | error e => rw [hp] at h; cases h
        | ok x => rw [hp] at h; simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; simp
    · split at h
      · next bs _ =>
        cases hp : place r (pc + bs.length) ls with
        | error e => rw [hp] at h; cases h
        | ok x => rw [hp] at h; simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; simp
      · cases h

theorem place_cons (it : Item) (r : List Item) (pc : Nat) (labels : List (String × Nat)) :
    place (it :: r) pc labels =
      match it with
      | .label n =>
        if labels.any (·.1 == n) then .error s!"label {n} defined twice"
        else (place r pc ((n, pc) :: labels)).map fun x => (pc :: x.1, x.2)
      | .equ n v =>
        if labels.any (·.1 == n) then .error s!"label {n} defined twice"
        else (place r pc ((n, v) :: labels)).map fun x => (pc :: x.1, x.2)
      | _ =>
        match it.encode { sizing := true, pc := Int.ofNat pc } with
        | .ok bs => (place r (pc + bs.length) labels).map fun x => (pc :: x.1, x.2)
        | .error e => .error e := by
  cases it <;> rfl

/-- **The first pass, a stretch then the rest.** -/
theorem place_step : ∀ (a b : List Item) (pc pc' : Nat) (ls ls' : List (String × Nat)) (A : List Nat)
    (R : List Nat × List (String × Nat)),
    place a pc ls = .ok (A ++ [pc'], ls') → place b pc' ls' = .ok R → place (a ++ b) pc ls = .ok (A ++ R.1, R.2)
  | [], b, pc, pc', ls, ls', A, R, h1, h2 => by
    simp only [place, Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨h1, rfl⟩ := h1
    cases A with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, and_true] at h1
      subst h1
      simpa using h2
    | cons x A => simp at h1
  | it :: r, b, pc, pc', ls, ls', A, R, h1, h2 => by
    -- one item: its address, then the rest from where it ends
    have key : ∀ (pc2 : Nat) (ls2 : List (String × Nat)),
        place (it :: r) pc ls = (place r pc2 ls2).map (fun x => (pc :: x.1, x.2)) →
        place (it :: r ++ b) pc ls = (place (r ++ b) pc2 ls2).map (fun x => (pc :: x.1, x.2)) →
        place (it :: r ++ b) pc ls = .ok (A ++ R.1, R.2) := by
      intro pc2 ls2 e1 e2
      rw [e1] at h1
      cases hp : place r pc2 ls2 with
      | error e => rw [hp] at h1; cases h1
      | ok x =>
        obtain ⟨X, L⟩ := x
        rw [hp] at h1
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨hX, rfl⟩ := h1
        cases A with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hX
          exact absurd hX.2 (place_ne r pc2 ls2 X L hp)
        | cons a0 A' =>
          simp only [List.cons_append, List.cons.injEq] at hX
          obtain ⟨rfl, rfl⟩ := hX
          rw [e2, place_step r b pc2 pc' ls2 L A' R hp h2]
          rfl
    rw [place_cons] at h1
    split at h1
    · next n =>
      split at h1
      · cases h1
      · next hd =>
        refine key pc ((n, pc) :: ls) ?_ ?_ <;> (simp only [List.cons_append, place_cons, hd, Bool.false_eq_true, if_false])
    · next n v =>
      split at h1
      · cases h1
      · next hd =>
        refine key pc ((n, v) :: ls) ?_ ?_ <;> (simp only [List.cons_append, place_cons, hd, Bool.false_eq_true, if_false])
    · next hl he =>
      split at h1
      · next bs hbs =>
        refine key (pc + bs.length) ls ?_ ?_ <;>
          ((try simp only [List.cons_append]); rw [place_cons]; split <;> first | (exfalso; solve_by_elim) | (simp only [hbs]))
      · cases h1

theorem emit_cons (res : String → Option Int) (it : Item) (r : List Item) (a0 a1 : Nat) (as : List Nat) :
    emit res (it :: r) (a0 :: a1 :: as) =
      match it.encode { resolve := res, pc := Int.ofNat a0 } with
      | .ok bs =>
        if a1 != a0 + bs.length then .error s!"{it.text}: its size changed between the passes"
        else (emit res r (a1 :: as)).map (bs ++ ·)
      | .error e => .error e := rfl

/-- **The second pass, a stretch then the rest.** -/
theorem emit_step (res : String → Option Int) : ∀ (a b : List Item) (A : List Nat) (q : Nat) (B : List Nat)
    (x y : List UInt8),
    A.length = a.length → emit res a (A ++ [q]) = .ok x → emit res b (q :: B) = .ok y →
    emit res (a ++ b) (A ++ q :: B) = .ok (x ++ y)
  | [], b, A, q, B, x, y, hA, h1, h2 => by
    cases A with
    | nil =>
      simp only [List.nil_append] at h1 ⊢
      cases h1
      simpa using h2
    | cons _ _ => simp at hA
  | it :: r, b, A, q, B, x, y, hA, h1, h2 => by
    cases A with
    | nil => simp at hA
    | cons a0 A' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hA
      cases A' with
      | nil =>
        -- `it` is the last of the stretch: the next address is `q`
        have hr : r = [] := List.eq_nil_of_length_eq_zero hA.symm
        subst hr
        simp only [List.nil_append, List.cons_append] at h1 ⊢
        rw [emit_cons] at h1 ⊢
        cases henc : it.encode { resolve := res, pc := Int.ofNat a0 } with
        | error e => rw [henc] at h1; cases h1
        | ok bs =>
          rw [henc] at h1
          simp only at h1 ⊢
          split at h1
          · cases h1
          · next hne =>
            rw [if_neg hne]
            simp only [emit, Except.map, Except.ok.injEq, List.append_nil] at h1
            subst h1
            rw [h2]
            rfl
      | cons a1 C =>
        simp only [List.cons_append] at h1 ⊢
        rw [emit_cons] at h1 ⊢
        cases henc : it.encode { resolve := res, pc := Int.ofNat a0 } with
        | error e => rw [henc] at h1; cases h1
        | ok bs =>
          rw [henc] at h1
          simp only at h1 ⊢
          split at h1
          · cases h1
          · next hne =>
            rw [if_neg hne]
            cases he : emit res r (a1 :: (C ++ [q])) with
            | error e => rw [he] at h1; cases h1
            | ok x' =>
              rw [he] at h1
              simp only [Except.map, Except.ok.injEq] at h1
              subst h1
              have := emit_step res r b (a1 :: C) q B x' y (by simpa using hA) (by simpa using he) h2
              simp only [List.cons_append] at this
              rw [this]
              simp [Except.map]

/-- The same, the rest's addresses given as one list. -/
theorem emit_step' (res : String → Option Int) (a b : List Item) (A : List Nat) (q : Nat) (C : List Nat)
    (x y : List UInt8) (hA : A.length = a.length) (hC : C.head? = some q)
    (h1 : emit res a (A ++ [q]) = .ok x) (h2 : emit res b C = .ok y) :
    emit res (a ++ b) (A ++ C) = .ok (x ++ y) := by
  cases C with
  | nil => cases hC
  | cons c B =>
    simp only [List.head?_cons, Option.some.injEq] at hC
    subst hC
    exact emit_step res a b A c B x y hA h1 h2

/-- **The assembler, from its passes.** -/
theorem assemble_of (items : List Item) (A : List Nat) (e : Nat) (L : List (String × Nat)) (B : List UInt8)
    (hp : place items 0 [] = .ok (A ++ [e], L.reverse)) (he : e ≤ 0x10000)
    (hm : emit (fun s => (L.reverse.lookup s).map Int.ofNat) items (A ++ [e]) = .ok B) :
    assemble items = .ok { origin := 0, bytes := ByteArray.mk B.toArray, labels := L, addrs := A.toArray } := by
  unfold assemble
  rw [hp]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
  rw [if_neg (by omega), hm]
  simp

end Ember.Proof.Z80Gen
