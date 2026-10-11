import Ember.Proof.CStmt
import Ember.Proof.IRMem
import Ember.Proof.IRFuel

/-!
# Ember.Proof.IRTypes — well-typed expressions, for the IR's lowering (plan M7.1)

The lowering has its own environment (`IR.Env`: where every variable is
in memory) and its own `Env.tyOf`.  `WT` is what the proofs need of a
checked expression, over that; `evalE_hasTy`: a well-typed expression
evaluates to a value of its type.  Values and their types (`HasTy`) are
those of `Ember.Proof.CTypes`.
-/

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record hasTy_mask hasTy_bool_mk
  hasTy_int_mk binop_hasTy lookup_of_findIdx mask_lt)

/-- Offset of the `i`-th field. -/
def fldOff (p : Prog) : List (String × Ty) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | (_, t) :: rest, i + 1 => sizeOf p t + fldOff p rest i

theorem fieldOffIn_of_findIdx (p : Prog) (fs : List (String × Ty)) (f : String) (o i : Nat)
    (h : fs.findIdx? (·.1 == f) = some i) :
    ∃ hi : i < fs.length, fieldOffIn p fs f o = some (o + fldOff p fs i, fs[i].2) := by
  induction fs generalizing o i with
  | nil => simp at h
  | cons a t ih =>
    obtain ⟨k, x⟩ := a
    rw [List.findIdx?_cons] at h
    by_cases hk : (k == f) = true
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h
      exact ⟨by simp, by simp [fieldOffIn, hk, fldOff]⟩
    · simp only [hk, Bool.false_eq_true, if_false] at h
      cases hj : t.findIdx? (·.1 == f) with
      | none => simp [hj] at h
      | some j =>
        simp only [hj, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hj', hl⟩ := ih (o + sizeOf p x) j hj
        refine ⟨by simp; omega, ?_⟩
        simp only [fieldOffIn, hk, Bool.false_eq_true, if_false, hl, fldOff, List.getElem_cons_succ]
        rw [Nat.add_assoc]

theorem fieldOffIn_none (p : Prog) (fs : List (String × Ty)) (f : String) (o : Nat)
    (h : fs.findIdx? (·.1 == f) = none) : fieldOffIn p fs f o = none := by
  induction fs generalizing o with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨k, x⟩ := a
    rw [List.findIdx?_cons] at h
    by_cases hk : (k == f) = true
    · simp [hk] at h
    · simp only [hk, Bool.false_eq_true, if_false, Option.map_eq_none_iff] at h
      simp only [fieldOffIn, hk, Bool.false_eq_true, if_false]
      exact ih _ h

/-- What the proofs need of a checked expression. -/
def WT (g : IR.Env) : Expr → Prop
  | .lit v (some w) => v < 2 ^ w.bits
  | .lit _ none => False
  | .blit _ => True
  | .var _ => True
  | .field b _ => WT g b
  | .index b i => WT g b ∧ WT g i ∧ (∃ w, g.tyOf i = .ok (.int w)) ∧
      ∀ el n, g.tyOf b = .ok (.arr el n) → n < 65536
  | .bin op a b => WT g a ∧ WT g b ∧
      (if op.isLogic then g.tyOf a = .ok .bool ∧ g.tyOf b = .ok .bool
       else if op.isShift then (∃ w, g.tyOf a = .ok (.int w)) ∧ ∃ w, g.tyOf b = .ok (.int w)
       else if op = .eq ∨ op = .ne then ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true
       else ∃ w, g.tyOf a = .ok (.int w) ∧ g.tyOf b = .ok (.int w))
  | .un op a => WT g a ∧ (if op = .lnot then g.tyOf a = .ok .bool else ∃ w, g.tyOf a = .ok (.int w))
  | .cast _ a => WT g a ∧ ∃ t, g.tyOf a = .ok t ∧ t.isScalar = true
  | .cond c a b => WT g c ∧ WT g a ∧ WT g b ∧ g.tyOf c = .ok .bool ∧
      ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true

/-- Every variable in scope holds a value of its type. -/
def VarsTyped (g : IR.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) : Prop :=
  ∀ x v info, Lang.Sem.lookup st env x = some v → g.varInfo x = .ok info → HasTy g.prog info.ty v

theorem evalE_hasTy (g : IR.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) (hv : VarsTyped g st env) :
    ∀ (e : Expr) (v : Val) (t : Ty), WT g e → Lang.Sem.evalE g.prog st env e = some v → g.tyOf e = .ok t →
      HasTy g.prog t v
  | .lit n (some w), v, t, _, h, ht => by
    simp only [Lang.Sem.evalE, Option.some.injEq] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst h ht
    exact hasTy_mask _ _ _
  | .lit _ none, _, _, hw, _, _ => absurd hw (by simp [WT])
  | .blit b, v, t, _, h, ht => by
    simp only [Lang.Sem.evalE, Option.some.injEq] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst h ht
    exact hasTy_bool_mk _ _
  | .var x, v, t, _, h, ht => by
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hi : g.varInfo x with
    | error m => simp [hi] at ht
    | ok info =>
      simp only [hi, Except.ok.injEq] at ht
      subst ht
      exact hv x v info h hi
  | .field b f, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hb : Lang.Sem.evalE g.prog st env b with
    | none => simp [hb] at h
    | some bv =>
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb =>
        have ih := evalE_hasTy g st env hv b bv tb hw hb htb
        cases tb with
        | record r =>
          obtain ⟨fs, sd, rfl, hsd, hsz, hfs⟩ := hasTy_record ih
          simp only [hb, Lang.Sem.fieldIndex, hsd] at h
          simp only [htb, fieldOff, hsd, Option.map_some, Option.getD_some] at ht
          cases hi : sd.fields.findIdx? (·.1 == f) with
          | none => simp [hi] at h
          | some i =>
            simp only [hi] at h
            obtain ⟨hlt, hl⟩ := fieldOffIn_of_findIdx g.prog sd.fields f 0 i hi
            simp only [hl, Except.ok.injEq] at ht
            subst ht
            have hlt' : i < fs.size := by omega
            rw [Array.getElem?_eq_getElem hlt'] at h
            simp only [Option.some.injEq] at h
            subst h
            exact (hfs i hlt' hlt).hasTy
        | int _ => simp [htb, Env.err] at ht
        | bool => simp [htb, Env.err] at ht
        | arr _ _ => simp [htb, Env.err] at ht
  | .index b i, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hb : Lang.Sem.evalE g.prog st env b with
    | none => simp [hb] at h
    | some bv =>
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb =>
        have ih := evalE_hasTy g st env hv b bv tb hw.1 hb htb
        cases tb with
        | arr el n =>
          obtain ⟨xs, rfl, _, hxs⟩ := hasTy_arr ih
          simp only [htb, Except.ok.injEq] at ht
          subst ht
          cases hi : Lang.Sem.evalE g.prog st env i with
          | none => simp [hb, hi] at h
          | some iv =>
            simp only [hb, hi] at h
            exact (hxs v (Array.mem_of_getElem? h)).hasTy
        | int _ => simp [htb, Env.err] at ht
        | bool => simp [htb, Env.err] at ht
        | record _ => simp [htb, Env.err] at ht
  | .bin op a b, v, t, hw, h, ht => by
    simp only [WT] at hw
    obtain ⟨wa, wb, hty⟩ := hw
    simp only [Lang.Sem.evalE] at h
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => simp [ha] at h
    | some x =>
      cases hb : Lang.Sem.evalE g.prog st env b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        have hex : (∃ ta, g.tyOf a = .ok ta) ∧ (∃ tb, g.tyOf b = .ok tb) := by
          split at hty
          · exact ⟨⟨_, hty.1⟩, ⟨_, hty.2⟩⟩
          · split at hty
            · obtain ⟨⟨w, h1⟩, ⟨w', h2⟩⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
            · split at hty
              · obtain ⟨t, h1, h2, _⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
              · obtain ⟨w, h1, h2⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
        obtain ⟨hta, htb⟩ := hex
        obtain ⟨ta, hta⟩ := hta
        obtain ⟨tb, htb⟩ := htb
        have iha := evalE_hasTy g st env hv a x ta wa ha hta
        have ihb := evalE_hasTy g st env hv b y tb wb hb htb
        have hres := binop_hasTy g.prog op x y v ta tb iha ihb (by
          simp only [hta, htb, Except.ok.injEq] at hty
          by_cases h1 : op.isLogic = true
          · rw [if_pos h1] at hty ⊢; exact hty
          · rw [if_neg h1] at hty ⊢
            by_cases h2 : op.isShift = true
            · rw [if_pos h2] at hty ⊢; exact hty
            · rw [if_neg h2] at hty ⊢
              by_cases h3 : op = .eq ∨ op = .ne
              · rw [if_pos h3] at hty ⊢; obtain ⟨t', rfl, rfl, hs⟩ := hty; exact ⟨rfl, hs⟩
              · rw [if_neg h3] at hty ⊢; obtain ⟨w, rfl, rfl⟩ := hty; exact ⟨w, rfl, rfl⟩) h
        simp only [Env.tyOf] at ht
        split at ht
        · rename_i hc
          simp only [Except.ok.injEq] at ht
          subst ht
          simpa [hc] using hres
        · rename_i hc
          rw [hta] at ht
          simp only [Except.ok.injEq] at ht
          subst ht
          simpa [hc] using hres
  | .un op a, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => cases op <;> simp [ha] at h
    | some x =>
      have ih := evalE_hasTy g st env hv a x t hw.1 ha ht
      cases op with
      | lnot =>
        simp only [if_true] at hw
        rw [hw.2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl⟩ := hasTy_bool ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_bool_mk _ _
      | bnot =>
        simp only [reduceCtorEq, if_false] at hw
        obtain ⟨w, hw2⟩ := hw.2
        rw [hw2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl, _⟩ := hasTy_int ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
      | neg =>
        simp only [reduceCtorEq, if_false] at hw
        obtain ⟨w, hw2⟩ := hw.2
        rw [hw2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl, _⟩ := hasTy_int ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
  | .cast w a, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst ht
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => simp [ha] at h
    | some x =>
      cases x with
      | int w' xv =>
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
      | bool b =>
        simp only [ha, Option.some.injEq] at h
        subst h
        refine hasTy_int_mk _ _ _ ?_
        cases b <;> cases w <;> decide
      | arr _ => simp [ha] at h
      | record _ _ => simp [ha] at h
  | .cond c a b, v, t, hw, h, ht => by
    simp only [WT] at hw
    obtain ⟨wc, wa, wb, _, t', hta, htb, _⟩ := hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    rw [hta] at ht
    simp only [Except.ok.injEq] at ht
    subst ht
    cases hc : Lang.Sem.evalE g.prog st env c with
    | none => simp [hc] at h
    | some cv =>
      cases ha : Lang.Sem.evalE g.prog st env a with
      | none => simp [hc, ha] at h
      | some x =>
        cases hb : Lang.Sem.evalE g.prog st env b with
        | none => simp [hc, ha, hb] at h
        | some y =>
          simp only [hc, ha, hb, Option.some.injEq] at h
          subst h
          split
          · exact evalE_hasTy g st env hv a x _ wa ha hta
          · exact evalE_hasTy g st env hv b y _ wb hb htb


end Ember.Proof.IRSim
