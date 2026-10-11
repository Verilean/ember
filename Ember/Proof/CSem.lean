import Ember.C.Sem

/-!
# Ember.Proof.CSem — facts about the C semantics (plan M5.8)

* an expression that has a value keeps it when variables with new names
  are declared (`evalC_ext`);
* a list of statements run as a prefix of a block (`Runs`, `Traps`).
-/

namespace Ember.C.Sem

/-! ## More variables -/

/-- The names of `xs` are new: not in `env`, not global. -/
def Ext (xs env : Env) (st : St) : Prop :=
  ∀ y, y ∈ xs.map (·.1) → env.lookup y = none ∧ st.globals.lookup y = none

theorem lookup_eq_none_of_not_mem {xs : Env} {x : String} (h : x ∉ xs.map (·.1)) : xs.lookup x = none := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨y, v⟩ := a
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (x == y) = false := by simpa using h.1
    simp only [List.lookup, hne]
    exact ih h.2

theorem lookup_ext {xs env : Env} {st : St} (hx : Ext xs env st) {x : String} {v : CVal}
    (h : env.lookup x = some v) : (xs ++ env).lookup x = some v := by
  have hn : x ∉ xs.map (·.1) := fun hm => by
    have := (hx x hm).1
    rw [h] at this
    exact absurd this (by simp)
  rw [List.lookup_append, lookup_eq_none_of_not_mem hn]
  simpa using h

theorem lookup_ext_none {xs env : Env} {st : St} (hx : Ext xs env st) {x : String}
    (h : env.lookup x = none) (hg : (st.globals.lookup x).isSome) : (xs ++ env).lookup x = none := by
  have hn : x ∉ xs.map (·.1) := fun hm => by
    have := (hx x hm).2
    rw [this] at hg
    exact absurd hg (by simp)
  rw [List.lookup_append, lookup_eq_none_of_not_mem hn]
  simpa using h

theorem varLoc_ext {xs env : Env} {st : St} (hx : Ext xs env st) {x : String} {l : Loc}
    (h : varLoc st env x = some l) : varLoc st (xs ++ env) x = some l := by
  unfold varLoc at h ⊢
  cases he : env.lookup x with
  | some v =>
    rw [he] at h
    rw [lookup_ext hx he]
    exact h
  | none =>
    rw [he] at h
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
    by_cases hg : (st.globals.lookup x).isSome
    · rw [lookup_ext_none hx he hg]
      simpa [hg] using h
    · simp [hg] at h

theorem readBase_ext {xs env : Env} {st : St} (hx : Ext xs env st) {b : Base} {v : CVal}
    (h : readBase st env b = some v) : readBase st (xs ++ env) b = some v := by
  cases b with
  | global g => exact h
  | frame d x =>
    simp only [readBase] at h ⊢
    by_cases hd : d = st.stack.length
    · rw [if_pos hd] at h ⊢
      exact lookup_ext hx h
    · rw [if_neg hd] at h ⊢
      exact h

theorem read_ext {xs env : Env} {st : St} (hx : Ext xs env st) {l : Loc} {v : CVal}
    (h : read st env l = some v) : read st (xs ++ env) l = some v := by
  unfold read at h ⊢
  cases hb : readBase st env l.base with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some b =>
    rw [hb] at h
    rw [readBase_ext hx hb]
    exact h

theorem idxLoc_ext {xs env : Env} {st : St} (hx : Ext xs env st) {la l : Loc} {i : CVal}
    (h : idxLoc st env la i = some l) : idxLoc st (xs ++ env) la i = some l := by
  unfold idxLoc at h ⊢
  cases i with
  | int b iv =>
    simp only at h ⊢
    cases hr : read st env la with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some v => rw [hr] at h; rw [read_ext hx hr]; exact h
  | _ => exact absurd h (by simp)

theorem dotLoc_ext {cp : CProg} {xs env : Env} {st : St} (hx : Ext xs env st) {la l : Loc} {f : String}
    (h : dotLoc cp st env la f = some l) : dotLoc cp st (xs ++ env) la f = some l := by
  unfold dotLoc at h ⊢
  cases hr : read st env la with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some v => rw [hr] at h; rw [read_ext hx hr]; exact h

theorem arrowLoc_ext {cp : CProg} {xs env : Env} {st : St} (hx : Ext xs env st) {la l : Loc} {f : String}
    (h : arrowLoc cp st env la f = some l) : arrowLoc cp st (xs ++ env) la f = some l := by
  unfold arrowLoc at h ⊢
  cases hr : read st env la with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some v =>
    rw [hr] at h
    rw [read_ext hx hr]
    cases v with
    | ptr l' => exact dotLoc_ext hx h
    | _ => exact absurd h (by simp)

section
variable {cp : CProg} {xs env : Env} {st : St}

mutual

theorem lval_ext (hx : Ext xs env st) : ∀ (e : CExpr) {l : Loc},
    lval cp st env e = some l → lval cp st (xs ++ env) e = some l
  | .var x, l, h => by
    simp only [lval] at h ⊢
    exact varLoc_ext hx h
  | .index a i, l, h => by
    simp only [lval] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      cases hi : evalC cp st env i with
      | none => simp [ha, hi] at h
      | some iv =>
        simp only [ha, hi] at h
        simp only [lval_ext hx a ha, evalC_ext hx i hi]
        exact idxLoc_ext hx h
  | .dot a f, l, h => by
    simp only [lval] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      simp only [ha] at h
      simp only [lval_ext hx a ha]
      exact dotLoc_ext hx h
  | .arrow a f, l, h => by
    simp only [lval] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      simp only [ha] at h
      simp only [lval_ext hx a ha]
      exact arrowLoc_ext hx h
  | .lit _ _, _, h => by simp [lval] at h
  | .blit _, _, h => by simp [lval] at h
  | .bin _ _ _, _, h => by simp [lval] at h
  | .un _ _, _, h => by simp [lval] at h
  | .cast _ _, _, h => by simp [lval] at h
  | .cond _ _ _, _, h => by simp [lval] at h
  | .addr _, _, h => by simp [lval] at h
  | .call _ _, _, h => by simp [lval] at h
  | .str _, _, h => by simp [lval] at h

theorem evalC_ext (hx : Ext xs env st) : ∀ (e : CExpr) {v : CVal},
    evalC cp st env e = some v → evalC cp st (xs ++ env) e = some v
  | .var x, v, h => by
    simp only [evalC] at h ⊢
    cases hv : varLoc st env x with
    | none => simp [hv] at h
    | some l =>
      simp only [hv] at h
      simp only [varLoc_ext hx hv]
      exact read_ext hx h
  | .index a i, v, h => by
    simp only [evalC] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      cases hi : evalC cp st env i with
      | none => simp [ha, hi] at h
      | some iv =>
        simp only [ha, hi] at h
        simp only [lval_ext hx a ha, evalC_ext hx i hi]
        cases hl : idxLoc st env la iv with
        | none => simp [hl] at h
        | some l =>
          simp only [hl] at h
          simp only [idxLoc_ext hx hl]
          exact read_ext hx h
  | .dot a f, v, h => by
    simp only [evalC] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      simp only [ha] at h
      simp only [lval_ext hx a ha]
      cases hl : dotLoc cp st env la f with
      | none => simp [hl] at h
      | some l =>
        simp only [hl] at h
        simp only [dotLoc_ext hx hl]
        exact read_ext hx h
  | .arrow a f, v, h => by
    simp only [evalC] at h ⊢
    cases ha : lval cp st env a with
    | none => simp [ha] at h
    | some la =>
      simp only [ha] at h
      simp only [lval_ext hx a ha]
      cases hl : arrowLoc cp st env la f with
      | none => simp [hl] at h
      | some l =>
        simp only [hl] at h
        simp only [arrowLoc_ext hx hl]
        exact read_ext hx h
  | .lit _ _, _, h => by simpa only [evalC] using h
  | .blit _, _, h => by simpa only [evalC] using h
  | .cast t a, v, h => by
    simp only [evalC] at h ⊢
    cases ha : evalC cp st env a with
    | none => simp [ha] at h
    | some av =>
      simp only [ha] at h
      simp only [evalC_ext hx a ha]
      exact h
  | .cond c a b, v, h => by
    simp only [evalC] at h ⊢
    cases hc : evalC cp st env c with
    | none => simp [hc] at h
    | some cv =>
      simp only [hc] at h
      simp only [evalC_ext hx c hc]
      cases ht : truthy cv with
      | none => simp [ht] at h
      | some t =>
        cases t with
        | true => simp only [ht] at h ⊢; exact evalC_ext hx a h
        | false => simp only [ht] at h ⊢; exact evalC_ext hx b h
  | .bin op a b, v, h => by
    simp only [evalC] at h ⊢
    have bt : ∀ (e : CExpr) (t : Bool), (∀ {v : CVal}, evalC cp st env e = some v → evalC cp st (xs ++ env) e = some v) →
        (evalC cp st env e).bind truthy = some t → (evalC cp st (xs ++ env) e).bind truthy = some t := by
      intro e t ih ht
      cases he : evalC cp st env e with
      | none => simp [he] at ht
      | some ev => rw [ih he]; rw [he] at ht; exact ht
    by_cases h1 : (op == "&&") = true
    · simp only [h1, if_true] at h ⊢
      cases hta : (evalC cp st env a).bind truthy with
      | none => simp [hta] at h
      | some t =>
        simp only [hta] at h
        simp only [bt a t (evalC_ext hx a) hta]
        cases t with
        | false => exact h
        | true =>
          simp only at h ⊢
          cases htb : (evalC cp st env b).bind truthy with
          | none => simp [htb] at h
          | some t' => rw [htb] at h; rw [bt b t' (evalC_ext hx b) htb]; exact h
    · simp only [h1, Bool.false_eq_true, if_false] at h ⊢
      by_cases h2 : (op == "||") = true
      · simp only [h2, if_true] at h ⊢
        cases hta : (evalC cp st env a).bind truthy with
        | none => simp [hta] at h
        | some t =>
          simp only [hta] at h
          simp only [bt a t (evalC_ext hx a) hta]
          cases t with
          | true => exact h
          | false =>
            simp only at h ⊢
            cases htb : (evalC cp st env b).bind truthy with
            | none => simp [htb] at h
            | some t' => rw [htb] at h; rw [bt b t' (evalC_ext hx b) htb]; exact h
      · simp only [h2, Bool.false_eq_true, if_false] at h ⊢
        cases ha : evalC cp st env a with
        | none => simp [ha] at h
        | some av =>
          cases hb : evalC cp st env b with
          | none => simp [ha, hb] at h
          | some bv =>
            simp only [ha, hb] at h
            simp only [evalC_ext hx a ha, evalC_ext hx b hb]
            exact h
  | .un op a, v, h => by
    simp only [evalC] at h ⊢
    cases ha : evalC cp st env a with
    | none => simp [ha] at h
    | some av =>
      simp only [ha] at h
      simp only [evalC_ext hx a ha]
      exact h
  | .call f args, v, h => by
    simp only [evalC] at h ⊢
    cases has : evalCs cp st env args with
    | none => cases hh : helper f <;> simp [has, hh] at h
    | some vs =>
      simp only [has] at h
      simp only [evalCs_ext hx args has]
      exact h
  | .addr _, _, h => by simp [evalC] at h
  | .str _, _, h => by simp [evalC] at h

theorem evalCs_ext (hx : Ext xs env st) : ∀ (es : List CExpr) {vs : List CVal},
    evalCs cp st env es = some vs → evalCs cp st (xs ++ env) es = some vs
  | [], vs, h => by simpa only [evalCs] using h
  | e :: es, vs, h => by
    simp only [evalCs] at h ⊢
    cases he : evalC cp st env e with
    | none => simp [he] at h
    | some v =>
      cases hes : evalCs cp st env es with
      | none => simp [he, hes] at h
      | some vs' =>
        simp only [he, hes] at h
        simp only [evalC_ext hx e he, evalCs_ext hx es hes]
        exact h

end

end

/-! ## Statements run as the beginning of a block -/

/-- The statements `pre` run to the end, leave the state alone and turn
the variables `env` into `env'` — as the beginning of any block, with any
fuel from 5 up for what follows. -/
def Runs (cp : CProg) (st : St) (env : Env) (pre : List CStmt) (env' : Env) : Prop :=
  ∀ n rest, execL (n + 5 + pre.length) cp st env (pre ++ rest) = execL (n + 5) cp st env' rest

/-- The statements `pre` end in `ember_trap`. -/
def Traps (cp : CProg) (st : St) (env : Env) (pre : List CStmt) : Prop :=
  ∀ n rest, execL (n + 5 + pre.length) cp st env (pre ++ rest) = .trap st

variable {cp : CProg} {st : St} {env env1 env2 : Env} {p1 p2 : List CStmt}

theorem Runs.nil : Runs cp st env [] env := fun _ _ => rfl

theorem Runs.append (h1 : Runs cp st env p1 env1) (h2 : Runs cp st env1 p2 env2) :
    Runs cp st env (p1 ++ p2) env2 := by
  intro n rest
  rw [List.append_assoc, List.length_append, show n + 5 + (p1.length + p2.length) = n + p2.length + 5 + p1.length by omega,
    h1 (n + p2.length), show n + p2.length + 5 = n + 5 + p2.length by omega, h2 n]

theorem Runs.traps (h1 : Runs cp st env p1 env1) (h2 : Traps cp st env1 p2) : Traps cp st env (p1 ++ p2) := by
  intro n rest
  rw [List.append_assoc, List.length_append, show n + 5 + (p1.length + p2.length) = n + p2.length + 5 + p1.length by omega,
    h1 (n + p2.length), show n + p2.length + 5 = n + 5 + p2.length by omega, h2 n]

theorem Traps.append (h1 : Traps cp st env p1) : Traps cp st env (p1 ++ p2) := by
  intro n rest
  rw [List.append_assoc, List.length_append, show n + 5 + (p1.length + p2.length) = n + p2.length + 5 + p1.length by omega,
    h1 (n + p2.length)]

theorem Runs.single {s : CStmt} (h : ∀ m, execS (m + 5) cp st env s = .ok st env1 .normal) :
    Runs cp st env [s] env1 := by
  intro n rest
  show execL (n + 5 + 1) cp st env (s :: rest) = _
  rw [execL, h n]

theorem Traps.single {s : CStmt} (h : ∀ m, execS (m + 5) cp st env s = .trap st) : Traps cp st env [s] := by
  intro n rest
  show execL (n + 5 + 1) cp st env (s :: rest) = _
  rw [execL, h n]

end Ember.C.Sem

namespace Ember.C

/-! ## `CExpr.same` is equality -/

mutual
theorem CExpr.same_eq : ∀ (a b : CExpr), a.same b = true → a = b
  | .var x, b, h => by
    cases b with
    | var y => simp only [CExpr.same, beq_iff_eq] at h; rw [h]
    | _ => simp [CExpr.same] at h
  | .lit n s, b, h => by
    cases b with
    | lit m t => simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
    | _ => simp [CExpr.same] at h
  | .blit x, b, h => by
    cases b with
    | blit y => simp only [CExpr.same, beq_iff_eq] at h; rw [h]
    | _ => simp [CExpr.same] at h
  | .bin o a1 a2, b, h => by
    cases b with
    | bin o' b1 b2 =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, CExpr.same_eq a1 b1 h.1.2, CExpr.same_eq a2 b2 h.2]
    | _ => simp [CExpr.same] at h
  | .un o a1, b, h => by
    cases b with
    | un o' b1 =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, CExpr.same_eq a1 b1 h.2]
    | _ => simp [CExpr.same] at h
  | .cast t a1, b, h => by
    cases b with
    | cast t' b1 =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, CExpr.same_eq a1 b1 h.2]
    | _ => simp [CExpr.same] at h
  | .cond c a1 a2, b, h => by
    cases b with
    | cond c' b1 b2 =>
      simp only [CExpr.same, Bool.and_eq_true] at h
      rw [CExpr.same_eq c c' h.1.1, CExpr.same_eq a1 b1 h.1.2, CExpr.same_eq a2 b2 h.2]
    | _ => simp [CExpr.same] at h
  | .index a1 i, b, h => by
    cases b with
    | index b1 j =>
      simp only [CExpr.same, Bool.and_eq_true] at h
      rw [CExpr.same_eq a1 b1 h.1, CExpr.same_eq i j h.2]
    | _ => simp [CExpr.same] at h
  | .dot a1 f, b, h => by
    cases b with
    | dot b1 f' =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [CExpr.same_eq a1 b1 h.1, h.2]
    | _ => simp [CExpr.same] at h
  | .arrow a1 f, b, h => by
    cases b with
    | arrow b1 f' =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [CExpr.same_eq a1 b1 h.1, h.2]
    | _ => simp [CExpr.same] at h
  | .addr a1, b, h => by
    cases b with
    | addr b1 =>
      simp only [CExpr.same] at h
      rw [CExpr.same_eq a1 b1 h]
    | _ => simp [CExpr.same] at h
  | .call f as, b, h => by
    cases b with
    | call f' bs =>
      simp only [CExpr.same, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, CExpr.sameL_eq as bs h.2]
    | _ => simp [CExpr.same] at h
  | .str s, b, h => by
    cases b with
    | str t => simp only [CExpr.same, beq_iff_eq] at h; rw [h]
    | _ => simp [CExpr.same] at h

theorem CExpr.sameL_eq : ∀ (as bs : List CExpr), CExpr.sameL as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [CExpr.sameL, Bool.and_eq_true] at h
    rw [CExpr.same_eq a b h.1, CExpr.sameL_eq as bs h.2]
  | [], _ :: _, h => by simp [CExpr.sameL] at h
  | _ :: _, [], h => by simp [CExpr.sameL] at h
end

end Ember.C
