import Ember.Proof.CSem

/-!
# Ember.Proof.CFuel — more fuel changes nothing (plan M5.8)

A run of the C semantics that ends (normally, in a trap, or without a
meaning) ends the same way with more fuel; so statements can be put
together without counting (`Exec`).
-/

namespace Ember.C.Sem

/-- The run ended: it did not stop for lack of fuel. -/
def Res.Done : Res → Prop
  | .fuel => False
  | _ => True

theorem dich {a b : Res} (h : ∀ r, a = r → r.Done → b = r) : a = .fuel ∨ b = a := by
  cases ha : a with
  | fuel => exact Or.inl rfl
  | ok st env o => exact Or.inr (h _ ha trivial)
  | trap st => exact Or.inr (h _ ha trivial)
  | undef => exact Or.inr (h _ ha trivial)

theorem not_done_fuel {r : Res} (h : Res.fuel = r) (hr : r.Done) : False := by
  subst h; exact hr

/-- One more unit of fuel. -/
theorem mono1 (m : Nat) :
    (∀ cp st env ss r, execB m cp st env ss = r → r.Done → execB (m + 1) cp st env ss = r) ∧
    (∀ cp st env ss r, execL m cp st env ss = r → r.Done → execL (m + 1) cp st env ss = r) ∧
    (∀ cp st env f args r, callC m cp st env f args = r → r.Done → callC (m + 1) cp st env f args = r) ∧
    (∀ cp st env s r, execS m cp st env s = r → r.Done → execS (m + 1) cp st env s = r) ∧
    (∀ cp st env i hi body r, forC m cp st env i hi body = r → r.Done → forC (m + 1) cp st env i hi body = r) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro cp st env ss r h hr; rw [execB] at h; exact (not_done_fuel h hr).elim
    · intro cp st env ss r h hr; rw [execL] at h; exact (not_done_fuel h hr).elim
    · intro cp st env f args r h hr; rw [callC] at h; exact (not_done_fuel h hr).elim
    · intro cp st env s r h hr; rw [execS] at h; exact (not_done_fuel h hr).elim
    · intro cp st env i hi body r h hr; rw [forC] at h; exact (not_done_fuel h hr).elim
  | succ m ih =>
    obtain ⟨ihB, ihL, ihC, ihS, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro cp st env ss r h hr
      rw [execB] at h ⊢
      rcases dich (ihL cp st env ss) with hf | he
      · rw [hf] at h; exact (not_done_fuel h hr).elim
      · rw [he]; exact h
    · intro cp st env ss r h hr
      cases ss with
      | nil => rw [execL] at h ⊢; exact h
      | cons s rest =>
        rw [execL] at h ⊢
        rcases dich (ihS cp st env s) with hf | he
        · rw [hf] at h; exact (not_done_fuel h hr).elim
        · rw [he]
          cases hs : execS m cp st env s with
          | ok st' env' o =>
            rw [hs] at h
            cases o with
            | normal =>
              simp only at h ⊢
              exact ihL _ _ _ _ _ h hr
            | brk => exact h
            | ret v => exact h
          | trap st' => rw [hs] at h; exact h
          | undef => rw [hs] at h; exact h
          | fuel => rw [hs] at h; exact h
    · intro cp st env f args r h hr
      rw [callC] at h ⊢
      by_cases ht : (f == "ember_trap") = true
      · simp only [ht, if_true] at h ⊢; exact h
      · simp only [ht, Bool.false_eq_true, if_false] at h ⊢
        cases hfd : cp.unit.fns.find? (·.name == f) with
        | none => simp only [hfd] at h ⊢; exact h
        | some fd =>
          simp only [hfd] at h ⊢
          cases hav : argVals cp st env fd.params args with
          | none => simp only [hav] at h ⊢; exact h
          | some vs =>
            simp only [hav] at h ⊢
            rcases dich (ihB cp { st with stack := env :: st.stack } ((fd.params.map (·.2)).zip vs) fd.body) with hf | he
            · rw [hf] at h; exact (not_done_fuel h hr).elim
            · rw [he]; exact h
    · intro cp st env s r h hr
      cases s with
      | decl t x init =>
        cases init with
        | none => simp only [execS] at h ⊢; exact h
        | some e =>
          simp only [execS] at h ⊢
          cases ha : asCall e with
          | none => simp only [ha] at h ⊢; exact h
          | some fa =>
            obtain ⟨f, args⟩ := fa
            simp only [ha] at h ⊢
            rcases dich (ihC cp st env f args) with hf | he
            · rw [hf] at h; exact (not_done_fuel h hr).elim
            · rw [he]; exact h
      | declZero t x => simp only [execS] at h ⊢; exact h
      | assign l e =>
        simp only [execS] at h ⊢
        cases ha : asCall e with
        | none => simp only [ha] at h ⊢; exact h
        | some fa =>
          obtain ⟨f, args⟩ := fa
          simp only [ha] at h ⊢
          cases hl : lval cp st env l with
          | none => simp only [hl] at h ⊢; exact h
          | some loc =>
            simp only [hl] at h ⊢
            rcases dich (ihC cp st env f args) with hf | he
            · rw [hf] at h; exact (not_done_fuel h hr).elim
            · rw [he]; exact h
      | expr e =>
        simp only [execS] at h ⊢
        cases ha : asCall e with
        | none => simp only [ha] at h ⊢; exact h
        | some fa =>
          obtain ⟨f, args⟩ := fa
          simp only [ha] at h ⊢
          rcases dich (ihC cp st env f args) with hf | he
          · rw [hf] at h; exact (not_done_fuel h hr).elim
          · rw [he]; exact h
      | ite c t e =>
        simp only [execS] at h ⊢
        cases hc : evalC cp st env c with
        | none => simp only [hc] at h ⊢; exact h
        | some cv =>
          simp only [hc] at h ⊢
          cases htv : truthy cv with
          | none => simp only [htv] at h ⊢; exact h
          | some b =>
            cases b with
            | true => simp only [htv] at h ⊢; exact ihB _ _ _ _ _ h hr
            | false => simp only [htv] at h ⊢; exact ihB _ _ _ _ _ h hr
      | forUp t i lo hi body =>
        simp only [execS] at h ⊢
        cases hlo : evalC cp st env lo with
        | none => simp only [hlo] at h ⊢; exact h
        | some v =>
          simp only [hlo] at h ⊢
          cases hcv : convTo cp t v with
          | none => simp only [hcv] at h ⊢; exact h
          | some v' =>
            simp only [hcv] at h ⊢
            rcases dich (ihF cp st ((i, v') :: env) i hi body) with hf | he
            · rw [hf] at h; exact (not_done_fuel h hr).elim
            · rw [he]; exact h
      | brk => simp only [execS] at h ⊢; exact h
      | ret e => cases e <;> (simp only [execS] at h ⊢; exact h)
      | block ss => simp only [execS] at h ⊢; exact ihB _ _ _ _ _ h hr
      | line n f => simp only [execS] at h ⊢; exact h
      | comment s => simp only [execS] at h ⊢; exact h
    · intro cp st env i hi body r h hr
      rw [forC] at h ⊢
      cases hl : env.lookup i with
      | none => simp only [hl] at h ⊢; exact h
      | some iv =>
        cases hh : evalC cp st env hi with
        | none => simp only [hl, hh] at h ⊢; exact h
        | some hv =>
          cases iv with
          | int b v =>
            cases hv with
            | int b' hval =>
              simp only [hl, hh] at h ⊢
              by_cases hlt : v < hval
              · simp only [hlt, if_true] at h ⊢
                rcases dich (ihB cp st env body) with hf | he
                · rw [hf] at h; exact (not_done_fuel h hr).elim
                · rw [he]
                  cases hb : execB m cp st env body with
                  | ok st' env' o =>
                    rw [hb] at h
                    cases o with
                    | normal =>
                      simp only at h ⊢
                      cases hl' : env'.lookup i with
                      | none => simp only [hl'] at h ⊢; exact h
                      | some iv' =>
                        cases iv' with
                        | int b2 v2 => simp only [hl'] at h ⊢; exact ihF _ _ _ _ _ _ _ h hr
                        | _ => simp only [hl'] at h ⊢; exact h
                    | brk => exact h
                    | ret v => exact h
                  | trap st' => rw [hb] at h; exact h
                  | undef => rw [hb] at h; exact h
                  | fuel => rw [hb] at h; exact h
              · simp only [hlt, if_false] at h ⊢; exact h
            | _ => simp only [hl, hh] at h ⊢; exact h
          | _ => simp only [hl, hh] at h ⊢; exact h

section
variable {cp : CProg} {st st1 : St} {env env1 : Env} {r : Res}

theorem execB_mono {ss : List CStmt} {m : Nat} (k : Nat) (h : execB m cp st env ss = r) (hr : r.Done) :
    execB (m + k) cp st env ss = r := by
  induction k with
  | zero => exact h
  | succ k ih => exact (mono1 (m + k)).1 _ _ _ _ _ ih hr

theorem execL_mono {ss : List CStmt} {m : Nat} (k : Nat) (h : execL m cp st env ss = r) (hr : r.Done) :
    execL (m + k) cp st env ss = r := by
  induction k with
  | zero => exact h
  | succ k ih => exact (mono1 (m + k)).2.1 _ _ _ _ _ ih hr

theorem callC_mono {f : String} {args : List CExpr} {m : Nat} (k : Nat) (h : callC m cp st env f args = r)
    (hr : r.Done) : callC (m + k) cp st env f args = r := by
  induction k with
  | zero => exact h
  | succ k ih => exact (mono1 (m + k)).2.2.1 _ _ _ _ _ _ ih hr

theorem execS_mono {s : CStmt} {m : Nat} (k : Nat) (h : execS m cp st env s = r) (hr : r.Done) :
    execS (m + k) cp st env s = r := by
  induction k with
  | zero => exact h
  | succ k ih => exact (mono1 (m + k)).2.2.2.1 _ _ _ _ _ ih hr

theorem forC_mono {i : String} {hi : CExpr} {body : List CStmt} {m : Nat} (k : Nat)
    (h : forC m cp st env i hi body = r) (hr : r.Done) : forC (m + k) cp st env i hi body = r := by
  induction k with
  | zero => exact h
  | succ k ih => exact (mono1 (m + k)).2.2.2.2 _ _ _ _ _ _ _ ih hr

theorem execB_le {ss : List CStmt} {m m' : Nat} (hm : m ≤ m') (h : execB m cp st env ss = r) (hr : r.Done) :
    execB m' cp st env ss = r := by
  have := execB_mono (m' - m) h hr
  rwa [show m + (m' - m) = m' by omega] at this

theorem execL_le {ss : List CStmt} {m m' : Nat} (hm : m ≤ m') (h : execL m cp st env ss = r) (hr : r.Done) :
    execL m' cp st env ss = r := by
  have := execL_mono (m' - m) h hr
  rwa [show m + (m' - m) = m' by omega] at this

theorem callC_le {f : String} {args : List CExpr} {m m' : Nat} (hm : m ≤ m') (h : callC m cp st env f args = r)
    (hr : r.Done) : callC m' cp st env f args = r := by
  have := callC_mono (m' - m) h hr
  rwa [show m + (m' - m) = m' by omega] at this

theorem execS_le {s : CStmt} {m m' : Nat} (hm : m ≤ m') (h : execS m cp st env s = r) (hr : r.Done) :
    execS m' cp st env s = r := by
  have := execS_mono (m' - m) h hr
  rwa [show m + (m' - m) = m' by omega] at this

theorem forC_le {i : String} {hi : CExpr} {body : List CStmt} {m m' : Nat} (hm : m ≤ m')
    (h : forC m cp st env i hi body = r) (hr : r.Done) : forC m' cp st env i hi body = r := by
  have := forC_mono (m' - m) h hr
  rwa [show m + (m' - m) = m' by omega] at this

/-! ## Statements in sequence, without counting fuel -/

/-- The statements `code`, as a whole list in one scope, end with `r`. -/
def Exec (cp : CProg) (st : St) (env : Env) (code : List CStmt) (r : Res) : Prop :=
  r.Done ∧ ∃ m, execL m cp st env code = r

theorem Exec.nil : Exec cp st env [] (.ok st env .normal) := ⟨trivial, 1, rfl⟩

/-- A result that ends the list: not "finished normally". -/
def Res.Stops : Res → Prop
  | .ok _ _ .normal => False
  | .fuel => False
  | _ => True

theorem Res.Stops.done {r : Res} (h : r.Stops) : r.Done := by
  cases r with
  | fuel => exact h
  | _ => trivial

theorem execL_stop {c1 : List CStmt} (c2 : List CStmt) : ∀ {m : Nat} {st : St} {env : Env},
    execL m cp st env c1 = r → r.Stops → execL m cp st env (c1 ++ c2) = r := by
  induction c1 with
  | nil =>
    intro m st env h hs
    cases m with
    | zero => rw [execL] at h; subst h; exact hs.elim
    | succ m => rw [execL] at h; subst h; exact hs.elim
  | cons s rest ih =>
    intro m st env h hs
    cases m with
    | zero => rw [execL] at h; subst h; exact hs.elim
    | succ m =>
      rw [List.cons_append, execL]
      rw [execL] at h
      cases hx : execS m cp st env s with
      | ok st' env' o =>
        rw [hx] at h
        cases o with
        | normal => exact ih h hs
        | brk => exact h
        | ret v => exact h
      | trap st' => rw [hx] at h; exact h
      | undef => rw [hx] at h; exact h
      | fuel => rw [hx] at h; exact h

theorem Exec.stop {c1 : List CStmt} (c2 : List CStmt) (h : Exec cp st env c1 r) (hs : r.Stops) :
    Exec cp st env (c1 ++ c2) r := by
  obtain ⟨hd, m, hm⟩ := h
  exact ⟨hd, m, execL_stop c2 hm hs⟩

theorem execL_seq {c1 : List CStmt} (c2 : List CStmt) : ∀ {m : Nat} {st : St} {env : Env},
    execL m cp st env c1 = .ok st1 env1 .normal → ∀ {m2 : Nat}, execL m2 cp st1 env1 c2 = r → r.Done →
    ∃ M, execL M cp st env (c1 ++ c2) = r := by
  induction c1 with
  | nil =>
    intro m st env h m2 h2 _
    cases m with
    | zero => rw [execL] at h; cases h
    | succ m =>
      rw [execL] at h
      cases h
      exact ⟨m2, h2⟩
  | cons s rest ih =>
    intro m st env h m2 h2 hr
    cases m with
    | zero => rw [execL] at h; cases h
    | succ m =>
      rw [execL] at h
      cases hx : execS m cp st env s with
      | ok st' env' o =>
        rw [hx] at h
        cases o with
        | normal =>
          obtain ⟨M, hM⟩ := ih h h2 hr
          refine ⟨max m M + 1, ?_⟩
          rw [List.cons_append, execL, execS_le (Nat.le_max_left m M) hx trivial]
          exact execL_le (Nat.le_max_right m M) hM hr
        | brk => cases h
        | ret v => cases h
      | trap st' => rw [hx] at h; cases h
      | undef => rw [hx] at h; cases h
      | fuel => rw [hx] at h; cases h

theorem Exec.seq {c1 c2 : List CStmt} (h1 : Exec cp st env c1 (.ok st1 env1 .normal)) (h2 : Exec cp st1 env1 c2 r) :
    Exec cp st env (c1 ++ c2) r := by
  obtain ⟨_, m, hm⟩ := h1
  obtain ⟨hr, m2, hm2⟩ := h2
  exact ⟨hr, execL_seq c2 hm hm2 hr⟩

theorem Runs.exec {pre rest : List CStmt} (h1 : Runs cp st env pre env1) (h2 : Exec cp st env1 rest r) :
    Exec cp st env (pre ++ rest) r := by
  obtain ⟨hr, m, hm⟩ := h2
  refine ⟨hr, m + 5 + pre.length, ?_⟩
  rw [h1 m rest]
  exact execL_le (by omega) hm hr

theorem Traps.exec {pre : List CStmt} (rest : List CStmt) (h1 : Traps cp st env pre) :
    Exec cp st env (pre ++ rest) (.trap st) :=
  ⟨trivial, 0 + 5 + pre.length, h1 0 rest⟩

/-- One statement. -/
theorem Exec.one {s : CStmt} {m : Nat} (h : execS m cp st env s = r) (hr : r.Done) : Exec cp st env [s] r := by
  refine ⟨hr, m + 2, ?_⟩
  rw [execL, execS_le (Nat.le_succ m) h hr]
  cases r with
  | ok st' env' o =>
    cases o with
    | normal => rfl
    | brk => rfl
    | ret v => rfl
  | trap st' => rfl
  | undef => rfl
  | fuel => exact hr.elim

/-- A block: its variables end with it. -/
theorem Exec.block {ss : List CStmt} {st' : St} {env' : Env} {o : Out} (h : Exec cp st env ss (.ok st' env' o)) :
    ∃ m, execB m cp st env ss = .ok st' (env'.drop (env'.length - env.length)) o := by
  obtain ⟨_, m, hm⟩ := h
  exact ⟨m + 1, by rw [execB, hm]⟩

theorem Exec.block_trap {ss : List CStmt} {st' : St} (h : Exec cp st env ss (.trap st')) :
    ∃ m, execB m cp st env ss = .trap st' := by
  obtain ⟨_, m, hm⟩ := h
  exact ⟨m + 1, by rw [execB, hm]⟩

end

end Ember.C.Sem
