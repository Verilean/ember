import Ember.C.Compile
import Ember.Proof.CFuel

/-!
# Ember.Proof.CVoid — `(void)x;` changes nothing (plan M5.8)

`C.voidUnread` puts `(void)v_x;` after the declaration of a local, so
that the C compiler does not report it as unused.  A statement list runs
the same with these statements in it.
-/

namespace Ember.C.Sem
open Ember.C

theorem exec_void' {cp : CProg} {st : St} {env : Env} (m : Nat) (e : CExpr) :
    execS (m + 1) cp st env (.expr (.cast .void e)) = .ok st env .normal := by
  simp only [execS, asCall]

/-- A declaration followed by `(void)x;`. -/
theorem exec_with_void {cp : CProg} {st : St} {env : Env} {s : CStmt} {m : Nat} {r : Res} (x : String)
    (h : execS m cp st env s = r) (hr : r.Done) : Exec cp st env [s, .expr (.cast .void (.var x))] r := by
  have h1 : Exec cp st env [s] r := Exec.one h hr
  cases r with
  | ok st' env' o =>
    cases o with
    | normal => exact h1.seq (Exec.one (exec_void' 0 _) trivial)
    | brk => exact h1.stop [_] trivial
    | ret v => exact h1.stop [_] trivial
  | trap st' => exact h1.stop [_] trivial
  | undef => exact h1.stop [_] trivial
  | fuel => exact hr.elim

theorem void_all (cp : CProg) (u : List String) : ∀ m : Nat,
    (∀ st env ss r, execB m cp st env ss = r → r.Done → ∃ m', execB m' cp st env (voidUnread u ss) = r) ∧
    (∀ st env ss r, execL m cp st env ss = r → r.Done → ∃ m', execL m' cp st env (voidUnread u ss) = r) ∧
    (∀ st env s r, execS m cp st env s = r → r.Done → Exec cp st env (voidUnreadS u s) r) ∧
    (∀ st env i hi body r, forC m cp st env i hi body = r → r.Done →
      ∃ m', forC m' cp st env i hi (voidUnread u body) = r)
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro st env ss r h hr; rw [execB] at h; exact (not_done_fuel h hr).elim
    · intro st env ss r h hr; rw [execL] at h; exact (not_done_fuel h hr).elim
    · intro st env s r h hr; rw [execS] at h; exact (not_done_fuel h hr).elim
    · intro st env i hi body r h hr; rw [forC] at h; exact (not_done_fuel h hr).elim
  | m + 1 => by
    obtain ⟨ihB, ihL, ihS, ihF⟩ := void_all cp u m
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro st env ss r h hr
      rw [execB] at h
      cases hL : execL m cp st env ss with
      | fuel => rw [hL] at h; exact (not_done_fuel h hr).elim
      | ok st1 env1 o1 =>
        obtain ⟨m', hm'⟩ := ihL _ _ _ _ hL trivial
        rw [hL] at h
        exact ⟨m' + 1, by rw [execB, hm']; exact h⟩
      | trap st1 =>
        obtain ⟨m', hm'⟩ := ihL _ _ _ _ hL trivial
        rw [hL] at h
        exact ⟨m' + 1, by rw [execB, hm']; exact h⟩
      | undef =>
        obtain ⟨m', hm'⟩ := ihL _ _ _ _ hL trivial
        rw [hL] at h
        exact ⟨m' + 1, by rw [execB, hm']; exact h⟩
    · intro st env ss r h hr
      cases ss with
      | nil => exact ⟨m + 1, by rw [voidUnread]; exact h⟩
      | cons s rest =>
        rw [execL] at h
        rw [voidUnread]
        cases hS : execS m cp st env s with
        | fuel => rw [hS] at h; exact (not_done_fuel h hr).elim
        | ok st1 env1 o1 =>
          rw [hS] at h
          obtain ⟨_, m1, h1⟩ := ihS _ _ _ _ hS trivial
          cases o1 with
          | normal =>
            obtain ⟨m2, h2⟩ := ihL _ _ _ _ h hr
            exact execL_seq _ h1 h2 hr
          | brk => subst h; exact ⟨m1, execL_stop _ h1 trivial⟩
          | ret v => subst h; exact ⟨m1, execL_stop _ h1 trivial⟩
        | trap st1 =>
          rw [hS] at h
          obtain ⟨_, m1, h1⟩ := ihS _ _ _ _ hS trivial
          subst h
          exact ⟨m1, execL_stop _ h1 trivial⟩
        | undef =>
          rw [hS] at h
          obtain ⟨_, m1, h1⟩ := ihS _ _ _ _ hS trivial
          subst h
          exact ⟨m1, execL_stop _ h1 trivial⟩
    · intro st env s r h hr
      cases s with
      | decl t x i =>
        rw [voidUnreadS]
        split
        · exact exec_with_void x h hr
        · exact Exec.one h hr
      | declZero t x =>
        rw [voidUnreadS]
        split
        · exact exec_with_void x h hr
        · exact Exec.one h hr
      | ite c t e =>
        rw [voidUnreadS]
        simp only [execS] at h
        cases hc : evalC cp st env c with
        | none =>
          simp only [hc] at h
          exact Exec.one (m := 1) (by simp only [execS, hc]; exact h) hr
        | some cv =>
          simp only [hc] at h
          cases htv : truthy cv with
          | none =>
            simp only [htv] at h
            exact Exec.one (m := 1) (by simp only [execS, hc, htv]; exact h) hr
          | some b =>
            simp only [htv] at h
            cases b with
            | true =>
              obtain ⟨m', hm'⟩ := ihB _ _ _ _ h hr
              exact Exec.one (m := m' + 1) (by simp only [execS, hc, htv]; exact hm') hr
            | false =>
              obtain ⟨m', hm'⟩ := ihB _ _ _ _ h hr
              exact Exec.one (m := m' + 1) (by simp only [execS, hc, htv]; exact hm') hr
      | forUp t i lo hi b =>
        rw [voidUnreadS]
        simp only [execS] at h
        cases hlo : evalC cp st env lo with
        | none =>
          simp only [hlo] at h
          exact Exec.one (m := 1) (by simp only [execS, hlo]; exact h) hr
        | some v =>
          simp only [hlo] at h
          cases hcv : convTo cp t v with
          | none =>
            simp only [hcv] at h
            exact Exec.one (m := 1) (by simp only [execS, hlo, hcv]; exact h) hr
          | some v' =>
            simp only [hcv] at h
            cases hF : forC m cp st ((i, v') :: env) i hi b with
            | fuel => simp only [hF] at h; exact (not_done_fuel h hr).elim
            | ok st1 env1 o1 =>
              obtain ⟨m', hm'⟩ := ihF _ _ _ _ _ _ hF trivial
              simp only [hF] at h
              exact Exec.one (m := m' + 1) (by simp only [execS, hlo, hcv, hm']; exact h) hr
            | trap st1 =>
              obtain ⟨m', hm'⟩ := ihF _ _ _ _ _ _ hF trivial
              simp only [hF] at h
              exact Exec.one (m := m' + 1) (by simp only [execS, hlo, hcv, hm']; exact h) hr
            | undef =>
              obtain ⟨m', hm'⟩ := ihF _ _ _ _ _ _ hF trivial
              simp only [hF] at h
              exact Exec.one (m := m' + 1) (by simp only [execS, hlo, hcv, hm']; exact h) hr
      | block b =>
        rw [voidUnreadS]
        simp only [execS] at h
        obtain ⟨m', hm'⟩ := ihB _ _ _ _ h hr
        exact Exec.one (m := m' + 1) (by simp only [execS]; exact hm') hr
      | assign l e => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
      | expr e => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
      | brk => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
      | ret e => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
      | line n f => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
      | comment c => rw [voidUnreadS] <;> first | exact Exec.one h hr | (intros; contradiction)
    · intro st env i hi body r h hr
      rw [forC] at h
      cases hl : env.lookup i with
      | none =>
        simp only [hl] at h
        exact ⟨1, by rw [forC]; simp only [hl]; exact h⟩
      | some iv =>
        cases hh : evalC cp st env hi with
        | none =>
          simp only [hl, hh] at h
          exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
        | some hv =>
          cases iv with
          | int b v =>
            cases hv with
            | int b' hval =>
              simp only [hl, hh] at h
              by_cases hlt : v < hval
              · simp only [hlt, if_true] at h
                cases hb : execB m cp st env body with
                | fuel => rw [hb] at h; exact (not_done_fuel h hr).elim
                | ok st' env' o =>
                  rw [hb] at h
                  obtain ⟨m1, h1⟩ := ihB _ _ _ _ hb trivial
                  cases o with
                  | normal =>
                    simp only at h
                    cases hl' : env'.lookup i with
                    | none =>
                      simp only [hl'] at h
                      exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1, hl']; exact h⟩
                    | some iv' =>
                      cases iv' with
                      | int b2 v2 =>
                        simp only [hl'] at h
                        obtain ⟨m2, h2⟩ := ihF _ _ _ _ _ _ h hr
                        refine ⟨max m1 m2 + 1, ?_⟩
                        rw [forC]
                        simp only [hl, hh, hlt, if_true, execB_le (Nat.le_max_left m1 m2) h1 trivial, hl']
                        exact forC_le (Nat.le_max_right m1 m2) h2 hr
                      | bool _ =>
                        simp only [hl'] at h
                        exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1, hl']; exact h⟩
                      | arr _ =>
                        simp only [hl'] at h
                        exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1, hl']; exact h⟩
                      | strct _ _ =>
                        simp only [hl'] at h
                        exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1, hl']; exact h⟩
                      | ptr _ =>
                        simp only [hl'] at h
                        exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1, hl']; exact h⟩
                  | brk => exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1]; exact h⟩
                  | ret v => exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1]; exact h⟩
                | trap st' =>
                  rw [hb] at h
                  obtain ⟨m1, h1⟩ := ihB _ _ _ _ hb trivial
                  exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1]; exact h⟩
                | undef =>
                  rw [hb] at h
                  obtain ⟨m1, h1⟩ := ihB _ _ _ _ hb trivial
                  exact ⟨m1 + 1, by rw [forC]; simp only [hl, hh, hlt, if_true, h1]; exact h⟩
              · simp only [hlt, if_false] at h
                exact ⟨1, by rw [forC]; simp only [hl, hh, hlt, if_false]; exact h⟩
            | bool _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
            | arr _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
            | strct _ _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
            | ptr _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
          | bool _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
          | arr _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
          | strct _ _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩
          | ptr _ => simp only [hl, hh] at h; exact ⟨1, by rw [forC]; simp only [hl, hh]; exact h⟩

/-- **`voidUnread` keeps what a statement list does.** -/
theorem Exec.void {cp : CProg} {st : St} {env : Env} {ss : List CStmt} {r : Res} (u : List String)
    (h : Exec cp st env ss r) : Exec cp st env (voidUnread u ss) r := by
  obtain ⟨hr, m, hm⟩ := h
  exact ⟨hr, (void_all cp u m).2.1 _ _ _ _ hm hr⟩

end Ember.C.Sem
