import Ember.Lang.Sem

/-!
# Ember.Proof.SemTrapped — the Ember semantics records no trap (plan M7.3)

`World.trapped` says a trap was recorded: the harness of a machine sets
it when the program writes its trap port (`Z80HarnessW.hdev`).  Here:
the Ember semantics never sets it — statements, blocks, calls and the
effects leave it as it was (`execB_trapped`, `call_trapped`), whether
they end normally or in a trap of the language (`Res.trap`).
-/

namespace Ember.Lang.Sem
open Ember.Trace

theorem World.normalize_trapped : ∀ (n : Nat) (w : World), n = w.inputs.size - w.pos →
    w.normalize.trapped = w.trapped := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hn
    rw [World.normalize]
    by_cases hf : w.framed
    · simp only [hf, if_true]
    · simp only [hf, Bool.false_eq_true, if_false]
      by_cases h : w.pos < w.inputs.size
      · simp only [h, dite_true]
        split
        · split
          · rw [ih (w.inputs.size - (w.pos + 1)) (by omega) _ rfl]
          · rfl
        · rfl
      · simp only [h, dite_false]

theorem World.normalize_trapped' (w : World) : w.normalize.trapped = w.trapped :=
  World.normalize_trapped _ w rfl

theorem World.next_trapped (w : World) : w.next.2.trapped = w.trapped := by
  unfold World.next
  dsimp only
  split
  · split <;> simp only [World.normalize_trapped']
  · simp only [World.normalize_trapped']

theorem World.nextFramed_trapped (w : World) : w.nextFramed.2.trapped = w.trapped := by
  unfold World.nextFramed
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem effect_trapped (p : Prog) (st : St) (e : Effect) (vs : List Val) :
    (effect p st e vs).2.world.trapped = st.world.trapped := by
  cases e <;> simp only [effect, World.emit, World.next_trapped, World.nextFramed_trapped]

theorem update_world (p : Prog) (st : St) (env : Env) :
    ∀ (e : Expr) (f : Val → Option Val) (st' : St) (env' : Env),
      update p st env e f = some (st', env') → st'.world = st.world := by
  intro e
  induction e with
  | var x =>
    intro f st' env' h
    unfold update at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · split at h
      · split at h
        · cases h; rfl
        · cases h
      · cases h
  | field e fld ih =>
    intro f st' env' h
    unfold update at h
    exact ih _ _ _ h
  | index e i ih _ =>
    intro f st' env' h
    unfold update at h
    split at h
    · exact ih _ _ _ h
    · cases h
  | _ => intro f st' env' h; unfold update at h; cases h

theorem assign_world {p : Prog} {st : St} {env : Env} {l : Expr} {v : Val} {st' : St} {env' : Env}
    (h : assign p st env l v = some (st', env')) : st'.world = st.world :=
  update_world p st env l _ st' env' h

theorem copyBack_world (p : Prog) (callee : Env) :
    ∀ (ps : List Param) (as : List Expr) (st : St) (env : Env) (st' : St) (env' : Env),
      copyBack p callee ps as st env = some (st', env') → st'.world = st.world
  | prm :: ps, a :: as, st, env, st', env', h => by
    unfold copyBack at h
    split at h
    · split at h
      · split at h
        · rename_i st1 env1 h1
          rw [copyBack_world p callee ps as st1 env1 st' env' h, assign_world h1]
        · cases h
      · cases h
    · exact copyBack_world p callee ps as st env st' env' h
  | [], _, st, env, st', env', h => by unfold copyBack at h; cases h; rfl
  | _ :: _, [], st, env, st', env', h => by unfold copyBack at h; cases h; rfl

/-- How a statement ended keeps the flag off: normally or in a trap of
the language, the world's `trapped` is `false`. -/
def NoTrap : Res → Prop
  | .ok st _ _ => st.world.trapped = false
  | .trap st => st.world.trapped = false
  | .fuel => True

theorem storeResult_noTrap {p : Prog} {st : St} {env : Env} {dst : Option Expr} {r : Option Val}
    (h : st.world.trapped = false) : NoTrap (storeResult p st env dst r) := by
  unfold storeResult
  split
  · split
    · rename_i h1
      show _ = false
      rw [assign_world h1]; exact h
    · exact h
  · exact h

theorem exec_trapped : ∀ (n : Nat),
    (∀ p st env ss, st.world.trapped = false → NoTrap (execB n p st env ss)) ∧
    (∀ p st env ss, st.world.trapped = false → NoTrap (execL n p st env ss)) ∧
    (∀ p st env s, st.world.trapped = false → NoTrap (execS n p st env s)) ∧
    (∀ p st env x w cur hi body, st.world.trapped = false → NoTrap (forLoop n p st env x w cur hi body)) ∧
    (∀ p st env k body, st.world.trapped = false → NoTrap (loopN n p st env k body)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [execB, execL, execS, forLoop, loopN, NoTrap]
  | succ n ih =>
    obtain ⟨hB, hL, hS, hF, hN⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p st env ss h
      unfold execB
      have := hL p st env ss h
      split
      · rename_i heq; rw [heq] at this; exact this
      · exact this
    · intro p st env ss h
      cases ss with
      | nil => exact h
      | cons s rest =>
        unfold execL
        have := hS p st env s h
        split
        · rename_i heq; rw [heq] at this; exact hL p _ _ rest this
        · exact this
    · intro p st env s h
      unfold execS
      cases s with
      | «at» _ s => exact hS p st env s h
      | decl x ty init =>
        simp only
        split
        · split
          · exact h
          · exact h
        · exact h
      | assign l r =>
        simp only
        split
        · split
          · rename_i h1; show _ = false; rw [assign_world h1]; exact h
          · exact h
        · exact h
      | ite c t e =>
        simp only
        split
        · split
          · exact hB p st env t h
          · exact hB p st env e h
        · exact h
      | forRange x w lo hi body =>
        simp only
        split
        · rename_i _ _ a b _ _
          have := hF p st ((x, .int (w.getD .w32) (UInt64.ofNat a.toNat)) :: env) x (w.getD .w32) a.toNat b.toNat body h
          split
          · rename_i heq; rw [heq] at this; exact this
          · exact this
        · exact h
      | loop max body => exact hN p st env max body h
      | brk => exact h
      | ret e =>
        cases e with
        | none => exact h
        | some e =>
          simp only
          split
          · exact h
          · exact h
      | call dst f args =>
        simp only
        cases hfd : p.fn? f with
        | none => exact h
        | some fd =>
          simp only
          cases hvs : evalArgs p st env args with
          | none => exact h
          | some vs =>
            simp only
            have := hB p st ((fd.params.map (·.name)).zip vs) fd.body h
            split
            · rename_i st' cenv o heq
              rw [heq] at this
              split
              · rename_i st'' env'' h2
                apply storeResult_noTrap
                rw [copyBack_world p cenv _ _ _ _ _ _ h2]; exact this
              · exact this
            · exact this
      | eff dst e args =>
        simp only
        split
        · apply storeResult_noTrap
          rw [effect_trapped]; exact h
        · exact h
    · intro p st env x w cur hi body h
      unfold forLoop
      split
      · have := hB p st (setFirst env x (.int w (UInt64.ofNat cur))) body h
        split
        · rename_i heq; rw [heq] at this; exact hF p _ _ x w (cur + 1) hi body this
        · rename_i heq; rw [heq] at this; exact this
        · exact this
      · exact h
    · intro p st env k body h
      cases k with
      | zero => exact h
      | succ k =>
        unfold loopN
        have := hB p st env body h
        split
        · rename_i heq; rw [heq] at this; exact hN p _ _ k body this
        · rename_i heq; rw [heq] at this; exact this
        · exact this

/-- **A call of the Ember semantics records no trap**: when it returns,
the world's `trapped` is still `false`. -/
theorem call_trapped {fuel : Nat} {p : Prog} {st : St} {f : String} {args : List Val} {v : Option Val} {st' : St}
    (h : st.world.trapped = false) (hc : call fuel p st f args = .ok v st') : st'.world.trapped = false := by
  unfold call at hc
  split at hc
  · rename_i fd _
    have := (exec_trapped fuel).1 p st ((fd.params.map (·.name)).zip args) fd.body h
    split at hc
    · cases hc; rename_i heq; rw [heq] at this; exact this
    · cases hc; rename_i heq; rw [heq] at this; exact this
    · cases hc
    · cases hc
  · cases hc

theorem initial_trapped (p : Prog) (inputs : Array Input) : (initial p inputs).world.trapped = false := rfl

end Ember.Lang.Sem
