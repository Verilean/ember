import Ember.Z80.IRSem

/-!
# Ember.Proof.IRFuel — the IR's semantics without counting fuel (plan M7.1)

`IR.Sem.exec` runs on fuel.  More fuel does not change a result
(`exec_mono`, `callF_mono`), so the proofs speak of

* `Reach c f pc tmps st pc' tmps' st'`: whatever the function ends with
  from the second point, it ends with from the first — the first leads
  to the second;
* `Ends c f pc tmps st r`: from this point the function ends with `r`.

One lemma per kind of step (`Reach.next`, `Reach.goto`, `Reach.call`,
`Ends.stop`, …) is all that is needed of `exec` after this file.
-/

namespace Ember.Proof.IRSim
open Ember Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run

theorem exec_zero (c : Ctx) (f : Fn) (pc : Nat) (tmps : Array Nat) (st : St) : exec 0 c f pc tmps st = .fuel := by
  rw [exec]

theorem callF_zero (c : Ctx) (g : String) (st : St) : callF 0 c g st = .fuel := by rw [callF]

theorem exec_succ (k : Nat) (c : Ctx) (f : Fn) (pc : Nat) (tmps : Array Nat) (st : St) :
    exec (k + 1) c f pc tmps st =
      match f.body[pc]? with
      | none => .ok none st
      | some ins =>
        match step c st tmps ins with
        | .next st' tmps' => exec k c f (pc + 1) tmps' st'
        | .goto l =>
          match labelAt f l with
          | some i => exec k c f i tmps st
          | none => .bad
        | .call g st1 ret =>
          match callF k c g st1 with
          | .ok r st2 => exec k c f (pc + 1) (setRet c st2 tmps ret r).2 (setRet c st2 tmps ret r).1
          | .trap st2 => .trap st2
          | .fuel => .fuel
          | .bad => .bad
        | .stop r => r := by
  rw [exec]
  rfl

theorem callF_succ (k : Nat) (c : Ctx) (g : String) (st : St) :
    callF (k + 1) c g st =
      match c.prog.fn? g with
      | some f => exec k c f 0 (Array.replicate f.tmps.size 0) st
      | none => .bad := by
  rw [callF]
  rfl

/-- One more unit of fuel does not change a result. -/
theorem mono1 : ∀ k,
    (∀ c f pc tmps st, exec k c f pc tmps st ≠ .fuel → exec (k + 1) c f pc tmps st = exec k c f pc tmps st) ∧
    (∀ c g st, callF k c g st ≠ .fuel → callF (k + 1) c g st = callF k c g st)
  | 0 => ⟨fun c f pc tmps st h => absurd (exec_zero c f pc tmps st) h, fun c g st h => absurd (callF_zero c g st) h⟩
  | k + 1 => by
    obtain ⟨ihe, ihc⟩ := mono1 k
    refine ⟨fun c f pc tmps st h => ?_, fun c g st h => ?_⟩
    · rw [exec_succ k c f pc tmps st] at h ⊢
      rw [exec_succ (k + 1) c f pc tmps st]
      cases hb : f.body[pc]? with
      | none => rfl
      | some ins =>
        simp only [hb] at h ⊢
        cases hs : step c st tmps ins with
        | next st' tmps' =>
          simp only [hs] at h ⊢
          exact ihe _ _ _ _ _ h
        | goto l =>
          simp only [hs] at h ⊢
          cases hl : labelAt f l with
          | none => rfl
          | some i =>
            simp only [hl] at h ⊢
            exact ihe _ _ _ _ _ h
        | call g st1 ret =>
          simp only [hs] at h ⊢
          cases hc : callF k c g st1 with
          | fuel => simp [hc] at h
          | ok r st2 =>
            simp only [hc] at h
            rw [ihc c g st1 (by rw [hc]; simp), hc]
            exact ihe _ _ _ _ _ h
          | trap st2 => rw [ihc c g st1 (by rw [hc]; simp), hc]
          | bad => rw [ihc c g st1 (by rw [hc]; simp), hc]
        | stop r => rfl
    · rw [callF_succ k c g st] at h ⊢
      rw [callF_succ (k + 1) c g st]
      cases hf : c.prog.fn? g with
      | none => rfl
      | some f =>
        simp only [hf] at h ⊢
        exact ihe _ _ _ _ _ h

theorem exec_mono {k j : Nat} {c : Ctx} {f : Fn} {pc : Nat} {tmps : Array Nat} {st : St}
    (h : exec k c f pc tmps st ≠ .fuel) (hj : k ≤ j) : exec j c f pc tmps st = exec k c f pc tmps st := by
  induction hj with
  | refl => rfl
  | step _ ih => rw [(mono1 _).1 c f pc tmps st (by rw [ih]; exact h), ih]

theorem callF_mono {k j : Nat} {c : Ctx} {g : String} {st : St}
    (h : callF k c g st ≠ .fuel) (hj : k ≤ j) : callF j c g st = callF k c g st := by
  induction hj with
  | refl => rfl
  | step _ ih => rw [(mono1 _).2 c g st (by rw [ih]; exact h), ih]

/-- The first point leads to the second: whatever the function ends
with from the second, it ends with from the first. -/
def Reach (c : Ctx) (f : Fn) (pc : Nat) (tmps : Array Nat) (st : St) (pc' : Nat) (tmps' : Array Nat) (st' : St) :
    Prop :=
  ∀ n, exec n c f pc' tmps' st' ≠ .fuel → ∃ m, exec m c f pc tmps st = exec n c f pc' tmps' st'

/-- From this point the function ends with `r`. -/
def Ends (c : Ctx) (f : Fn) (pc : Nat) (tmps : Array Nat) (st : St) (r : Res) : Prop :=
  r ≠ .fuel ∧ ∃ m, exec m c f pc tmps st = r

section
variable {c : Ctx} {f : Fn} {pc pc' pc'' : Nat} {tmps tmps' tmps'' : Array Nat} {st st' st'' : St}

theorem Reach.refl : Reach c f pc tmps st pc tmps st := fun n _ => ⟨n, rfl⟩

theorem Reach.trans (h1 : Reach c f pc tmps st pc' tmps' st') (h2 : Reach c f pc' tmps' st' pc'' tmps'' st'') :
    Reach c f pc tmps st pc'' tmps'' st'' := fun n hn => by
  obtain ⟨m, hm⟩ := h2 n hn
  obtain ⟨m', hm'⟩ := h1 m (by rw [hm]; exact hn)
  exact ⟨m', by rw [hm', hm]⟩

theorem Reach.ends {r : Res} (h1 : Reach c f pc tmps st pc' tmps' st') (h2 : Ends c f pc' tmps' st' r) :
    Ends c f pc tmps st r := by
  obtain ⟨hr, m, hm⟩ := h2
  obtain ⟨m', hm'⟩ := h1 m (by rw [hm]; exact hr)
  exact ⟨hr, m', by rw [hm', hm]⟩

/-- An instruction that goes on to the next. -/
theorem Reach.next {ins : Instr} (hb : f.body[pc]? = some ins) (hs : step c st tmps ins = .next st' tmps') :
    Reach c f pc tmps st (pc + 1) tmps' st' := fun n _ =>
  ⟨n + 1, by rw [exec_succ]; simp only [hb, hs]⟩

/-- A jump taken. -/
theorem Reach.goto {ins : Instr} {l i : Nat} (hb : f.body[pc]? = some ins) (hs : step c st tmps ins = .goto l)
    (hl : labelAt f l = some i) : Reach c f pc tmps st i tmps st := fun n _ =>
  ⟨n + 1, by rw [exec_succ]; simp only [hb, hs, hl]⟩

/-- A call that returns. -/
theorem Reach.call {ins : Instr} {g : String} {st1 st2 : St} {ret : Option (Nat × Dst)} {r : Option Nat} {k : Nat}
    (hb : f.body[pc]? = some ins) (hs : step c st tmps ins = .call g st1 ret)
    (hc : callF k c g st1 = .ok r st2) :
    Reach c f pc tmps st (pc + 1) (setRet c st2 tmps ret r).2 (setRet c st2 tmps ret r).1 := fun n hn => by
  refine ⟨Nat.max n k + 1, ?_⟩
  rw [exec_succ]
  simp only [hb, hs]
  rw [callF_mono (by rw [hc]; simp) (Nat.le_max_right n k), hc]
  exact exec_mono hn (Nat.le_max_left n k)

/-- A call that traps. -/
theorem Ends.call_trap {ins : Instr} {g : String} {st1 st2 : St} {ret : Option (Nat × Dst)} {k : Nat}
    (hb : f.body[pc]? = some ins) (hs : step c st tmps ins = .call g st1 ret)
    (hc : callF k c g st1 = .trap st2) : Ends c f pc tmps st (.trap st2) :=
  ⟨by simp, k + 1, by rw [exec_succ]; simp only [hb, hs, hc]⟩

/-- An instruction that ends the function. -/
theorem Ends.stop {ins : Instr} {r : Res} (hb : f.body[pc]? = some ins) (hs : step c st tmps ins = .stop r)
    (hr : r ≠ .fuel) : Ends c f pc tmps st r :=
  ⟨hr, 1, by rw [exec_succ]; simp only [hb, hs]⟩

/-- A call from its first instruction. -/
theorem callF_of_ends {g : String} {r : Res} (hf : c.prog.fn? g = some f)
    (h : Ends c f 0 (Array.replicate f.tmps.size 0) st r) : ∃ m, callF m c g st = r := by
  obtain ⟨_, m, hm⟩ := h
  exact ⟨m + 1, by rw [callF_succ]; simp only [hf]; exact hm⟩

end

end Ember.Proof.IRSim
