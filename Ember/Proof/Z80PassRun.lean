import Ember.Proof.Z80PassCtl

/-!
# Ember.Proof.Z80PassRun — two machines side by side, to the end (plan M7.3)

`sim_halts`: a relation between the states of two machines, kept by
segments of their runs — the first machine some steps (at least one),
the second some (maybe none) — and under which a halted first machine
means a halted second one with the same devices: then, when the first
machine halts, so does the second, its devices as the first left them.

What relation the images keep, and that their segments keep it, is in
the files that use this one.  A halted CPU stays halted and leaves the
devices alone (`mrun_halted`).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc

/-- A halted CPU stays halted, and the devices as they are. -/
theorem mstep_halted (D : Dev) (x : Cpu × D.W) (h : x.1.halted = true) :
    (mstep D x).1.halted = true ∧ (mstep D x).2 = x.2 := by
  obtain ⟨s, w⟩ := x
  have h' : s.halted = true := h
  have e : s.step (D.bus w) = (({ s with io := .none, eiDelay := false } : Cpu).bumpR).tick 4 := by
    simp only [Cpu.step, h', if_true]
  refine ⟨?_, ?_⟩
  · show (s.step (D.bus w)).halted = true
    rw [e]; exact h
  · show D.dev w (s.step (D.bus w)).io = w
    rw [e]; exact D.quiet w

theorem mrun_halted (D : Dev) : ∀ (n : Nat) (x : Cpu × D.W), x.1.halted = true →
    (mrun D n x).1.halted = true ∧ (mrun D n x).2 = x.2
  | 0, _, h => ⟨h, rfl⟩
  | n + 1, x, h => by
    obtain ⟨h1, h2⟩ := mstep_halted D x h
    obtain ⟨h3, h4⟩ := mrun_halted D n (mstep D x) h1
    exact ⟨h3, by rw [mrun, h4, h2]⟩

/-- **Two machines side by side, to the end.**  `R` relates a state of the first machine and one of
the second, both stepped in the same devices (`D`: the two images run in the same harness); from
related states, the first machine not halted, some steps of the first (at least one) and some of
the second lead to related states; related states with the first machine halted have the second
halted, with the same devices.  Then if the first machine halts after `N` steps, the second halts
after some number of steps, with the devices the first has then. -/
theorem sim_halts (D : Dev) (R : Cpu × D.W → Cpu × D.W → Prop)
    (seg : ∀ x y, R x y → x.1.halted = false → ∃ a b, 0 < a ∧ R (mrun D a x) (mrun D b y))
    (fin : ∀ x y, R x y → x.1.halted = true → y.1.halted = true ∧ y.2 = x.2) :
    ∀ (N : Nat) (x y : Cpu × D.W), R x y → (mrun D N x).1.halted = true →
      ∃ M, (mrun D M y).1.halted = true ∧ (mrun D M y).2 = (mrun D N x).2 := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro x y hR hN
    cases hx : x.1.halted with
    | true =>
      obtain ⟨hy, hw⟩ := fin x y hR hx
      obtain ⟨_, hNw⟩ := mrun_halted D N x hx
      exact ⟨0, hy, by rw [hNw]; exact hw⟩
    | false =>
      obtain ⟨a, b, ha, hR'⟩ := seg x y hR hx
      by_cases hle : a ≤ N
      · have e : mrun D N x = mrun D (N - a) (mrun D a x) := by
          rw [← mrun_add]; congr 1; omega
        rw [e] at hN ⊢
        obtain ⟨M, hM, hw⟩ := ih (N - a) (by omega) _ _ hR' hN
        refine ⟨b + M, ?_, ?_⟩
        · rw [mrun_add]; exact hM
        · rw [mrun_add]; exact hw
      · -- the first machine halted inside the segment and stayed halted
        have e : mrun D a x = mrun D (a - N) (mrun D N x) := by
          rw [← mrun_add]; congr 1; omega
        obtain ⟨ha1, ha2⟩ := mrun_halted D (a - N) _ hN
        rw [← e] at ha1 ha2
        obtain ⟨hy, hw⟩ := fin _ _ hR' ha1
        exact ⟨b, hy, by rw [hw, ha2]⟩

/-- info: 'Ember.Proof.PassSim.sim_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sim_halts

end Ember.Proof.PassSim
