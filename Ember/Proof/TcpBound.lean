import Ember.Proof.Stack

/-!
# Ember.Proof.TcpBound — the tick counters stay small

`idle` counts ticks up to `idleTicks`, `retries` retransmissions up to
`maxRetries`; both are natural numbers in the Spec and bytes in the
stack.  `Bnd` says they are within those limits; segment arrival and the
tick keep it, so it holds in every reachable state (`reach_bnd`) — which
is what `tick_step` needs (`idle < 255`, `retries < 255`).
-/

namespace Ember.Spec.Tcp
open Ember

/-- The tick counters are within their limits. -/
structure Bnd (t : Tcb) : Prop where
  idle : t.idle < idleTicks
  retries : t.retries ≤ maxRetries

theorem bnd_default : Bnd {} := by
  constructor <;> decide

theorem Bnd.frame {t t' : Tcb} (h : Bnd t) (e1 : t'.idle ≤ t.idle) (e2 : t'.retries ≤ t.retries) : Bnd t' :=
  ⟨Nat.lt_of_le_of_lt e1 h.idle, Nat.le_trans e2 h.retries⟩

/-- Prove `Bnd` of an explicitly updated control block. -/
macro "bnd_leaf" : tactic => `(tactic| (
  constructor <;> (try dsimp only [idleTicks, maxRetries] at *) <;>
    first
    | with_reducible assumption | omega | decide | assumption
    | exact (by decide : (0 : Nat) ≤ 8) | exact (by decide : (0 : Nat) < 60) | (simp_all; done)))

theorem output_bnd (a : Bool) (c : Ctx) (h : Bnd c.tcb) : wp (output a) (fun _ c' => Bnd c'.tcb) c := by
  obtain ⟨h1, h2⟩ := h
  wp_simp [output, wp_armTimer] <;> repeat' split
  all_goals bnd_leaf

theorem listenInput_bnd (src : UInt32) (s : Seg) (c : Ctx) (h : Bnd c.tcb) :
    wp (listenInput src s) (fun _ c' => Bnd c'.tcb) c := by
  wp_simp [listenInput, wp_sendSynAck, wp_sendReset]
  repeat' split
  all_goals first | exact h | bnd_leaf

theorem ackInput_bnd (s : Seg) (c : Ctx) (h : Bnd c.tcb) : wp (ackInput s) (fun _ c' => Bnd c'.tcb) c := by
  obtain ⟨h1, h2⟩ := h
  wp_simp [ackInput] <;> repeat' split
  all_goals bnd_leaf

theorem ackStep_bnd (src : UInt32) (s : Seg) (t : Tcb) (k : TcpM Unit)
    (hk : ∀ c, Bnd c.tcb → wp k (fun _ c' => Bnd c'.tcb) c) (c : Ctx) (h : Bnd c.tcb) :
    wp (ackStep src s t k) (fun _ c' => Bnd c'.tcb) c := by
  by_cases hsyn : t.st = .synRcvd
  · wp_simp [ackStep, hsyn, wp_sendReset]
    split
    · exact h
    · apply hk
      obtain ⟨h1, h2⟩ := h
      bnd_leaf
  · wp_simp [ackStep, hsyn]
    refine wp_mono (ackInput_bnd s c h) ?_
    intro b c' hc'
    cases b
    · exact hc'
    · exact hk c' hc'

theorem dataStep_bnd (s : Seg) (k : Bool → Bool → TcpM Unit)
    (hk : ∀ a i c, Bnd c.tcb → wp (k a i) (fun _ c' => Bnd c'.tcb) c) (c : Ctx) (h : Bnd c.tcb) :
    wp (dataStep s k) (fun _ c' => Bnd c'.tcb) c := by
  obtain ⟨h1, h2⟩ := h
  wp_simp [dataStep] <;> repeat' split
  all_goals first | apply hk | skip
  all_goals bnd_leaf

theorem finStep_bnd (s : Seg) (a i : Bool) (k : Bool → TcpM Unit)
    (hk : ∀ a c, Bnd c.tcb → wp (k a) (fun _ c' => Bnd c'.tcb) c) (c : Ctx) (h : Bnd c.tcb) :
    wp (finStep s a i k) (fun _ c' => Bnd c'.tcb) c := by
  obtain ⟨h1, h2⟩ := h
  wp_simp [finStep] <;> repeat' split
  all_goals first | apply hk | skip
  all_goals bnd_leaf

theorem connStep_bnd (src : UInt32) (s : Seg) (t : Tcb) (c : Ctx) (h : Bnd c.tcb) :
    wp (connStep src s t) (fun _ c' => Bnd c'.tcb) c := by
  wp_simp [connStep]
  repeat' split
  all_goals first | exact bnd_default | exact h | skip
  refine ackStep_bnd src s t _ (fun c hc => ?_) c h
  refine dataStep_bnd s _ (fun a i c hc => ?_) c hc
  refine finStep_bnd s a i _ (fun a c hc => ?_) c hc
  wp_simp [wp_pure]
  exact output_bnd a c hc

/-- The counters stay within their limits when a segment arrives. -/
theorem input_bnd (src : UInt32) (s : Seg) (c : Ctx) (h : Bnd c.tcb) : Bnd ((input src s).run c).2.tcb := by
  show wp (input src s) (fun _ c' => Bnd c'.tcb) c
  rw [input_eq]
  wp_simp [wp_sendReset, wp_sendSynAck]
  repeat' split
  all_goals first
    | exact h
    | exact listenInput_bnd src s c h
    | exact h.frame (Nat.zero_le _) (Nat.le_refl _)
    | skip
  exact connStep_bnd src s c.tcb _ (h.frame (Nat.zero_le _) (Nat.le_refl _))

/-- The counters stay within their limits over a tick. -/
theorem tick_bnd (c : Ctx) (h : Bnd c.tcb) : Bnd (tick.run c).2.tcb := by
  show wp tick (fun _ c' => Bnd c'.tcb) c
  obtain ⟨h1, h2⟩ := h
  cases hst : c.tcb.st <;> wp_simp [tick, rexmit, output, wp_armTimer, wp_sendSynAck, hst] <;> repeat' split
  all_goals first | exact bnd_default | bnd_leaf

end Ember.Spec.Tcp

namespace Ember.Spec
open Ember Ember.Trace

theorem step_bnd (s : State) (i : Input) (h : Tcp.Bnd s.tcb) : Tcp.Bnd (step s i).1.tcb :=
  step_preserves Tcp.input_bnd Tcp.tick_bnd s i h

/-- In every reachable state `idle < idleTicks` and `retries ≤ maxRetries`. -/
theorem reach_bnd (cfg : Config) (inputs : List Input) : Tcp.Bnd (reach cfg inputs).tcb :=
  reach_preserves Tcp.input_bnd Tcp.tick_bnd Tcp.bnd_default cfg inputs

/-- info: 'Ember.Spec.reach_bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reach_bnd

end Ember.Spec
