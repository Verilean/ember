import Ember.Spec.Stack
import Ember.Proof.Tcp

/-!
# Ember.Proof.Stack — TCP invariants over `Spec.step` (plan M5.3)

The control block of the stack state changes only where `runTcp` runs
`Tcp.input` or `Tcp.tick`; everything else `step` does (framing, IP,
ICMP, UDP, ARP, DHCP, sending) leaves it alone.  So a property of the
control block that segment arrival and the tick preserve is preserved by
`step` (`step_preserves`), and holds in every state the stack reaches
from `State.init` when it holds for the initial control block
(`reach_preserves`).  With `Tcp.Inv` that gives the invariants of
`Ember.Proof.Tcp` for the whole stack (`step_inv`, `reach_inv` and the
corollaries below).
-/

namespace Ember.Spec
open Ember Ember.Trace

/-- `m` keeps `P` of the stack state. -/
def Pres (P : State → Prop) (m : StackM α) : Prop := ∀ st, P st.1 → P (m.run st).2.1

namespace Pres
variable {P : State → Prop}

theorem pure (a : α) : Pres P (Pure.pure a : StackM α) := fun _ h => h

theorem bind {m : StackM α} {f : α → StackM β} (hm : Pres P m) (hf : ∀ a, Pres P (f a)) :
    Pres P (m >>= f) := fun st h => hf _ _ (hm st h)

theorem ev (e : Event) : Pres P (ev e) := fun _ h => h

theorem dropR (r : String) : Pres P (dropR r) := fun _ h => h

theorem getS : Pres P getS := fun _ h => h

theorem modifyS {f : State → State} (hf : ∀ s, P s → P (f s)) : Pres P (modifyS f) :=
  fun st h => hf st.1 h

/-- Like `bind` after `getS`, keeping the fact that the value read is the state. -/
theorem bind_getS {f : State → StackM β}
    (hf : ∀ st : State × Array Event, P st.1 → P ((f st.1).run st).2.1) : Pres P (Spec.getS >>= f) :=
  fun st h => hf st h

theorem forIn_list {γ β : Type} {l : List γ} {init : β} {f : γ → β → StackM (ForInStep β)}
    (hf : ∀ x b, Pres P (f x b)) : Pres P (forIn l init f) := by
  induction l generalizing init with
  | nil => exact pure _
  | cons x t ih =>
    rw [List.forIn_cons]
    refine bind (hf x init) fun r => ?_
    cases r
    · exact pure _
    · exact ih

theorem forIn_array {γ β : Type} {xs : Array γ} {init : β} {f : γ → β → StackM (ForInStep β)}
    (hf : ∀ x b, Pres P (f x b)) : Pres P (forIn xs init f) := by
  rw [← Array.forIn_toList]
  exact forIn_list hf

end Pres

/-- A call whose `Pres` lemma is already proved (rules are added below). -/
syntax "pres_call" : tactic

/-- Decompose a `Pres` goal along the structure of the action. -/
macro "pres" : tactic => `(tactic| repeat' (first
  | with_reducible exact Pres.pure _
  | with_reducible exact Pres.ev _
  | with_reducible exact Pres.dropR _
  | with_reducible exact Pres.getS
  | with_reducible exact Pres.modifyS (fun _ h => h)
  | with_reducible assumption
  | with_reducible pres_call
  | with_reducible refine Pres.bind ?_ (fun _ => ?_)
  | with_reducible refine Pres.forIn_list (fun _ _ => ?_)
  | with_reducible refine Pres.forIn_array (fun _ _ => ?_)
  | split
  | dsimp only))

section
variable {P : Tcp.Tcb → Prop}

theorem txFrame_pres (frame : ByteArray) : Pres (fun s => P s.tcb) (txFrame frame) := by
  unfold txFrame
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact txFrame_pres _)

theorem sendIp_pres (proto : UInt8) (dst : UInt32) (payload : ByteArray) :
    Pres (fun s => P s.tcb) (sendIp proto dst payload) := by
  unfold sendIp
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact sendIp_pres _ _ _)

/-- `runTcp` keeps a property of the control block that the TCP action keeps. -/
theorem runTcp_pres (act : Tcp.TcpM Unit) (hact : ∀ c : Tcp.Ctx, P c.tcb → P (act.run c).2.tcb) :
    Pres (fun s => P s.tcb) (runTcp act) := by
  unfold runTcp
  refine Pres.bind_getS fun st h => ?_
  have hc := hact { tcb := st.1.tcb, iss := st.1.iss, ourIp := st.1.ip, mss := mssFor st.1.cfg.mtu } h
  generalize StateT.run act
    { tcb := st.1.tcb, iss := st.1.iss, ourIp := st.1.ip, mss := mssFor st.1.cfg.mtu } = r at hc ⊢
  obtain ⟨u, c⟩ := r
  refine Pres.bind (P := fun s => P s.tcb) (Pres.modifyS fun _ _ => hc) (fun _ => ?_) st h
  pres

theorem dhcpApply_pres (o : Dhcp.Out) : Pres (fun s => P s.tcb) (dhcpApply o) := by
  unfold dhcpApply
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact dhcpApply_pres _)

theorem udpInput_pres (h : Ipv4.Hdr) (p : ByteArray) : Pres (fun s => P s.tcb) (udpInput h p) := by
  unfold udpInput
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact udpInput_pres _ _)

/-- `P` of the control block survives the arrival of any segment. -/
def KeepsInput (P : Tcp.Tcb → Prop) : Prop :=
  ∀ (src : UInt32) (s : Tcp.Seg) (c : Tcp.Ctx), P c.tcb → P ((Tcp.input src s).run c).2.tcb

/-- `P` of the control block survives a tick. -/
def KeepsTick (P : Tcp.Tcb → Prop) : Prop := ∀ c : Tcp.Ctx, P c.tcb → P (Tcp.tick.run c).2.tcb

theorem ipInput_pres (hin : KeepsInput P) (pkt : ByteArray) : Pres (fun s => P s.tcb) (ipInput pkt) := by
  have := fun src s => runTcp_pres (P := P) (Tcp.input src s) (hin src s)
  unfold ipInput
  pres
  all_goals exact this _ _

theorem ethInput_pres (hin : KeepsInput P) (f : ByteArray) : Pres (fun s => P s.tcb) (ethInput f) := by
  have := ipInput_pres hin
  unfold ethInput
  pres
  all_goals first | exact this _ | with_reducible exact Pres.modifyS (fun _ h => h)

theorem frameInput_pres (hin : KeepsInput P) (f : ByteArray) :
    Pres (fun s => P s.tcb) (frameInput f) := by
  have h1 := ipInput_pres hin
  have h2 := ethInput_pres hin
  unfold frameInput
  pres
  all_goals first | exact h1 _ | exact h2 _

theorem tickInput_pres (htick : KeepsTick P) : Pres (fun s => P s.tcb) tickInput := by
  have := runTcp_pres (P := P) Tcp.tick htick
  unfold tickInput
  pres

theorem tickArrives_pres (htick : KeepsTick P) : Pres (fun s => P s.tcb) tickArrives := by
  have h2 := tickInput_pres htick
  unfold tickArrives
  pres
  all_goals first | exact h2 | with_reducible exact Pres.modifyS (fun _ h => h)

theorem slipByte_pres (hin : KeepsInput P) (c : UInt8) : Pres (fun s => P s.tcb) (slipByte c) := by
  have h1 := frameInput_pres hin
  unfold slipByte
  pres
  all_goals first | exact h1 _ | with_reducible exact Pres.modifyS (fun _ h => h)

theorem byteInput_pres (hin : KeepsInput P) (htick : KeepsTick P) (c : UInt8) :
    Pres (fun s => P s.tcb) (byteInput c) := by
  have h1 := slipByte_pres hin
  have h2 := tickInput_pres htick
  unfold byteInput
  pres
  all_goals first | exact h1 _ | exact h2 | with_reducible exact Pres.modifyS (fun _ h => h)

theorem input_pres (hin : KeepsInput P) (htick : KeepsTick P) (i : Input) :
    Pres (fun s => P s.tcb) (input i) := by
  have h1 := frameInput_pres hin
  have h2 := byteInput_pres hin htick
  have h3 := tickArrives_pres htick
  cases i <;> unfold input
  · pres
    all_goals first | exact h1 _ | exact h2 _
  · exact h3

/-- M5.3, the induction step: a property of the control block that
segment arrival and the tick preserve is preserved by `step`. -/
theorem step_preserves (hin : KeepsInput P) (htick : KeepsTick P) (s : State) (i : Input)
    (h : P s.tcb) : P (step s i).1.tcb :=
  input_pres hin htick i (s, #[]) h

/-- The state the stack is in after a sequence of inputs (what `run` threads through). -/
def reach (cfg : Config) (inputs : List Input) : State :=
  inputs.foldl (fun s i => (step s i).1) (State.init cfg)

/-- M5.3, the induction: such a property, true of the initial control
block, holds in every state the stack reaches. -/
theorem reach_preserves (hin : KeepsInput P) (htick : KeepsTick P) (h0 : P {}) (cfg : Config)
    (inputs : List Input) : P (reach cfg inputs).tcb := by
  unfold reach
  have : ∀ (l : List Input) (s : State), P s.tcb → P (l.foldl (fun s i => (step s i).1) s).tcb := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons i t ih => exact fun s h => ih _ (step_preserves hin htick s i h)
  exact this inputs _ h0

end
end Ember.Spec

namespace Ember.Spec
open Ember Ember.Trace

/-! ## The invariants, for every reachable state -/

theorem step_inv (s : State) (i : Input) (h : Tcp.Inv s.tcb) : Tcp.Inv (step s i).1.tcb :=
  step_preserves Tcp.input_inv Tcp.tick_inv s i h

/-- `Tcp.Inv` holds in every state reached from `State.init`. -/
theorem reach_inv (cfg : Config) (inputs : List Input) : Tcp.Inv (reach cfg inputs).tcb :=
  reach_preserves Tcp.input_inv Tcp.tick_inv Tcp.inv_default cfg inputs

/-- M5.3: `snd.una ≤ snd.nxt` in every reachable state. -/
theorem reach_seqGe (cfg : Config) (inputs : List Input) :
    Tcp.seqGe (reach cfg inputs).tcb.sndNxt (reach cfg inputs).tcb.sndUna = true :=
  (reach_inv cfg inputs).seqGe

/-- M5.3: in every reachable state the application holds data only in
ESTABLISHED, CLOSE-WAIT or LAST-ACK. -/
theorem reach_holds (cfg : Config) (inputs : List Input)
    (h : 0 < (reach cfg inputs).tcb.pending.size) :
    (reach cfg inputs).tcb.st = .established ∨ (reach cfg inputs).tcb.st = .closeWait ∨
      (reach cfg inputs).tcb.st = .lastAck :=
  (reach_inv cfg inputs).holds h

/-- The echo buffer never exceeds its capacity, so the receive window
`cap − pending.size` never underflows. -/
theorem reach_pending_le (cfg : Config) (inputs : List Input) :
    (reach cfg inputs).tcb.pending.size ≤ (reach cfg inputs).tcb.cap :=
  (reach_inv cfg inputs).pendingCap

/-! ## Axioms -/

/-- info: 'Ember.Spec.step_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_preserves

/-- info: 'Ember.Spec.reach_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reach_inv

/-- info: 'Ember.Spec.reach_seqGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reach_seqGe

/-- info: 'Ember.Spec.reach_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reach_holds

end Ember.Spec
