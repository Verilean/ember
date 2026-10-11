import Ember.Proof.RefineIpInput
import Ember.Spec.Stack

/-!
# Ember.Proof.RefineRx — the receive path of the stack, byte by byte (plan M5.6, in part)

`slip_rx` is what the stack's `main` calls for every received byte.  The
theorem here puts the pieces of M5.5 together:

```
slip_rx_refines :  RxInv st d …  →  slip_rx(c) ends in st' with
                   RxInv st' (d.feed c).1 …  and
                   st'.world = st.world + rxOut … (d.feed c).2
```

— the globals follow the Spec's SLIP decoder (`Slip.Dec.feed`), and when
a frame is complete the trace gets what the Spec does with it:
`ipSpec`, which is `Spec.ipInput` with the `pkt` diagnostics left out
(`ipInput_obs` proves that against the Spec's own monadic definition).

Not here: TCP (a frame whose protocol field is 6 is excluded by
hypothesis), ticks, and the step from "every call of `slip_rx`" to the
trace `Sem.run` returns.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## What the Spec does with a frame, in observable terms -/

/-- The trace lines `Spec.ipInput` produces for the packet `f` that are
compared with an implementation (`drop` and `tx`; not the diagnostic
`pkt` lines), and the IP identification afterwards. -/
def ipSpec (id : UInt16) (ourIp : UInt32) (f : ByteArray) : List Trace.Event × UInt16 :=
  match Spec.Ipv4.validate f ourIp with
  | .error r => ([.drop r], id)
  | .ok (h, payload) =>
    if h.dst == Spec.Ipv4.broadcast && h.proto != 17 then ([.drop "broadcast"], id)
    else if h.proto = 1 then
      match Spec.Icmp.reply payload with
      | .error r => ([.drop r], id)
      | .ok m => ([.tx (Spec.Slip.encode (Spec.Ipv4.packet 1 id ourIp h.src m))], id + 1)
    else if h.proto = 17 then
      match Spec.Udp.parse h.src h.dst payload with
      | .error r => ([.drop r], id)
      | .ok dg =>
        if dg.dport = 7 then
          ([.tx (Spec.Slip.encode
            (Spec.Ipv4.packet 17 id ourIp h.src (Spec.Udp.emit ourIp h.src dg.dport dg.sport dg.data)))], id + 1)
        else ([.drop "udp-port-closed"], id)
    else ([.drop "unsupported-protocol"], id)

/-- The state after the receive path has handled a frame: the buffer
`B`, the identification `id`, the events appended. -/
def rxSt (st : St) (B : ByteArray) (id : UInt16) (evs : List Trace.Event) : St :=
  { stIp st B id with world := evs.foldl World.emit st.world }

theorem stIp_self (st : St) (b : ByteArray) (id : UInt16) (hb : st.globals.lookup "buf" = some (bufVal b))
    (hid : st.globals.lookup "ip_id" = some (u16 id)) : stIp st b id = st := by
  have e1 : setG st "ip_id" (u16 id) = st := setG_same st _ _ hid
  simp only [stIp, e1, setG_same st _ _ hb]

theorem stIp_buf (st : St) (B : ByteArray) (id : UInt16) (hid : st.globals.lookup "ip_id" = some (u16 id)) :
    stIp st B id = setG st "buf" (bufVal B) := by
  simp only [stIp, setG_same st _ _ hid]

theorem dropSt_eq (st : St) (B : ByteArray) (id : UInt16) (r : String) :
    dropSt (stIp st B id) r = rxSt st B id [.drop r] := rfl

theorem txOut_eq (st : St) (B : ByteArray) (id : UInt16) (f : ByteArray) (hfr : st.world.frame = .empty) :
    txOut (stIp st B id) (st.world.frame ++ f) = rxSt st B id [.tx f] := by
  have he : (ByteArray.empty ++ f) = f := by
    apply ByteArray.ext; simp [ByteArray.data_append]
  simp only [txOut, rxSt, hfr, he, List.foldl, World.emit]
  rfl

/-- **`ip_input`, summed up**: for a packet that is not TCP, the call
ends in the state with the Spec's events appended and the Spec's next
identification; the packet buffer keeps its size. -/
theorem ip_input_summary (p : Prog) (hP : InProg p) (st : St) (b : ByteArray) (L id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hlen : st.globals.lookup "len" = some (u16 L))
    (hid : st.globals.lookup "ip_id" = some (u16 id)) (ourIp : UInt32) (hK : InConsts st ourIp)
    (hL : L.toNat ≤ b.size) (hsz : b.size < 65536) (hntcp : 20 ≤ L.toNat → Bytes.get b 9 ≠ 6)
    (hfr : st.world.frame = .empty) (d : Nat) :
    ∃ B : ByteArray, B.size = b.size ∧
      Sem.call (d + L.toNat + 500) p st "ip_input" []
        = .ok none (rxSt st B (ipSpec id ourIp (b.extract 0 L.toNat)).2 (ipSpec id ourIp (b.extract 0 L.toNat)).1) := by
  obtain ⟨st', hc, hres⟩ := ip_input_refines p hP st b L id hb hlen hid ourIp hK hL hsz hntcp d
  rw [hc]
  have hself := stIp_self st b id hb hid
  have hdrop : ∀ (B : ByteArray) (r : String), dropSt (setG st "buf" (bufVal B)) r = rxSt st B id [.drop r] := by
    intro B r; rw [← stIp_buf st B id hid, dropSt_eq]
  unfold ipSpec
  cases hv : Spec.Ipv4.validate (b.extract 0 L.toNat) ourIp with
  | error r =>
    rw [hv] at hres
    simp only at hres
    refine ⟨b, rfl, ?_⟩
    rw [hres, ← dropSt_eq, hself]
  | ok hp =>
    obtain ⟨h, payload⟩ := hp
    rw [hv] at hres
    simp only [ipOutcome] at hres
    obtain ⟨B, hB, hres⟩ := hres
    simp only []
    by_cases c1 : (h.dst == Spec.Ipv4.broadcast && h.proto != 17) = true
    · rw [if_pos c1] at hres ⊢
      exact ⟨B, hB, by rw [hres, hdrop]⟩
    · rw [if_neg c1] at hres ⊢
      by_cases c2 : h.proto = 1
      · rw [if_pos c2] at hres ⊢
        cases hr : Spec.Icmp.reply payload with
        | error r =>
          rw [hr] at hres
          exact ⟨B, hB, by rw [hres, hdrop]⟩
        | ok m =>
          rw [hr] at hres
          obtain ⟨B', hB', hres⟩ := hres
          exact ⟨B', hB', by rw [hres, txOut_eq st B' _ _ hfr]⟩
      · rw [if_neg c2] at hres ⊢
        by_cases c3 : h.proto = 17
        · rw [if_pos c3] at hres ⊢
          cases hr : Spec.Udp.parse h.src h.dst payload with
          | error r =>
            rw [hr] at hres
            exact ⟨B, hB, by rw [hres, hdrop]⟩
          | ok dg =>
            rw [hr] at hres
            simp only [] at hres ⊢
            by_cases c4 : dg.dport = 7
            · rw [if_pos c4] at hres ⊢
              obtain ⟨B', hB', hres⟩ := hres
              exact ⟨B', hB', by rw [hres, txOut_eq st B' _ _ hfr]⟩
            · rw [if_neg c4] at hres ⊢
              exact ⟨B, hB, by rw [hres, hdrop]⟩
        · rw [if_neg c3] at hres ⊢
          exact ⟨B, hB, by rw [hres, hdrop]⟩

/-! ## `ipSpec` is `Spec.ipInput` -/

/-- The lines of a trace that are compared between implementations:
everything but the `pkt` diagnostics. -/
def obs (es : Array Trace.Event) : List Trace.Event :=
  es.toList.filter fun e => match e with | .pkt _ => false | _ => true

theorem obs_push_pkt (es : Array Trace.Event) (t : String) : obs (es.push (.pkt t)) = obs es := by
  simp [obs]

theorem obs_push_drop (es : Array Trace.Event) (r : String) : obs (es.push (.drop r)) = obs es ++ [.drop r] := by
  simp [obs]

theorem obs_push_tx (es : Array Trace.Event) (f : ByteArray) : obs (es.push (.tx f)) = obs es ++ [.tx f] := by
  simp [obs]

/-- **`ipSpec` is what `Spec.ipInput` does**, on a SLIP link without
DHCP and for a packet that is not TCP: run from the state `s` it appends
the lines `ipSpec` lists (and `pkt` diagnostics), and leaves `s` with the
identification `ipSpec` gives and nothing else changed. -/
theorem ipInput_obs (s : Spec.State) (es : Array Trace.Event) (f : ByteArray) (hslip : s.cfg.link = .slip)
    (hdhcp : s.cfg.dhcp = false)
    (hntcp : ∀ h pl, Spec.Ipv4.validate f s.ip = .ok (h, pl) → h.proto ≠ 6) :
    ∃ es', ((Spec.ipInput f).run (s, es)).2 = ({ s with ipId := (ipSpec s.ipId s.ip f).2 }, es') ∧
      obs es' = obs es ++ (ipSpec s.ipId s.ip f).1 := by
  generalize hR : ((Spec.ipInput f).run (s, es)).2 = R
  unfold ipSpec
  cases hv : Spec.Ipv4.validate f s.ip with
  | error r =>
    simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv] at hR
    subst hR
    exact ⟨_, rfl, obs_push_drop es r⟩
  | ok hp =>
    obtain ⟨h, payload⟩ := hp
    have hnt := hntcp h payload hv
    simp only []
    by_cases c1 : (h.dst == Spec.Ipv4.broadcast && h.proto != 17) = true
    · rw [if_pos c1]
      simp at c1
      simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, c1.1, c1.2] at hR
      subst hR
      exact ⟨_, rfl, obs_push_drop es _⟩
    · rw [if_neg c1]
      simp at c1
      by_cases c2 : h.proto = 1
      · rw [if_pos c2]
        have hd : ¬ h.dst = Spec.Ipv4.broadcast := by
          intro e
          have := c1 e
          rw [c2] at this
          exact absurd this (by decide)
        cases hr : Spec.Icmp.reply payload with
        | error r =>
          simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, hd, c2, hr] at hR
          subst hR
          exact ⟨_, rfl, obs_push_drop es _⟩
        | ok m =>
          simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, hd, c2, hr] at hR
          subst hR
          exact ⟨_, rfl, by simp [obs]⟩
      · rw [if_neg c2]
        by_cases c3 : h.proto = 17
        · rw [if_pos c3]
          cases hr : Spec.Udp.parse h.src h.dst payload with
          | error r =>
            simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, c3, hr] at hR
            subst hR
            exact ⟨_, rfl, obs_push_drop es _⟩
          | ok dg =>
            simp only []
            by_cases c4 : dg.dport = 7
            · rw [if_pos c4]
              simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, c3, hr, c4] at hR
              subst hR
              exact ⟨_, rfl, by simp [obs, c4]⟩
            · rw [if_neg c4]
              simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, c3, hr, c4] at hR
              subst hR
              exact ⟨_, rfl, obs_push_drop es _⟩
        · rw [if_neg c3]
          have hd : ¬ h.dst = Spec.Ipv4.broadcast := fun e => c3 (c1 e)
          simp [Spec.ipInput, Spec.udpInput, Spec.sendIp, Spec.txFrame, Spec.getS, Spec.modifyS, Spec.dropR, Spec.ev, StateT.run, bind, StateT.bind, Functor.map, StateT.map, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoUdp, Spec.Ipv4.protoTcp, Spec.echoPort, hslip, hdhcp, hv, hd, c2, c3, hnt] at hR
          subst hR
          exact ⟨_, rfl, obs_push_drop es _⟩

/-! ## The receive path of the stack: `slip_rx` -/

def slip_rx : Fn := checked_fn% Net.prog, "slip_rx"
#guard (Net.prog.check.toOption.bind (·.fn? "slip_rx")) == some slip_rx

/-- A program with the receive path (TCP apart). -/
structure RxProg (p : Prog) : Prop extends InProg p where
  slip_store : p.fn? "slip_store" = some slip_store
  slip_rx : p.fn? "slip_rx" = some slip_rx
  r0 : p.dropReasons[0]? = some "oversize-frame"

/-- The constants keep their values when only the receive path's
variables change. -/
theorem inConsts_of_same (st st' : St) (ourIp : UInt32) (h : InConsts st ourIp)
    (hs : ∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → x ≠ "ip_id" →
      st'.globals.lookup x = st.globals.lookup x) : InConsts st' ourIp :=
  ⟨⟨(by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.icmp.ourIp), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.icmp.ttl), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.icmp.d11), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.icmp.d12), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.icmp.d13)⟩,
   ⟨(by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.ourIp), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.ttl), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.echo), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.d14), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.d15), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.d16), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.udp.d17)⟩,
   (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d1), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d2), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d3), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d4), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d5), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d6), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d7), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d8), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d9), (by rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.d10)⟩

/-- What the Spec does with the result of feeding one byte to the
decoder: the trace lines, and the identification afterwards. -/
def rxOut (id : UInt16) (ourIp : UInt32) : Spec.Slip.Result → List Trace.Event × UInt16
  | .none => ([], id)
  | .drop r => ([.drop r], id)
  | .frame f => ipSpec id ourIp f

/-- The receive path's state between two bytes: the globals hold the
decoder state `d` and the identification `id`; the buffer has `N` bytes;
no frame is half transmitted. -/
def RxInv (st : St) (d : Spec.Slip.Dec) (mtu id : UInt16) (ourIp : UInt32) (N : Nat) : Prop :=
  SlipRel st d mtu ∧ BufSize st N ∧ N < 65536 ∧ st.world.frame = .empty ∧
    st.globals.lookup "ip_id" = some (u16 id) ∧ InConsts st ourIp ∧
    st.globals.lookup "D_OVERSIZE" = some (u8 0)

theorem foldl_emit_frame (evs : List Trace.Event) (w : World) : (evs.foldl World.emit w).frame = w.frame := by
  induction evs generalizing w with
  | nil => rfl
  | cons e t ih => rw [List.foldl_cons, ih]; rfl

@[simp] theorem globals_rxSt (st : St) (B : ByteArray) (id : UInt16) (evs : List Trace.Event) :
    (rxSt st B id evs).globals = (stIp st B id).globals := rfl

@[simp] theorem world_rxSt (st : St) (B : ByteArray) (id : UInt16) (evs : List Trace.Event) :
    (rxSt st B id evs).world = evs.foldl World.emit st.world := rfl

/-- After a frame has been handled: the receiver is reset. -/
theorem rx_reset (st : St) (d : Spec.Slip.Dec) (mtu id : UInt16) (ourIp : UInt32) (N : Nat)
    (hinv : RxInv st d mtu id ourIp N) (B : ByteArray) (hB : B.size = N) (id' : UInt16)
    (evs : List Trace.Event) :
    RxInv (setG (setG (setG (rxSt st B id' evs) "len" (.int .w16 0)) "esc" (.bool false)) "over" (.bool false))
      {} mtu id' ourIp N := by
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hK, hdo⟩ := hinv
  have hbb : b.size = N := by rw [← hN]; exact bufVal_size_eq (Option.some.inj (hbuf.symm.trans hb0))
  have lk : ∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → x ≠ "ip_id" →
      (setG (setG (setG (rxSt st B id' evs) "len" (.int .w16 0)) "esc" (.bool false)) "over"
        (.bool false)).globals.lookup x = st.globals.lookup x := by
    intro x h1 h2 h3 h4 h5
    rw [lookup_setG_ne _ _ _ _ (Ne.symm h4), lookup_setG_ne _ _ _ _ (Ne.symm h3),
      lookup_setG_ne _ _ _ _ (Ne.symm h2), globals_rxSt, stIp, lookup_setG_ne _ _ _ _ (Ne.symm h1),
      lookup_setG_ne _ _ _ _ (Ne.symm h5)]
  refine ⟨⟨B, ?_⟩, ⟨B, ?_, hB⟩, hN', ?_, ?_, inConsts_of_same st _ ourIp hK lk, ?_⟩
  · simp [stIp, lookup_setG_ne, lookup_setG_self, hbuf, hlen, hesc, hover, hmtu, hid]
    omega
  · simp [stIp, lookup_setG_ne, lookup_setG_self, hbuf, hid]
  · show (evs.foldl World.emit st.world).frame = _
    rw [foldl_emit_frame, hfr]
  · simp [stIp, lookup_setG_ne, lookup_setG_self, hbuf, hid]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hdo

theorem rxSt_self (st : St) (b : ByteArray) (id : UInt16) (evs : List Trace.Event)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id)) :
    rxSt st b id evs = { st with world := evs.foldl World.emit st.world } := by
  simp only [rxSt, stIp_self st b id hb hid]

/-- **One byte through the stack's receive path is one byte through the
Spec's**, for traffic that is not TCP.  `slip_rx(c)` takes the globals
from holding the decoder state `d` to holding `(d.feed c).1`; and for
what the decoder yields the trace gets the Spec's lines: nothing, the
drop of an oversize frame, or — for a complete frame — what
`Spec.ipInput` does with it (`ipSpec`: validation, ICMP echo, UDP echo,
with their drop reasons and their replies), the identification counter
moving as the Spec's does. -/
theorem slip_rx_refines (p : Prog) (hP : RxProg p) (st : St) (d : Spec.Slip.Dec) (mtu id : UInt16)
    (ourIp : UInt32) (N : Nat) (hinv : RxInv st d mtu id ourIp N) (c : UInt8)
    (hntcp : ∀ f, (d.feed c mtu.toNat).2 = .frame f → Bytes.get f 9 ≠ 6) (n : Nat) :
    ∃ st', Sem.call (n + mtu.toNat + 600) p st "slip_rx" [u8 c] = .ok none st' ∧
      RxInv st' (d.feed c mtu.toNat).1 mtu (rxOut id ourIp (d.feed c mtu.toNat).2).2 ourIp N ∧
      st'.world = (rxOut id ourIp (d.feed c mtu.toNat).2).1.foldl World.emit st.world := by
  have hinv0 := hinv
  have hrel := hinv.1
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hK, hdo⟩ := hinv
  have hbb : b.size = N := by rw [← hN]; exact bufVal_size_eq (Option.some.inj (hbuf.symm.trans hb0))
  have hm := mtu.toNat_lt
  have k192 : mask .w8 (UInt64.ofNat 192) = (192 : UInt8).toUInt64 := rfl
  have k219 : mask .w8 (UInt64.ofNat 219) = (219 : UInt8).toUInt64 := rfl
  have k220 : mask .w8 (UInt64.ofNat 220) = (220 : UInt8).toUInt64 := rfl
  have k221 : mask .w8 (UInt64.ofNat 221) = (221 : UInt8).toUInt64 := rfl
  have ecv : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
      evalE p st' [("c", u8 c)] (.bin .eq (.var "c") (.lit k (some .w8))) = some (.bool (c == kv)) := by
    intro st' k kv hk
    have e1 : evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, e1, Sem.binop, hk, toUInt64_eq_iff8]
  have hk : (UInt16.ofNat d.buf.size).toNat = d.buf.size := by
    rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Sem.call, hP.slip_rx, slip_rx, execB_succ, execL_cons, execS_at, execS_ite, List.map, List.zip,
    List.zipWith, ecv st 192 192 k192]
  by_cases h1 : c = 192
  · subst h1
    have hfeed : Spec.Slip.Dec.feed d 192 mtu.toNat = (({} : Spec.Slip.Dec),
        if d.over then Spec.Slip.Result.drop "oversize-frame"
        else if d.buf.size == 0 then Spec.Slip.Result.none else Spec.Slip.Result.frame d.buf) := rfl
    rw [hfeed] at hntcp ⊢
    cases hov : d.over with
    | true =>
      rw [hov] at hover
      have e := rx_reset st d mtu id ourIp N hinv0 b hbb id [.drop "oversize-frame"]
      rw [rxSt_self st b id _ hbuf hid] at e
      simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
        evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
        Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, hP.r0, rxOut]
      exact e
    | false =>
      rw [hov] at hover
      by_cases h0 : d.buf.size = 0
      · have hlen0 : st.globals.lookup "len" = some (u16 0) := by rw [hlen, h0]; rfl
        have e := rx_reset st d mtu id ourIp N hinv0 b hbb id []
        rw [rxSt_self st b id _ hbuf hid] at e
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen0, hdo, assign_var,
          Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, Sem.binop, h0, rxOut]
        exact e
      · have hpos : decide (0 < (UInt16.ofNat d.buf.size).toNat) = true := by simp [hk]; omega
        have hpos' : 0 < d.buf.size := by omega
        have hmod : d.buf.size % 65536 = d.buf.size := Nat.mod_eq_of_lt (by omega)
        have hnt : 20 ≤ (UInt16.ofNat d.buf.size).toNat → Bytes.get b 9 ≠ 6 := by
          intro h20
          rw [hk] at h20
          have h9 := hntcp d.buf (by simp [hov, h0])
          rw [← hpre, get_extract b 0 _ 9 (by omega) (by omega)] at h9
          exact h9
        obtain ⟨B, hBs, hc⟩ := ip_input_summary p hP.toInProg st b (UInt16.ofNat d.buf.size) id hbuf hlen hid
          ourIp hK (by omega) (by omega) hnt hfr (n + (mtu.toNat - d.buf.size) + 84)
        rw [show n + (mtu.toNat - d.buf.size) + 84 + (UInt16.ofNat d.buf.size).toNat + 500
          = n + mtu.toNat + 584 by omega, hk, hpre] at hc
        have hcall : execS (n + mtu.toNat + 585) p st [("c", u8 192)] (.call none "ip_input" [])
            = .ok (rxSt st B (ipSpec id ourIp d.buf).2 (ipSpec id ourIp d.buf).1) [("c", u8 192)] .normal :=
          execS_call_val p st _ (n + mtu.toNat + 584) none "ip_input" [] hP.ip_input
            (by simp [ip_input_fn]) (by simp [evalArgs]) hc
        have e := rx_reset st d mtu id ourIp N hinv0 B (by rw [hBs, hbb]) (ipSpec id ourIp d.buf).2
          (ipSpec id ourIp d.buf).1
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
          Val.toBool, lookup_setG_ne, lookup_setG_self, mask16_zero, Sem.binop,
          toUInt64_gt_zero, hpos, h0, hmod, hcall, hpos', rxOut, stIp, hid, hbuf]
        exact e
  · have h1' : (c == 192) = false := by simp [h1]
    have evc : ∀ st' : St, evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by
      intro st'; simp [evalE, lookup, List.lookup]
    have elit : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
        evalE p st' [("c", u8 c)] (.lit k (some .w8)) = some (u8 kv) := by
      intro st' k kv hk; rw [evalE_lit, hk]
    have eesc : evalE p st [("c", u8 c)] (.var "esc") = some (.bool d.esc) := by
      simp [evalE, lookup, List.lookup, hesc]
    -- every case that stores a byte ends the same way
    have fin : ∀ (st' : St) (v : UInt8), SlipRel st' (d.store v mtu.toNat) mtu → st'.world = st.world →
        (∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → SameG st st' x) →
        (∀ N, BufSize st N → BufSize st' N) →
        Spec.Slip.Dec.feed d c mtu.toNat = (d.store v mtu.toNat, .none) →
        RxInv st' (d.feed c mtu.toNat).1 mtu (rxOut id ourIp (d.feed c mtu.toNat).2).2 ourIp N ∧
          st'.world = (rxOut id ourIp (d.feed c mtu.toNat).2).1.foldl World.emit st.world := by
      intro st' v hr hw hs hbs hf
      rw [hf]
      refine ⟨⟨hr, hbs N ⟨b0, hb0, hN⟩, hN', by rw [hw]; exact hfr, ?_,
        inConsts_of_same st st' ourIp hK (fun x a1 a2 a3 a4 _ => hs x a1 a2 a3 a4), ?_⟩, by rw [hw]; rfl⟩
      · show st'.globals.lookup "ip_id" = some (u16 id)
        rw [hs "ip_id" (by decide) (by decide) (by decide) (by decide)]; exact hid
      · rw [hs "D_OVERSIZE" (by decide) (by decide) (by decide) (by decide)]; exact hdo
    simp only [Val.toBool, h1', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at,
      execS_ite, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, eesc]
    cases hde : d.esc with
    | true =>
      simp only [if_true, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, ecv st 220 220 k220, Val.toBool]
      by_cases h2 : c = 220
      · subst h2
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 220)] d mtu hrel _ 192
          (elit st 192 192 k192) (n + mtu.toNat + 588) (n + mtu.toNat + 575) (by omega)
        simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
        exact ⟨st', rfl, fin st' 192 hr hw hsm.1 hsm.2 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, hde])⟩
      · have h2' : (c == 220) = false := by simp [h2]
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
          ecv st 221 221 k221, Val.toBool]
        by_cases h3 : c = 221
        · subst h3
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 221)] d mtu hrel _ 219
            (elit st 219 219 k219) (n + mtu.toNat + 584) (n + mtu.toNat + 571) (by omega)
          simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
          exact ⟨st', rfl, fin st' 219 hr hw hsm.1 hsm.2 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde])⟩
        · have h3' : (c == 221) = false := by simp [h3]
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 c)] d mtu hrel _ c
            (evc st) (n + mtu.toNat + 584) (n + mtu.toNat + 571) (by omega)
          simp only [h3', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs,
            execS_ret_none]
          exact ⟨st', rfl, fin st' c hr hw hsm.1 hsm.2 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde,
              h1, h2, h3])⟩
    | false =>
      simp only [Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
        ecv st 219 219 k219, Val.toBool]
      by_cases h2 : c = 219
      · subst h2
        rw [hde] at hesc
        have hf : Spec.Slip.Dec.feed d 219 mtu.toNat = ({ d with esc := true }, .none) := by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde]
        rw [hf]
        have lk : ∀ x, x ≠ "esc" → (setG st "esc" (.bool true)).globals.lookup x = st.globals.lookup x :=
          fun x hx => lookup_setG_ne _ _ _ _ (Ne.symm hx)
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_assign, evalE, assign_var, List.lookup, hesc]
        refine ⟨⟨⟨b, ?_⟩, ⟨b0, by rw [lk _ (by decide)]; exact hb0, hN⟩, hN', hfr, ?_,
          inConsts_of_same st _ ourIp hK (fun x _ _ a3 _ _ => lk x a3), ?_⟩, rfl⟩
        · simp [lookup_setG_ne, lookup_setG_self, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre]
        · show (setG st "esc" (.bool true)).globals.lookup "ip_id" = _
          rw [lk _ (by decide)]; exact hid
        · rw [lk _ (by decide)]; exact hdo
      · have h2' : (c == 219) = false := by simp [h2]
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 c)] d mtu hrel _ c
          (evc st) (n + mtu.toNat + 591) (n + mtu.toNat + 578) (by omega)
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs]
        exact ⟨st', rfl, fin st' c hr hw hsm.1 hsm.2 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde, h1, h2])⟩

/-- What `slip_rx(c)` ends in, with the handling of a complete frame left
open (`Post`: what `ip_input` did): for a byte that completes a frame,
`ip_input` ran and the receiver was reset; for any other byte the
decoder moved on, the trace got what the Spec's decoder yields, and no
global but the receiver's changed. -/
def RxGenPost (Post : St → Prop) (st : St) (c : UInt8) (over : Bool) (sz : Nat) (d' : Spec.Slip.Dec)
    (r : Spec.Slip.Result) (mtu id : UInt16) (ourIp : UInt32) (N : Nat) (st' : St) : Prop :=
  ((c = 192 ∧ over = false ∧ sz ≠ 0) →
    ∃ st1, Post st1 ∧
      st' = setG (setG (setG st1 "len" (.int .w16 0)) "esc" (.bool false)) "over" (.bool false)) ∧
  (¬ (c = 192 ∧ over = false ∧ sz ≠ 0) →
    RxInv st' d' mtu (rxOut id ourIp r).2 ourIp N ∧ st'.world = (rxOut id ourIp r).1.foldl World.emit st.world ∧
      ∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → st'.globals.lookup x = st.globals.lookup x)

theorem rxGenPost_plain (Post : St → Prop) (st : St) (c : UInt8) (over : Bool) (sz : Nat) (d' : Spec.Slip.Dec)
    (r : Spec.Slip.Result) (mtu id : UInt16) (ourIp : UInt32) (N : Nat) (st' : St)
    (hc : ¬ (c = 192 ∧ over = false ∧ sz ≠ 0)) (h1 : RxInv st' d' mtu (rxOut id ourIp r).2 ourIp N)
    (h2 : st'.world = (rxOut id ourIp r).1.foldl World.emit st.world)
    (h3 : ∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → st'.globals.lookup x = st.globals.lookup x) :
    RxGenPost Post st c over sz d' r mtu id ourIp N st' :=
  ⟨fun q => absurd q hc, fun _ => ⟨h1, h2, h3⟩⟩

theorem rxGenPost_frame (Post : St → Prop) (st : St) (c : UInt8) (over : Bool) (sz : Nat) (d' : Spec.Slip.Dec)
    (r : Spec.Slip.Result) (mtu id : UInt16) (ourIp : UInt32) (N : Nat) (st' : St)
    (h1 : c = 192) (h2 : over = false) (h3 : sz ≠ 0) (st1 : St) (hp : Post st1)
    (he : st' = setG (setG (setG st1 "len" (.int .w16 0)) "esc" (.bool false)) "over" (.bool false)) :
    RxGenPost Post st c over sz d' r mtu id ourIp N st' :=
  ⟨fun _ => ⟨st1, hp, he⟩, fun q => absurd ⟨h1, h2, h3⟩ q⟩

/-- **`slip_rx(c)`, whatever `ip_input` does**: the receive path per
byte, with the handling of a complete frame as a parameter (`hIp`). -/
theorem slip_rx_gen (p : Prog) (hP : RxProg p) (st : St) (d : Spec.Slip.Dec) (mtu id : UInt16)
    (ourIp : UInt32) (N : Nat) (hinv : RxInv st d mtu id ourIp N) (c : UInt8) (n : Nat) (Post : St → Prop)
    (hIp : c = 192 → d.over = false → d.buf.size ≠ 0 →
      ∃ st1, Sem.call (n + mtu.toNat + 584) p st "ip_input" [] = .ok none st1 ∧ Post st1 ∧
        (∃ v, st1.globals.lookup "len" = some v) ∧ (∃ v, st1.globals.lookup "esc" = some v) ∧
        (∃ v, st1.globals.lookup "over" = some v)) :
    ∃ st', Sem.call (n + mtu.toNat + 600) p st "slip_rx" [u8 c] = .ok none st' ∧
      RxGenPost Post st c d.over d.buf.size (d.feed c mtu.toNat).1 (d.feed c mtu.toNat).2 mtu id ourIp N st' := by
  have hinv0 := hinv
  have hrel := hinv.1
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hK, hdo⟩ := hinv
  have hbb : b.size = N := by rw [← hN]; exact bufVal_size_eq (Option.some.inj (hbuf.symm.trans hb0))
  have hm := mtu.toNat_lt
  have k192 : mask .w8 (UInt64.ofNat 192) = (192 : UInt8).toUInt64 := rfl
  have k219 : mask .w8 (UInt64.ofNat 219) = (219 : UInt8).toUInt64 := rfl
  have k220 : mask .w8 (UInt64.ofNat 220) = (220 : UInt8).toUInt64 := rfl
  have k221 : mask .w8 (UInt64.ofNat 221) = (221 : UInt8).toUInt64 := rfl
  have ecv : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
      evalE p st' [("c", u8 c)] (.bin .eq (.var "c") (.lit k (some .w8))) = some (.bool (c == kv)) := by
    intro st' k kv hk
    have e1 : evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, e1, Sem.binop, hk, toUInt64_eq_iff8]
  have hk : (UInt16.ofNat d.buf.size).toNat = d.buf.size := by
    rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Sem.call, hP.slip_rx, slip_rx, execB_succ, execL_cons, execS_at, execS_ite, List.map, List.zip,
    List.zipWith, ecv st 192 192 k192]
  by_cases h1 : c = 192
  · subst h1
    have hfeed : Spec.Slip.Dec.feed d 192 mtu.toNat = (({} : Spec.Slip.Dec),
        if d.over then Spec.Slip.Result.drop "oversize-frame"
        else if d.buf.size == 0 then Spec.Slip.Result.none else Spec.Slip.Result.frame d.buf) := rfl
    rw [hfeed]
    cases hov : d.over with
    | true =>
      rw [hov] at hover
      have e := rx_reset st d mtu id ourIp N hinv0 b hbb id [.drop "oversize-frame"]
      rw [rxSt_self st b id _ hbuf hid] at e
      simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
        evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
        Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, hP.r0]
      exact rxGenPost_plain Post st _ _ _ _ _ mtu id ourIp N _ (by simp) e rfl (by
        intro x h1 h2 h3 h4
        rw [lookup_setG_ne _ _ _ _ (Ne.symm h4), lookup_setG_ne _ _ _ _ (Ne.symm h3),
          lookup_setG_ne _ _ _ _ (Ne.symm h2)])
    | false =>
      rw [hov] at hover
      by_cases h0 : d.buf.size = 0
      · have hlen0 : st.globals.lookup "len" = some (u16 0) := by rw [hlen, h0]; rfl
        have e := rx_reset st d mtu id ourIp N hinv0 b hbb id []
        rw [rxSt_self st b id _ hbuf hid] at e
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen0, hdo, assign_var,
          Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, Sem.binop, h0]
        exact rxGenPost_plain Post st _ _ _ _ _ mtu id ourIp N _ (by simp [h0]) e rfl (by
          intro x h1 h2 h3 h4
          rw [lookup_setG_ne _ _ _ _ (Ne.symm h4), lookup_setG_ne _ _ _ _ (Ne.symm h3),
            lookup_setG_ne _ _ _ _ (Ne.symm h2)])
      · have hpos : decide (0 < (UInt16.ofNat d.buf.size).toNat) = true := by simp [hk]; omega
        have hpos' : 0 < d.buf.size := by omega
        have hmod : d.buf.size % 65536 = d.buf.size := Nat.mod_eq_of_lt (by omega)
        obtain ⟨st1, hc, hpost, ⟨vl, hvl⟩, ⟨ve, hve⟩, ⟨vo, hvo⟩⟩ := hIp rfl hov h0
        have hcall : execS (n + mtu.toNat + 585) p st [("c", u8 192)] (.call none "ip_input" [])
            = .ok st1 [("c", u8 192)] .normal :=
          execS_call_val p st _ (n + mtu.toNat + 584) none "ip_input" [] hP.ip_input
            (by simp [ip_input_fn]) (by simp [evalArgs]) hc
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
          Val.toBool, lookup_setG_ne, lookup_setG_self, mask16_zero, Sem.binop,
          toUInt64_gt_zero, hpos, h0, hmod, hcall, hpos', hvl, hve, hvo]
        exact rxGenPost_frame Post st _ _ _ _ _ mtu id ourIp N _ rfl rfl h0 st1 hpost rfl
  · have h1' : (c == 192) = false := by simp [h1]
    have evc : ∀ st' : St, evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by
      intro st'; simp [evalE, lookup, List.lookup]
    have elit : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
        evalE p st' [("c", u8 c)] (.lit k (some .w8)) = some (u8 kv) := by
      intro st' k kv hk; rw [evalE_lit, hk]
    have eesc : evalE p st [("c", u8 c)] (.var "esc") = some (.bool d.esc) := by
      simp [evalE, lookup, List.lookup, hesc]
    -- every case that stores a byte ends the same way
    have fin : ∀ (st' : St) (v : UInt8), SlipRel st' (d.store v mtu.toNat) mtu → st'.world = st.world →
        (∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → SameG st st' x) →
        (∀ N, BufSize st N → BufSize st' N) →
        Spec.Slip.Dec.feed d c mtu.toNat = (d.store v mtu.toNat, .none) →
        RxGenPost Post st c d.over d.buf.size (d.feed c mtu.toNat).1 (d.feed c mtu.toNat).2 mtu id ourIp N
          st' := by
      intro st' v hr hw hs hbs hf
      rw [hf]
      refine rxGenPost_plain Post st _ _ _ _ _ mtu id ourIp N _ (fun q => h1 q.1) ?_ (by rw [hw]; rfl)
        (fun x a1 a2 a3 a4 => hs x a1 a2 a3 a4)
      refine ⟨hr, hbs N ⟨b0, hb0, hN⟩, hN', by rw [hw]; exact hfr, ?_,
        inConsts_of_same st st' ourIp hK (fun x a1 a2 a3 a4 _ => hs x a1 a2 a3 a4), ?_⟩
      · show st'.globals.lookup "ip_id" = some (u16 id)
        rw [hs "ip_id" (by decide) (by decide) (by decide) (by decide)]; exact hid
      · rw [hs "D_OVERSIZE" (by decide) (by decide) (by decide) (by decide)]; exact hdo
    simp only [Val.toBool, h1', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at,
      execS_ite, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, eesc]
    cases hde : d.esc with
    | true =>
      simp only [if_true, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, ecv st 220 220 k220, Val.toBool]
      by_cases h2 : c = 220
      · subst h2
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 220)] d mtu hrel _ 192
          (elit st 192 192 k192) (n + mtu.toNat + 588) (n + mtu.toNat + 575) (by omega)
        simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
        exact ⟨st', rfl, fin st' 192 hr hw hsm.1 hsm.2 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, hde])⟩
      · have h2' : (c == 220) = false := by simp [h2]
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
          ecv st 221 221 k221, Val.toBool]
        by_cases h3 : c = 221
        · subst h3
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 221)] d mtu hrel _ 219
            (elit st 219 219 k219) (n + mtu.toNat + 584) (n + mtu.toNat + 571) (by omega)
          simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
          exact ⟨st', rfl, fin st' 219 hr hw hsm.1 hsm.2 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde])⟩
        · have h3' : (c == 221) = false := by simp [h3]
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 c)] d mtu hrel _ c
            (evc st) (n + mtu.toNat + 584) (n + mtu.toNat + 571) (by omega)
          simp only [h3', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs,
            execS_ret_none]
          exact ⟨st', rfl, fin st' c hr hw hsm.1 hsm.2 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde,
              h1, h2, h3])⟩
    | false =>
      simp only [Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
        ecv st 219 219 k219, Val.toBool]
      by_cases h2 : c = 219
      · subst h2
        rw [hde] at hesc
        have hf : Spec.Slip.Dec.feed d 219 mtu.toNat = ({ d with esc := true }, .none) := by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde]
        rw [hf]
        have lk : ∀ x, x ≠ "esc" → (setG st "esc" (.bool true)).globals.lookup x = st.globals.lookup x :=
          fun x hx => lookup_setG_ne _ _ _ _ (Ne.symm hx)
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_assign, evalE, assign_var, List.lookup, hesc]
        refine rxGenPost_plain Post st _ _ _ _ _ mtu id ourIp N _ (fun q => h1 q.1) ?_ rfl
          (fun x _ _ a3 _ => lk x a3)
        refine ⟨⟨b, ?_⟩, ⟨b0, by rw [lk _ (by decide)]; exact hb0, hN⟩, hN', hfr, ?_,
          inConsts_of_same st _ ourIp hK (fun x _ _ a3 _ _ => lk x a3), ?_⟩
        · simp [lookup_setG_ne, lookup_setG_self, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre]
        · show (setG st "esc" (.bool true)).globals.lookup "ip_id" = _
          rw [lk _ (by decide)]; exact hid
        · rw [lk _ (by decide)]; exact hdo
      · have h2' : (c == 219) = false := by simp [h2]
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.slip_store st [("c", u8 c)] d mtu hrel _ c
          (evc st) (n + mtu.toNat + 591) (n + mtu.toNat + 578) (by omega)
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs]
        exact ⟨st', rfl, fin st' c hr hw hsm.1 hsm.2 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde, h1, h2])⟩

/-- The stack's initial state: the decoder's initial state, identification 1. -/
theorem rx_initial (inputs : Array Trace.Input) :
    RxInv (Sem.initial Net.prog inputs) {} 296 1 Spec.ourIpDefault 296 := by
  have hbufI : List.lookup "buf" (Sem.initial Net.prog inputs).globals
      = some (bufVal ⟨Array.replicate 296 0⟩) := by
    have hz : mask .w8 (UInt64.ofNat 0) = (0 : UInt8).toUInt64 := rfl
    have : List.lookup "buf" (Sem.initial Net.prog inputs).globals
        = some (.arr ((Array.range 296).map fun _ => Val.int .w8 (mask .w8 (UInt64.ofNat 0)))) := rfl
    rw [this, hz, bufVal]
    congr 2
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  have hsize : (ByteArray.mk (Array.replicate 296 0)).size = 296 := by simp [ByteArray.size]
  refine ⟨⟨⟨Array.replicate 296 0⟩, hbufI, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩, ⟨⟨Array.replicate 296 0⟩, hbufI, hsize⟩,
    by omega, rfl, rfl, net_consts_in inputs, rfl⟩
  · rw [hsize]; decide
  · show 0 ≤ 296
    omega
  · show (ByteArray.mk (Array.replicate 296 0)).extract 0 0 = ByteArray.empty
    apply eq_of_toList_eq
    rw [toList_extract _ _ (Nat.zero_le _)]
    simp [ByteArray.toList_empty]

-- the checked stack is an `RxProg` (with the `#guard`s at the functions)
#guard (Net.prog.check.toOption.bind (·.fn? "slip_store")) == some slip_store

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.slip_rx_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slip_rx_refines

/-- info: 'Ember.Proof.Refine.slip_rx_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slip_rx_gen

/-- info: 'Ember.Proof.Refine.rx_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rx_initial

/-- info: 'Ember.Proof.Refine.ipInput_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ipInput_obs

end Ember.Proof.Refine
