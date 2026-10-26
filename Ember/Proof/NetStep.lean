import Ember.Proof.TcpRx

/-!
# Ember.Proof.NetStep — one input item through the stack, TCP included (plan M5.6)

The invariant `NetInv` relates the stack's globals to the Spec's stack
state: the SLIP decoder (`RxInv`), the TCP control block and counters
(`StRel`), the constants.  Then:

* `slip_rx_step`: **one received byte** — `slip_rx(c)` does not trap,
  keeps `NetInv` against the Spec's state after the same byte (`byteM`),
  and the two traces get the same transmissions and drops;
* `tick_step`: **one tick** — `tcp_tick()` likewise against
  `Spec.tickInput`.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## Constants -/

/-- The globals `slip_rx` and `tcp_tick` write; they leave all others alone. -/
def mutables : List String := ["t", "sg", "pend", "buf", "ip_id", "iss", "len", "esc", "over"]

/-- The globals the stack writes (`main` writes the last two); all others are constants. -/
def written : List String := mutables ++ ["booted", "tick_due"]

/-- `st'` has the globals of `st`, but for those in `xs`. -/
def SameOff (xs : List String) (st st' : St) : Prop := ∀ x, x ∉ xs → st'.globals.lookup x = st.globals.lookup x

/-- `st'` has the constants of `st`. -/
def SameConsts (st st' : St) : Prop := SameOff written st st'

theorem SameOff.consts {st st' : St} (h : SameOff mutables st st') : SameConsts st st' :=
  fun x hx => h x fun hm => hx (List.mem_append_left _ hm)

theorem SameConsts.refl (st : St) : SameConsts st st := fun _ _ => rfl

theorem SameConsts.trans {a b c : St} (h1 : SameConsts a b) (h2 : SameConsts b c) : SameConsts a c :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem tcpConsts_same {st st' : St} (h : TcpConsts st) (hs : SameConsts st st') : TcpConsts st' :=
  ⟨by rw [hs _ (by decide)]; exact h.MTU, by rw [hs _ (by decide)]; exact h.OUR_MSS, by rw [hs _ (by decide)]; exact h.ECHO_PORT, by rw [hs _ (by decide)]; exact h.TTL, by rw [hs _ (by decide)]; exact h.RTO_INIT, by rw [hs _ (by decide)]; exact h.RTO_MAX, by rw [hs _ (by decide)]; exact h.MAX_RETRIES, by rw [hs _ (by decide)]; exact h.TIME_WAIT_TICKS, by rw [hs _ (by decide)]; exact h.IDLE_TICKS, by rw [hs _ (by decide)]; exact h.ISS_INIT, by rw [hs _ (by decide)]; exact h.ISS_STEP, by rw [hs _ (by decide)]; exact h.LISTEN, by rw [hs _ (by decide)]; exact h.SYN_RCVD, by rw [hs _ (by decide)]; exact h.ESTABLISHED, by rw [hs _ (by decide)]; exact h.CLOSE_WAIT, by rw [hs _ (by decide)]; exact h.LAST_ACK, by rw [hs _ (by decide)]; exact h.FIN_WAIT_1, by rw [hs _ (by decide)]; exact h.FIN_WAIT_2, by rw [hs _ (by decide)]; exact h.CLOSING, by rw [hs _ (by decide)]; exact h.TIME_WAIT, by rw [hs _ (by decide)]; exact h.F_FIN, by rw [hs _ (by decide)]; exact h.F_SYN, by rw [hs _ (by decide)]; exact h.F_RST, by rw [hs _ (by decide)]; exact h.F_PSH, by rw [hs _ (by decide)]; exact h.F_ACK, by rw [hs _ (by decide)]; exact h.D_OVERSIZE, by rw [hs _ (by decide)]; exact h.D_SHORT_PACKET, by rw [hs _ (by decide)]; exact h.D_BAD_VERSION, by rw [hs _ (by decide)]; exact h.D_BAD_IHL, by rw [hs _ (by decide)]; exact h.D_BAD_IP_CHECKSUM, by rw [hs _ (by decide)]; exact h.D_BAD_LENGTH, by rw [hs _ (by decide)]; exact h.D_FRAGMENT, by rw [hs _ (by decide)]; exact h.D_TTL_ZERO, by rw [hs _ (by decide)]; exact h.D_NOT_FOR_US, by rw [hs _ (by decide)]; exact h.D_BROADCAST, by rw [hs _ (by decide)]; exact h.D_UNSUPPORTED_PROTOCOL, by rw [hs _ (by decide)]; exact h.D_SHORT_ICMP, by rw [hs _ (by decide)]; exact h.D_BAD_ICMP_CHECKSUM, by rw [hs _ (by decide)]; exact h.D_UNSUPPORTED_ICMP_TYPE, by rw [hs _ (by decide)]; exact h.D_SHORT_UDP, by rw [hs _ (by decide)]; exact h.D_BAD_UDP_LENGTH, by rw [hs _ (by decide)]; exact h.D_BAD_UDP_CHECKSUM, by rw [hs _ (by decide)]; exact h.D_UDP_PORT_CLOSED, by rw [hs _ (by decide)]; exact h.D_SHORT_TCP, by rw [hs _ (by decide)]; exact h.D_BAD_TCP_HEADER, by rw [hs _ (by decide)]; exact h.D_BAD_TCP_CHECKSUM, by rw [hs _ (by decide)]; exact h.D_TCP_PORT_CLOSED, by rw [hs _ (by decide)]; exact h.D_RST_NO_CONNECTION, by rw [hs _ (by decide)]; exact h.D_SECOND_CONNECTION, by rw [hs _ (by decide)]; exact h.D_RST_IN_LISTEN, by rw [hs _ (by decide)]; exact h.D_ACK_IN_LISTEN, by rw [hs _ (by decide)]; exact h.D_NO_SYN_IN_LISTEN, by rw [hs _ (by decide)]; exact h.D_RST_OUT_OF_WINDOW, by rw [hs _ (by decide)]; exact h.D_DUPLICATE_SYN, by rw [hs _ (by decide)]; exact h.D_OUT_OF_WINDOW, by rw [hs _ (by decide)]; exact h.D_SYN_IN_WINDOW, by rw [hs _ (by decide)]; exact h.D_NO_ACK, by rw [hs _ (by decide)]; exact h.D_BAD_ACK_SYN_RCVD, by rw [hs _ (by decide)]; exact h.D_ACK_OF_UNSENT, by rw [hs _ (by decide)]; exact h.D_OUT_OF_ORDER, by rw [hs _ (by decide)]; exact h.D_GIVE_UP, by rw [hs _ (by decide)]; exact h.D_FIN_WAIT_2_TIMEOUT⟩

theorem inConsts_same {st st' : St} {ourIp : UInt32} (h : InConsts st ourIp) (hs : SameConsts st st') :
    InConsts st' ourIp :=
  ⟨⟨by rw [hs _ (by decide)]; exact h.icmp.ourIp, by rw [hs _ (by decide)]; exact h.icmp.ttl, by rw [hs _ (by decide)]; exact h.icmp.d11, by rw [hs _ (by decide)]; exact h.icmp.d12, by rw [hs _ (by decide)]; exact h.icmp.d13⟩,
   ⟨by rw [hs _ (by decide)]; exact h.udp.ourIp, by rw [hs _ (by decide)]; exact h.udp.ttl, by rw [hs _ (by decide)]; exact h.udp.echo, by rw [hs _ (by decide)]; exact h.udp.d14, by rw [hs _ (by decide)]; exact h.udp.d15, by rw [hs _ (by decide)]; exact h.udp.d16, by rw [hs _ (by decide)]; exact h.udp.d17⟩,
   by rw [hs _ (by decide)]; exact h.d1, by rw [hs _ (by decide)]; exact h.d2, by rw [hs _ (by decide)]; exact h.d3, by rw [hs _ (by decide)]; exact h.d4, by rw [hs _ (by decide)]; exact h.d5, by rw [hs _ (by decide)]; exact h.d6, by rw [hs _ (by decide)]; exact h.d7, by rw [hs _ (by decide)]; exact h.d8, by rw [hs _ (by decide)]; exact h.d9, by rw [hs _ (by decide)]; exact h.d10⟩

/-! ## The invariant -/

/-- The TCP globals of `st` hold `w` (and nothing is pending in `w.evs`). -/
structure TcpHolds (st : St) (w : TW) : Prop where
  t : st.globals.lookup "t" = some w.r.val
  sg : st.globals.lookup "sg" = some w.sg.val
  pend : st.globals.lookup "pend" = some (bufVal w.pd)
  buf : st.globals.lookup "buf" = some (bufVal w.b)
  ip_id : st.globals.lookup "ip_id" = some (u16 w.id)
  iss : st.globals.lookup "iss" = some (u32 w.iss)
  evs : w.evs = []

theorem tcpSt_self {st : St} {w : TW} (h : TcpHolds st w) : tcpSt st w = st := by
  simp only [tcpSt, h.evs, List.foldl_nil]
  rw [show ({ st with world := st.world } : St) = st from rfl, setG_same _ _ _ h.t, setG_same _ _ _ h.sg,
    setG_same _ _ _ h.pend, setG_same _ _ _ h.buf, setG_same _ _ _ h.ip_id, setG_same _ _ _ h.iss]

theorem TcpHolds.base {st : St} {w : TW} (h : TcpHolds st w) (hf : st.world.frame = .empty) : TcpBase st :=
  ⟨⟨_, h.t⟩, ⟨_, h.sg⟩, ⟨_, h.pend⟩, ⟨_, h.buf⟩, ⟨_, h.ip_id⟩, ⟨_, h.iss⟩, hf⟩

/-- A state built by `tcpSt` holds its TCP state, once the pending trace lines are in the world. -/
theorem tcpHolds_tcpSt (st : St) (hB : TcpBase st) (w : TW) : TcpHolds (tcpSt st w) { w with evs := [] } :=
  ⟨lookup_tcpSt_t st hB w, lookup_tcpSt_sg st hB w, lookup_tcpSt_pend st hB w, lookup_tcpSt_buf st hB w,
    lookup_tcpSt_ip_id st hB w, lookup_tcpSt_iss st hB w, rfl⟩

/-- **The invariant of the stack between two input items**: the globals
hold the TCP state `w` and the SLIP decoder of the Spec's state `s`, the
control blocks agree, the constants have their values. -/
structure NetInv (st : St) (s : Spec.State) (w : TW) (mtu : UInt16) (ourIp : UInt32) (N : Nat) : Prop where
  holds : TcpHolds st w
  rel : StRel ourIp w s
  rx : RxInv st s.slip mtu w.id ourIp N
  consts : TcpConsts st
  ip : st.globals.lookup "OUR_IP" = some (u32 ourIp)
  n296 : 296 ≤ N
  mtu : mtu.toNat = s.cfg.mtu

/-! ## The Spec, one byte -/

/-- What `Spec.input (.rx bytes)` does with each byte on a SLIP link,
before the tick that may have waited: `Spec.slipByte`. -/
abbrev byteM (c : UInt8) : Spec.StackM Unit := Spec.slipByte c

theorem byteM_none (c : UInt8) (s : Spec.State) (es : Array Trace.Event)
    (h : (s.slip.feed c s.cfg.mtu).2 = .none) :
    ((byteM c).run (s, es)).2 = ({ s with slip := (s.slip.feed c s.cfg.mtu).1 }, es) := by
  unfold byteM Spec.slipByte
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  generalize hf : s.slip.feed c s.cfg.mtu = fr at h
  obtain ⟨d, r⟩ := fr
  simp only at h
  subst h
  rfl

theorem byteM_drop (c : UInt8) (s : Spec.State) (es : Array Trace.Event) (reason : String)
    (h : (s.slip.feed c s.cfg.mtu).2 = .drop reason) :
    ((byteM c).run (s, es)).2 = ({ s with slip := (s.slip.feed c s.cfg.mtu).1 }, es.push (.drop reason)) := by
  unfold byteM Spec.slipByte
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  generalize hf : s.slip.feed c s.cfg.mtu = fr at h
  obtain ⟨d, r⟩ := fr
  simp only at h
  subst h
  rfl

theorem byteM_frame (c : UInt8) (s : Spec.State) (es : Array Trace.Event) (f : ByteArray)
    (hslip : s.cfg.link = .slip) (h : (s.slip.feed c s.cfg.mtu).2 = .frame f) :
    ∃ t, ((byteM c).run (s, es)).2
      = ((Spec.ipInput f).run ({ s with slip := (s.slip.feed c s.cfg.mtu).1 }, es.push (.pkt t))).2 := by
  unfold byteM Spec.slipByte
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  generalize hf : s.slip.feed c s.cfg.mtu = fr at h
  obtain ⟨d, r⟩ := fr
  simp only at h
  subst h
  obtain ⟨cfg, sl, ipId, ip, tcb, iss, arp, dhcp⟩ := s
  obtain ⟨link, dh, cip, mac, mtu⟩ := cfg
  simp only at hslip
  subst hslip
  exact ⟨_, rfl⟩

/-- Only the byte END, on a decoder holding a frame that is not
oversize, completes a frame. -/
theorem feed_cases (d : Spec.Slip.Dec) (c : UInt8) (m : Nat) :
    (c = 192 ∧ d.over = false ∧ d.buf.size ≠ 0 ∧ d.feed c m = ({}, .frame d.buf)) ∨
    (¬ (c = 192 ∧ d.over = false ∧ d.buf.size ≠ 0) ∧
      ((d.feed c m).2 = .none ∨ ∃ reason, (d.feed c m).2 = .drop reason)) := by
  by_cases h1 : c = 192
  · subst h1
    have hfeed : Spec.Slip.Dec.feed d 192 m = (({} : Spec.Slip.Dec),
        if d.over then Spec.Slip.Result.drop "oversize-frame"
        else if d.buf.size == 0 then Spec.Slip.Result.none else Spec.Slip.Result.frame d.buf) := rfl
    rw [hfeed]
    cases hov : d.over
    · by_cases h0 : d.buf.size = 0
      · exact Or.inr ⟨fun q => q.2.2 h0, Or.inl (by simp [h0])⟩
      · exact Or.inl ⟨rfl, rfl, h0, by simp [h0]⟩
    · exact Or.inr ⟨fun q => by simp at q, Or.inr ⟨"oversize-frame", by simp⟩⟩
  · refine Or.inr ⟨fun q => h1 q.1, Or.inl ?_⟩
    have h1' : (c == Spec.Slip.END) = false := by simpa [Spec.Slip.END] using h1
    unfold Spec.Slip.Dec.feed
    rw [h1']
    simp only [Bool.false_eq_true, if_false]
    split
    · rfl
    · split <;> rfl

/-! ## One byte -/

theorem bufVal_inj {a b : ByteArray} (h : bufVal a = bufVal b) : a = b := by
  have hs := bufVal_size_eq h
  have h' : (a.data.map fun x => u8 x) = (b.data.map fun x => u8 x) := by
    simpa [bufVal] using h
  apply Bytes.ext_get hs
  intro i hi
  have e1 := bufVal_get a i hi
  have e2 := bufVal_get b i (hs ▸ hi)
  rw [h'] at e1
  have e3 : u8 (Bytes.get a i) = u8 (Bytes.get b i) := Option.some.inj (e1.symm.trans e2)
  have e4 : (Bytes.get a i).toUInt64 = (Bytes.get b i).toUInt64 := by
    simpa [u8] using e3
  apply UInt8.toNat_inj.mp
  have := congrArg UInt64.toNat e4
  simpa using this

theorem not_mem_mutables {x : String} (h : x ∉ mutables) :
    x ≠ "t" ∧ x ≠ "sg" ∧ x ≠ "pend" ∧ x ≠ "buf" ∧ x ≠ "ip_id" ∧ x ≠ "iss" ∧ x ≠ "len" ∧ x ≠ "esc" ∧ x ≠ "over" := by
  simp [mutables] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

/-- What `ip_input` leaves for a complete frame, against the Spec's state after the byte that completed it. -/
def FramePost (ourIp : UInt32) (st : St) (w : TW) (s : Spec.State) (es : Array Trace.Event) (c : UInt8)
    (st1 : St) : Prop :=
  ∃ w1 X, st1 = tcpSt st w1 ∧ w1.b.size = w.b.size ∧ StRel ourIp w1 ((byteM c).run (s, es)).2.1 ∧
    ((byteM c).run (s, es)).2.1.slip = {} ∧ ((byteM c).run (s, es)).2.1.cfg = s.cfg ∧
    ((byteM c).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X ∧ w1.evs.filter keep = X

/-- **One received byte.**  From `NetInv`, `slip_rx(c)` does not trap and
ends in a state that satisfies `NetInv` against the Spec's state after
the same byte; what the two add to their traces is the same
transmissions and drops (`X` are the lines the stack adds). -/
theorem slip_rx_step (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (s : Spec.State) (w : TW)
    (mtu : UInt16) (ourIp : UInt32) (N : Nat) (hinv : NetInv st s w mtu ourIp N) (c : UInt8)
    (es : Array Trace.Event) (n : Nat) :
    ∃ (st' : St) (w' : TW) (X : List Trace.Event),
      Sem.call (n + mtu.toNat + 4400) p st "slip_rx" [u8 c] = .ok none st' ∧
      NetInv st' ((byteM c).run (s, es)).2.1 w' mtu ourIp N ∧
      st'.world = X.foldl World.emit st.world ∧
      ((byteM c).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X.filter keep ∧
      SameOff mutables st st' := by
  obtain ⟨hh, hrel, hrx, hK, hip, h296, hmtu⟩ := hinv
  have hrx0 := hrx
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtuG, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hKin, hdo⟩ := hrx
  have hB : TcpBase st := hh.base hfr
  have hself := tcpSt_self hh
  have hbw : b = w.b := bufVal_inj (Option.some.inj (hbuf.symm.trans hh.buf))
  have hb0w : b0 = w.b := bufVal_inj (Option.some.inj (hb0.symm.trans hh.buf))
  subst hbw
  subst hb0w
  have hm := mtu.toNat_lt
  have hk : (UInt16.ofNat s.slip.buf.size).toNat = s.slip.buf.size := by
    rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨st', hcall, hpost⟩ := slip_rx_gen p hP.toTcpProg.toRxProg st s.slip mtu w.id ourIp N hrx0 c (n + 3800)
    (FramePost ourIp st w s es c) (by
      intro hc hov h0
      subst hc
      have hfeed : s.slip.feed 192 s.cfg.mtu = ({}, .frame s.slip.buf) := by
        rcases feed_cases s.slip 192 s.cfg.mtu with ⟨_, _, _, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd ⟨rfl, hov, h0⟩ h
      obtain ⟨t, hrun⟩ := byteM_frame 192 s es s.slip.buf hrel.slip (by rw [hfeed])
      rw [hfeed] at hrun
      have hrel1 : StRel ourIp w { s with slip := {} } :=
        ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩
      obtain ⟨w1, X, hc1, hbs, hr1, hsl, hcfg, hev, hwev⟩ := frame_refines p hP hR st hB hK ourIp hip w
        (by rw [hself]; exact hKin) { s with slip := {} } (es.push (.pkt t)) hrel1
        (UInt16.ofNat s.slip.buf.size) hlen (by rw [hk]; omega) (by omega) (by omega)
        (n + (mtu.toNat - s.slip.buf.size) + 684)
      rw [hself, hk] at hc1
      rw [hk, hpre] at hr1 hsl hcfg hev
      refine ⟨tcpSt st w1, ?_, ⟨w1, X, rfl, hbs, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [show n + 3800 + mtu.toNat + 584
          = n + (mtu.toNat - s.slip.buf.size) + 684 + s.slip.buf.size + 3700 by omega]
        exact hc1
      · rw [hrun]; exact hr1
      · rw [hrun]; exact hsl
      · rw [hrun]; exact hcfg
      · rw [hrun, hev]; simp [keep]
      · rw [hwev, hh.evs]; simp
      · exact ⟨_, by
          rw [lookup_tcpSt_ne st w1 "len" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hlen⟩
      · exact ⟨_, by
          rw [lookup_tcpSt_ne st w1 "esc" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hesc⟩
      · exact ⟨_, by
          rw [lookup_tcpSt_ne st w1 "over" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hover⟩)
  have hfuel : n + mtu.toNat + 4400 = n + 3800 + mtu.toNat + 600 := by omega
  rw [hmtu] at hpost
  rcases feed_cases s.slip c s.cfg.mtu with ⟨hc, hov, h0, hfeed⟩ | ⟨hnf, hres⟩
  · -- the byte completes a frame
    obtain ⟨st1, ⟨w1, X, hst1, hbs, hr1, hsl, hcfg, hev, hwev⟩, hst'⟩ := hpost.1 ⟨hc, hov, h0⟩
    subst hst1
    have lk : ∀ x, x ≠ "len" → x ≠ "esc" → x ≠ "over" →
        st'.globals.lookup x = (tcpSt st w1).globals.lookup x := by
      intro x a1 a2 a3
      rw [hst', lookup_setG_ne _ _ _ _ (Ne.symm a3), lookup_setG_ne _ _ _ _ (Ne.symm a2),
        lookup_setG_ne _ _ _ _ (Ne.symm a1)]
    have hsame9 : SameOff mutables st st' := by
      intro x hx
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := not_mem_mutables hx
      rw [lk x m7 m8 m9, lookup_tcpSt_ne st w1 x m1 m2 m3 m4 m5 m6]
    have hsame := hsame9.consts
    refine ⟨st', { w1 with evs := [] }, w1.evs, by rw [hfuel]; exact hcall, ?_, by rw [hst']; rfl,
      by rw [hev, hwev], hsame9⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, ⟨hr1.tcb, hr1.iss, hr1.id, hr1.ip, hr1.mss, hr1.slip, hr1.dhcp⟩, ?_,
      tcpConsts_same hK hsame, by rw [hsame "OUR_IP" (by decide)]; exact hip, h296, by rw [hcfg]; exact hmtu⟩
    · rw [lk "t" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_t st hB w1
    · rw [lk "sg" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_sg st hB w1
    · rw [lk "pend" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_pend st hB w1
    · rw [lk "buf" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_buf st hB w1
    · rw [lk "ip_id" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_ip_id st hB w1
    · rw [lk "iss" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_iss st hB w1
    · rw [hsl]
      have hl1 : (tcpSt st w1).globals.lookup "len" = some (u16 (UInt16.ofNat s.slip.buf.size)) := by
        rw [lookup_tcpSt_ne st w1 "len" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hlen
      have he1 : (tcpSt st w1).globals.lookup "esc" = some (.bool s.slip.esc) := by
        rw [lookup_tcpSt_ne st w1 "esc" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hesc
      have ho1 : (tcpSt st w1).globals.lookup "over" = some (.bool s.slip.over) := by
        rw [lookup_tcpSt_ne st w1 "over" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hover
      refine ⟨⟨w1.b, ?_, by omega, Nat.zero_le _, ?_, ?_, ?_, ?_, extract_empty w1.b 0⟩, ⟨w1.b, ?_, by omega⟩, hN', ?_,
        ?_, inConsts_same hKin hsame, by rw [hsame "D_OVERSIZE" (by decide)]; exact hdo⟩
      · rw [lk "buf" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_buf st hB w1
      · rw [hst', lookup_setG_ne _ "over" "len" _ (by decide), lookup_setG_ne _ "esc" "len" _ (by decide),
          lookup_setG _ _ _ _ hl1]
        rfl
      · rw [hst', lookup_setG_ne _ "over" "esc" _ (by decide),
          lookup_setG _ _ _ _ (by rw [lookup_setG_ne _ "len" "esc" _ (by decide)]; exact he1)]
      · rw [hst', lookup_setG _ _ _ _ (by
          rw [lookup_setG_ne _ "esc" "over" _ (by decide), lookup_setG_ne _ "len" "over" _ (by decide)]; exact ho1)]
      · rw [hsame "MTU" (by decide)]; exact hmtuG
      · rw [lk "buf" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_buf st hB w1
      · rw [hst']; exact frame_tcpSt st hB w1
      · rw [lk "ip_id" (by decide) (by decide) (by decide)]; exact lookup_tcpSt_ip_id st hB w1
  · -- any other byte
    obtain ⟨hrx', hworld, hsame4⟩ := hpost.2 hnf
    have hsame9 : SameOff mutables st st' := by
      intro x hx
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := not_mem_mutables hx
      exact hsame4 x m4 m7 m8 m9
    have hsame := hsame9.consts
    have hrx'' := hrx'
    obtain ⟨⟨b', hbuf', _⟩, _⟩ := hrx'
    have hholds : TcpHolds st' { w with b := b' } :=
      ⟨by rw [hsame4 "t" (by decide) (by decide) (by decide) (by decide)]; exact hh.t,
        by rw [hsame4 "sg" (by decide) (by decide) (by decide) (by decide)]; exact hh.sg,
        by rw [hsame4 "pend" (by decide) (by decide) (by decide) (by decide)]; exact hh.pend,
        hbuf',
        by rw [hsame4 "ip_id" (by decide) (by decide) (by decide) (by decide)]; exact hh.ip_id,
        by rw [hsame4 "iss" (by decide) (by decide) (by decide) (by decide)]; exact hh.iss, hh.evs⟩
    have hip' : st'.globals.lookup "OUR_IP" = some (u32 ourIp) := by
      rw [hsame "OUR_IP" (by decide)]; exact hip
    rcases hres with hnone | ⟨reason, hdrop⟩
    · have hS := byteM_none c s es hnone
      rw [hnone] at hrx'' hworld
      refine ⟨st', { w with b := b' }, [], by rw [hfuel]; exact hcall, ?_, hworld, by rw [hS]; simp, hsame9⟩
      rw [hS]
      exact ⟨hholds, ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩, hrx'',
        tcpConsts_same hK hsame, hip', h296, hmtu⟩
    · have hS := byteM_drop c s es reason hdrop
      rw [hdrop] at hrx'' hworld
      refine ⟨st', { w with b := b' }, [Trace.Event.drop reason], by rw [hfuel]; exact hcall, ?_, hworld,
        by rw [hS]; simp [keep], hsame9⟩
      rw [hS]
      exact ⟨hholds, ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩, hrx'',
        tcpConsts_same hK hsame, hip', h296, hmtu⟩

/-- info: 'Ember.Proof.Refine.slip_rx_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slip_rx_step

/-! ## One tick -/

theorem tickInput_run (s : Spec.State) (es : Array Trace.Event) (hslip : s.cfg.link = .slip)
    (hdhcp : s.cfg.dhcp = false) :
    ((Spec.tickInput).run (s, es)).2 = ((Spec.runTcp Spec.Tcp.tick).run (s, es)).2 := by
  obtain ⟨es', hrun, _⟩ := runTcp_keep Spec.Tcp.tick s es hslip
  have hfull : (Spec.runTcp Spec.Tcp.tick).run (s, es) = ((), ((Spec.runTcp Spec.Tcp.tick).run (s, es)).2) := rfl
  unfold Spec.tickInput
  rw [run_bind_eq _ _ _ _ _ hfull, hrun]
  have hg : ∀ (x : Spec.State) (y : Array Trace.Event), (Spec.getS).run (x, y) = (x, (x, y)) := fun _ _ => rfl
  rw [run_bind_eq _ _ _ _ _ (hg _ _)]
  simp only [hdhcp]
  rfl

theorem size_zero_eq_empty (b : ByteArray) (h : b.size = 0) : b = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero h

/-- **One tick**, between two frames.  From `NetInv` with no frame half
received, `tcp_tick()` does not trap and ends in a state that satisfies
`NetInv` against the Spec's state after `Spec.tickInput`; the same
transmissions and drops.

The hypothesis `s.slip.buf.size = 0` is needed: the stack builds what a
tick sends in the packet buffer, which also holds the frame being
received.  `main` therefore calls `tcp_tick()` only when `len = 0` and
lets a tick in the middle of a frame wait (`Spec.tickArrives`; see
`Proof/README.md` for the defect this proof found). -/
theorem tick_step (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (s : Spec.State) (w : TW)
    (mtu : UInt16) (ourIp : UInt32) (N : Nat) (hinv : NetInv st s w mtu ourIp N)
    (hI : Spec.Tcp.Inv s.tcb) (hidle : s.tcb.idle < 255) (hretr : s.tcb.retries < 255)
    (hempty : s.slip.buf.size = 0) (es : Array Trace.Event) (n : Nat) :
    ∃ (st' : St) (w' : TW) (X : List Trace.Event),
      Sem.call (n + 2000) p st "tcp_tick" [] = .ok none st' ∧
      NetInv st' ((Spec.tickInput).run (s, es)).2.1 w' mtu ourIp N ∧
      st'.world = X.foldl World.emit st.world ∧
      ((Spec.tickInput).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X.filter keep ∧
      SameOff mutables st st' := by
  obtain ⟨hh, hrel, hrx, hK, hip, h296, hmtu⟩ := hinv
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtuG, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hKin, hdo⟩ := hrx
  have hB : TcpBase st := hh.base hfr
  have hself := tcpSt_self hh
  have hbw : b = w.b := bufVal_inj (Option.some.inj (hbuf.symm.trans hh.buf))
  have hb0w : b0 = w.b := bufVal_inj (Option.some.inj (hb0.symm.trans hh.buf))
  subst hbw
  subst hb0w
  have hsim := hrel.sim
  rw [hh.evs] at hsim
  obtain ⟨w1, hcall, hbs, hs1⟩ := tcp_tick_refines p hP hR st hB hK ourIp hip w (ctxOf s) _ w.id hsim rfl hI hidle
    hretr (by omega) (by omega) n
  rw [hself] at hcall
  obtain ⟨es', hrun, hk⟩ := runTcp_keep Spec.Tcp.tick s es hrel.slip
  have hS := (tickInput_run s es hrel.slip hrel.dhcp).trans hrun
  have hsame9 : SameOff mutables st (tcpSt st w1) := by
    intro x hx
    obtain ⟨m1, m2, m3, m4, m5, m6, _, _, _⟩ := not_mem_mutables hx
    exact lookup_tcpSt_ne st w1 x m1 m2 m3 m4 m5 m6
  have hsame := hsame9.consts
  have lk : ∀ x, x ≠ "t" → x ≠ "sg" → x ≠ "pend" → x ≠ "buf" → x ≠ "ip_id" → x ≠ "iss" →
      (tcpSt st w1).globals.lookup x = st.globals.lookup x := fun x => lookup_tcpSt_ne st w1 x
  refine ⟨tcpSt st w1, { w1 with evs := [] }, w1.evs, hcall, ?_, rfl, ?_, hsame9⟩
  · rw [hS]
    refine ⟨tcpHolds_tcpSt st hB w1,
      ⟨hs1.tcb, hs1.iss, by show w1.id = _; rw [hs1.id, hrel.id], hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩, ?_,
      tcpConsts_same hK hsame, by rw [hsame "OUR_IP" (by decide)]; exact hip, h296, hmtu⟩
    refine ⟨⟨w1.b, lookup_tcpSt_buf st hB w1, by omega, hle, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨w1.b, lookup_tcpSt_buf st hB w1, by omega⟩, hN', frame_tcpSt st hB w1, lookup_tcpSt_ip_id st hB w1,
      inConsts_same hKin hsame, by rw [hsame "D_OVERSIZE" (by decide)]; exact hdo⟩
    · rw [lk "len" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlen
    · rw [lk "esc" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hesc
    · rw [lk "over" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hover
    · rw [lk "MTU" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmtuG
    · show w1.b.extract 0 s.slip.buf.size = s.slip.buf
      rw [hempty, size_zero_eq_empty _ hempty]
      exact extract_empty w1.b 0
  · rw [hS]
    show es'.toList.filter keep = _
    rw [hk, hs1.evs, hrel.ip, hrel.id]
    simp

/-- info: 'Ember.Proof.Refine.tick_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tick_step

end Ember.Proof.Refine
