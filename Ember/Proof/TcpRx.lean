import Ember.Proof.TcpSimParse

/-!
# Ember.Proof.TcpRx — TCP inside the receive path (plan M5.6, in part)

`ip_input_refines_tcp` (`RefineIpInput.lean`) leaves open what the call
`tcp_input(src, dst, n)` does; `tcp_input_refines` says what it does.

* `ip_input_tcp`: `ip_input` on any packet, from a TCP state that agrees
  with the Spec's;
* `runTcp_keep`: what `Spec.runTcp` does with the result of a TCP action
  (the queued segments go out as IP packets, then the drops);
* `frame_refines`: **a frame through `ip_input` is a frame through
  `Spec.ipInput`**, every protocol: the stack's TCP state and the Spec's
  stack state agree before (`StRel`) and after, and the two traces get
  the same transmissions and drops.

Not here yet: the same per received byte (`slip_rx`), the tick, `main`.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-- What `ip_input` does with a TCP segment: the TCP state `w'` it ends
in is what `Spec.Tcp.parse` and `Spec.Tcp.input` give for the segment at
offset 20 of the buffer `B` (the packet with its IP options removed). -/
def tcpOutcome (st0 : St) (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (B : ByteArray) (src dst : UInt32) (n : UInt16) (st' : St) : Prop :=
  ∃ w', st' = tcpSt st0 w' ∧ w'.b.size = B.size ∧
    (∀ r, Spec.Tcp.parse src dst (B.extract 20 (20 + n.toNat)) = .error r → w' = dropW { w with b := B } r) ∧
    (∀ S, Spec.Tcp.parse src dst (B.extract 20 (20 + n.toNat)) = .ok S →
      Sim ourIp w' ((Spec.Tcp.input src S).run c).2 ev0 id0)

/-- **`ip_input` with TCP**: from the TCP state `w` that agrees with the
Spec's `c`, the packet `buf[0, len)` gets the drop line of the first IPv4
check that fails, or the Spec's ICMP or UDP handling, or — protocol 6 —
`Spec.Tcp.parse` and `Spec.Tcp.input` (`tcpOutcome`).  The call does not
trap. -/
theorem ip_input_tcp (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st0 : St) (hB : TcpBase st0)
    (hK : TcpConsts st0) (ourIp : UInt32) (hip : st0.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hKin : InConsts (tcpSt st0 w) ourIp) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (L : UInt16)
    (hlen : st0.globals.lookup "len" = some (u16 L)) (hL : L.toNat ≤ w.b.size) (hb296 : 296 ≤ w.b.size)
    (hb : w.b.size < 65536) (d : Nat) :
    ∃ st', Sem.call (d + L.toNat + 3700) p (tcpSt st0 w) "ip_input" [] = .ok none st' ∧
      match Spec.Ipv4.validate (w.b.extract 0 L.toNat) ourIp with
      | .error r => st' = dropSt (tcpSt st0 w) r
      | .ok (hh, payload) =>
        ipOutcomeT (tcpOutcome st0 ourIp w c ev0 id0) (tcpSt st0 w) st' w.b w.id ourIp hh payload := by
  have hlen' : (tcpSt st0 w).globals.lookup "len" = some (u16 L) := by
    rw [lookup_tcpSt_ne st0 w "len" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hlen
  have key := ip_input_refines_tcp p hP.toTcpProg.toRxProg.toInProg (tcpSt st0 w) w.b L w.id
    (lookup_tcpSt_buf st0 hB w) hlen' (lookup_tcpSt_ip_id st0 hB w) ourIp hKin hL hb (d + 3200)
    (tcpOutcome st0 ourIp w c ev0 id0) (by
      intro _ _ B env src dst n hBs hn hnL e1 e2 e3
      rw [setG_tcpSt_buf] at e1 e2 e3 ⊢
      obtain ⟨w', hcall, hbs, hr, hs⟩ := tcp_input_refines p hP hR st0 hB hK ourIp hip { w with b := B } c ev0 id0
        ⟨h.tcb, h.iss, h.ip, h.id, h.evs, h.mss⟩ hd src dst n hn (by show 296 ≤ B.size; omega)
        (by show B.size < 65536; omega) (d + L.toNat + 559 - n.toNat)
      refine ⟨tcpSt st0 w', ?_, w', rfl, hbs, hr, hs⟩
      rw [show d + 3200 + L.toNat + 460 = (d + L.toNat + 559 - n.toNat + n.toNat + 3100) + 1 by omega]
      rw [execS_call_val p _ env _ none "tcp_input" [.var "src", .var "dst", .var "n"] hP.tcp_input
        (by simp [tcp_input]) (by simp [evalArgs, e1, e2, e3]) hcall]
      rfl)
  rw [show d + 3200 + L.toNat + 500 = d + L.toNat + 3700 by omega] at key
  exact key

/-- info: 'Ember.Proof.Refine.ip_input_tcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ip_input_tcp

/-! ## What `Spec.runTcp` does with the result of a TCP action -/

/-- Running `m >>= f` in a state monad, given what `m` does. -/
theorem run_bind_eq {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β) (x : σ) (a : α) (x' : σ)
    (hm : m.run x = (a, x')) : (m >>= f).run x = (f a).run x' := by
  show (do let p ← m.run x; (f p.1).run p.2 : Id (β × σ)) = _
  rw [hm]
  rfl

theorem sendIp_run_slip (s : Spec.State) (es : Array Trace.Event) (proto : UInt8) (dst : UInt32)
    (payload : ByteArray) (hslip : s.cfg.link = .slip) :
    ∃ t, (Spec.sendIp proto dst payload).run (s, es)
      = ((), ({ s with ipId := s.ipId + 1 },
          (es.push (.pkt t)).push (.tx (Spec.Slip.encode (Spec.Ipv4.packet proto s.ipId s.ip dst payload))))) := by
  obtain ⟨cfg, sl, ipId, ip, tcb, iss, arp, dhcp⟩ := s
  obtain ⟨link, dh, cip, mac, mtu⟩ := cfg
  simp only at hslip
  subst hslip
  exact ⟨_, rfl⟩

theorem filter_keep_push_pkt_tx (es : Array Trace.Event) (t : String) (f : ByteArray) :
    ((es.push (.pkt t)).push (.tx f)).toList.filter keep = es.toList.filter keep ++ [.tx f] := by
  simp [keep]

/-- The segments a TCP action queued go out in order, each taking the next identification. -/
theorem sends_run (l : List (UInt32 × ByteArray)) : ∀ (s : Spec.State) (es : Array Trace.Event),
    s.cfg.link = .slip →
    ∃ es', (forIn (m := Spec.StackM) l PUnit.unit fun x _ => do
          Spec.sendIp Spec.Ipv4.protoTcp x.fst x.snd
          pure (ForInStep.yield PUnit.unit)).run (s, es)
        = (PUnit.unit, ({ s with ipId := s.ipId + UInt16.ofNat l.length }, es')) ∧
      es'.toList.filter keep = es.toList.filter keep ++ txEvs s.ip s.ipId l := by
  induction l with
  | nil =>
    intro s es _
    refine ⟨es, ?_, by simp [txEvs]⟩
    have : s.ipId + UInt16.ofNat 0 = s.ipId := by simp
    simp [this]
    rfl
  | cons x l ih =>
    intro s es hslip
    obtain ⟨dst, seg⟩ := x
    obtain ⟨t, ht⟩ := sendIp_run_slip s es Spec.Ipv4.protoTcp dst seg hslip
    obtain ⟨es', h1, h2⟩ := ih { s with ipId := s.ipId + 1 }
      ((es.push (.pkt t)).push (.tx (Spec.Slip.encode (Spec.Ipv4.packet Spec.Ipv4.protoTcp s.ipId s.ip dst seg))))
      hslip
    refine ⟨es', ?_, ?_⟩
    · rw [List.forIn_cons]
      have e : s.ipId + 1 + UInt16.ofNat l.length = s.ipId + UInt16.ofNat (l.length + 1) := by
        apply UInt16.toNat_inj.mp
        simp only [UInt16.toNat_add, UInt16.toNat_ofNat']
        have t1 : (1 : UInt16).toNat = 1 := rfl
        rw [t1]; omega
      have hstep : (do Spec.sendIp Spec.Ipv4.protoTcp dst seg; pure (ForInStep.yield PUnit.unit) :
          Spec.StackM (ForInStep PUnit)).run (s, es)
          = (ForInStep.yield PUnit.unit, ({ s with ipId := s.ipId + 1 },
              (es.push (.pkt t)).push
                (.tx (Spec.Slip.encode (Spec.Ipv4.packet Spec.Ipv4.protoTcp s.ipId s.ip dst seg))))) := by
        rw [run_bind_eq _ _ _ _ _ ht]; rfl
      rw [run_bind_eq _ _ _ _ _ hstep]
      refine h1.trans ?_
      show (PUnit.unit, ({ s with ipId := s.ipId + 1 + UInt16.ofNat l.length }, es')) = _
      rw [e]; rfl
    · rw [h2, filter_keep_push_pkt_tx, List.append_assoc]
      rfl

theorem diags_run (l : List Trace.Event) : ∀ (s : Spec.State) (es : Array Trace.Event),
    (forIn (m := Spec.StackM) l PUnit.unit fun d _ => do
          Spec.ev d
          pure (ForInStep.yield PUnit.unit)).run (s, es)
        = (PUnit.unit, (s, es ++ l.toArray)) := by
  induction l with
  | nil => intro s es; simp; rfl
  | cons d l ih =>
    intro s es
    rw [List.forIn_cons]
    have hstep : (do Spec.ev d; pure (ForInStep.yield PUnit.unit) : Spec.StackM (ForInStep PUnit)).run (s, es)
        = (ForInStep.yield PUnit.unit, (s, es.push d)) := rfl
    rw [run_bind_eq _ _ _ _ _ hstep]
    refine (ih s (es.push d)).trans ?_
    simp

/-- The TCP context `Spec.runTcp` builds from the stack state. -/
def ctxOf (s : Spec.State) : Spec.Tcp.Ctx :=
  { tcb := s.tcb, iss := s.iss, ourIp := s.ip, mss := Spec.mssFor s.cfg.mtu }

/-- **`Spec.runTcp`**, on a SLIP link: the control block and `iss` are
the action's, and the trace gets — among lines that are not compared —
the queued segments as IP packets and then the action's drops. -/
theorem runTcp_keep (act : Spec.Tcp.TcpM Unit) (s : Spec.State) (es : Array Trace.Event)
    (hslip : s.cfg.link = .slip) :
    ∃ es', ((Spec.runTcp act).run (s, es)).2
        = ({ s with tcb := (act.run (ctxOf s)).2.tcb, iss := (act.run (ctxOf s)).2.iss,
                    ipId := s.ipId + UInt16.ofNat (act.run (ctxOf s)).2.out.size }, es') ∧
      es'.toList.filter keep = es.toList.filter keep ++ txEvs s.ip s.ipId (act.run (ctxOf s)).2.out.toList
        ++ (act.run (ctxOf s)).2.diag.toList.filter keep := by
  have hc0 : (act.run { tcb := s.tcb, iss := s.iss, ourIp := s.ip, mss := Spec.mssFor s.cfg.mtu })
      = act.run (ctxOf s) := rfl
  generalize hc : act.run (ctxOf s) = rc at hc0
  clear hc
  have hc := hc0
  obtain ⟨u, c⟩ := rc
  obtain ⟨es1, h1, h2⟩ := sends_run c.out.toList { s with tcb := c.tcb, iss := c.iss } es hslip
  refine ⟨es1 ++ c.diag.toList.toArray, ?_, ?_⟩
  · unfold Spec.runTcp
    simp only [← Array.forIn_toList]
    have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
    rw [run_bind_eq _ _ _ _ _ hg, hc]
    have hm : (Spec.modifyS fun s => { s with tcb := c.tcb, iss := c.iss }).run (s, es)
        = ((), ({ s with tcb := c.tcb, iss := c.iss }, es)) := rfl
    show (((Spec.modifyS fun s => { s with tcb := c.tcb, iss := c.iss }) >>= fun _ => _).run (s, es)).2 = _
    rw [run_bind_eq _ _ _ _ _ hm, run_bind_eq _ _ _ _ _ h1, run_bind_eq _ _ _ _ _ (diags_run _ _ _)]
    simp only [Array.length_toList]
    rfl
  · simp only [Array.toList_append, List.filter_append, h2]

/-! ## `Spec.ipInput` on a TCP packet -/

theorem validate_ok_facts (f : ByteArray) (ip : UInt32) (h : Spec.Ipv4.Hdr) (pl : ByteArray)
    (hv : Spec.Ipv4.validate f ip = .ok (h, pl)) : 20 ≤ f.size ∧ h.proto = Bytes.get f 9 := by
  rw [validate_eq] at hv
  by_cases h20 : f.size < 20
  · rw [if_pos h20] at hv; cases hv
  · refine ⟨by omega, ?_⟩
    rw [if_neg h20] at hv
    repeat' (split at hv)
    all_goals first
      | (cases hv; rfl)
      | cases hv

theorem ipInput_err_run (s : Spec.State) (es : Array Trace.Event) (f : ByteArray) (r : String)
    (hv : Spec.Ipv4.validate f s.ip = .error r) :
    ((Spec.ipInput f).run (s, es)).2 = (s, es.push (.drop r)) := by
  unfold Spec.ipInput
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  simp only [hv]
  rfl

theorem ipInput_tcp_run (s : Spec.State) (es : Array Trace.Event) (f : ByteArray) (h : Spec.Ipv4.Hdr)
    (pl : ByteArray) (hv : Spec.Ipv4.validate f s.ip = .ok (h, pl)) (h6 : h.proto = 6) :
    ((Spec.ipInput f).run (s, es)).2 =
      if (h.dst == Spec.Ipv4.broadcast) = true then (s, es.push (.drop "broadcast"))
      else
        match Spec.Tcp.parse h.src h.dst pl with
        | .error r => (s, es.push (.drop r))
        | .ok S => ((Spec.runTcp (Spec.Tcp.input h.src S)).run (s, es)).2 := by
  unfold Spec.ipInput
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  simp only [hv, h6]
  by_cases hb : (h.dst == Spec.Ipv4.broadcast) = true
  · rw [if_pos hb]
    simp only [hb, Spec.Ipv4.protoUdp, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoTcp]
    rfl
  · rw [if_neg hb]
    have hb' : (h.dst == Spec.Ipv4.broadcast) = false := by simpa using hb
    simp only [hb', Spec.Ipv4.protoUdp, Spec.Ipv4.protoIcmp, Spec.Ipv4.protoTcp]
    cases Spec.Tcp.parse h.src h.dst pl <;> rfl

/-! ## A frame through `ip_input`, TCP included -/

theorem filter_keep_obs (es : Array Trace.Event) : (obs es).filter keep = es.toList.filter keep := by
  simp only [obs, List.filter_filter]
  congr 1
  funext e
  cases e <;> rfl

theorem rxSt_tcpSt (st0 : St) (w : TW) (B : ByteArray) (id : UInt16) (evs : List Trace.Event) :
    rxSt (tcpSt st0 w) B id evs = tcpSt st0 { w with b := B, id := id, evs := w.evs ++ evs } := by
  simp only [rxSt, stIp, setG_tcpSt_ip_id, setG_tcpSt_buf]
  simp only [tcpSt, setG, List.foldl_append]

/-- The TCP state of the stack and the Spec's stack state agree. -/
structure StRel (ourIp : UInt32) (w : TW) (s : Spec.State) : Prop where
  tcb : TcbRel w.r w.pd s.tcb
  iss : w.iss = s.iss
  id : w.id = s.ipId
  ip : s.ip = ourIp
  mss : Spec.mssFor s.cfg.mtu = 256
  slip : s.cfg.link = .slip
  dhcp : s.cfg.dhcp = false

theorem StRel.sim {ourIp : UInt32} {w : TW} {s : Spec.State} (h : StRel ourIp w s) :
    Sim ourIp w (ctxOf s) (w.evs.filter keep) w.id :=
  ⟨h.tcb, h.iss, h.ip, by show w.id = w.id + UInt16.ofNat 0; simp,
    by show _ = _ ++ [] ++ []; simp, h.mss⟩

/-- **A frame through `ip_input` is a frame through `Spec.ipInput`**,
TCP included: from states that agree, the call does not trap and ends in
states that agree; what the two add to their traces is the same
transmissions and drops (`X`). -/
theorem frame_refines (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st0 : St) (hB : TcpBase st0)
    (hK : TcpConsts st0) (ourIp : UInt32) (hip : st0.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hKin : InConsts (tcpSt st0 w) ourIp) (s : Spec.State) (es : Array Trace.Event) (hrel : StRel ourIp w s)
    (L : UInt16) (hlen : st0.globals.lookup "len" = some (u16 L)) (hL : L.toNat ≤ w.b.size)
    (hb296 : 296 ≤ w.b.size) (hb : w.b.size < 65536) (d : Nat) :
    ∃ w' X, Sem.call (d + L.toNat + 3700) p (tcpSt st0 w) "ip_input" [] = .ok none (tcpSt st0 w') ∧
      w'.b.size = w.b.size ∧
      StRel ourIp w' ((Spec.ipInput (w.b.extract 0 L.toNat)).run (s, es)).2.1 ∧
      ((Spec.ipInput (w.b.extract 0 L.toNat)).run (s, es)).2.1.slip = s.slip ∧
      ((Spec.ipInput (w.b.extract 0 L.toNat)).run (s, es)).2.1.cfg = s.cfg ∧
      ((Spec.ipInput (w.b.extract 0 L.toNat)).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X ∧
      w'.evs.filter keep = w.evs.filter keep ++ X := by
  have hlen' : (tcpSt st0 w).globals.lookup "len" = some (u16 L) := by
    rw [lookup_tcpSt_ne st0 w "len" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hlen
  have hfsz : (w.b.extract 0 L.toNat).size = L.toNat := by rw [ByteArray.size_extract]; omega
  by_cases htcp : 20 ≤ L.toNat ∧ Bytes.get w.b 9 = 6
  · -- a TCP packet
    obtain ⟨st', hcall, hres⟩ := ip_input_tcp p hP hR st0 hB hK ourIp hip w hKin (ctxOf s) (w.evs.filter keep) w.id
      hrel.sim rfl L hlen hL hb296 hb d
    cases hv : Spec.Ipv4.validate (w.b.extract 0 L.toNat) ourIp with
    | error r =>
      rw [hv] at hres
      simp only at hres
      subst hres
      rw [dropSt_tcpSt] at hcall
      have hS := ipInput_err_run s es (w.b.extract 0 L.toNat) r (by rw [hrel.ip]; exact hv)
      refine ⟨_, [.drop r], hcall, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hS]; exact ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩
      · rw [hS]
      · rw [hS]
      · rw [hS]; simp [keep]
      · simp [keep]
    | ok hp =>
      obtain ⟨h, pl⟩ := hp
      rw [hv] at hres
      simp only at hres
      obtain ⟨B, hBs, ho⟩ := hres
      obtain ⟨hsz20, hproto⟩ := validate_ok_facts _ _ _ _ hv
      have h6 : h.proto = 6 := by
        rw [hproto, get_extract w.b 0 _ 9 (by omega) hL, Nat.zero_add]; exact htcp.2
      have hS := ipInput_tcp_run s es (w.b.extract 0 L.toNat) h pl (by rw [hrel.ip]; exact hv) h6
      by_cases c1 : (h.dst == Spec.Ipv4.broadcast && h.proto != 17) = true
      · rw [if_pos c1] at ho
        have hbc : (h.dst == Spec.Ipv4.broadcast) = true := ((Bool.and_eq_true _ _).mp c1).1
        rw [if_pos hbc] at hS
        subst ho
        rw [setG_tcpSt_buf, dropSt_tcpSt] at hcall
        refine ⟨_, [.drop "broadcast"], hcall, hBs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hS]; exact ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩
        · rw [hS]
        · rw [hS]
        · rw [hS]; simp [keep]
        · simp [keep]
      · rw [if_neg c1, if_neg (by rw [h6]; decide), if_neg (by rw [h6]; decide), if_pos h6] at ho
        obtain ⟨n, hpl, hn, w', hst', hbs', herr, hok⟩ := ho
        have hbc : ¬ (h.dst == Spec.Ipv4.broadcast) = true := by
          intro q; apply c1; rw [q, h6]; rfl
        rw [if_neg hbc] at hS
        subst hst'
        rw [← hpl] at herr hok
        cases hp : Spec.Tcp.parse h.src h.dst pl with
        | error r =>
          rw [hp] at hS
          have hw' := herr r hp
          subst hw'
          refine ⟨_, [.drop r], hcall, hBs, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hS]; exact ⟨hrel.tcb, hrel.iss, hrel.id, hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩
          · rw [hS]
          · rw [hS]
          · rw [hS]; simp [keep]
          · simp [keep, dropW]
        | ok S =>
          rw [hp] at hS
          replace hS : ((Spec.ipInput (w.b.extract 0 L.toNat)).run (s, es)).2
              = ((Spec.runTcp (Spec.Tcp.input h.src S)).run (s, es)).2 := hS
          have hsim := hok S hp
          obtain ⟨es', hrun, hk⟩ := runTcp_keep (Spec.Tcp.input h.src S) s es hrel.slip
          refine ⟨w', txEvs s.ip s.ipId ((Spec.Tcp.input h.src S).run (ctxOf s)).2.out.toList
            ++ ((Spec.Tcp.input h.src S).run (ctxOf s)).2.diag.toList.filter keep, hcall, hbs'.trans hBs, ?_, ?_, ?_,
            ?_, ?_⟩
          · rw [hS, hrun]
            exact ⟨hsim.tcb, hsim.iss, by rw [hsim.id, hrel.id], hrel.ip, hrel.mss, hrel.slip, hrel.dhcp⟩
          · rw [hS, hrun]
          · rw [hS, hrun]
          · rw [hS, hrun]; simp only [hk, List.append_assoc]
          · rw [hsim.evs, hrel.ip, hrel.id, List.append_assoc]
  · -- not TCP
    have hnt : 20 ≤ L.toNat → Bytes.get w.b 9 ≠ 6 := fun a b => htcp ⟨a, b⟩
    obtain ⟨B, hBs, hcall⟩ := ip_input_summary p hP.toTcpProg.toRxProg.toInProg (tcpSt st0 w) w.b L w.id
      (lookup_tcpSt_buf st0 hB w) hlen' (lookup_tcpSt_ip_id st0 hB w) ourIp hKin hL hb hnt (frame_tcpSt st0 hB w)
      (d + 3200)
    obtain ⟨es', hrun, hobs⟩ := ipInput_obs s es (w.b.extract 0 L.toNat) hrel.slip hrel.dhcp (by
      intro h pl hv
      obtain ⟨hsz20, hproto⟩ := validate_ok_facts _ _ _ _ hv
      rw [hproto, get_extract w.b 0 _ 9 (by omega) hL, Nat.zero_add]
      exact hnt (by omega))
    rw [rxSt_tcpSt, show d + 3200 + L.toNat + 500 = d + L.toNat + 3700 by omega] at hcall
    rw [← hrel.id, hrel.ip] at hobs hrun
    refine ⟨_, (ipSpec w.id ourIp (w.b.extract 0 L.toNat)).1.filter keep, hcall, hBs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrun]; exact ⟨hrel.tcb, hrel.iss, rfl, rfl, hrel.mss, hrel.slip, hrel.dhcp⟩
    · rw [hrun]
    · rw [hrun]
    · rw [hrun]
      show es'.toList.filter keep = _
      rw [← filter_keep_obs, hobs, List.filter_append, filter_keep_obs]
    · show (w.evs ++ _).filter keep = _
      rw [List.filter_append]

/-- info: 'Ember.Proof.Refine.frame_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frame_refines

end Ember.Proof.Refine
