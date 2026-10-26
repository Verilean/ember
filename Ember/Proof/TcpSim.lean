import Ember.Proof.RefineTcpTick
import Ember.Proof.Tcp

/-!
# Ember.Proof.TcpSim — TCP: the transcribed functions against the Spec (plan M5.5, second layer)

`RefineTcp*.lean` show that the TCP code computes Lean functions on `TW`
(machine integers, the echo buffer a fixed array).  This file relates
those functions to `Ember.Spec.Tcp` (naturals, a `ByteArray`):

* `TcbRel`, `SegRel`: the connection record and the Spec's control
  block, the segment record and the Spec's parsed segment;
* `Sim`: the two states of a TCP step agree and the trace so far is the
  segments the Spec queued (as `Spec.runTcp` transmits them) followed by
  its drops.  Compared are transmissions and drops (`keep`); the Spec's
  `tcb` lines and the notes (whose texts differ) are not;
* one correspondence per function, stated with `Spec.Tcp.wp` so that
  they compose along the Spec's `do` blocks: `acceptable`, `tcp_emit`,
  `send_seg`, `send_syn_ack`, `send_reset`, `rexmit`, `output`,
  `listen_input`, `ack_input` (with the echo buffer moved down), the
  data and FIN stages, and then
* `segment_wp`: **`tcp_segment` is `Spec.Tcp.input`**;
* `tick_wp`: **`tcp_tick` is `Spec.Tcp.tick`** (`rto` is `Spec.rto`).

`TcpSimParse.lean` adds parsing and states the two results.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## The two control blocks -/

/-- The connection record of the stack holds the Spec's control block
`T`; the echo buffer starts with `T.pending`. -/
structure TcbRel (r : RawTcb) (pd : ByteArray) (T : Spec.Tcp.Tcb) : Prop where
  st : r.st = UInt8.ofNat T.st.code
  rip : r.rip = T.rip
  rport : r.rport = T.rport
  una : r.snd_una = T.sndUna
  nxt : r.snd_nxt = T.sndNxt
  rcv : r.rcv_nxt = T.rcvNxt
  plen : r.pend_len.toNat = T.pending.size
  sent : r.sent.toNat = T.sent
  fin : r.fin_sent = T.finSent
  peer : r.peer_mss.toNat = T.peerMss
  our : r.our_mss.toNat = T.ourMss
  lw : r.last_wnd.toNat = T.lastWnd
  rt : r.rt_timer.toNat = T.rtTimer
  re : r.retries.toNat = T.retries
  tw : r.tw_timer.toNat = T.twTimer
  idle : r.idle.toNat = T.idle
  cr : r.close_req = T.closeReq
  pend : pd.extract 0 T.pending.size = T.pending
  pdsz : pd.size = 256
  hsent : T.sent ≤ T.pending.size
  hcap : T.pending.size ≤ T.cap
  hour : T.ourMss ≤ 256

/-- The segment record holds the Spec's parsed segment `S`, whose data
lies in the packet buffer. -/
structure SegRel (s : RawSeg) (b : ByteArray) (S : Spec.Tcp.Seg) : Prop where
  sport : s.sport = S.sport
  dport : s.dport = S.dport
  seq : s.seq = S.seq
  ack : s.ack = S.ack
  flags : s.flags = S.flags
  mss : S.mss = if s.has_mss then some s.mss else none
  data : S.data = b.extract s.doff.toNat (s.doff.toNat + s.dlen.toNat)
  fits : s.doff.toNat + s.dlen.toNat ≤ b.size

theorem TcbRel.cap_eq {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    r.cap.toNat = T.cap := by
  simp only [RawTcb.cap, Spec.Tcp.Tcb.cap, ← h.our, ← h.peer]
  split
  · rename_i hlt
    have := UInt16.lt_iff_toNat_lt.mp hlt
    omega
  · rename_i hlt
    have := mt UInt16.lt_iff_toNat_lt.mpr hlt
    omega

theorem TcbRel.wnd_eq {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    r.wnd.toNat = T.wnd := by
  have hc := h.cap_eq
  have := h.hcap
  simp only [RawTcb.wnd, Spec.Tcp.Tcb.wnd, UInt16.toNat_sub, hc, h.plen]
  have := r.cap.toNat_lt
  omega

theorem SegRel.size_data {s : RawSeg} {b : ByteArray} {S : Spec.Tcp.Seg} (h : SegRel s b S) :
    S.data.size = s.dlen.toNat := by
  rw [h.data, ByteArray.size_extract]; have := h.fits; omega

theorem SegRel.len_eq {s : RawSeg} {b : ByteArray} {S : Spec.Tcp.Seg} (h : SegRel s b S) :
    s.len.toNat = S.len := by
  have hd := h.size_data
  have hl := s.dlen.toNat_lt
  simp only [RawSeg.len, Spec.Tcp.Seg.len, Spec.Tcp.has, Spec.Tcp.SYN, Spec.Tcp.FIN, hd, ← h.flags]
  have t1 : (1 : UInt32).toNat = 1 := rfl
  have t0 : (0 : UInt32).toNat = 0 := rfl
  split <;> split <;> simp only [UInt32.toNat_add, UInt16.toNat_toUInt32, t1, t0] <;> omega

/-! ## Acceptability -/

theorem lt_wnd_iff (x : UInt32) (wn : UInt16) : (x < wn.toUInt32) ↔ x.toNat < wn.toNat := by
  rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32]

/-- **`acceptable`**: the stack's test is the Spec's (RFC 9293's four cases). -/
theorem acc_rel (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (hr : TcbRel w.r w.pd T) (hs : SegRel w.sg w.b S) :
    accW w = Spec.Tcp.acceptable T S := by
  have hw := hr.wnd_eq
  have hl := hs.len_eq
  have hw0 : (w.r.wnd == 0) = (T.wnd == 0) := by
    have t0 : (0 : UInt16).toNat = 0 := rfl
    have : w.r.wnd = 0 ↔ T.wnd = 0 := by
      rw [← hw, ← UInt16.toNat_inj, t0]
    by_cases h : w.r.wnd = 0
    · rw [h, this.mp h]; rfl
    · have h' : ¬ T.wnd = 0 := fun e => h (this.mpr e)
      rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']
  have hl0 : (w.sg.len == 0) = (S.len == 0) := by
    have t0 : (0 : UInt32).toNat = 0 := rfl
    have : w.sg.len = 0 ↔ S.len = 0 := by
      rw [← hl, ← UInt32.toNat_inj, t0]
    by_cases h : w.sg.len = 0
    · rw [h, this.mp h]; rfl
    · have h' : ¬ S.len = 0 := fun e => h (this.mpr e)
      rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']
  simp only [accW, Spec.Tcp.acceptable, Spec.Tcp.dist, hw0, hl0, hs.seq, hr.rcv, lt_wnd_iff, hw]
  split
  · rfl
  · split
    · rfl
    · rename_i _ hne
      have hpos : 0 < S.len := by
        have : ¬ S.len = 0 := by simpa using hne
        omega
      have hll := w.sg.len.toNat_lt
      have e1 : S.seq + w.sg.len - 1 - T.rcvNxt = S.seq + UInt32.ofNat (S.len - 1) - T.rcvNxt := by
        congr 1
        have : w.sg.len - 1 = UInt32.ofNat (S.len - 1) := by
          apply UInt32.toNat_inj.mp
          have t1 : (1 : UInt32).toNat = 1 := rfl
          rw [UInt32.toNat_sub, t1, UInt32.toNat_ofNat', hl]
          omega
        rw [← this]
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, UInt32.toNat_sub]
        omega
      rw [e1]
      congr 1 <;> simp

/-! ## The trace of a TCP step -/

/-- The trace lines that are compared: transmissions and drops. -/
def keep : Trace.Event → Bool
  | .tx _ => true
  | .drop _ => true
  | _ => false

/-- What `Spec.runTcp` transmits for the segments a TCP step queued:
each in the Spec's IPv4 packet with the next identification. -/
def txEvs (ourIp : UInt32) : UInt16 → List (UInt32 × ByteArray) → List Trace.Event
  | _, [] => []
  | id, (dst, seg) :: rest =>
    .tx (Spec.Slip.encode (Spec.Ipv4.packet 6 id ourIp dst seg)) :: txEvs ourIp (id + 1) rest

theorem txEvs_append (ourIp : UInt32) (l : List (UInt32 × ByteArray)) (dst : UInt32) (seg : ByteArray) :
    ∀ id, txEvs ourIp id (l ++ [(dst, seg)])
      = txEvs ourIp id l ++ [.tx (Spec.Slip.encode (Spec.Ipv4.packet 6 (id + UInt16.ofNat l.length) ourIp dst seg))] := by
  induction l with
  | nil => intro id; simp [txEvs]
  | cons hd tl ih =>
    intro id
    obtain ⟨d', s'⟩ := hd
    have e : id + 1 + UInt16.ofNat tl.length = id + UInt16.ofNat (tl.length + 1) := by
      apply UInt16.toNat_inj.mp
      simp only [UInt16.toNat_add, UInt16.toNat_ofNat']
      have t1 : (1 : UInt16).toNat = 1 := rfl
      rw [t1]; omega
    simp only [List.cons_append, txEvs, ih, List.length_cons, e]

/-- The stack's TCP state `w` and the Spec's context `c` agree, the trace
of the step so far being the segments queued and then the diagnostics
(`ev0`, `id0`: the trace and the identification before the step). -/
structure Sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16) : Prop where
  tcb : TcbRel w.r w.pd c.tcb
  iss : w.iss = c.iss
  ip : c.ourIp = ourIp
  id : w.id = id0 + UInt16.ofNat c.out.size
  evs : w.evs.filter keep = ev0 ++ txEvs ourIp id0 c.out.toList ++ c.diag.toList.filter keep
  mss : c.mss = 256

theorem sendSegW_r (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).r = { w.r with last_wnd := w.r.wnd } := by
  simp only [sendSegW, emitW]
theorem sendSegW_pd (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).pd = w.pd := by
  simp only [sendSegW, emitW]
theorem sendSegW_iss (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).iss = w.iss := by
  simp only [sendSegW, emitW]
theorem sendSegW_id (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).id = w.id + 1 := by
  simp only [sendSegW, emitW]
theorem sendSegW_evs (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).evs = w.evs ++ [.tx (Spec.Slip.encode (Spec.Ipv4.packet 6 w.id ourIp w.r.rip
      (Spec.Tcp.emit ourIp w.r.rip (Spec.Tcp.Seg.mk 7 w.r.rport seq w.r.rcv_nxt flags w.r.wnd
        (if m then some w.r.our_mss else none) (w.pd.extract so.toNat (so.toNat + n.toNat))))))] := by
  simp only [sendSegW, emitW]

/-- **`send_seg` is `Spec.Tcp.sendSeg`** (before any diagnostic of the step). -/
theorem sendSeg_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (flags : UInt8) (seq : UInt32)
    (so n : UInt16) (mssB : Bool) (data : ByteArray) (mss : Option UInt16)
    (hdata : data = w.pd.extract so.toNat (so.toNat + n.toNat))
    (hmss : mss = if mssB then some w.r.our_mss else none) :
    Sim ourIp (sendSegW w ourIp flags seq so n mssB) ((Spec.Tcp.sendSeg flags seq data mss).run c).2 ev0 id0 := by
  have hw := h.tcb.wnd_eq
  have hwn : UInt16.ofNat c.tcb.wnd = w.r.wnd := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_ofNat', ← hw]; exact Nat.mod_eq_of_lt w.r.wnd.toNat_lt
  have hrun : ((Spec.Tcp.sendSeg flags seq data mss).run c).2
      = { c with out := c.out.push (c.tcb.rip, Spec.Tcp.emit c.ourIp c.tcb.rip
            { sport := Spec.echoPort, dport := c.tcb.rport, seq := seq, ack := c.tcb.rcvNxt, flags := flags,
              wnd := UInt16.ofNat c.tcb.wnd, mss := mss, data := data }),
                 tcb := { c.tcb with lastWnd := c.tcb.wnd } } := rfl
  rw [hrun]
  have t := h.tcb
  refine ⟨?_, ?_, h.ip, ?_, ?_, h.mss⟩
  · rw [sendSegW_r, sendSegW_pd]
    exact ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, hw, t.rt, t.re, t.tw,
      t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩
  · rw [sendSegW_iss]; exact h.iss
  · rw [sendSegW_id, h.id]
    have hsz : (c.out.push (c.tcb.rip, Spec.Tcp.emit c.ourIp c.tcb.rip
        { sport := Spec.echoPort, dport := c.tcb.rport, seq := seq, ack := c.tcb.rcvNxt, flags := flags,
          wnd := UInt16.ofNat c.tcb.wnd, mss := mss, data := data })).size = c.out.size + 1 := Array.size_push ..
    simp only [hsz]
    apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_add, UInt16.toNat_ofNat']
    have t1 : (1 : UInt16).toNat = 1 := rfl
    rw [t1]; omega
  · rw [sendSegW_evs]
    simp only [List.filter_append, h.evs, hd, List.append_nil, Array.toList_push, txEvs_append]
    have hk : ∀ f : ByteArray, [Trace.Event.tx f].filter keep = [.tx f] := fun f => rfl
    rw [hk, h.id, h.ip, t.rip, t.rport, t.rcv, hwn, hdata, hmss, List.append_assoc, Array.length_toList]
    rfl

theorem extract_empty (b : ByteArray) (k : Nat) : b.extract k (k + 0) = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.eq_empty_of_size_eq_zero
  show (b.extract k (k + 0)).size = 0
  rw [ByteArray.size_extract]; omega

/-- **`tcp_emit` is `Spec.Tcp.send`** of the same segment (before any
diagnostic of the step): the control block is untouched. -/
theorem emit_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (dst : UInt32) (sport dport : UInt16)
    (seq ack : UInt32) (flags : UInt8) (wn : UInt16) (mssB : Bool) (so n : UInt16) (seg : Spec.Tcp.Seg)
    (hseg : seg = Spec.Tcp.Seg.mk sport dport seq ack flags wn (if mssB then some w.r.our_mss else none)
      (w.pd.extract so.toNat (so.toNat + n.toNat))) :
    Sim ourIp (emitW w ourIp dst sport dport seq ack flags wn mssB so n) ((Spec.Tcp.send dst seg).run c).2 ev0
      id0 := by
  have hrun : ((Spec.Tcp.send dst seg).run c).2
      = { c with out := c.out.push (dst, Spec.Tcp.emit c.ourIp dst seg) } := rfl
  rw [hrun]
  have t := h.tcb
  have hr : (emitW w ourIp dst sport dport seq ack flags wn mssB so n).r = w.r := by simp only [emitW]
  have hp : (emitW w ourIp dst sport dport seq ack flags wn mssB so n).pd = w.pd := by simp only [emitW]
  have hi : (emitW w ourIp dst sport dport seq ack flags wn mssB so n).iss = w.iss := by simp only [emitW]
  have hid : (emitW w ourIp dst sport dport seq ack flags wn mssB so n).id = w.id + 1 := by simp only [emitW]
  have he : (emitW w ourIp dst sport dport seq ack flags wn mssB so n).evs
      = w.evs ++ [.tx (Spec.Slip.encode (Spec.Ipv4.packet 6 w.id ourIp dst (Spec.Tcp.emit ourIp dst
          (Spec.Tcp.Seg.mk sport dport seq ack flags wn (if mssB then some w.r.our_mss else none)
            (w.pd.extract so.toNat (so.toNat + n.toNat))))))] := by simp only [emitW]
  refine ⟨?_, ?_, h.ip, ?_, ?_, h.mss⟩
  · rw [hr, hp]; exact t
  · rw [hi]; exact h.iss
  · rw [hid, h.id]
    simp only [Array.size_push]
    apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_add, UInt16.toNat_ofNat']
    have t1 : (1 : UInt16).toNat = 1 := rfl
    rw [t1]; omega
  · rw [he]
    simp only [List.filter_append, h.evs, hd, List.append_nil, Array.toList_push, txEvs_append]
    have hk : ∀ f : ByteArray, [Trace.Event.tx f].filter keep = [.tx f] := fun f => rfl
    rw [hk, h.id, h.ip, hseg, List.append_assoc, Array.length_toList]

/-- A `drop` on both sides. -/
theorem drop_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (r : String) :
    Sim ourIp (dropW w r) ((Spec.Tcp.dropR r).run c).2 ev0 id0 := by
  have hrun : ((Spec.Tcp.dropR r).run c).2 = { c with diag := c.diag.push (.drop r) } := rfl
  rw [hrun]
  refine ⟨h.tcb, h.iss, h.ip, h.id, ?_, h.mss⟩
  show (w.evs ++ [Trace.Event.drop r]).filter keep = _
  simp only [List.filter_append, h.evs, Array.toList_push, List.append_assoc]

/-- **`send_reset` is `Spec.Tcp.sendReset`** for the segment in `sg`. -/
theorem sendReset_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src : UInt32) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hsrc : w.sg.src = src) :
    Sim ourIp (resetW w ourIp) ((Spec.Tcp.sendReset src S).run c).2 ev0 id0 := by
  subst hsrc
  have hl := hs.len_eq
  have hlen : w.sg.len = UInt32.ofNat S.len := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofNat', ← hl]; exact (Nat.mod_eq_of_lt w.sg.len.toNat_lt).symm
  have hz := extract_empty w.pd 0
  simp only [resetW, Spec.Tcp.sendReset, Spec.Tcp.has, Spec.Tcp.ACK, ← hs.flags]
  split
  · exact emit_sim ourIp w c ev0 id0 h hd _ _ _ _ _ _ _ false 0 0 _ (by
      rw [hs.sport, hs.dport, hs.ack]
      show _ = Spec.Tcp.Seg.mk _ _ _ _ _ _ none (w.pd.extract 0 (0 + 0))
      rw [hz]; rfl)
  · exact emit_sim ourIp w c ev0 id0 h hd _ _ _ _ _ _ _ false 0 0 _ (by
      rw [hs.sport, hs.dport, hs.seq, hlen]
      show _ = Spec.Tcp.Seg.mk _ _ _ _ _ _ none (w.pd.extract 0 (0 + 0))
      rw [hz]; rfl)

/-- The state codes agree: a test of `t.st` is the Spec's test of the state. -/
theorem TcbRel.st_beq {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (s : Spec.Tcp.St) :
    (r.st == UInt8.ofNat s.code) = (T.st == s) := by
  rw [h.st]
  cases T.st <;> cases s <;> rfl

/-- A part of the pending bytes is the same part of the echo buffer. -/
theorem TcbRel.extract_pending {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (a n : Nat)
    (hn : a + n ≤ T.pending.size) : T.pending.extract a (a + n) = pd.extract a (a + n) := by
  have hc := h.hcap
  have hsz : T.pending.size ≤ pd.size := by
    have := h.pdsz
    have : T.cap ≤ 256 := by
      have := h.hour
      simp only [Spec.Tcp.Tcb.cap]; omega
    omega
  apply Bytes.ext_get
  · rw [ByteArray.size_extract, ByteArray.size_extract]; omega
  · intro j hj
    rw [ByteArray.size_extract] at hj
    rw [get_extract _ a _ j (by omega) (by omega), get_extract _ a _ j (by omega) (by omega), ← h.pend,
      get_extract pd 0 _ (a + j) (by omega) (by omega), Nat.zero_add]

/-- What the two Spec senders leave behind, as records (a bare `rfl` between them is slow). -/
theorem sendSeg_run (c : Spec.Tcp.Ctx) (flags : UInt8) (seq : UInt32) (data : ByteArray) (mss : Option UInt16) :
    ((Spec.Tcp.sendSeg flags seq data mss).run c).2
      = { c with out := c.out.push (c.tcb.rip, Spec.Tcp.emit c.ourIp c.tcb.rip
            { sport := Spec.echoPort, dport := c.tcb.rport, seq := seq, ack := c.tcb.rcvNxt, flags := flags,
              wnd := UInt16.ofNat c.tcb.wnd, mss := mss, data := data }),
                 tcb := { c.tcb with lastWnd := c.tcb.wnd } } := rfl
theorem sendSynAck_run (c : Spec.Tcp.Ctx) :
    (Spec.Tcp.sendSynAck.run c).2
      = { c with out := c.out.push (c.tcb.rip, Spec.Tcp.emit c.ourIp c.tcb.rip
            { sport := Spec.echoPort, dport := c.tcb.rport, seq := c.tcb.sndUna, ack := c.tcb.rcvNxt,
              flags := Spec.Tcp.SYN ||| Spec.Tcp.ACK,
              wnd := UInt16.ofNat c.tcb.wnd, mss := some (UInt16.ofNat c.tcb.ourMss), data := .empty }),
                 tcb := { c.tcb with lastWnd := c.tcb.wnd } } := rfl

/-- **`send_syn_ack` is `Spec.Tcp.sendSynAck`.** -/
theorem sendSynAck_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) :
    Sim ourIp (sendSegW w ourIp (2 ||| 16) w.r.snd_una 0 0 true) (Spec.Tcp.sendSynAck.run c).2 ev0 id0 := by
  have e0 : (0 : UInt16).toNat = 0 := rfl
  have hdata : ByteArray.empty = w.pd.extract (0 : UInt16).toNat ((0 : UInt16).toNat + (0 : UInt16).toNat) := by
    rw [e0]; exact (extract_empty w.pd 0).symm
  have hmss : some (UInt16.ofNat c.tcb.ourMss) = if true = true then some w.r.our_mss else none := by
    have : UInt16.ofNat c.tcb.ourMss = w.r.our_mss := by
      apply UInt16.toNat_inj.mp
      rw [UInt16.toNat_ofNat', ← h.tcb.our]; exact Nat.mod_eq_of_lt w.r.our_mss.toNat_lt
    rw [this, if_pos rfl]
  have key := sendSeg_sim ourIp w c ev0 id0 h hd (2 ||| 16) w.r.snd_una 0 0 true .empty
    (some (UInt16.ofNat c.tcb.ourMss)) hdata hmss
  have hf : (Spec.Tcp.SYN ||| Spec.Tcp.ACK) = (2 ||| 16 : UInt8) := by decide
  have hrun : (Spec.Tcp.sendSynAck.run c).2
      = ((Spec.Tcp.sendSeg (Spec.Tcp.SYN ||| Spec.Tcp.ACK) c.tcb.sndUna .empty
          (some (UInt16.ofNat c.tcb.ourMss))).run c).2 := by
    rw [sendSynAck_run, sendSeg_run]
  rw [hrun, hf, ← h.tcb.una]
  exact key

/-! ## Retransmission -/

theorem rexmit_run (c : Spec.Tcp.Ctx) :
    (Spec.Tcp.rexmit.run c).2
      = if c.tcb.st == .synRcvd then (Spec.Tcp.sendSynAck.run c).2
        else ((Spec.Tcp.sendSeg (Spec.Tcp.ACK ||| (if c.tcb.sent > 0 then Spec.Tcp.PSH else 0)
                ||| (if c.tcb.finSent then Spec.Tcp.FIN else 0)) c.tcb.sndUna
                (Bytes.slice c.tcb.pending 0 c.tcb.sent)).run c).2 := by
  show ((if c.tcb.st == .synRcvd then Spec.Tcp.sendSynAck else _ : Spec.Tcp.TcpM Unit).run c).2 = _
  cases (c.tcb.st == Spec.Tcp.St.synRcvd)
  · exact rfl
  · exact rfl

theorem TcbRel.sent_pos {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    (0 < r.sent) ↔ T.sent > 0 := by
  rw [UInt16.lt_iff_toNat_lt, h.sent]; exact Iff.rfl

/-- **`rexmit` is `Spec.Tcp.rexmit`.** -/
theorem rexmit_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) :
    Sim ourIp (rexmitW w ourIp) (Spec.Tcp.rexmit.run c).2 ev0 id0 := by
  have t := h.tcb
  have hst : (w.r.st == 1) = (c.tcb.st == .synRcvd) := t.st_beq .synRcvd
  rw [rexmit_run, rexmitW, hst]
  cases hc : (c.tcb.st == Spec.Tcp.St.synRcvd)
  · rw [if_neg (by simp), if_neg (by simp)]
    have e0 : (0 : UInt16).toNat = 0 := rfl
    have hp := t.sent_pos
    have hfl : (Spec.Tcp.ACK ||| (if c.tcb.sent > 0 then Spec.Tcp.PSH else 0)
        ||| (if c.tcb.finSent then Spec.Tcp.FIN else 0)) = rexFlags w.r := by
      simp only [rexFlags, t.fin, Spec.Tcp.ACK, Spec.Tcp.PSH, Spec.Tcp.FIN]
      by_cases h0 : 0 < w.r.sent
      · rw [if_pos h0, if_pos (hp.mp h0)]; cases c.tcb.finSent <;> rfl
      · rw [if_neg h0, if_neg (fun x => h0 (hp.mpr x))]; cases c.tcb.finSent <;> rfl
    have hdata : Bytes.slice c.tcb.pending 0 c.tcb.sent
        = w.pd.extract (0 : UInt16).toNat ((0 : UInt16).toNat + w.r.sent.toNat) := by
      rw [e0, t.sent]
      exact t.extract_pending 0 c.tcb.sent (by have := t.hsent; omega)
    rw [hfl, ← t.una]
    exact sendSeg_sim ourIp w c ev0 id0 h hd (rexFlags w.r) w.r.snd_una 0 w.r.sent false _ none hdata rfl
  · rw [if_pos rfl, if_pos rfl]
    exact sendSynAck_sim ourIp w c ev0 id0 h hd

/-! ## `output`

From here the correspondences are stated with `Spec.Tcp.wp`, so that
they compose along a `do` block: the Spec action, run from a state the
stack simulates, ends in a state the stack's function simulates. -/

open Ember.Spec.Tcp (wp wp_bind wp_get wp_ite wp_modify wp_pure wp_armTimer wp_set wp_dropR wp_logTcb
  wp_closeConn wp_send wp_map)

/-- `sendSeg_sim` as a step of a `do` block. -/
theorem sendSeg_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (flags : UInt8) (seq : UInt32)
    (so n : UInt16) (mssB : Bool) (data : ByteArray) (mss : Option UInt16)
    (hdata : data = w.pd.extract so.toNat (so.toNat + n.toNat))
    (hmss : mss = if mssB then some w.r.our_mss else none) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (sendSegW w ourIp flags seq so n mssB) c' ev0 id0 → c'.diag = c.diag → Q () c') :
    wp (Spec.Tcp.sendSeg flags seq data mss) Q c :=
  hQ _ (sendSeg_sim ourIp w c ev0 id0 h hd flags seq so n mssB data mss hdata hmss) rfl

/-- The control block replaced on both sides. -/
theorem Sim.setTcb {ourIp : UInt32} {w : TW} {c : Spec.Tcp.Ctx} {ev0 : List Trace.Event} {id0 : UInt16}
    (h : Sim ourIp w c ev0 id0) (r' : RawTcb) (T' : Spec.Tcp.Tcb) (hr : TcbRel r' w.pd T') :
    Sim ourIp { w with r := r' } { c with tcb := T' } ev0 id0 :=
  ⟨hr, h.iss, h.ip, h.id, h.evs, h.mss⟩

theorem TcbRel.unsent {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    (r.pend_len - r.sent).toNat = T.pending.size - T.sent := by
  have := h.plen; have := h.sent; have := h.hsent
  have := r.pend_len.toNat_lt; have := r.sent.toNat_lt
  rw [UInt16.toNat_sub]; omega

/-- What `output` does when there is neither data nor a FIN to send. -/
theorem outRest_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (a : Bool)
    (Q : Spec.Tcp.Ctx → Prop) (hQ : ∀ c', Sim ourIp (outRest w ourIp a) c' ev0 id0 → c'.diag = c.diag → Q c') :
    if (c.tcb.st == Spec.Tcp.St.listen || c.tcb.st == Spec.Tcp.St.synRcvd) = true then Q c
    else
      if (a || c.tcb.lastWnd == 0 && decide (c.tcb.wnd > 0)) = true then
        wp (Spec.Tcp.sendSeg Spec.Tcp.ACK c.tcb.sndNxt) (fun _ c' => Q c') c
      else Q c := by
  have t := h.tcb
  have e0 : (w.r.st == 0) = (c.tcb.st == .listen) := t.st_beq .listen
  have e1 : (w.r.st == 1) = (c.tcb.st == .synRcvd) := t.st_beq .synRcvd
  have hw := t.wnd_eq
  have el : (w.r.last_wnd == 0) = (c.tcb.lastWnd == 0) := by
    have z : (0 : UInt16).toNat = 0 := rfl
    have : w.r.last_wnd = 0 ↔ c.tcb.lastWnd = 0 := by rw [← t.lw, ← UInt16.toNat_inj, z]
    by_cases x : w.r.last_wnd = 0
    · rw [x, this.mp x]; rfl
    · rw [beq_eq_false_iff_ne.mpr x, beq_eq_false_iff_ne.mpr (fun y => x (this.mpr y))]
  have ew : decide (0 < w.r.wnd) = decide (c.tcb.wnd > 0) := by
    have z : (0 : UInt16).toNat = 0 := rfl
    exact decide_eq_decide.mpr (by rw [UInt16.lt_iff_toNat_lt, z, hw])
  have hR : outRest w ourIp a
      = if (c.tcb.st == Spec.Tcp.St.listen || c.tcb.st == Spec.Tcp.St.synRcvd) = true then w
        else if (a || c.tcb.lastWnd == 0 && decide (c.tcb.wnd > 0)) = true then
          sendSegW w ourIp 16 w.r.snd_nxt 0 0 false
        else w := by
    rw [outRest, e0, e1, el, ew]
  rw [hR] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ; exact hQ c h rfl
  · rename_i x
    rw [if_neg x] at hQ
    split
    · rename_i y
      rw [if_pos y] at hQ
      have z : (0 : UInt16).toNat = 0 := rfl
      rw [← t.nxt]
      exact sendSeg_wp ourIp w c ev0 id0 h hd 16 w.r.snd_nxt 0 0 false .empty none
        (by rw [z]; exact (extract_empty w.pd 0).symm) rfl _ (fun c' hs hdg => hQ c' hs hdg)
    · rename_i y; rw [if_neg y] at hQ; exact hQ c h rfl

/-- The control block after `output` decided to send (`cl`: with a FIN). -/
def outR2 (r : RawTcb) (cl : Bool) : RawTcb :=
  let r1 : RawTcb := if cl then { r with st := if r.st == 3 then 4 else 5, fin_sent := true } else r
  { r1 with sent := r.pend_len, snd_nxt := r.snd_nxt + (r.pend_len - r.sent).toUInt32 + (if cl then 1 else 0) }

def outFlags (r : RawTcb) (cl : Bool) : UInt8 :=
  let f1 : UInt8 := if 0 < r.pend_len - r.sent then 16 ||| 8 else 16
  if cl then f1 ||| 1 else f1

/-- The retransmission timer is started unless something was in flight. -/
def armW (w : TW) (was : Bool) : TW :=
  if was then w else { w with r := { w.r with rt_timer := 3, retries := 0 } }

theorem outputW_data (w : TW) (ourIp : UInt32) (a : Bool)
    (hc : ((w.r.st == 2 || w.r.st == 3) && (decide (0 < w.r.pend_len - w.r.sent)
        || ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent))) = true) :
    outputW w ourIp a
      = armW (sendSegW { w with r := outR2 w.r ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent) } ourIp
          (outFlags w.r ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent)) w.r.snd_nxt w.r.sent
          (w.r.pend_len - w.r.sent) false) (w.r.snd_una != w.r.snd_nxt) := by
  show (if _ then _ else _) = _
  rw [if_pos hc]
  simp only [armW, outR2, outFlags]

theorem armTimer_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (was : Bool) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (armW w was) c' ev0 id0 → c'.diag = c.diag → Q () c') :
    wp (Spec.Tcp.armTimer was) Q c := by
  rw [wp_armTimer]
  cases was
  · rw [if_neg (by simp)]
    have t := h.tcb
    exact hQ _ ⟨⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, rfl, rfl,
      t.tw, t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩, h.iss, h.ip, h.id, h.evs, h.mss⟩ rfl
  · rw [if_pos rfl]; exact hQ c h rfl

theorem outR2_rel {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (t : TcbRel r pd T) (cl : Bool) :
    TcbRel (outR2 r cl) pd { T with
      sent := T.pending.size, finSent := T.finSent || cl,
      st := if (!cl) = true then T.st else if (T.st == Spec.Tcp.St.closeWait) = true then .lastAck else .finWait1,
      sndNxt := T.sndNxt + UInt32.ofNat (T.pending.size - T.sent) + (if cl = true then 1 else 0) } := by
  have e3 : (r.st == 3) = (T.st == .closeWait) := t.st_beq .closeWait
  have hu : (r.pend_len - r.sent).toUInt32 = UInt32.ofNat (T.pending.size - T.sent) := by
    apply UInt32.toNat_inj.mp
    rw [UInt16.toNat_toUInt32, t.unsent, UInt32.toNat_ofNat']
    have := t.plen; have := r.pend_len.toNat_lt
    omega
  cases cl
  · exact ⟨t.st, t.rip, t.rport, t.una, by simp only [outR2, t.nxt, hu], t.rcv, t.plen, t.plen,
      by simp [outR2, t.fin], t.peer, t.our, t.lw, t.rt, t.re, t.tw, t.idle, t.cr, t.pend, t.pdsz, Nat.le_refl _,
      t.hcap, t.hour⟩
  · exact ⟨by
        show (if r.st == 3 then (4 : UInt8) else 5) = _
        rw [e3]; cases (T.st == Spec.Tcp.St.closeWait) <;> rfl,
      t.rip, t.rport, t.una, by simp only [outR2, t.nxt, hu], t.rcv, t.plen, t.plen,
      by simp [outR2], t.peer, t.our, t.lw, t.rt, t.re, t.tw, t.idle, t.cr, t.pend, t.pdsz, Nat.le_refl _,
      t.hcap, t.hour⟩

/-- **`output` is `Spec.Tcp.output`.** -/
theorem output_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (a : Bool)
    (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (outputW w ourIp a) c' ev0 id0 → c'.diag = c.diag → Q () c') :
    wp (Spec.Tcp.output a) Q c := by
  have t := h.tcb
  have e2 : (w.r.st == 2) = (c.tcb.st == .established) := t.st_beq .established
  have e3 : (w.r.st == 3) = (c.tcb.st == .closeWait) := t.st_beq .closeWait
  have hU := t.unsent
  have eU : decide (0 < w.r.pend_len - w.r.sent) = decide (c.tcb.pending.size - c.tcb.sent > 0) := by
    have z : (0 : UInt16).toNat = 0 := rfl
    exact decide_eq_decide.mpr (by rw [UInt16.lt_iff_toNat_lt, z, hU])
  simp only [Spec.Tcp.output, wp_bind, wp_get, wp_ite, wp_modify, wp_pure]
  have hrest : ∀ (hc : ((w.r.st == 2 || w.r.st == 3) && (decide (0 < w.r.pend_len - w.r.sent)
        || ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent))) = false),
      if (c.tcb.st == Spec.Tcp.St.listen || c.tcb.st == Spec.Tcp.St.synRcvd) = true then Q () c
      else
        if (a || c.tcb.lastWnd == 0 && decide (c.tcb.wnd > 0)) = true then
          wp (Spec.Tcp.sendSeg Spec.Tcp.ACK c.tcb.sndNxt) (fun _ c' => Q () c') c
        else Q () c := by
    intro hc
    have hO : outputW w ourIp a = outRest w ourIp a := by
      simp only [outputW, hc, Bool.false_eq_true, if_false]
    rw [hO] at hQ
    exact outRest_wp ourIp w c ev0 id0 h hd a (fun c' => Q () c') hQ
  cases hA : (c.tcb.st == Spec.Tcp.St.established || c.tcb.st == Spec.Tcp.St.closeWait)
  · rw [if_neg (by simp)]
    exact hrest (by rw [e2, e3, hA]; rfl)
  rw [if_pos rfl]
  cases hB : (decide (c.tcb.pending.size - c.tcb.sent > 0) ||
            (c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent)
  · rw [if_neg (by simp)]
    exact hrest (by rw [e2, e3, hA, eU, t.cr, t.fin, hB]; rfl)
  rw [if_pos rfl]
  have eC : ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent)
      = ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) := by rw [e3, t.cr, t.fin]
  have hcW : ((w.r.st == 2 || w.r.st == 3) && (decide (0 < w.r.pend_len - w.r.sent)
        || ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent))) = true := by
    rw [e2, e3, hA, eU, t.cr, t.fin, hB]; rfl
  have eO : (w.r.snd_una != w.r.snd_nxt) = c.tcb.outstanding := by
    rw [Spec.Tcp.Tcb.outstanding, t.una, t.nxt]
  rw [outputW_data w ourIp a hcW, eC, eO, t.nxt] at hQ
  have hrel := outR2_rel t ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent)
  have hF : ((Spec.Tcp.ACK ||| if c.tcb.pending.size - c.tcb.sent > 0 then Spec.Tcp.PSH else 0) |||
        if ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) = true then Spec.Tcp.FIN
        else 0)
      = outFlags w.r ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) := by
    have z : (0 : UInt16).toNat = 0 := rfl
    have hp : (0 < w.r.pend_len - w.r.sent) ↔ c.tcb.pending.size - c.tcb.sent > 0 := by
      rw [UInt16.lt_iff_toNat_lt, z, hU]
    simp only [outFlags, Spec.Tcp.ACK, Spec.Tcp.PSH, Spec.Tcp.FIN]
    by_cases h0 : 0 < w.r.pend_len - w.r.sent
    · rw [if_pos h0, if_pos (hp.mp h0)]
      cases ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) <;> rfl
    · rw [if_neg h0, if_neg (fun x => h0 (hp.mpr x))]
      cases ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) <;> rfl
  rw [hF]
  refine sendSeg_wp ourIp
    { w with r := outR2 w.r ((c.tcb.st == Spec.Tcp.St.closeWait || c.tcb.closeReq) && !c.tcb.finSent) } _ ev0 id0
    (h.setTcb _ _ hrel) hd _ _ w.r.sent (w.r.pend_len - w.r.sent) false _ none ?_ rfl _ ?_
  · show _ = w.pd.extract _ _
    rw [t.sent, hU]
    exact t.extract_pending _ _ (by have := t.hsent; omega)
  · intro c' hs hdg
    exact armTimer_wp ourIp _ c' ev0 id0 hs _ _ (fun c'' hs' hdg' => hQ c'' hs' (hdg'.trans hdg))

/-! ## A segment in LISTEN -/

theorem SegRel.has {s : RawSeg} {b : ByteArray} {S : Spec.Tcp.Seg} (h : SegRel s b S) (f : UInt8) :
    (s.flags &&& f != 0) = Spec.Tcp.has S.flags f := by rw [h.flags]; rfl

/-- **`listen_input` is `Spec.Tcp.listenInput`.** -/
theorem listen_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src : UInt32) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hsrc : w.sg.src = src) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (listenW w ourIp) c' ev0 id0 → Q () c') :
    wp (Spec.Tcp.listenInput src S) Q c := by
  have t := h.tcb
  have e0 : (w.r.st != 0) = (c.tcb.st != Spec.Tcp.St.listen) := by
    show (!(w.r.st == 0)) = !(c.tcb.st == Spec.Tcp.St.listen)
    rw [show (w.r.st == 0) = (c.tcb.st == Spec.Tcp.St.listen) from t.st_beq .listen]
  have f4 : (w.sg.flags &&& 4 != 0) = Spec.Tcp.has S.flags Spec.Tcp.RST := hs.has 4
  have f16 : (w.sg.flags &&& 16 != 0) = Spec.Tcp.has S.flags Spec.Tcp.ACK := hs.has 16
  have f2 : (w.sg.flags &&& 2 == 0) = !Spec.Tcp.has S.flags Spec.Tcp.SYN := by
    have := hs.has 2
    rw [show Spec.Tcp.has S.flags Spec.Tcp.SYN = (w.sg.flags &&& 2 != 0) from this.symm]
    show _ = !(!(w.sg.flags &&& 2 == 0))
    rw [Bool.not_not]
  simp only [Spec.Tcp.listenInput, wp_bind, wp_get, wp_ite, wp_pure, wp_set]
  rw [listenW, e0, f4, f16, f2] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ; exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
    · rename_i y; rw [if_neg y] at hQ
      exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendReset_sim ourIp w c ev0 id0 h hd src S hs hsrc) _)
  · rename_i x; rw [if_neg x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ; exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
    · rename_i y; rw [if_neg y] at hQ
      split
      · rename_i z; rw [if_pos z] at hQ
        exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendReset_sim ourIp w c ev0 id0 h hd src S hs hsrc) _)
      · rename_i z; rw [if_neg z] at hQ
        split
        · rename_i u; rw [if_pos u] at hQ; exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
        · rename_i u; rw [if_neg u] at hQ
          refine hQ (Spec.Tcp.sendSynAck.run _).2 ?_
          have hpeer : (if w.sg.has_mss then (if w.sg.mss == 0 then 1 else w.sg.mss) else (536 : UInt16)).toNat
              = (match S.mss with | some m => max 1 m.toNat | none => 536) := by
            rw [hs.mss]
            cases w.sg.has_mss
            · rfl
            · by_cases m0 : w.sg.mss = 0
              · rw [m0]; rfl
              · have : w.sg.mss.toNat ≠ 0 := fun e => m0 (UInt16.toNat_inj.mp e)
                simp only [if_true, beq_iff_eq, m0, if_false]
                omega
          exact sendSynAck_sim ourIp
            { w with iss := w.iss + 65536, r :=
              { RawTcb.reset with
                st := 1, rip := w.sg.src, rport := w.sg.sport, rcv_nxt := w.sg.seq + 1, snd_una := w.iss,
                snd_nxt := w.iss + 1,
                peer_mss := if w.sg.has_mss then (if w.sg.mss == 0 then 1 else w.sg.mss) else 536,
                rt_timer := 3 } } _ ev0 id0
            ⟨⟨rfl, hsrc, hs.sport, h.iss, by rw [← h.iss], by rw [← hs.seq], rfl, rfl, rfl, hpeer,
                by rw [h.mss]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, extract_empty w.pd 0, t.pdsz, Nat.le_refl _,
                Nat.zero_le _, by rw [h.mss]; exact Nat.le_refl _⟩,
              by show w.iss + 65536 = c.iss + Spec.issStep; rw [h.iss]; rfl, h.ip, h.id, h.evs, h.mss⟩ hd

/-! ## The ACK -/

def ackD (w : TW) : UInt32 := w.sg.ack - w.r.snd_una
def ackAcked (w : TW) : UInt16 := if ackD w < w.r.sent.toUInt32 then (ackD w).toUInt16 else w.r.sent
def ackPd (w : TW) : ByteArray := shiftIn w.pd (ackAcked w).toNat (w.r.pend_len - ackAcked w).toNat
def ackR1 (w : TW) : RawTcb :=
  { w.r with pend_len := w.r.pend_len - ackAcked w, sent := w.r.sent - ackAcked w, snd_una := w.sg.ack,
             retries := 0, rt_timer := if w.sg.ack != w.r.snd_nxt then 3 else 0 }

theorem ackW_unsent (w : TW) (ourIp : UInt32) (h : w.r.snd_nxt - w.r.snd_una < ackD w) :
    ackW w ourIp = (false, dropW (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false) "ack-of-unsent") := by
  show (if w.r.snd_nxt - w.r.snd_una < ackD w then _ else _) = _
  rw [if_pos h]

theorem ackW_zero (w : TW) (ourIp : UInt32) (h1 : ¬ w.r.snd_nxt - w.r.snd_una < ackD w)
    (h2 : (ackD w == 0) = true) : ackW w ourIp = (true, w) := by
  show (if w.r.snd_nxt - w.r.snd_una < ackD w then _ else _) = _
  rw [if_neg h1]
  show (if (ackD w == 0) = true then _ else _) = _
  rw [if_pos h2]

theorem ackW_adv (w : TW) (ourIp : UInt32) (h1 : ¬ w.r.snd_nxt - w.r.snd_una < ackD w)
    (h2 : ¬ (ackD w == 0) = true) :
    ackW w ourIp =
      if (ackAcked w).toUInt32 < ackD w then
        if w.r.st == 5 then (true, { w with pd := ackPd w, r := { ackR1 w with st := 6 } })
        else if w.r.st == 7 then (true, { w with pd := ackPd w, r := { ackR1 w with st := 8, tw_timer := 20 } })
        else if w.r.st == 4 then (false, { w with pd := ackPd w, r := RawTcb.reset })
        else (true, { w with pd := ackPd w, r := ackR1 w })
      else (true, { w with pd := ackPd w, r := ackR1 w }) := by
  show (if w.r.snd_nxt - w.r.snd_una < ackD w then _ else _) = _
  rw [if_neg h1]
  show (if (ackD w == 0) = true then _ else _) = _
  rw [if_neg h2]
  rfl

/-- The Spec's control block after an ACK of new data (the state apart). -/
def ackT (T : Spec.Tcp.Tcb) (ack : UInt32) : Spec.Tcp.Tcb :=
  { T with pending := T.pending.extract (min (Spec.Tcp.dist ack T.sndUna) T.sent) T.pending.size,
           sent := T.sent - min (Spec.Tcp.dist ack T.sndUna) T.sent, sndUna := ack, retries := 0,
           rtTimer := if (ack != T.sndNxt) = true then Spec.rto 0 else 0 }

theorem ackD_eq (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T) (ha : w.sg.ack = S.ack) :
    (ackD w).toNat = Spec.Tcp.dist S.ack T.sndUna := by
  simp only [ackD, Spec.Tcp.dist, ha, t.una]

theorem ackAcked_eq (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (ha : w.sg.ack = S.ack) : (ackAcked w).toNat = min (Spec.Tcp.dist S.ack T.sndUna) T.sent := by
  rw [← ackD_eq w T S t ha, ← t.sent]
  have := w.r.sent.toNat_lt
  simp only [ackAcked]
  split
  · rename_i x
    rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32] at x
    rw [UInt32.toNat_toUInt16]; omega
  · rename_i x
    rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32] at x
    omega

/-- The acknowledged bytes leave the echo buffer on both sides. -/
theorem ack_rel (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T) (ha : w.sg.ack = S.ack) :
    TcbRel (ackR1 w) (ackPd w) (ackT T S.ack) := by
  have hA := ackAcked_eq w T S t ha
  have hpl := t.plen; have hse := t.sent; have hle := t.hsent; have hcap := t.hcap; have hsz := t.pdsz
  have hour := t.hour
  have hc : T.cap ≤ 256 := by simp only [Spec.Tcp.Tcb.cap]; omega
  have b1 := w.r.pend_len.toNat_lt; have b2 := w.r.sent.toNat_lt; have b3 := (ackAcked w).toNat_lt
  have hp1 : (w.r.pend_len - ackAcked w).toNat
      = T.pending.size - min (Spec.Tcp.dist S.ack T.sndUna) T.sent := by
    rw [UInt16.toNat_sub]; omega
  have hs1 : (w.r.sent - ackAcked w).toNat = T.sent - min (Spec.Tcp.dist S.ack T.sndUna) T.sent := by
    rw [UInt16.toNat_sub]; omega
  obtain ⟨z1, z2, _⟩ := shiftIn_spec w.pd (ackAcked w).toNat (w.r.pend_len - ackAcked w).toNat (by omega)
  refine ⟨t.st, t.rip, t.rport, ha, t.nxt, t.rcv, ?_, hs1, t.fin, t.peer, t.our, t.lw, ?_, rfl, t.tw, t.idle,
    t.cr, ?_, ?_, ?_, ?_, t.hour⟩
  · show (w.r.pend_len - ackAcked w).toNat = (T.pending.extract _ _).size
    rw [ByteArray.size_extract, hp1]; omega
  · simp only [ackR1, ackT]
    rw [ha, t.nxt]
    cases (S.ack != T.sndNxt) <;> rfl
  · show (ackPd w).extract 0 (T.pending.extract _ _).size = T.pending.extract _ _
    apply Bytes.ext_get
    · rw [ByteArray.size_extract, ByteArray.size_extract]
      show min _ (shiftIn _ _ _).size - 0 = _
      rw [z1]; omega
    · intro j hj
      rw [ByteArray.size_extract, ByteArray.size_extract] at hj
      rw [get_extract _ 0 _ j (by rw [ByteArray.size_extract]; omega)
          (by rw [ByteArray.size_extract]; show _ ≤ (shiftIn _ _ _).size; rw [z1]; omega),
        get_extract _ _ _ j (by omega) (Nat.le_refl _), Nat.zero_add]
      show Bytes.get (shiftIn _ _ _) j = _
      rw [z2 j (by omega), hA, ← t.pend, get_extract _ 0 _ _ (by omega) (by omega), Nat.zero_add, Nat.add_comm]
  · show (shiftIn _ _ _).size = 256
    rw [z1]; exact hsz
  · show T.sent - _ ≤ (T.pending.extract _ _).size
    rw [ByteArray.size_extract]; omega
  · show (T.pending.extract _ _).size ≤ T.cap
    rw [ByteArray.size_extract]; omega

theorem TcbRel.setSt {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (s : Spec.Tcp.St) :
    TcbRel { r with st := UInt8.ofNat s.code } pd { T with st := s } :=
  ⟨rfl, h.rip, h.rport, h.una, h.nxt, h.rcv, h.plen, h.sent, h.fin, h.peer, h.our, h.lw, h.rt, h.re, h.tw,
    h.idle, h.cr, h.pend, h.pdsz, h.hsent, h.hcap, h.hour⟩

theorem TcbRel.setTw {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (n : UInt8) :
    TcbRel { r with tw_timer := n } pd { T with twTimer := n.toNat } :=
  ⟨h.st, h.rip, h.rport, h.una, h.nxt, h.rcv, h.plen, h.sent, h.fin, h.peer, h.our, h.lw, h.rt, h.re, rfl,
    h.idle, h.cr, h.pend, h.pdsz, h.hsent, h.hcap, h.hour⟩

/-- A closed connection: LISTEN on both sides. -/
theorem reset_rel (pd : ByteArray) (hsz : pd.size = 256) : TcbRel RawTcb.reset pd {} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, extract_empty pd 0, hsz,
    Nat.le_refl _, Nat.zero_le _, by decide⟩

/-- **`ack_input` is `Spec.Tcp.ackInput`.** -/
theorem ack_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (Q : Bool → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (ackW w ourIp).2 c' ev0 id0 → ((ackW w ourIp).1 = true → c'.diag = c.diag) →
      Q (ackW w ourIp).1 c') :
    wp (Spec.Tcp.ackInput S) Q c := by
  have t := h.tcb
  have hD := ackD_eq w c.tcb S t hs.ack
  have hO : (w.r.snd_nxt - w.r.snd_una).toNat = Spec.Tcp.dist c.tcb.sndNxt c.tcb.sndUna := by
    simp only [Spec.Tcp.dist, t.nxt, t.una]
  have hA := ackAcked_eq w c.tcb S t hs.ack
  have c1 : (w.r.snd_nxt - w.r.snd_una < ackD w)
      ↔ Spec.Tcp.dist S.ack c.tcb.sndUna > Spec.Tcp.dist c.tcb.sndNxt c.tcb.sndUna := by
    rw [UInt32.lt_iff_toNat_lt, hD, hO]
  have c2 : (ackD w == 0) = true ↔ (Spec.Tcp.dist S.ack c.tcb.sndUna == 0) = true := by
    rw [beq_iff_eq, beq_iff_eq, ← hD, ← UInt32.toNat_inj]; exact Iff.rfl
  have c3 : ((ackAcked w).toUInt32 < ackD w)
      ↔ Spec.Tcp.dist S.ack c.tcb.sndUna > min (Spec.Tcp.dist S.ack c.tcb.sndUna) c.tcb.sent := by
    rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32, hA, hD]
  simp only [Spec.Tcp.ackInput, wp_bind, wp_get, wp_ite, wp_modify, wp_pure]
  split
  · rename_i x
    rw [ackW_unsent w ourIp (c1.mpr x)] at hQ
    rw [← t.nxt]
    have z : (0 : UInt16).toNat = 0 := rfl
    exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendSeg_sim ourIp w c ev0 id0 h hd 16 w.r.snd_nxt 0 0 false .empty
      none (by rw [z]; exact (extract_empty w.pd 0).symm) rfl) _) (fun y => absurd y (by simp))
  · rename_i x
    have x' := fun y => x (c1.mp y)
    split
    · rename_i y
      rw [ackW_zero w ourIp x' (c2.mpr y)] at hQ
      exact hQ c h (fun _ => rfl)
    · rename_i y
      have y' := fun z => y (c2.mp z)
      rw [ackW_adv w ourIp x' y'] at hQ
      have hrel := ack_rel w c.tcb S t hs.ack
      split
      · rename_i x3
        rw [if_pos (c3.mpr x3)] at hQ
        generalize hst : c.tcb.st = st0
        have hn : w.r.st = UInt8.ofNat st0.code := by rw [t.st, hst]
        rw [hn] at hQ
        revert hQ
        cases st0 <;> intro hQ <;> simp only [wp_bind, wp_modify, wp_pure, wp_closeConn] <;>
          simp (config := { decide := true }) only [if_true, if_false] at hQ <;> (try rw [← hst]) <;>
          first
          | exact hQ _ ⟨hrel, h.iss, h.ip, h.id, h.evs, h.mss⟩ (fun _ => rfl)
          | exact hQ _ ⟨hrel.setSt .finWait2, h.iss, h.ip, h.id, h.evs, h.mss⟩ (fun _ => rfl)
          | exact hQ _ ⟨(hrel.setSt .timeWait).setTw 20, h.iss, h.ip, h.id, h.evs, h.mss⟩ (fun _ => rfl)
          | exact hQ _ ⟨reset_rel _ hrel.pdsz, h.iss, h.ip, h.id, h.evs, h.mss⟩ (fun y => absurd y (by simp))
      · rename_i x3
        rw [if_neg (fun z => x3 (c3.mp z))] at hQ
        exact hQ _ ⟨hrel, h.iss, h.ip, h.id, h.evs, h.mss⟩ (fun _ => rfl)

/-! ## The FIN -/

theorem segFinW_no (w : TW) (fin i a : Bool)
    (hc : ¬ (fin && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) = true) :
    segFinW w fin i a = (w, a) := by
  show (if (fin && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) = true then _ else _) = _
  rw [if_neg hc]

theorem segFinW_fin (w : TW) (fin i a : Bool)
    (hc : (fin && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) = true) :
    segFinW w fin i a =
      if w.r.st == 2 then ({ w with r := { w.r with st := 3, rcv_nxt := w.r.rcv_nxt + 1 } }, true)
      else if w.r.st == 5 then ({ w with r := { w.r with st := 7, rcv_nxt := w.r.rcv_nxt + 1 } }, true)
      else if w.r.st == 6 then
        ({ w with r := { w.r with st := 8, tw_timer := 20, rcv_nxt := w.r.rcv_nxt + 1 } }, true)
      else (w, a) := by
  show (if (fin && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) = true then _ else _) = _
  rw [if_pos hc]

theorem TcbRel.finSt {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (s : Spec.Tcp.St) :
    TcbRel { r with st := UInt8.ofNat s.code, rcv_nxt := r.rcv_nxt + 1 } pd
      { T with st := s, rcvNxt := T.rcvNxt + 1 } :=
  ⟨rfl, h.rip, h.rport, h.una, h.nxt, by show r.rcv_nxt + 1 = T.rcvNxt + 1; rw [h.rcv], h.plen, h.sent, h.fin,
    h.peer, h.our, h.lw, h.rt, h.re, h.tw, h.idle, h.cr, h.pend, h.pdsz, h.hsent, h.hcap, h.hour⟩

theorem TcbRel.finStTw {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) (s : Spec.Tcp.St)
    (n : UInt8) :
    TcbRel { r with st := UInt8.ofNat s.code, rcv_nxt := r.rcv_nxt + 1, tw_timer := n } pd
      { T with st := s, rcvNxt := T.rcvNxt + 1, twTimer := n.toNat } :=
  ⟨rfl, h.rip, h.rport, h.una, h.nxt, by show r.rcv_nxt + 1 = T.rcvNxt + 1; rw [h.rcv], h.plen, h.sent, h.fin,
    h.peer, h.our, h.lw, h.rt, h.re, rfl, h.idle, h.cr, h.pend, h.pdsz, h.hsent, h.hcap, h.hour⟩

/-- **The FIN stage is `finStep`.** -/
theorem fin_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (S : Spec.Tcp.Seg) (hs : SegRel w.sg w.b S) (a i : Bool)
    (k : Bool → Spec.Tcp.TcpM Unit) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hk : ∀ c', Sim ourIp (segFinW w (w.sg.flags &&& 1 != 0) i a).1 c' ev0 id0 → c'.diag = c.diag →
      wp (k (segFinW w (w.sg.flags &&& 1 != 0) i a).2) Q c') :
    wp (Spec.Tcp.finStep S a i k) Q c := by
  have t := h.tcb
  have f1 : (w.sg.flags &&& 1 != 0) = Spec.Tcp.has S.flags Spec.Tcp.FIN := hs.has 1
  have hdl : w.sg.dlen.toUInt32 = UInt32.ofNat S.data.size := by
    apply UInt32.toNat_inj.mp
    rw [UInt16.toNat_toUInt32, UInt32.toNat_ofNat', hs.size_data]
    have := w.sg.dlen.toNat_lt; omega
  have hcond : ((w.sg.flags &&& 1 != 0) && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt)))
      = (Spec.Tcp.has S.flags Spec.Tcp.FIN && i && S.seq + UInt32.ofNat S.data.size == c.tcb.rcvNxt) := by
    rw [f1, hs.seq, t.rcv, hdl, Bool.and_assoc]
  simp only [Spec.Tcp.finStep, wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map]
  split
  · rename_i x
    rw [segFinW_fin w _ i a (hcond.trans x)] at hk
    generalize hst : c.tcb.st = st0
    have hn : w.r.st = UInt8.ofNat st0.code := by rw [t.st, hst]
    rw [hn] at hk
    revert hk
    cases st0 <;> intro hk <;> simp only [wp_bind, wp_modify] <;>
      simp (config := { decide := true }) only [if_true, if_false] at hk <;>
      first
      | exact hk c h rfl
      | exact hk _ ⟨t.finSt .closeWait, h.iss, h.ip, h.id, h.evs, h.mss⟩ rfl
      | exact hk _ ⟨t.finSt .closing, h.iss, h.ip, h.id, h.evs, h.mss⟩ rfl
      | exact hk _ ⟨t.finStTw .timeWait 20, h.iss, h.ip, h.id, h.evs, h.mss⟩ rfl
  · rename_i x
    rw [segFinW_no w _ i a (fun y => x (hcond.symm.trans y))] at hk
    exact hk c h rfl

/-! ## Data -/

/-- The bytes of the segment not yet received, and how many of them fit the window. -/
def dFresh (w : TW) : UInt16 :=
  if w.r.rcv_nxt - w.sg.seq < w.sg.dlen.toUInt32 then w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16 else 0
def dTake (w : TW) : UInt16 := if w.r.wnd < dFresh w then w.r.wnd else dFresh w

def dW1 (w : TW) : TW :=
  if w.r.st == 2 then
    { w with pd := dataPd w (dTake w).toNat, r := { w.r with pend_len := w.r.pend_len + dTake w } }
  else w
/-- The state after the data stage took `dTake` bytes. -/
def dW (w : TW) : TW := { dW1 w with r := { (dW1 w).r with rcv_nxt := w.r.rcv_nxt + (dTake w).toUInt32 } }

theorem dW_iss (w : TW) : (dW w).iss = w.iss := by unfold dW dW1; split <;> rfl
theorem dW_id (w : TW) : (dW w).id = w.id := by unfold dW dW1; split <;> rfl
theorem dW_evs (w : TW) : (dW w).evs = w.evs := by unfold dW dW1; split <;> rfl
theorem dW_sg (w : TW) : (dW w).sg = w.sg := by unfold dW dW1; split <;> rfl
theorem dW_b (w : TW) : (dW w).b = w.b := by unfold dW dW1; split <;> rfl

theorem segDataW_none (w : TW)
    (hc : ¬ (0 < w.sg.dlen ∧ (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true)) :
    segDataW w = (w, false, true) := by
  show (if 0 < w.sg.dlen then (if (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true then _ else _) else _) = _
  by_cases h0 : 0 < w.sg.dlen
  · rw [if_pos h0, if_neg (fun y => hc ⟨h0, y⟩)]
  · rw [if_neg h0]

theorem segDataW_take (w : TW) (h0 : 0 < w.sg.dlen)
    (h1 : (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true) :
    segDataW w = (dW w, true, dTake w == dFresh w) := by
  show (if 0 < w.sg.dlen then (if (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true then _ else _) else _) = _
  rw [if_pos h0, if_pos h1]
  rfl

theorem dFresh_eq (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (hs : SegRel w.sg w.b S) : (dFresh w).toNat = S.data.size - Spec.Tcp.dist T.rcvNxt S.seq := by
  have hdl := hs.size_data
  have hsk : (w.r.rcv_nxt - w.sg.seq).toNat = Spec.Tcp.dist T.rcvNxt S.seq := by
    simp only [Spec.Tcp.dist, t.rcv, hs.seq]
  have := w.sg.dlen.toNat_lt
  simp only [dFresh]
  split
  · rename_i x
    rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32] at x
    rw [UInt16.toNat_sub, UInt32.toNat_toUInt16]; omega
  · rename_i x
    rw [UInt32.lt_iff_toNat_lt, UInt16.toNat_toUInt32] at x
    show (0 : UInt16).toNat = _
    have z : (0 : UInt16).toNat = 0 := rfl
    omega

theorem dTake_eq (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (hs : SegRel w.sg w.b S) :
    (dTake w).toNat = min (S.data.size - Spec.Tcp.dist T.rcvNxt S.seq) T.wnd := by
  have hF := dFresh_eq w T S t hs
  have hw := t.wnd_eq
  simp only [dTake]
  split
  · rename_i x; rw [UInt16.lt_iff_toNat_lt] at x; omega
  · rename_i x; rw [UInt16.lt_iff_toNat_lt] at x; omega

/-- The data taken joins the echo buffer on both sides. -/
theorem data_rel (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (hs : SegRel w.sg w.b S) (hb : w.b.size < 65536) :
    TcbRel (dW w).r (dW w).pd { T with
      rcvNxt := T.rcvNxt
        + UInt32.ofNat (min (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).size T.wnd),
      pending :=
        if (T.st == Spec.Tcp.St.established) = true then
          T.pending ++ (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).extract 0
            (min (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).size T.wnd)
        else T.pending } := by
  have hdl := hs.size_data
  have hsk : (w.r.rcv_nxt - w.sg.seq).toNat = Spec.Tcp.dist T.rcvNxt S.seq := by
    simp only [Spec.Tcp.dist, t.rcv, hs.seq]
  have hfs : (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).size
      = S.data.size - Spec.Tcp.dist T.rcvNxt S.seq := by rw [ByteArray.size_extract]; omega
  have hF := dFresh_eq w T S t hs
  have hT := dTake_eq w T S t hs
  have bT := (dTake w).toNat_lt
  have hrcv : w.r.rcv_nxt + (dTake w).toUInt32 = T.rcvNxt
      + UInt32.ofNat (min (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).size T.wnd) := by
    rw [t.rcv, hfs]
    congr 1
    apply UInt32.toNat_inj.mp
    rw [UInt16.toNat_toUInt32, hT, UInt32.toNat_ofNat']; omega
  have e2 : (w.r.st == 2) = (T.st == Spec.Tcp.St.established) := t.st_beq .established
  rw [hfs]
  rw [hfs] at hrcv
  cases hE : (T.st == Spec.Tcp.St.established)
  · have hW : dW w = { w with r := { w.r with rcv_nxt := w.r.rcv_nxt + (dTake w).toUInt32 } } := by
      simp only [dW, dW1, e2, hE, Bool.false_eq_true, if_false]
    rw [hW]
    exact ⟨t.st, t.rip, t.rport, t.una, t.nxt, hrcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, t.rt, t.re,
      t.tw, t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩
  · have hW : dW w = { w with pd := dataPd w (dTake w).toNat, r :=
        { w.r with pend_len := w.r.pend_len + dTake w, rcv_nxt := w.r.rcv_nxt + (dTake w).toUInt32 } } := by
      simp only [dW, dW1, e2, hE, if_true]
    rw [hW]
    have hwn : T.wnd = T.cap - T.pending.size := rfl
    have hpl := t.plen; have hcap := t.hcap; have hsz := t.pdsz; have hour := t.hour; have hse := t.hsent
    have hc : T.cap ≤ 256 := by simp only [Spec.Tcp.Tcb.cap]; omega
    have hfit := hs.fits
    obtain ⟨z1, z2, z3⟩ := cpIn_spec w.pd w.b w.r.pend_len.toNat
      (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat (dTake w).toNat (by omega)
    have hPs : (T.pending ++ (S.data.extract (Spec.Tcp.dist T.rcvNxt S.seq) S.data.size).extract 0
        (min (S.data.size - Spec.Tcp.dist T.rcvNxt S.seq) T.wnd)).size
        = T.pending.size + (dTake w).toNat := by
      rw [ByteArray.size_append, ByteArray.size_extract, hfs]; omega
    refine ⟨t.st, t.rip, t.rport, t.una, t.nxt, hrcv, ?_, t.sent, t.fin, t.peer, t.our, t.lw, t.rt, t.re, t.tw,
      t.idle, t.cr, ?_, ?_, ?_, ?_, t.hour⟩
    · show (w.r.pend_len + dTake w).toNat = _
      rw [if_pos rfl, hPs, UInt16.toNat_add]; omega
    · show (dataPd w (dTake w).toNat).extract 0 _ = _
      rw [if_pos rfl]
      apply Bytes.ext_get
      · rw [ByteArray.size_extract, hPs]
        show min _ (cpIn _ _ _ _ _).size - 0 = _
        rw [z1]; omega
      · intro j hj
        rw [ByteArray.size_extract, hPs] at hj
        have hj' : j < T.pending.size + (dTake w).toNat := by omega
        rw [get_extract _ 0 _ j (by rw [hPs]; omega)
          (by rw [hPs]; show _ ≤ (cpIn _ _ _ _ _).size; rw [z1]; omega), Nat.zero_add, Bytes.get_append]
        show Bytes.get (cpIn _ _ _ _ _) j = _
        by_cases hlt : j < T.pending.size
        · rw [if_pos hlt, z3 j (Or.inl (by omega)), ← t.pend, get_extract _ 0 _ j (by omega) (by omega),
            Nat.zero_add]
        · rw [if_neg hlt]
          have hpos : 0 < (dTake w).toNat := by omega
          have hskl : Spec.Tcp.dist T.rcvNxt S.seq < S.data.size := by omega
          have hoff : (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat
              = w.sg.doff.toNat + Spec.Tcp.dist T.rcvNxt S.seq := by
            rw [UInt16.toNat_add, UInt32.toNat_toUInt16, hsk]; omega
          have e : j = w.r.pend_len.toNat + (j - T.pending.size) := by omega
          conv => lhs; rw [e]
          rw [z2 (j - T.pending.size) (by omega), hoff,
            get_extract _ 0 _ _ (by omega) (by rw [hfs]; omega), Nat.zero_add,
            get_extract _ _ _ _ (by omega) (Nat.le_refl _), hs.data,
            get_extract _ _ _ _ (by omega) hfit]
          congr 1; omega
    · show (cpIn _ _ _ _ _).size = 256
      rw [z1]; exact hsz
    · show T.sent ≤ _
      rw [if_pos rfl, hPs]; omega
    · show _ ≤ T.cap
      rw [if_pos rfl, hPs]; omega

/-! ## Data, FIN, output: the tail of `tcp_segment` -/

theorem beq_congr_iff {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a b : α} {c d : β}
    (h : a = b ↔ c = d) : (a == b) = (c == d) := by
  by_cases x : a = b
  · rw [beq_iff_eq.mpr x, beq_iff_eq.mpr (h.mp x)]
  · rw [beq_eq_false_iff_ne.mpr x, beq_eq_false_iff_ne.mpr (fun y => x (h.mpr y))]

/-- The Spec's `tcb` line is not compared. -/
theorem logTcb_sim {ourIp : UInt32} {w : TW} {c : Spec.Tcp.Ctx} {ev0 : List Trace.Event} {id0 : UInt16}
    (h : Sim ourIp w c ev0 id0) (e : Trace.Event) (he : keep e = false) :
    Sim ourIp w { c with diag := c.diag.push e } ev0 id0 := by
  refine ⟨h.tcb, h.iss, h.ip, h.id, ?_, h.mss⟩
  have : (c.diag.push e).toList.filter keep = c.diag.toList.filter keep := by
    rw [Array.toList_push, List.filter_append, List.filter_cons, he]
    simp
  show w.evs.filter keep = _ ++ _ ++ (c.diag.push _).toList.filter keep
  rw [this]; exact h.evs

theorem segTailW_oo (w : TW) (ourIp : UInt32)
    (hc : ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
      && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq)) = true) :
    segTailW w ourIp = dropW (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false) "out-of-order" := by
  show (if ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
      && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq)) = true then _ else _) = _
  rw [if_pos hc]

theorem segTailW_in (w : TW) (ourIp : UInt32)
    (hc : ¬ ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
      && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq)) = true) :
    segTailW w ourIp
      = outputW (segFinW (segDataW w).1 (w.sg.flags &&& 1 != 0) (segDataW w).2.2 (segDataW w).2.1).1 ourIp
          (segFinW (segDataW w).1 (w.sg.flags &&& 1 != 0) (segDataW w).2.2 (segDataW w).2.1).2 := by
  show (if ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
      && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq)) = true then _ else _) = _
  rw [if_neg hc]

/-- **Steps 6 to 8 of `tcp_segment` are the Spec's** (`dataStep`, `finStep`, `output`). -/
theorem tail_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hb : w.b.size < 65536) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (segTailW w ourIp) c' ev0 id0 → Q () c') :
    wp (Spec.Tcp.dataStep S fun ackNow inOrder => Spec.Tcp.finStep S ackNow inOrder fun ackNow => do
      Spec.Tcp.output ackNow
      Spec.Tcp.logTcb) Q c := by
  have t := h.tcb
  have hdl := hs.size_data
  have hsk : (w.r.rcv_nxt - w.sg.seq).toNat = Spec.Tcp.dist c.tcb.rcvNxt S.seq := by
    simp only [Spec.Tcp.dist, t.rcv, hs.seq]
  have z0 : (0 : UInt16).toNat = 0 := rfl
  have hpos : (0 < w.sg.dlen) ↔ S.data.size > 0 := by
    rw [UInt16.lt_iff_toNat_lt, z0, hdl]
  have hge : decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq) = !Spec.Tcp.seqGe c.tcb.rcvNxt S.seq := by
    have z : (2147483648 : UInt32).toNat = 2147483648 := rfl
    cases hq : Spec.Tcp.seqGe c.tcb.rcvNxt S.seq
    · have : ¬ Spec.Tcp.dist c.tcb.rcvNxt S.seq < 0x80000000 := by simpa [Spec.Tcp.seqGe] using hq
      exact decide_eq_true (by rw [UInt32.le_iff_toNat_le, z, hsk]; omega)
    · have : Spec.Tcp.dist c.tcb.rcvNxt S.seq < 0x80000000 := by simpa [Spec.Tcp.seqGe] using hq
      exact decide_eq_false (by rw [UInt32.le_iff_toNat_le, z, hsk]; omega)
  have hoo : ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
        && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq))
      = ((decide (S.data.size > 0) || Spec.Tcp.has S.flags Spec.Tcp.FIN)
        && !Spec.Tcp.seqGe c.tcb.rcvNxt S.seq) := by
    rw [hge, show (w.sg.flags &&& 1 != 0) = Spec.Tcp.has S.flags Spec.Tcp.FIN from hs.has 1,
      decide_eq_decide.mpr hpos]
  -- the FIN stage and `output`, from any state the data stage leaves
  have hfin : ∀ (w1 : TW) (c1 : Spec.Tcp.Ctx) (a i : Bool), Sim ourIp w1 c1 ev0 id0 → c1.diag = c.diag →
      w1.sg = w.sg → w1.b = w.b →
      (∀ c', Sim ourIp (outputW (segFinW w1 (w.sg.flags &&& 1 != 0) i a).1 ourIp
        (segFinW w1 (w.sg.flags &&& 1 != 0) i a).2) c' ev0 id0 → Q () c') →
      wp (Spec.Tcp.finStep S a i fun ackNow => do Spec.Tcp.output ackNow; Spec.Tcp.logTcb) Q c1 := by
    intro w1 c1 a i h1 hd1 esg eb hQ1
    rw [← esg] at hQ1
    refine fin_wp ourIp w1 c1 ev0 id0 h1 S (by rw [esg, eb]; exact hs) a i _ Q ?_
    intro c2 h2 hd2
    rw [wp_bind]
    refine output_wp ourIp _ c2 ev0 id0 h2 (by rw [hd2, hd1]; exact hd) _ _ ?_
    intro c3 h3 _
    rw [Spec.Tcp.wp_logTcb]
    exact hQ1 _ (logTcb_sim h3 _ rfl)
  simp only [Spec.Tcp.dataStep, wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map]
  split
  · rename_i x
    rw [segTailW_oo w ourIp (hoo.trans x)] at hQ
    rw [← t.nxt]
    simp only [Spec.Tcp.wp_logTcb]
    exact hQ _ (logTcb_sim (drop_sim ourIp _ _ ev0 id0 (sendSeg_sim ourIp w c ev0 id0 h hd 16 w.r.snd_nxt 0 0
      false .empty none (by rw [z0]; exact (extract_empty w.pd 0).symm) rfl) _) _ rfl)
  · rename_i x
    rw [segTailW_in w ourIp (fun y => x (hoo.symm.trans y))] at hQ
    have e2 : (w.r.st == 2) = (c.tcb.st == Spec.Tcp.St.established) := t.st_beq .established
    have e5 : (w.r.st == 5) = (c.tcb.st == Spec.Tcp.St.finWait1) := t.st_beq .finWait1
    have e6 : (w.r.st == 6) = (c.tcb.st == Spec.Tcp.St.finWait2) := t.st_beq .finWait2
    have hstc : (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6))
        = (c.tcb.st == Spec.Tcp.St.established || c.tcb.st == Spec.Tcp.St.finWait1
          || c.tcb.st == Spec.Tcp.St.finWait2) := by rw [e2, e5, e6, Bool.or_assoc]
    split
    · rename_i y
      split
      · rename_i u
        rw [segDataW_take w (hpos.mpr y) (hstc.trans u)] at hQ
        have hF := dFresh_eq w c.tcb S t hs
        have hT := dTake_eq w c.tcb S t hs
        have hfs : (S.data.extract (Spec.Tcp.dist c.tcb.rcvNxt S.seq) S.data.size).size
            = S.data.size - Spec.Tcp.dist c.tcb.rcvNxt S.seq := by rw [ByteArray.size_extract]; omega
        have hbq : (min (S.data.extract (Spec.Tcp.dist c.tcb.rcvNxt S.seq) S.data.size).size c.tcb.wnd
              == (S.data.extract (Spec.Tcp.dist c.tcb.rcvNxt S.seq) S.data.size).size)
            = (dTake w == dFresh w) := by
          apply beq_congr_iff
          rw [hfs, ← UInt16.toNat_inj, hT, hF]
        rw [hbq]
        exact hfin (dW w) _ true _ ⟨data_rel w c.tcb S t hs hb, by rw [dW_iss]; exact h.iss, h.ip,
          by rw [dW_id]; exact h.id, by rw [dW_evs]; exact h.evs, h.mss⟩ rfl (dW_sg w) (dW_b w) hQ
      · rename_i u
        rw [segDataW_none w (fun q => u (hstc.symm.trans q.2))] at hQ
        exact hfin w c false true h rfl rfl rfl hQ
    · rename_i y
      rw [segDataW_none w (fun q => y (hpos.mp q.1))] at hQ
      exact hfin w c false true h rfl rfl rfl hQ

/-! ## `tcp_segment` against `Spec.Tcp.input` -/

theorem SegRel.hasNot {s : RawSeg} {b : ByteArray} {S : Spec.Tcp.Seg} (h : SegRel s b S) (f : UInt8) :
    (s.flags &&& f == 0) = !Spec.Tcp.has S.flags f := by
  rw [← h.has f]
  show _ = !(!(s.flags &&& f == 0))
  rw [Bool.not_not]

/-- A line the comparison ignores, on the stack's side. -/
theorem Sim.wEv {ourIp : UInt32} {w : TW} {c : Spec.Tcp.Ctx} {ev0 : List Trace.Event} {id0 : UInt16}
    (h : Sim ourIp w c ev0 id0) (e : Trace.Event) (he : keep e = false) :
    Sim ourIp { w with evs := w.evs ++ [e] } c ev0 id0 := by
  refine ⟨h.tcb, h.iss, h.ip, h.id, ?_, h.mss⟩
  show (w.evs ++ [e]).filter keep = _
  rw [List.filter_append, List.filter_cons, he]
  simp only [Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
  exact h.evs

theorem ackW_keep (w : TW) (ourIp : UInt32) (hok : (ackW w ourIp).1 = true) :
    (ackW w ourIp).2.sg = w.sg ∧ (ackW w ourIp).2.b = w.b := by
  by_cases h1 : w.r.snd_nxt - w.r.snd_una < ackD w
  · rw [ackW_unsent w ourIp h1] at hok; exact absurd hok (by simp)
  · by_cases h2 : (ackD w == 0) = true
    · rw [ackW_zero w ourIp h1 h2]; exact ⟨rfl, rfl⟩
    · rw [ackW_adv w ourIp h1 h2]
      repeat' split
      all_goals exact ⟨rfl, rfl⟩

theorem emitW_pd (w : TW) (ourIp dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8)
    (wn : UInt16) (m : Bool) (so n : UInt16) : (emitW w ourIp dst sport dport seq ack flags wn m so n).pd = w.pd := by
  simp only [emitW]

/-- A segment of the connection that is not acceptable. -/
theorem na_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (segNaW w ourIp) c' ev0 id0 → Q () c') :
    if Spec.Tcp.has S.flags Spec.Tcp.RST = true then
      wp (Spec.Tcp.dropR "rst-out-of-window") (fun _ c' => Q () c') c
    else
      if (c.tcb.st == Spec.Tcp.St.synRcvd && Spec.Tcp.has S.flags Spec.Tcp.SYN
          && !Spec.Tcp.has S.flags Spec.Tcp.ACK && S.seq + 1 == c.tcb.rcvNxt) = true then
        wp Spec.Tcp.sendSynAck (fun _ c' => wp (Spec.Tcp.dropR "duplicate-syn") (fun _ c' => Q () c') c') c
      else
        wp (Spec.Tcp.sendSeg Spec.Tcp.ACK c.tcb.sndNxt)
          (fun _ c' => wp (Spec.Tcp.dropR "out-of-window") (fun _ c' => Q () c') c') c := by
  have t := h.tcb
  have f4 : (w.sg.flags &&& 4 != 0) = Spec.Tcp.has S.flags Spec.Tcp.RST := hs.has 4
  have f2 : (w.sg.flags &&& 2 != 0) = Spec.Tcp.has S.flags Spec.Tcp.SYN := hs.has 2
  have f16 : (w.sg.flags &&& 16 == 0) = !Spec.Tcp.has S.flags Spec.Tcp.ACK := hs.hasNot 16
  have e1 : (w.r.st == 1) = (c.tcb.st == Spec.Tcp.St.synRcvd) := t.st_beq .synRcvd
  have hdup : (w.r.st == 1 && (w.sg.flags &&& 2 != 0 && (w.sg.flags &&& 16 == 0 && w.sg.seq + 1 == w.r.rcv_nxt)))
      = (c.tcb.st == Spec.Tcp.St.synRcvd && Spec.Tcp.has S.flags Spec.Tcp.SYN
          && !Spec.Tcp.has S.flags Spec.Tcp.ACK && S.seq + 1 == c.tcb.rcvNxt) := by
    rw [e1, f2, f16, hs.seq, t.rcv]; simp only [Bool.and_assoc]
  rw [segNaW, f4, hdup] at hQ
  have z0 : (0 : UInt16).toNat = 0 := rfl
  split
  · rename_i x; rw [if_pos x] at hQ; exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
  · rename_i x; rw [if_neg x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ
      exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendSynAck_sim ourIp w c ev0 id0 h hd) _)
    · rename_i y; rw [if_neg y] at hQ
      rw [← t.nxt]
      exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendSeg_sim ourIp w c ev0 id0 h hd 16 w.r.snd_nxt 0 0 false .empty
        none (by rw [z0]; exact (extract_empty w.pd 0).symm) rfl) _)

/-- Step 5 (the ACK) and what follows it. -/
theorem ackStep_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src : UInt32) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hsrc : w.sg.src = src) (hb : w.b.size < 65536) (T0 : Spec.Tcp.Tcb)
    (h0s : T0.st = c.tcb.st) (h0n : T0.sndNxt = c.tcb.sndNxt) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (match segAckW w ourIp with | .error w' => w' | .ok w1 => segTailW w1 ourIp) c' ev0
      id0 → Q () c') :
    wp (Spec.Tcp.ackStep src S T0 (Spec.Tcp.dataStep S fun ackNow inOrder =>
      Spec.Tcp.finStep S ackNow inOrder fun ackNow => do
        Spec.Tcp.output ackNow
        Spec.Tcp.logTcb)) Q c := by
  have t := h.tcb
  have e1 : (w.r.st == 1) = (c.tcb.st == Spec.Tcp.St.synRcvd) := t.st_beq .synRcvd
  have ea : (w.sg.ack != w.r.snd_nxt) = (S.ack != c.tcb.sndNxt) := by rw [hs.ack, t.nxt]
  simp only [Spec.Tcp.ackStep, wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map, h0s, h0n]
  rw [segAckW, e1, ea] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ
      exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendReset_sim ourIp w c ev0 id0 h hd src S hs hsrc) _)
    · rename_i y; rw [if_neg y] at hQ
      exact tail_wp ourIp { w with r := { w.r with st := 2, snd_una := w.sg.ack, rt_timer := 0, retries := 0 } }
        { c with tcb := { c.tcb with st := .established, sndUna := S.ack, rtTimer := 0, retries := 0 } } ev0 id0 ⟨⟨rfl, t.rip, t.rport, hs.ack, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, rfl, rfl,
          t.tw, t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩, h.iss, h.ip, h.id, h.evs, h.mss⟩ hd S hs hb
        Q hQ
  · rename_i x; rw [if_neg x] at hQ
    refine ack_wp ourIp w c ev0 id0 h hd S hs _ ?_
    intro c' hs' hdg
    cases hb1 : (ackW w ourIp).1
    · rw [hb1] at hQ
      simp only [Bool.not_false, if_true, Spec.Tcp.wp_logTcb]
      exact hQ _ (logTcb_sim hs' _ rfl)
    · rw [hb1] at hQ
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      obtain ⟨k1, k2⟩ := ackW_keep w ourIp hb1
      exact tail_wp ourIp (ackW w ourIp).2 c' ev0 id0 hs' (by rw [hdg hb1]; exact hd) S
        (by rw [k1, k2]; exact hs) (by rw [k2]; exact hb) Q hQ

/-- Steps 2 to 8 for an acceptable segment. -/
theorem conn_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src : UInt32) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hsrc : w.sg.src = src) (hb : w.b.size < 65536) (T0 : Spec.Tcp.Tcb)
    (h0s : T0.st = c.tcb.st) (h0n : T0.sndNxt = c.tcb.sndNxt) (h0i : T0.rip = c.tcb.rip)
    (h0p : T0.rport = c.tcb.rport) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (segAccW w ourIp) c' ev0 id0 → Q () c') :
    wp (Spec.Tcp.connStep src S T0) Q c := by
  have t := h.tcb
  have f4 : (w.sg.flags &&& 4 != 0) = Spec.Tcp.has S.flags Spec.Tcp.RST := hs.has 4
  have f2 : (w.sg.flags &&& 2 != 0) = Spec.Tcp.has S.flags Spec.Tcp.SYN := hs.has 2
  have f16 : (w.sg.flags &&& 16 == 0) = !Spec.Tcp.has S.flags Spec.Tcp.ACK := hs.hasNot 16
  unfold Spec.Tcp.connStep
  simp only [wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map]
  rw [segAccW, f4, f2, f16] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ
    exact hQ _ (logTcb_sim (logTcb_sim (Sim.wEv (h.setTcb RawTcb.reset {} (reset_rel _ t.pdsz))
      (.note "connection-reset-by-peer 0") rfl) (.note "connection reset by peer") rfl) _ rfl)
  · rename_i x; rw [if_neg x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ
      rw [h0i, h0p, h0n, ← t.rip, ← t.rport, ← t.nxt]
      have he := emit_sim ourIp w c ev0 id0 h hd w.r.rip 7 w.r.rport w.r.snd_nxt 0 4 0 false 0 0
        { sport := Spec.echoPort, dport := w.r.rport, seq := w.r.snd_nxt, ack := 0, flags := Spec.Tcp.RST, wnd := 0 }
        (by
          show _ = Spec.Tcp.Seg.mk _ _ _ _ _ _ none (w.pd.extract 0 (0 + 0))
          rw [extract_empty w.pd 0]; rfl)
      exact hQ _ (logTcb_sim (drop_sim ourIp _ _ ev0 id0 (he.setTcb RawTcb.reset {} (reset_rel _ (by rw [emitW_pd]; exact t.pdsz))) _) _ rfl)
    · rename_i y; rw [if_neg y] at hQ
      split
      · rename_i u; rw [if_pos u] at hQ; exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
      · rename_i u; rw [if_neg u] at hQ
        exact ackStep_wp ourIp w c ev0 id0 h hd src S hs hsrc hb T0 h0s h0n Q hQ

/-- **`tcp_segment` is `Spec.Tcp.input`**: from states that agree, the
Spec's step ends in a state the stack's function simulates, the
transmissions and drops of the two being the same. -/
theorem segment_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src : UInt32) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (hsrc : w.sg.src = src) (hb : w.b.size < 65536)
    (Q : Unit → Spec.Tcp.Ctx → Prop) (hQ : ∀ c', Sim ourIp (segW w ourIp) c' ev0 id0 → Q () c') :
    wp (Spec.Tcp.input src S) Q c := by
  have t := h.tcb
  have e0 : (w.r.st == 0) = (c.tcb.st == Spec.Tcp.St.listen) := t.st_beq .listen
  have hport : (w.sg.dport != 7) = (S.dport != Spec.echoPort) := by rw [hs.dport]; rfl
  have f4 : (w.sg.flags &&& 4 == 0) = !Spec.Tcp.has S.flags Spec.Tcp.RST := hs.hasNot 4
  have hl : (w.r.st == 0 || (w.sg.src != w.r.rip || w.sg.sport != w.r.rport))
      = (c.tcb.st == Spec.Tcp.St.listen || src != c.tcb.rip || S.sport != c.tcb.rport) := by
    rw [e0, hsrc, t.rip, hs.sport, t.rport, Bool.or_assoc]
  rw [Spec.Tcp.input_eq]
  simp only [wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map]
  rw [segW, hport, f4, hl] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ
      exact hQ _ (drop_sim ourIp _ _ ev0 id0 (sendReset_sim ourIp w c ev0 id0 h hd src S hs hsrc) _)
    · rename_i y; rw [if_neg y] at hQ
      exact hQ _ (drop_sim ourIp w c ev0 id0 h _)
  · rename_i x; rw [if_neg x] at hQ
    split
    · rename_i y; rw [if_pos y] at hQ
      exact listen_wp ourIp w c ev0 id0 h hd src S hs hsrc _
        (fun c' hs' => by rw [Spec.Tcp.wp_logTcb]; exact hQ _ (logTcb_sim hs' _ rfl))
    · rename_i y; rw [if_neg y] at hQ
      have h1 : Sim ourIp { w with r := { w.r with idle := 0 } } { c with tcb := { c.tcb with idle := 0 } } ev0
          id0 :=
        h.setTcb _ _ ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, t.rt,
          t.re, t.tw, rfl, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩
      have hacc : accW { w with r := { w.r with idle := 0 } } = Spec.Tcp.acceptable c.tcb S :=
        (acc_rel _ _ S h1.tcb hs).trans rfl
      rw [segConnW, hacc] at hQ
      split
      · rename_i u
        have : ¬ Spec.Tcp.acceptable c.tcb S = true := by simpa using u
        rw [if_neg this] at hQ
        exact na_wp ourIp _ _ ev0 id0 h1 hd S hs _ hQ
      · rename_i u
        have : Spec.Tcp.acceptable c.tcb S = true := by simpa using u
        rw [if_pos this] at hQ
        exact conn_wp ourIp _ _ ev0 id0 h1 hd src S hs hsrc hb c.tcb rfl rfl rfl rfl Q hQ

/-! ## The tick -/

theorem rtoStep_toNat (r : UInt16) (h : r.toNat ≤ 48) : (rtoStep r).toNat = min 48 (r.toNat * 2) := by
  have z48 : (48 : UInt16).toNat = 48 := rfl
  have z2 : (2 : UInt16).toNat = 2 := rfl
  simp only [rtoStep]
  split
  · rename_i x; rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_mul, z48, z2] at x; omega
  · rename_i x; rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_mul, z48, z2] at x
    rw [UInt16.toNat_mul, z2]; omega

theorem min48_mul (a p : Nat) (hp : 1 ≤ p) : min 48 (min 48 a * p) = min 48 (a * p) := by
  by_cases h : a ≤ 48
  · rw [Nat.min_eq_right h]
  · have h1 : 48 ≤ 48 * p := Nat.le_mul_of_pos_right 48 hp
    have h2 : 48 ≤ a * p := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right a hp)
    rw [Nat.min_eq_left (by omega : 48 ≤ a), Nat.min_eq_left h1, Nat.min_eq_left h2]

/-- The back-off loop computes `rtoInit · 2^n`, capped. -/
theorem rtoIter_toNat : ∀ (n : Nat) (r : UInt16), r.toNat ≤ 48 → (rtoIter n r).toNat = min 48 (r.toNat * 2 ^ n) := by
  intro n
  induction n with
  | zero => intro r h; show r.toNat = _; rw [Nat.pow_zero, Nat.mul_one]; omega
  | succ n ih =>
    intro r h
    show (rtoIter n (rtoStep r)).toNat = _
    have hs := rtoStep_toNat r h
    rw [ih (rtoStep r) (by omega), hs, min48_mul _ _ Nat.one_le_two_pow, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm 2]

/-- **`rto` is `Spec.rto`** (for the retry counts that occur). -/
theorem rto_spec (k : Nat) (hk : k ≤ 16) : (rtoIter k 3).toUInt8.toNat = Spec.rto k := by
  have h3 : (3 : UInt16).toNat = 3 := rfl
  have := rtoIter_toNat k 3 (by rw [h3]; omega)
  rw [UInt16.toNat_toUInt8, this, h3]
  show _ = min 48 (3 * 2 ^ (min k 16))
  rw [Nat.min_eq_left hk]
  omega

/-- The control block when the retransmission timer expires: one more try, the timeout doubled. -/
def rtR (r : RawTcb) : RawTcb :=
  { r with retries := r.retries + 1, rt_timer := (rtoIter (r.retries + 1).toNat 3).toUInt8 }

theorem tickRtW_eq (w : TW) (ourIp : UInt32) :
    tickRtW w ourIp =
      if w.r.rt_timer ≤ 1 then
        if 8 < w.r.retries + 1 then
          dropW { (emitW w ourIp w.r.rip 7 w.r.rport w.r.snd_nxt w.r.rcv_nxt (4 ||| 16) 0 false 0 0) with
            r := RawTcb.reset } "give-up"
        else rexmitW { w with r := rtR w.r } ourIp
      else { w with r := { w.r with rt_timer := w.r.rt_timer - 1 } } := rfl

/-- **`tcp_tick` is `Spec.Tcp.tick`**, for a control block that satisfies
the Spec's invariant and whose counters are not about to wrap. -/
theorem tick_wp (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (hI : Spec.Tcp.Inv c.tcb)
    (hidle : c.tcb.idle < 255) (hretr : c.tcb.retries < 255) (Q : Unit → Spec.Tcp.Ctx → Prop)
    (hQ : ∀ c', Sim ourIp (tickW w ourIp) c' ev0 id0 → Q () c') :
    wp Spec.Tcp.tick Q c := by
  have t := h.tcb
  have e0 : (w.r.st == 0) = (c.tcb.st == Spec.Tcp.St.listen) := t.st_beq .listen
  have e8 : (w.r.st == 8) = (c.tcb.st == Spec.Tcp.St.timeWait) := t.st_beq .timeWait
  have e6 : (w.r.st == 6) = (c.tcb.st == Spec.Tcp.St.finWait2) := t.st_beq .finWait2
  have e2 : (w.r.st == 2) = (c.tcb.st == Spec.Tcp.St.established) := t.st_beq .established
  have eO : (w.r.snd_una != w.r.snd_nxt) = c.tcb.outstanding := by
    rw [Spec.Tcp.Tcb.outstanding, t.una, t.nxt]
  have z1 : (1 : UInt8).toNat = 1 := rfl
  have z60 : (60 : UInt8).toNat = 60 := rfl
  have z8 : (8 : UInt8).toNat = 8 := rfl
  have bi := w.r.idle.toNat_lt
  have htw : (w.r.tw_timer ≤ 1) ↔ c.tcb.twTimer ≤ 1 := by rw [UInt8.le_iff_toNat_le, z1, t.tw]
  have hrt : (w.r.rt_timer ≤ 1) ↔ c.tcb.rtTimer ≤ 1 := by rw [UInt8.le_iff_toNat_le, z1, t.rt]
  have hid : (60 ≤ w.r.idle + 1) ↔ c.tcb.idle + 1 ≥ Spec.idleTicks := by
    have ti := t.idle
    rw [UInt8.le_iff_toNat_le, z60, UInt8.toNat_add, z1]
    show _ ↔ 60 ≤ c.tcb.idle + 1
    omega
  have hidn : (w.r.idle + 1).toNat = c.tcb.idle + 1 := by
    have ti := t.idle
    rw [UInt8.toNat_add, z1]; omega
  have hre : (8 < w.r.retries + 1) ↔ c.tcb.retries + 1 > Spec.maxRetries := by
    have tr := t.re
    rw [UInt8.lt_iff_toNat_lt, z8, UInt8.toNat_add, z1]
    show _ ↔ 8 < c.tcb.retries + 1
    omega
  have hren : (w.r.retries + 1).toNat = c.tcb.retries + 1 := by
    have tr := t.re
    rw [UInt8.toNat_add, z1]; omega
  have hpl : (w.r.pend_len == 0) = (c.tcb.pending.size == 0) := by
    apply beq_congr_iff
    have z : (0 : UInt16).toNat = 0 := rfl
    rw [← t.plen, ← UInt16.toNat_inj, z]
  simp only [Spec.Tcp.tick, wp_bind, wp_get, wp_ite, wp_modify, wp_pure, wp_map]
  rw [tickW, e0, e8, e6, eO, e2, hpl] at hQ
  split
  · rename_i x; rw [if_pos x] at hQ; exact hQ c h
  rename_i x; rw [if_neg x] at hQ
  split
  · rename_i y; rw [if_pos y] at hQ
    split
    · rename_i u; rw [if_pos (htw.mpr u)] at hQ
      exact hQ _ (logTcb_sim (h.setTcb RawTcb.reset {} (reset_rel _ t.pdsz)) _ rfl)
    · rename_i u; rw [if_neg (fun q => u (htw.mp q))] at hQ
      exact hQ _ (h.setTcb _ _ ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our,
        t.lw, t.rt, t.re, by
          show (w.r.tw_timer - 1).toNat = c.tcb.twTimer - 1
          have := t.tw; have := w.r.tw_timer.toNat_lt
          rw [UInt8.toNat_sub, z1]; omega,
        t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩)
  rename_i y; rw [if_neg y] at hQ
  -- the idle count, in FIN-WAIT-2 and in ESTABLISHED
  have hidleRel : TcbRel { w.r with idle := w.r.idle + 1 } w.pd { c.tcb with idle := c.tcb.idle + 1 } :=
    ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, t.rt, t.re, t.tw,
      hidn, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩
  cases hf : (c.tcb.st == Spec.Tcp.St.finWait2)
  · rw [hf, if_neg (by simp)] at hQ
    split
    · rename_i o; rw [if_pos o, tickRtW_eq] at hQ
      split
      · rename_i u; rw [if_pos (hrt.mpr u)] at hQ
        split
        · rename_i v; rw [if_pos (hre.mpr v)] at hQ
          rw [← t.rip, ← t.rport, ← t.nxt, ← t.rcv]
          have he := emit_sim ourIp w c ev0 id0 h hd w.r.rip 7 w.r.rport w.r.snd_nxt w.r.rcv_nxt (4 ||| 16) 0
            false 0 0
            { sport := Spec.echoPort, dport := w.r.rport, seq := w.r.snd_nxt, ack := w.r.rcv_nxt,
              flags := Spec.Tcp.RST ||| Spec.Tcp.ACK, wnd := 0 }
            (by
              show _ = Spec.Tcp.Seg.mk _ _ _ _ _ _ none (w.pd.extract 0 (0 + 0))
              rw [extract_empty w.pd 0]; rfl)
          exact hQ _ (logTcb_sim (drop_sim ourIp _ _ ev0 id0
            (he.setTcb RawTcb.reset {} (reset_rel _ (by rw [emitW_pd]; exact t.pdsz))) _) _ rfl)
        · rename_i v; rw [if_neg (fun q => v (hre.mp q))] at hQ
          have hk : c.tcb.retries + 1 ≤ 16 := by
            have : ¬ c.tcb.retries + 1 > 8 := v
            omega
          have h2 : Sim ourIp { w with r := rtR w.r }
              { c with tcb :=
                { c.tcb with retries := c.tcb.retries + 1, rtTimer := Spec.rto (c.tcb.retries + 1) } } ev0 id0 :=
            h.setTcb _ _ ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw,
              by
                show (rtoIter (w.r.retries + 1).toNat 3).toUInt8.toNat = Spec.rto (c.tcb.retries + 1)
                rw [hren]; exact rto_spec _ hk,
              hren, t.tw, t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩
          exact hQ _ (logTcb_sim (rexmit_sim ourIp _ _ ev0 id0 h2 hd) _ rfl)
      · rename_i u; rw [if_neg (fun q => u (hrt.mp q))] at hQ
        exact hQ _ (h.setTcb _ _ ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our,
          t.lw, by
            show (w.r.rt_timer - 1).toNat = c.tcb.rtTimer - 1
            have := t.rt; have := w.r.rt_timer.toNat_lt
            rw [UInt8.toNat_sub, z1]; omega,
          t.re, t.tw, t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩)
    · rename_i o; rw [if_neg o] at hQ
      simp only [Bool.false_eq_true, if_false]
      split
      · rename_i v; rw [if_pos v] at hQ
        split
        · rename_i u; rw [if_pos (hid.mpr u)] at hQ
          refine output_wp ourIp { w with r := { w.r with close_req := true, idle := 0 } }
            { c with tcb := { c.tcb with closeReq := true, idle := 0 } } ev0 id0
            (h.setTcb _ _ ⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw,
              t.rt, t.re, t.tw, rfl, rfl, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩) hd false _ ?_
          intro c' hs' _
          rw [Spec.Tcp.wp_logTcb]
          exact hQ _ (logTcb_sim hs' _ rfl)
        · rename_i u; rw [if_neg (fun q => u (hid.mp q))] at hQ
          exact hQ _ (h.setTcb _ _ hidleRel)
      · rename_i v; rw [if_neg v] at hQ; exact hQ c h
  · rw [hf, if_pos rfl] at hQ
    have hst : c.tcb.st = Spec.Tcp.St.finWait2 := by simpa using hf
    have ho : c.tcb.outstanding = false := by
      have h1 := hI.flight; have h2 := hI.holds; have h3 := hI.sentPending
      rw [hst] at h1 h2
      have hp0 : c.tcb.pending.size = 0 := by
        rcases Nat.eq_zero_or_pos c.tcb.pending.size with q | q
        · exact q
        · rcases h2 q with a | a | a <;> exact absurd a (by decide)
      have hd0 : Spec.Tcp.dist c.tcb.sndNxt c.tcb.sndUna = 0 := by
        rw [h1]; show c.tcb.sent + 0 = 0; omega
      have heq : c.tcb.sndUna = c.tcb.sndNxt := by
        apply UInt32.toNat_inj.mp
        have b1 := c.tcb.sndUna.toNat_lt; have b2 := c.tcb.sndNxt.toNat_lt
        simp only [Spec.Tcp.dist, UInt32.toNat_sub] at hd0
        omega
      simp [Spec.Tcp.Tcb.outstanding, heq]
    simp only [ho, Bool.false_eq_true, if_false, if_true]
    split
    · rename_i u; rw [if_pos (hid.mpr u)] at hQ
      exact hQ _ (logTcb_sim (drop_sim ourIp _ _ ev0 id0 (h.setTcb RawTcb.reset {} (reset_rel _ t.pdsz)) _) _ rfl)
    · rename_i u; rw [if_neg (fun q => u (hid.mp q))] at hQ
      exact hQ _ (h.setTcb _ _ hidleRel)

end Ember.Proof.Refine
