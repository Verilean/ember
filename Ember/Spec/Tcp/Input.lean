import Ember.Spec.Tcp.Output

/-!
# Ember.Spec.Tcp.Input — segment arrival (RFC 9293 §3.10.7, reduced)

Scope: one connection, passive open on port 7, in-order data only.
Order of processing for a segment of the current connection:

1. acceptability (window test; with a zero window a segment at
   `rcv.nxt` is accepted so that its ACK and RST are processed, its data
   trimmed away) — otherwise ACK and drop `out-of-window`;
2. RST → close;
3. SYN → reset and close (`syn-in-window`);
4. no ACK → drop `no-ack`;
5. ACK: completes the handshake in SYN-RCVD, otherwise advances
   `snd.una`, frees acknowledged echo data and moves the closing states;
6. data or FIN beyond `rcv.nxt` is out of order — ACK and drop;
   otherwise data is trimmed to `rcv.nxt` and the window and appended to
   the echo buffer;
7. FIN (only in order): CLOSE-WAIT / CLOSING / TIME-WAIT;
8. `output`.

Anything outside this scope is listed in `corpus/tcp/UNSUPPORTED.md`.
-/

namespace Ember.Spec.Tcp
open Ember

/-- `a - b` as a distance in sequence space. -/
@[inline] def dist (a b : UInt32) : Nat := (a - b).toNat

/-- `a` lies at or after `b` (modulo 2^32, within half the space). -/
@[inline] def seqGe (a b : UInt32) : Bool := dist a b < 0x80000000

def acceptable (t : Tcb) (s : Seg) : Bool :=
  let w := t.wnd
  let inWin (x : UInt32) := dist x t.rcvNxt < w
  if w == 0 then s.seq == t.rcvNxt
  else if s.len == 0 then inWin s.seq
  else inWin s.seq || inWin (s.seq + UInt32.ofNat (s.len - 1))

def logTcb : TcpM Unit :=
  modify fun c => { c with diag := c.diag.push (.tcb c.tcb.describe) }

/-- A segment in LISTEN (or for a tuple that is not the connection). -/
def listenInput (src : UInt32) (s : Seg) : TcpM Unit := do
  let t := (← get).tcb
  if t.st != .listen then
    if has s.flags RST then dropR "rst-no-connection"
    else
      sendReset src s
      dropR "unsupported-second-connection"
    return
  if has s.flags RST then dropR "rst-in-listen"; return
  if has s.flags ACK then
    sendReset src s
    dropR "ack-in-listen"
    return
  if !has s.flags SYN then dropR "no-syn-in-listen"; return
  let c ← get
  let iss := c.iss
  set { c with iss := iss + issStep, tcb := {
    st := .synRcvd, rip := src, rport := s.sport, rcvNxt := s.seq + 1,
    sndUna := iss, sndNxt := iss + 1,
    peerMss := (match s.mss with | some m => max 1 m.toNat | none => 536),
    ourMss := c.mss,
    rtTimer := rto 0 } }
  sendSynAck

/-- ACK processing in a synchronized state; `false` if the segment is done. -/
def ackInput (s : Seg) : TcpM Bool := do
  let t := (← get).tcb
  let d := dist s.ack t.sndUna
  let outN := dist t.sndNxt t.sndUna
  if d > outN then
    sendSeg ACK t.sndNxt
    dropR "ack-of-unsent"
    return false
  if d == 0 then return true
  let dataAcked := min d t.sent
  let finAcked := d > dataAcked
  let t := { t with pending := t.pending.extract dataAcked t.pending.size,
                    sent := t.sent - dataAcked, sndUna := s.ack, retries := 0 }
  let t := { t with rtTimer := if t.outstanding then rto 0 else 0 }
  if finAcked then
    match t.st with
    | .finWait1 => modify fun c => { c with tcb := { t with st := .finWait2 } }
    | .closing => modify fun c => { c with tcb := { t with st := .timeWait, twTimer := timeWaitTicks } }
    | .lastAck => closeConn; return false
    | _ => modify fun c => { c with tcb := t }
  else
    modify fun c => { c with tcb := t }
  return true

/-- Process a TCP segment from `src` that passed `parse`. -/
def input (src : UInt32) (s : Seg) : TcpM Unit := do
  if s.dport != echoPort then
    if !has s.flags RST then sendReset src s
    dropR "tcp-port-closed"
    return
  let t := (← get).tcb
  if t.st == .listen || src != t.rip || s.sport != t.rport then
    listenInput src s
    logTcb
    return
  modify fun c => { c with tcb := { c.tcb with idle := 0 } }
  -- 1. acceptability
  if !acceptable t s then
    if has s.flags RST then dropR "rst-out-of-window"; return
    if t.st == .synRcvd && has s.flags SYN && !has s.flags ACK && s.seq + 1 == t.rcvNxt then
      sendSynAck
      dropR "duplicate-syn"
      return
    sendSeg ACK t.sndNxt
    dropR "out-of-window"
    return
  -- 2. RST
  if has s.flags RST then
    closeConn
    modify fun c => { c with diag := c.diag.push (.note "connection reset by peer") }
    logTcb
    return
  -- 3. SYN in window
  if has s.flags SYN then
    send t.rip { sport := echoPort, dport := t.rport, seq := t.sndNxt, ack := 0, flags := RST, wnd := 0 }
    closeConn
    dropR "syn-in-window"
    logTcb
    return
  -- 4. ACK required
  if !has s.flags ACK then dropR "no-ack"; return
  -- 5. ACK
  if t.st == .synRcvd then
    if s.ack != t.sndNxt then
      sendReset src s
      dropR "bad-ack-in-syn-rcvd"
      return
    modify fun c => { c with tcb := { c.tcb with st := .established, sndUna := s.ack,
                                                 rtTimer := 0, retries := 0 } }
  else
    if !(← ackInput s) then logTcb; return
  -- 6. data
  let t ← (·.tcb) <$> get
  let mut ackNow := false
  let mut inOrder := true
  if (s.data.size > 0 || has s.flags FIN) && !seqGe t.rcvNxt s.seq then
    sendSeg ACK t.sndNxt
    dropR "out-of-order"
    logTcb
    return
  if s.data.size > 0 then
    if t.st == .established || t.st == .finWait1 || t.st == .finWait2 then
      let skip := dist t.rcvNxt s.seq
      let fresh := s.data.extract skip s.data.size
      let take := min fresh.size t.wnd
      let keep := if t.st == .established then t.pending ++ fresh.extract 0 take else t.pending
      modify fun c => { c with tcb := { c.tcb with pending := keep,
                                                   rcvNxt := t.rcvNxt + UInt32.ofNat take } }
      ackNow := true
      inOrder := take == fresh.size
  -- 7. FIN
  let t ← (·.tcb) <$> get
  if has s.flags FIN && inOrder && s.seq + UInt32.ofNat s.data.size == t.rcvNxt then
    let nst := match t.st with
      | .established => some St.closeWait
      | .finWait1 => some .closing
      | .finWait2 => some .timeWait
      | _ => none
    if let some nst := nst then
      let tw := if nst == .timeWait then timeWaitTicks else t.twTimer
      modify fun c => { c with tcb := { c.tcb with st := nst, rcvNxt := t.rcvNxt + 1, twTimer := tw } }
      ackNow := true
  -- 8. output
  output ackNow
  logTcb

end Ember.Spec.Tcp
