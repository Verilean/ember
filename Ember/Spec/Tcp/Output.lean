import Ember.Spec.Tcp.Tcb

/-!
# Ember.Spec.Tcp.Output — what the connection sends

`output` sends at most one segment per input: new echo data (with FIN
when the application has closed and nothing is left), otherwise a pure
ACK when one is owed (data or FIN received, unacceptable segment) or a
window update when the window reopens from zero.  Data segments carry
`ACK|PSH`.
-/

namespace Ember.Spec.Tcp
open Ember

/-- Send a segment from the connection's endpoint; records the window. -/
def sendSeg (flags : UInt8) (seq : UInt32) (data : ByteArray := .empty)
    (mss : Option UInt16 := none) : TcpM Unit := do
  let t := (← get).tcb
  let w := t.wnd
  send t.rip { sport := echoPort, dport := t.rport, seq, ack := t.rcvNxt, flags,
               wnd := UInt16.ofNat w, mss, data }
  modify fun c => { c with tcb := { c.tcb with lastWnd := w } }

/-- The SYN-ACK of a passive open (also its retransmission). -/
def sendSynAck : TcpM Unit := do
  let t := (← get).tcb
  sendSeg (SYN ||| ACK) t.sndUna .empty (some (UInt16.ofNat t.ourMss))

/-- RFC 793 reset for a segment that belongs to no connection. -/
def sendReset (dst : UInt32) (s : Seg) : TcpM Unit :=
  if has s.flags ACK then
    send dst { sport := s.dport, dport := s.sport, seq := s.ack, ack := 0, flags := RST, wnd := 0 }
  else
    send dst { sport := s.dport, dport := s.sport, seq := 0,
               ack := s.seq + UInt32.ofNat s.len, flags := RST ||| ACK, wnd := 0 }

/-- Start the retransmission timer if nothing was outstanding before. -/
def armTimer (wasOutstanding : Bool) : TcpM Unit :=
  modify fun c =>
    if wasOutstanding then c
    else { c with tcb := { c.tcb with rtTimer := rto 0, retries := 0 } }

def output (ackNow : Bool) : TcpM Unit := do
  let t := (← get).tcb
  if t.st == .established || t.st == .closeWait then
    let unsent := t.pending.size - t.sent
    let closing := (t.st == .closeWait || t.closeReq) && !t.finSent
    if unsent > 0 || closing then
      let was := t.outstanding
      let data := Bytes.slice t.pending t.sent unsent
      let fin := closing
      let flags := ACK ||| (if unsent > 0 then PSH else 0) ||| (if fin then FIN else 0)
      let seq := t.sndNxt
      let st' := if !fin then t.st else if t.st == .closeWait then .lastAck else .finWait1
      modify fun c => { c with tcb := { c.tcb with
        sent := t.pending.size, finSent := t.finSent || fin, st := st',
        sndNxt := t.sndNxt + UInt32.ofNat unsent + (if fin then 1 else 0) } }
      sendSeg flags seq data
      armTimer was
      return
  if t.st == .listen || t.st == .synRcvd then return
  if ackNow || (t.lastWnd == 0 && t.wnd > 0) then
    sendSeg ACK t.sndNxt

/-- Retransmission: regenerate everything unacknowledged from `snd.una`. -/
def rexmit : TcpM Unit := do
  let t := (← get).tcb
  if t.st == .synRcvd then sendSynAck
  else
    let data := Bytes.slice t.pending 0 t.sent
    let flags := ACK ||| (if t.sent > 0 then PSH else 0) ||| (if t.finSent then FIN else 0)
    sendSeg flags t.sndUna data

end Ember.Spec.Tcp
