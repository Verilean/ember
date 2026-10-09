import Ember.Spec.Peer
import Ember.Trace.Text

/-!
# Ember.Spec.Scenario — hand-written traces with expectations

A scenario drives the reference stack as a peer would, step by step, and
states what it expects after each step (segments sent, flags, state,
drop reason).  Running a scenario both *checks* those expectations and
*produces* the trace that is committed as a corpus fixture, so a
hand-written fixture is never just "whatever the Spec printed".

The TCP helpers keep the peer's view of the connection: its own next
sequence number (`cseq`) and the next sequence number it expects from
Ember (`sseq`).
-/

namespace Ember.Spec.Scenario
open Ember Ember.Trace Ember.Spec

structure ScState where
  st     : State
  steps  : Array (Input × List Event) := #[]
  port   : UInt16 := 40000
  cseq   : UInt32 := 1000
  sseq   : UInt32 := 0
  /-- Link frames sent by Ember in the last step (SLIP removed). -/
  last   : List ByteArray := []
  lastEv : List Event := []

abbrev Sc := StateT ScState (Except String)

def fail (msg : String) : Sc α := do
  let n := (← get).steps.size
  throw s!"after step {n - 1}: {msg}"

def expect (c : Bool) (msg : String) : Sc Unit := unless c do fail msg

/-- Feed one input; returns the frames Ember sent. -/
def feed (i : Input) : Sc (List ByteArray) := do
  let s ← get
  let (st', es) := step s.st i
  let frames := (outputs es).flatMap fun b =>
    if s.st.cfg.link == .eth then [b] else Slip.decodeAll b (maxLen := 65535)
  set { s with st := st', steps := s.steps.push (i, es), last := frames, lastEv := es }
  return frames

def sendPkt (pkt : ByteArray) : Sc (List ByteArray) := feed (Peer.slip pkt)
def sendRaw (b : ByteArray) : Sc (List ByteArray) := feed (.rx b)

def ticks (n : Nat) : Sc Unit := do
  for _ in [0:n] do discard <| feed .tick

/-! ## Expectations -/

def tcb : Sc Tcp.Tcb := do return (← get).st.tcb

def expectState (st : Tcp.St) : Sc Unit := do
  let t ← tcb
  expect (t.st == st) s!"expected state {st.toString}, got {t.st.toString}"

def expectDrop (r : String) : Sc Unit := do
  let es := (← get).lastEv
  expect (es.any (· == .drop r)) s!"expected drop reason={r}, got {(es.filter (·.kind == "drop")).map (·.payload)}"

def expectNoTx : Sc Unit := do
  let l := (← get).last
  expect l.isEmpty s!"expected no output, got {l.length} frame(s): {l.map Pretty.ipSummary}"

def expectTxCount (n : Nat) : Sc Unit := do
  let l := (← get).last
  expect (l.length == n) s!"expected {n} frame(s), got {l.length}: {l.map Pretty.ipSummary}"

/-- The single TCP segment sent in the last step. -/
def lastSeg : Sc Tcp.Seg := do
  let c ← get
  let ips := if c.st.cfg.link == .eth then c.last.map (fun f => f.extract 14 f.size) else c.last
  match ips with
  | [p] =>
    match Ipv4.validate p Peer.ip with
    | .error e => fail s!"sent packet invalid: {e}"
    | .ok (h, pl) =>
      expect (h.proto == Ipv4.protoTcp) "sent packet is not TCP"
      match Tcp.parse h.src h.dst pl with
      | .ok s => return s
      | .error e => fail s!"sent segment invalid: {e}"
  | l => fail s!"expected one segment, got {l.length}: {l.map Pretty.ipSummary}"

def flagsStr (f : UInt8) : String := Pretty.tcpFlags f

/-- One segment with exactly these flags; returns it. -/
def expectSeg (flags : UInt8) : Sc Tcp.Seg := do
  let s ← lastSeg
  expect (s.flags == flags) s!"expected flags {flagsStr flags}, got {flagsStr s.flags}"
  return s

/-- The segment acknowledges what the peer sent and starts where the
peer expects; advances `sseq` past it. -/
def expectInSeq (flags : UInt8) (data : ByteArray := .empty) : Sc Tcp.Seg := do
  let s ← expectSeg flags
  let c ← get
  expect (s.seq == c.sseq) s!"expected seq {c.sseq}, got {s.seq}"
  if Tcp.has flags Tcp.ACK then
    expect (s.ack == c.cseq) s!"expected ack {c.cseq}, got {s.ack}"
  expect (s.data.toList == data.toList) s!"expected data {Bytes.toHex data}, got {Bytes.toHex s.data}"
  modify fun c => { c with sseq := c.sseq + UInt32.ofNat s.len }
  return s

/-! ## The peer's side of a TCP connection -/

/-- Send a segment from the peer at `cseq`, acknowledging `sseq`; advances
`cseq` by the segment's length. -/
def seg (flags : UInt8) (data : ByteArray := .empty) (seq : Option UInt32 := none)
    (ack : Option UInt32 := none) (wnd : UInt16 := 64240) (mss : Option UInt16 := none)
    (dport : UInt16 := echoPort) (advance := true) : Sc (List ByteArray) := do
  let c ← get
  let sq := seq.getD c.cseq
  let ak := ack.getD (if Tcp.has flags Tcp.ACK then c.sseq else 0)
  let pkt := Peer.tcp c.port sq ak flags data wnd mss dport
  let len := data.size + (if Tcp.has flags Tcp.SYN then 1 else 0) + (if Tcp.has flags Tcp.FIN then 1 else 0)
  if advance && seq.isNone then modify fun c => { c with cseq := c.cseq + UInt32.ofNat len }
  sendPkt pkt

/-- Three-way handshake; afterwards ESTABLISHED. -/
def connect (mss : Option UInt16 := some 1460) : Sc Unit := do
  discard <| seg Tcp.SYN (mss := mss)
  let s ← expectSeg (Tcp.SYN ||| Tcp.ACK)
  expect (s.ack == (← get).cseq) "SYN-ACK acknowledges the SYN"
  expect (s.mss == some (UInt16.ofNat (mssFor (← get).st.cfg.mtu))) "SYN-ACK carries our MSS"
  modify fun c => { c with sseq := s.seq + 1 }
  expectState .synRcvd
  discard <| seg Tcp.ACK
  expectNoTx
  expectState .established

/-- Send data and expect it echoed in one segment. -/
def echo (d : ByteArray) : Sc Unit := do
  discard <| seg (Tcp.ACK ||| Tcp.PSH) d
  discard <| expectInSeq (Tcp.ACK ||| Tcp.PSH) d

/-- Peer closes first: FIN, Ember answers FIN-ACK (LAST-ACK), peer ACKs. -/
def closeFromPeer : Sc Unit := do
  discard <| seg (Tcp.ACK ||| Tcp.FIN)
  discard <| expectInSeq (Tcp.ACK ||| Tcp.FIN)
  expectState .lastAck
  discard <| seg Tcp.ACK
  expectNoTx
  expectState .listen

/-! ## Running -/

structure Scenario where
  name : String
  dir  : String
  doc  : String
  cfg  : Config := {}
  body : Sc Unit

def Scenario.run (sc : Scenario) : Except String Trace := do
  let (_, s) ← sc.body.run { st := State.init sc.cfg }
  return Trace.ofSteps (sc.cfg.header) s.steps

end Ember.Spec.Scenario
