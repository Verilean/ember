import Ember.Spec.Tcp.Header
import Ember.Trace.Event

/-!
# Ember.Spec.Tcp.Tcb — the one connection

Ember serves one TCP connection at a time, passive open on the echo
port.  CLOSED is transient: a closed connection is back in LISTEN.

There is no retransmission buffer in the stack (the uIP model).  The
echo application owns `pending`: bytes received and echoed but not yet
acknowledged, followed by bytes not yet sent.  On a retransmission
timeout the stack asks the application to regenerate the unacknowledged
part, which for echo means re-sending `pending[0, sent)`.  The receive
window is the room left in `pending`, so `pending` never exceeds one
segment.
-/

namespace Ember.Spec.Tcp
open Ember

inductive St where
  | listen | synRcvd | established | closeWait | lastAck
  | finWait1 | finWait2 | closing | timeWait
  deriving Inhabited, BEq, Repr, DecidableEq

def St.toString : St → String
  | .listen => "LISTEN" | .synRcvd => "SYN-RCVD" | .established => "ESTABLISHED"
  | .closeWait => "CLOSE-WAIT" | .lastAck => "LAST-ACK" | .finWait1 => "FIN-WAIT-1"
  | .finWait2 => "FIN-WAIT-2" | .closing => "CLOSING" | .timeWait => "TIME-WAIT"

/-- Numeric encoding shared with `Ember.Net` (lockstep compares these). -/
def St.code : St → Nat
  | .listen => 0 | .synRcvd => 1 | .established => 2 | .closeWait => 3 | .lastAck => 4
  | .finWait1 => 5 | .finWait2 => 6 | .closing => 7 | .timeWait => 8

structure Tcb where
  st      : St := .listen
  rip     : UInt32 := 0
  rport   : UInt16 := 0
  sndUna  : UInt32 := 0
  sndNxt  : UInt32 := 0
  rcvNxt  : UInt32 := 0
  /-- Echo application buffer: `[0, sent)` sent and unacknowledged, then unsent. -/
  pending : ByteArray := .empty
  sent    : Nat := 0
  finSent : Bool := false
  peerMss : Nat := 536
  /-- Our MSS (from the MTU), fixed when the connection opens. -/
  ourMss  : Nat := ourMss
  /-- Window announced in the last segment sent. -/
  lastWnd : Nat := 0
  /-- Ticks until retransmission; meaningful while data is outstanding. -/
  rtTimer : Nat := 0
  retries : Nat := 0
  twTimer : Nat := 0
  idle    : Nat := 0
  /-- The application asked to close (idle timeout). -/
  closeReq : Bool := false
  deriving Inhabited

/-- Size of the echo buffer: one segment in either direction. -/
def Tcb.cap (t : Tcb) : Nat := min t.ourMss t.peerMss

/-- Current receive window. -/
def Tcb.wnd (t : Tcb) : Nat := t.cap - t.pending.size

def Tcb.outstanding (t : Tcb) : Bool := t.sndUna != t.sndNxt

def Tcb.describe (t : Tcb) : String :=
  s!"state={t.st.toString} snd.una={t.sndUna} snd.nxt={t.sndNxt} rcv.nxt={t.rcvNxt} pending={t.pending.size} sent={t.sent} rt={t.rtTimer}/{t.retries}"

/-- Everything TCP reads and writes in one step. -/
structure Ctx where
  tcb   : Tcb := {}
  iss   : UInt32 := issInit
  ourIp : UInt32
  mss   : Nat := ourMss
  /-- Segments to send: (destination address, TCP bytes). -/
  out   : Array (UInt32 × ByteArray) := #[]
  diag  : Array Trace.Event := #[]
  deriving Inhabited

abbrev TcpM := StateM Ctx

def dropR (r : String) : TcpM Unit :=
  modify fun c => { c with diag := c.diag.push (.drop r) }

def send (dst : UInt32) (s : Seg) : TcpM Unit :=
  modify fun c => { c with out := c.out.push (dst, emit c.ourIp dst s) }

/-- Back to LISTEN (CLOSED is transient). -/
def closeConn : TcpM Unit :=
  modify fun c => { c with tcb := {} }

end Ember.Spec.Tcp
