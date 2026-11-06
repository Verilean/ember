import Ember.Spec.Tcp.Input

/-!
# Ember.Spec.Srv.Tcp — TCP with an application interface (plan M8.1)

`Ember.Spec.Tcp` has the echo application written into it: `Tcb.pending`
is the echo buffer, port 7 is everywhere, the window is the room left in
the buffer.  That stack, and every proof about it, stays as it is.  This
module is the same TCP with the application taken out and given as an
`App`: the connection asks it, uIP-style,

* how much it can take (`room`, the receive window),
* to take the in-order data that fits (`recv`),
* how many bytes it has from `snd.una` on (`avail`) and what they are
  (`bytes`: the stack keeps no copy, so a retransmission asks again),
* to forget what was acknowledged (`acked`),
* whether it is done and the connection should be closed once all of
  that is sent (`close`).

The connection logic is `Ember.Spec.Tcp`'s, statement for statement,
with these calls where the echo buffer was.  Three changes are needed
by applications that are not echo and change nothing for echo:

* a segment carries at most `cap - sent` new bytes, so no more than one
  segment's worth is in flight (echo never has more than that pending);
* the FIN goes with the last of the data only, not before it;
* the idle close (`idleTicks`) is the application's choice (`idleClose`).

`Ember.Spec.Srv.Stack` holds `n` connections; with `n = 1` and `echo`
it is checked to give the trace of `Ember.Spec.Stack` on the corpus and
on generated sessions (`Tests/Ember/SrvTests.lean`).
-/

namespace Ember.Spec.Srv
open Ember
open Ember.Spec.Tcp (St Seg has FIN SYN RST PSH ACK emit dist seqGe)

/-- An application on one listening port; `σ` is its state per connection. -/
structure App where
  σ : Type
  port : UInt16
  /-- The state of a connection that has just been opened. -/
  init : σ
  /-- The receive window, given `cap = min ourMss peerMss`. -/
  room : σ → Nat → Nat
  /-- In-order data in ESTABLISHED, already cut to `room`. -/
  recv : σ → ByteArray → σ
  /-- Bytes of the outgoing stream from `snd.una` on (sent or not). -/
  avail : σ → Nat
  /-- `bytes s off n`: bytes `[off, off + n)` of the stream from `snd.una`. -/
  bytes : σ → Nat → Nat → ByteArray
  /-- The first `n` bytes from `snd.una` were acknowledged. -/
  acked : σ → Nat → σ
  /-- The application is done: FIN once everything it has is sent. -/
  close : σ → Bool
  /-- Close after `idleTicks` ticks with nothing in flight (echo does). -/
  idleClose : Bool
  /-- A SYN that finds no connection in LISTEN takes one in TIME-WAIT
  (a server that closes first, as HTTP does, would otherwise refuse
  clients for `timeWaitTicks` after each one). -/
  reuseTimeWait : Bool := false

/-- The echo application of `Ember.Spec.Tcp`: the state is its buffer. -/
def echo : App where
  σ := ByteArray
  port := echoPort
  init := .empty
  room p cap := cap - p.size
  recv p d := p ++ d
  avail p := p.size
  bytes p off n := Bytes.slice p off n
  acked p n := p.extract n p.size
  close _ := false
  idleClose := true

section
variable (A : App)

structure Tcb where
  st      : St := .listen
  rip     : UInt32 := 0
  rport   : UInt16 := 0
  sndUna  : UInt32 := 0
  sndNxt  : UInt32 := 0
  rcvNxt  : UInt32 := 0
  app     : A.σ := A.init
  /-- Bytes of the application's stream sent and not acknowledged. -/
  sent    : Nat := 0
  finSent : Bool := false
  peerMss : Nat := 536
  ourMss  : Nat := Spec.ourMss
  lastWnd : Nat := 0
  rtTimer : Nat := 0
  retries : Nat := 0
  twTimer : Nat := 0
  idle    : Nat := 0
  /-- Idle close requested. -/
  closeReq : Bool := false

instance : Inhabited (Tcb A) := ⟨{}⟩

variable {A}

def Tcb.cap (t : Tcb A) : Nat := min t.ourMss t.peerMss

def Tcb.wnd (t : Tcb A) : Nat := A.room t.app t.cap

def Tcb.outstanding (t : Tcb A) : Bool := t.sndUna != t.sndNxt

def Tcb.describe (t : Tcb A) : String :=
  s!"state={t.st.toString} snd.una={t.sndUna} snd.nxt={t.sndNxt} rcv.nxt={t.rcvNxt} pending={A.avail t.app} sent={t.sent} rt={t.rtTimer}/{t.retries}"

variable (A)

/-- One connection and what TCP reads and writes in one step. -/
structure Ctx where
  tcb   : Tcb A := {}
  iss   : UInt32 := issInit
  ourIp : UInt32
  mss   : Nat := Spec.ourMss
  out   : Array (UInt32 × ByteArray) := #[]
  diag  : Array Trace.Event := #[]
  /-- Prefix of the `tcb` lines (the connection's number when there are several). -/
  tag   : String := ""

abbrev TcpM := StateM (Ctx A)

variable {A}

def dropR (r : String) : TcpM A Unit :=
  modify fun c => { c with diag := c.diag.push (.drop r) }

def send (dst : UInt32) (s : Seg) : TcpM A Unit :=
  modify fun c => { c with out := c.out.push (dst, emit c.ourIp dst s) }

def closeConn : TcpM A Unit :=
  modify fun c => { c with tcb := {} }

def logTcb : TcpM A Unit :=
  modify fun c => { c with diag := c.diag.push (.tcb (c.tag ++ c.tcb.describe)) }

def sendSeg (flags : UInt8) (seq : UInt32) (data : ByteArray := .empty)
    (mss : Option UInt16 := none) : TcpM A Unit := do
  let t := (← get).tcb
  let w := t.wnd
  send t.rip { sport := A.port, dport := t.rport, seq, ack := t.rcvNxt, flags,
               wnd := UInt16.ofNat w, mss, data }
  modify fun c => { c with tcb := { c.tcb with lastWnd := w } }

def sendSynAck : TcpM A Unit := do
  let t := (← get).tcb
  sendSeg (SYN ||| ACK) t.sndUna .empty (some (UInt16.ofNat t.ourMss))

def sendReset (dst : UInt32) (s : Seg) : TcpM A Unit :=
  if has s.flags ACK then
    send dst { sport := s.dport, dport := s.sport, seq := s.ack, ack := 0, flags := RST, wnd := 0 }
  else
    send dst { sport := s.dport, dport := s.sport, seq := 0,
               ack := s.seq + UInt32.ofNat s.len, flags := RST ||| ACK, wnd := 0 }

def armTimer (wasOutstanding : Bool) : TcpM A Unit :=
  modify fun c =>
    if wasOutstanding then c
    else { c with tcb := { c.tcb with rtTimer := rto 0, retries := 0 } }

def output (ackNow : Bool) : TcpM A Unit := do
  let t := (← get).tcb
  if t.st == .established || t.st == .closeWait then
    let unsent := A.avail t.app - t.sent
    let n := min unsent (t.cap - t.sent)
    let closing := (t.st == .closeWait || t.closeReq || A.close t.app) && !t.finSent
    let fin := closing && n == unsent
    if n > 0 || fin then
      let was := t.outstanding
      let data := A.bytes t.app t.sent n
      let flags := ACK ||| (if n > 0 then PSH else 0) ||| (if fin then FIN else 0)
      let seq := t.sndNxt
      let st' := if !fin then t.st else if t.st == .closeWait then .lastAck else .finWait1
      modify fun c => { c with tcb := { c.tcb with
        sent := t.sent + n, finSent := t.finSent || fin, st := st',
        sndNxt := t.sndNxt + UInt32.ofNat n + (if fin then 1 else 0) } }
      sendSeg flags seq data
      armTimer was
      return
  if t.st == .listen || t.st == .synRcvd then return
  if ackNow || (t.lastWnd == 0 && t.wnd > 0) then
    sendSeg ACK t.sndNxt

def rexmit : TcpM A Unit := do
  let t := (← get).tcb
  if t.st == .synRcvd then sendSynAck
  else
    let data := A.bytes t.app 0 t.sent
    let flags := ACK ||| (if t.sent > 0 then PSH else 0) ||| (if t.finSent then FIN else 0)
    sendSeg flags t.sndUna data

def acceptable (t : Tcb A) (s : Seg) : Bool :=
  let w := t.wnd
  let inWin (x : UInt32) := dist x t.rcvNxt < w
  if w == 0 then s.seq == t.rcvNxt
  else if s.len == 0 then inWin s.seq
  else inWin s.seq || inWin (s.seq + UInt32.ofNat (s.len - 1))

/-- A segment for a tuple that is no connection, when no connection is free. -/
def busyInput (src : UInt32) (s : Seg) : TcpM A Unit := do
  if has s.flags RST then dropR "rst-no-connection"
  else
    sendReset src s
    dropR "unsupported-second-connection"

/-- A segment for a connection in LISTEN (a free one). -/
def listenInput (src : UInt32) (s : Seg) : TcpM A Unit := do
  if has s.flags RST then dropR "rst-in-listen"; return
  if has s.flags ACK then
    sendReset src s
    dropR "ack-in-listen"
    return
  if !has s.flags SYN then dropR "no-syn-in-listen"; return
  let c : Ctx A ← get
  let iss := c.iss
  set (σ := Ctx A) { c with iss := iss + issStep, tcb := {
    st := .synRcvd, rip := src, rport := s.sport, rcvNxt := s.seq + 1,
    sndUna := iss, sndNxt := iss + 1,
    peerMss := (match s.mss with | some m => max 1 m.toNat | none => 536),
    ourMss := c.mss,
    rtTimer := rto 0 } }
  sendSynAck

def ackInput (s : Seg) : TcpM A Bool := do
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
  let t := { t with app := A.acked t.app dataAcked,
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

/-- A segment of this connection (the tuple matches, the state is not LISTEN). -/
def connInput (s : Seg) : TcpM A Unit := do
  let t := (← get).tcb
  modify fun c => { c with tcb := { c.tcb with idle := 0 } }
  if !acceptable t s then
    if has s.flags RST then dropR "rst-out-of-window"; return
    if t.st == .synRcvd && has s.flags SYN && !has s.flags ACK && s.seq + 1 == t.rcvNxt then
      sendSynAck
      dropR "duplicate-syn"
      return
    sendSeg ACK t.sndNxt
    dropR "out-of-window"
    return
  if has s.flags RST then
    closeConn
    modify fun c => { c with diag := c.diag.push (.note "connection reset by peer") }
    logTcb
    return
  if has s.flags SYN then
    send t.rip { sport := A.port, dport := t.rport, seq := t.sndNxt, ack := 0, flags := RST, wnd := 0 }
    closeConn
    dropR "syn-in-window"
    logTcb
    return
  if !has s.flags ACK then dropR "no-ack"; return
  if t.st == .synRcvd then
    if s.ack != t.sndNxt then
      sendReset t.rip s
      dropR "bad-ack-in-syn-rcvd"
      return
    modify fun c => { c with tcb := { c.tcb with st := .established, sndUna := s.ack,
                                                 rtTimer := 0, retries := 0 } }
  else
    if !(← ackInput s) then logTcb; return
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
      let app := if t.st == .established then A.recv t.app (fresh.extract 0 take) else t.app
      modify fun c => { c with tcb := { c.tcb with app,
                                                   rcvNxt := t.rcvNxt + UInt32.ofNat take } }
      ackNow := true
      inOrder := take == fresh.size
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
  output ackNow
  logTcb

def tick : TcpM A Unit := do
  let t := (← get).tcb
  if t.st == .listen then return
  if t.st == .timeWait then
    if t.twTimer ≤ 1 then closeConn; logTcb
    else modify fun c => { c with tcb := { c.tcb with twTimer := t.twTimer - 1 } }
    return
  if t.outstanding then
    if t.rtTimer ≤ 1 then
      let r := t.retries + 1
      if r > maxRetries then
        send t.rip { sport := A.port, dport := t.rport, seq := t.sndNxt, ack := t.rcvNxt,
                     flags := RST ||| ACK, wnd := 0 }
        closeConn
        dropR "give-up"
        logTcb
      else
        modify fun c => { c with tcb := { c.tcb with retries := r, rtTimer := rto r } }
        rexmit
        logTcb
    else
      modify fun c => { c with tcb := { c.tcb with rtTimer := t.rtTimer - 1 } }
    return
  if t.st == .finWait2 then
    if t.idle + 1 ≥ idleTicks then closeConn; dropR "fin-wait-2-timeout"; logTcb
    else modify fun c => { c with tcb := { c.tcb with idle := t.idle + 1 } }
    return
  if A.idleClose && t.st == .established && A.avail t.app == 0 then
    if t.idle + 1 ≥ idleTicks then
      modify fun c => { c with tcb := { c.tcb with closeReq := true, idle := 0 } }
      output false
      logTcb
    else
      modify fun c => { c with tcb := { c.tcb with idle := t.idle + 1 } }

end

end Ember.Spec.Srv
