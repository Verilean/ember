import Ember.Spec.Stack
import Ember.Spec.Srv.Tcp

/-!
# Ember.Spec.Srv.Stack — the reference stack with an application (plan M8.1)

`Ember.Spec.Stack` with TCP from `Ember.Spec.Srv.Tcp`: an `App` on one
port and `conns` connections.  Everything else — SLIP, Ethernet and ARP,
IPv4, ICMP, the UDP echo, DHCP, ticks in the middle of a SLIP frame — is
`Ember.Spec.Stack`'s, written over this state.

A segment goes to the connection whose tuple it carries; otherwise to the
first connection in LISTEN — or, when the application allows it
(`reuseTimeWait`), in TIME-WAIT; when there is none it is answered with RST
(`unsupported-second-connection`), as the one-connection stack does.  A
tick ticks every connection, in order.  With several connections the
`tcb` lines start with `conn=i `; with one they are `Ember.Spec.Stack`'s.
-/

namespace Ember.Spec.Srv
open Ember Ember.Trace
open Ember.Spec.Tcp (St Seg has RST)

structure Config extends Spec.Config where
  /-- Number of connections. -/
  conns : Nat := 1
  deriving Inhabited

section
variable (A : App)

structure State where
  cfg   : Config := {}
  slip  : Slip.Dec := {}
  ipId  : UInt16 := 1
  ip    : UInt32 := ourIpDefault
  conns : Array (Tcb A) := #[{}]
  iss   : UInt32 := issInit
  arp   : Arp.Cache := {}
  dhcp  : Dhcp.St := {}
  tickDue : Bool := false

instance : Inhabited (State A) := ⟨{}⟩

def State.init (cfg : Config := {}) : State A :=
  { cfg, ip := if cfg.dhcp then 0 else cfg.ip, conns := Array.replicate (max 1 cfg.conns) {} }

abbrev StackM := StateM (State A × Array Event)

variable {A}

def ev (e : Event) : StackM A Unit := modify fun (s, es) => (s, es.push e)
def dropS (r : String) : StackM A Unit := ev (.drop r)
def getS : StackM A (State A) := (·.1) <$> get
def modifyS (f : State A → State A) : StackM A Unit := modify fun (s, es) => (f s, es)

def txFrame (frame : ByteArray) : StackM A Unit := do
  let s ← getS
  ev (.pkt ("tx " ++ Pretty.summary s.cfg.link.name frame))
  match s.cfg.link with
  | .slip => ev (.tx (Slip.encode frame))
  | .eth => ev (.tx frame)

def sendIp (proto : UInt8) (dst : UInt32) (payload : ByteArray) : StackM A Unit := do
  let s ← getS
  modifyS fun s => { s with ipId := s.ipId + 1 }
  let pkt := Ipv4.packet proto s.ipId s.ip dst payload
  match s.cfg.link with
  | .slip => txFrame pkt
  | .eth =>
    let mac? := if dst == Ipv4.broadcast then some Arp.broadcastMac else s.arp.lookup dst
    match mac? with
    | some mac => txFrame (Arp.frame mac s.cfg.mac Arp.typeIpv4 pkt)
    | none =>
      txFrame (Arp.request s.cfg.mac s.ip dst)
      dropS "arp-miss"

/-- Run a TCP action on connection `i`. -/
def runTcp (i : Nat) (act : TcpM A Unit) : StackM A Unit := do
  let s ← getS
  let tag := if s.conns.size > 1 then s!"conn={i} " else ""
  let (_, c) := act.run { tcb := s.conns[i]?.getD {}, iss := s.iss, ourIp := s.ip,
                          mss := mssFor s.cfg.mtu, tag }
  modifyS fun s => { s with conns := s.conns.set! i c.tcb, iss := c.iss }
  for (dst, seg) in c.out do sendIp Ipv4.protoTcp dst seg
  for d in c.diag do ev d

def tcpInput (src : UInt32) (seg : Seg) : StackM A Unit := do
  if seg.dport != A.port then
    runTcp 0 do
      if !has seg.flags RST then sendReset src seg
      dropR "tcp-port-closed"
    return
  let s ← getS
  match s.conns.findIdx? (fun t => t.st != .listen && t.rip == src && t.rport == seg.sport) with
  | some i => runTcp i (connInput seg)
  | none =>
    match s.conns.findIdx? (·.st == .listen) with
    | some j => runTcp j (do listenInput src seg; logTcb)
    | none =>
      match (if A.reuseTimeWait then s.conns.findIdx? (·.st == .timeWait) else none) with
      | some j => runTcp j (do closeConn; listenInput src seg; logTcb)
      | none => runTcp 0 (do busyInput src seg; logTcb)

def dhcpApply (o : Dhcp.Out) : StackM A Unit := do
  modifyS fun s => { s with dhcp := o.st, ip := o.ip }
  if let some r := o.drop then dropS r
  if let some n := o.note then ev (.note n)
  if let some m := o.send then
    let s ← getS
    sendIp Ipv4.protoUdp Ipv4.broadcast (Udp.emit s.ip Ipv4.broadcast Dhcp.clientPort Dhcp.serverPort m)

def udpInput (h : Ipv4.Hdr) (p : ByteArray) : StackM A Unit := do
  match Udp.parse h.src h.dst p with
  | .error r => dropS r
  | .ok d =>
    let s ← getS
    if d.dport == echoPort then
      sendIp Ipv4.protoUdp h.src (Udp.emit s.ip h.src d.dport d.sport d.data)
    else if d.dport == Dhcp.clientPort && s.cfg.dhcp then
      dhcpApply (Dhcp.input s.dhcp s.ip s.cfg.mac (Bytes.slice p 8 (p.size - 8)))
    else dropS "udp-port-closed"

def ipInput (pkt : ByteArray) : StackM A Unit := do
  let s ← getS
  match Ipv4.validate pkt s.ip with
  | .error r => dropS r
  | .ok (h, payload) =>
    if h.dst == Ipv4.broadcast && h.proto != Ipv4.protoUdp then dropS "broadcast"
    else if h.proto == Ipv4.protoIcmp then
      match Icmp.reply payload with
      | .ok m => sendIp Ipv4.protoIcmp h.src m
      | .error r => dropS r
    else if h.proto == Ipv4.protoUdp then udpInput h payload
    else if h.proto == Ipv4.protoTcp then
      match Tcp.parse h.src h.dst payload with
      | .ok seg => tcpInput h.src seg
      | .error r => dropS r
    else dropS "unsupported-protocol"

def ethInput (f : ByteArray) : StackM A Unit := do
  let s ← getS
  if f.size < 14 then dropS "short-frame"; return
  let dst := (Bytes.slice f 0 6).toList
  if dst != s.cfg.mac.toList && dst != Arp.broadcastMac.toList then dropS "not-our-mac"; return
  let ty := Bytes.get16 f 12
  let payload := f.extract 14 f.size
  if ty == Arp.typeArp then
    let (c, r) := Arp.input s.arp s.cfg.mac s.ip payload
    modifyS fun s => { s with arp := c }
    match r with
    | .ok (some reply) => txFrame reply
    | .ok none => pure ()
    | .error e => dropS e
  else if ty == Arp.typeIpv4 then
    if payload.size > s.cfg.mtu then dropS "oversize-frame"; return
    if let .ok (h, _) := Ipv4.validate payload s.ip then
      if h.src != 0 then
        modifyS fun s => { s with arp := s.arp.update h.src (Bytes.slice f 6 6) true }
    ipInput payload
  else dropS "unsupported-ethertype"

def frameInput (f : ByteArray) : StackM A Unit := do
  let s ← getS
  ev (.pkt ("rx " ++ Pretty.summary s.cfg.link.name f))
  match s.cfg.link with
  | .slip => ipInput f
  | .eth => ethInput f

def tickInput : StackM A Unit := do
  let s ← getS
  for i in [0:s.conns.size] do
    runTcp i tick
  let s ← getS
  if s.cfg.dhcp then dhcpApply (Dhcp.tick s.dhcp s.ip s.cfg.mac)

def tickArrives : StackM A Unit := do
  let s ← getS
  match s.cfg.link with
  | .eth => tickInput
  | .slip =>
    if s.slip.buf.size == 0 then tickInput
    else if !s.tickDue then modifyS fun s => { s with tickDue := true }
    else
      modifyS fun s => { s with slip := { over := true }, tickDue := false }
      tickInput
      tickInput

def slipByte (c : UInt8) : StackM A Unit := do
  let s ← getS
  let (d, r) := s.slip.feed c s.cfg.mtu
  modifyS fun s => { s with slip := d }
  match r with
  | .frame f => frameInput f
  | .drop reason => dropS reason
  | .none => pure ()

def byteInput (c : UInt8) : StackM A Unit := do
  slipByte c
  let s ← getS
  if s.tickDue && s.slip.buf.size == 0 then
    modifyS fun s => { s with tickDue := false }
    tickInput

def input : Input → StackM A Unit
  | .tick => tickArrives
  | .rx bytes => do
    let s ← getS
    match s.cfg.link with
    | .eth => frameInput bytes
    | .slip =>
      for c in bytes.toList do
        byteInput c

def step (s : State A) (i : Input) : State A × List Event :=
  let ((), (s', es)) := (input i).run (s, #[])
  (s', es.toList)

variable (A)

def run (cfg : Config) (inputs : Array Input) (impl := "spec") : Trace := Id.run do
  let mut s := State.init A cfg
  let mut steps : Array (Input × List Event) := #[]
  for i in inputs do
    let (s', es) := step s i
    s := s'
    steps := steps.push (i, es)
  return Trace.ofSteps (cfg.header impl) steps

end

end Ember.Spec.Srv
