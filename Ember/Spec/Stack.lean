import Ember.Spec.Slip
import Ember.Spec.Icmp
import Ember.Spec.Tcp.Timer
import Ember.Spec.Arp
import Ember.Spec.Dhcp
import Ember.Util.Pretty

/-!
# Ember.Spec.Stack — the reference stack as one step function

```
step : State → Input → State × List Event
```

`Input` is a chunk of link bytes or a tick.  The events are the `tx`
lines (observable) interleaved with diagnostic `pkt`/`tcb`/`drop`/`note`
lines.  `outputs` keeps only the transmitted bytes.

Deterministic by construction: the IP identification and the TCP initial
sequence number come from counters, and time is the `tick` input.
-/

namespace Ember.Spec
open Ember Ember.Trace

inductive LinkKind where
  | slip | eth
  deriving Inhabited, BEq, Repr

def LinkKind.name : LinkKind → String
  | .slip => "slip" | .eth => "eth"

structure Config where
  link : LinkKind := .slip
  dhcp : Bool := false
  ip   : UInt32 := ourIpDefault
  mac  : ByteArray := Arp.ourMacDefault
  /-- Largest IP datagram accepted and sent (the packet buffer size). -/
  mtu  : Nat := Spec.mtu
  deriving Inhabited

structure State where
  cfg  : Config := {}
  slip : Slip.Dec := {}
  ipId : UInt16 := 1
  ip   : UInt32 := ourIpDefault
  tcb  : Tcp.Tcb := {}
  iss  : UInt32 := issInit
  arp  : Arp.Cache := {}
  dhcp : Dhcp.St := {}
  deriving Inhabited

/-- The trace header describing a configuration. -/
def Config.header (cfg : Config) (impl := "spec") : Header :=
  { impl, link := cfg.link.name, mtu := cfg.mtu, dhcp := cfg.dhcp }

def Config.ofHeader (h : Header) : Config :=
  { link := if h.link == "eth" then .eth else .slip, dhcp := h.dhcp, mtu := h.mtu }

def State.init (cfg : Config := {}) : State :=
  { cfg, ip := if cfg.dhcp then 0 else cfg.ip }

abbrev StackM := StateM (State × Array Event)

def ev (e : Event) : StackM Unit := modify fun (s, es) => (s, es.push e)
def dropR (r : String) : StackM Unit := ev (.drop r)
def getS : StackM State := (·.1) <$> get
def modifyS (f : State → State) : StackM Unit := modify fun (s, es) => (f s, es)

/-- Put a link frame on the wire. -/
def txFrame (frame : ByteArray) : StackM Unit := do
  let s ← getS
  ev (.pkt ("tx " ++ Pretty.summary s.cfg.link.name frame))
  match s.cfg.link with
  | .slip => ev (.tx (Slip.encode frame))
  | .eth => ev (.tx frame)

/-- Send an IP payload; takes the next IP identification. -/
def sendIp (proto : UInt8) (dst : UInt32) (payload : ByteArray) : StackM Unit := do
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
      dropR "arp-miss"

/-- Run a TCP action against the stack state. -/
def runTcp (act : Tcp.TcpM Unit) : StackM Unit := do
  let s ← getS
  let (_, c) := act.run { tcb := s.tcb, iss := s.iss, ourIp := s.ip, mss := mssFor s.cfg.mtu }
  modifyS fun s => { s with tcb := c.tcb, iss := c.iss }
  for (dst, seg) in c.out do sendIp Ipv4.protoTcp dst seg
  for d in c.diag do ev d

def dhcpApply (o : Dhcp.Out) : StackM Unit := do
  modifyS fun s => { s with dhcp := o.st, ip := o.ip }
  if let some r := o.drop then dropR r
  if let some n := o.note then ev (.note n)
  if let some m := o.send then
    let s ← getS
    sendIp Ipv4.protoUdp Ipv4.broadcast (Udp.emit s.ip Ipv4.broadcast Dhcp.clientPort Dhcp.serverPort m)

def udpInput (h : Ipv4.Hdr) (p : ByteArray) : StackM Unit := do
  match Udp.parse h.src h.dst p with
  | .error r => dropR r
  | .ok d =>
    let s ← getS
    if d.dport == echoPort then
      sendIp Ipv4.protoUdp h.src (Udp.emit s.ip h.src d.dport d.sport d.data)
    else if d.dport == Dhcp.clientPort && s.cfg.dhcp then
      dhcpApply (Dhcp.input s.dhcp s.ip s.cfg.mac (Bytes.slice p 8 (p.size - 8)))
    else dropR "udp-port-closed"

def ipInput (pkt : ByteArray) : StackM Unit := do
  let s ← getS
  match Ipv4.validate pkt s.ip with
  | .error r => dropR r
  | .ok (h, payload) =>
    if h.dst == Ipv4.broadcast && h.proto != Ipv4.protoUdp then dropR "broadcast"
    else if h.proto == Ipv4.protoIcmp then
      match Icmp.reply payload with
      | .ok m => sendIp Ipv4.protoIcmp h.src m
      | .error r => dropR r
    else if h.proto == Ipv4.protoUdp then udpInput h payload
    else if h.proto == Ipv4.protoTcp then
      match Tcp.parse h.src h.dst payload with
      | .ok seg => runTcp (Tcp.input h.src seg)
      | .error r => dropR r
    else dropR "unsupported-protocol"

def ethInput (f : ByteArray) : StackM Unit := do
  let s ← getS
  if f.size < 14 then dropR "short-frame"; return
  let dst := (Bytes.slice f 0 6).toList
  if dst != s.cfg.mac.toList && dst != Arp.broadcastMac.toList then dropR "not-our-mac"; return
  let ty := Bytes.get16 f 12
  let payload := f.extract 14 f.size
  if ty == Arp.typeArp then
    let (c, r) := Arp.input s.arp s.cfg.mac s.ip payload
    modifyS fun s => { s with arp := c }
    match r with
    | .ok (some reply) => txFrame reply
    | .ok none => pure ()
    | .error e => dropR e
  else if ty == Arp.typeIpv4 then
    if payload.size > s.cfg.mtu then dropR "oversize-frame"; return
    -- learn the sender (uIP's arp_ipin), only for well-formed IPv4 to us
    if let .ok (h, _) := Ipv4.validate payload s.ip then
      if h.src != 0 then
        modifyS fun s => { s with arp := s.arp.update h.src (Bytes.slice f 6 6) true }
    ipInput payload
  else dropR "unsupported-ethertype"

/-- A complete link frame arrived. -/
def frameInput (f : ByteArray) : StackM Unit := do
  let s ← getS
  ev (.pkt ("rx " ++ Pretty.summary s.cfg.link.name f))
  match s.cfg.link with
  | .slip => ipInput f
  | .eth => ethInput f

def tickInput : StackM Unit := do
  runTcp Tcp.tick
  let s ← getS
  if s.cfg.dhcp then dhcpApply (Dhcp.tick s.dhcp s.ip s.cfg.mac)

def input : Input → StackM Unit
  | .tick => tickInput
  | .rx bytes => do
    let s ← getS
    match s.cfg.link with
    | .eth => frameInput bytes
    | .slip =>
      for c in bytes.toList do
        let s ← getS
        let (d, r) := s.slip.feed c s.cfg.mtu
        modifyS fun s => { s with slip := d }
        match r with
        | .frame f => frameInput f
        | .drop reason => dropR reason
        | .none => pure ()

def step (s : State) (i : Input) : State × List Event :=
  let ((), (s', es)) := (input i).run (s, #[])
  (s', es.toList)

/-- Only the observable outputs of a step. -/
def outputs (es : List Event) : List ByteArray :=
  es.filterMap fun | .tx b => some b | _ => none

/-- Run a whole input sequence; the trace of the reference stack. -/
def run (cfg : Config) (inputs : Array Input) (impl := "spec") : Trace := Id.run do
  let mut s := State.init cfg
  let mut steps : Array (Input × List Event) := #[]
  for i in inputs do
    let (s', es) := step s i
    s := s'
    steps := steps.push (i, es)
  return Trace.ofSteps (cfg.header impl) steps

end Ember.Spec
