import Ember.Spec.Peer
import Ember.Util.Rand

/-!
# Ember.Spec.Gen — random sessions, mutations and properties (plan §3.4)

* `ping`, `udp`: random request streams (sizes, ids, ports, ticks);
* `tcp`: a *closed-loop* client that reacts to whatever the Spec sends:
  random segment sizes within the advertised window, delayed or
  piggybacked ACKs, lost echoes (recovered by retransmission), duplicated
  and out-of-order segments, idle periods, and every way of ending:
  peer FIN, idle close by Ember (with FIN-WAIT-2 or a simultaneous
  close), or an abort with RST.  It checks that
  every byte sent comes back, in order.  The recorded inputs are then an
  ordinary input stream that every other implementation must answer the
  same way;
* `mutate`: bit flips (with and without fixed-up checksums), truncation,
  bad checksums, out-of-window sequence numbers;
* `rechunk`: the same link bytes split at random places (SLIP is a byte
  stream).

`properties` holds for every session, mutated or not: every step that
completes a frame is accounted for (a `tx`, `drop`, `tcb` or `note`), and
every transmitted packet is well-formed (IP, ICMP, UDP and TCP
checksums, lengths).
-/

namespace Ember.Spec.Gen
open Ember Ember.Trace Ember.Spec

structure Session where
  kind    : String
  cfg     : Config := {}
  inputs  : Array Input
  mutated : Bool := false
  deriving Inhabited

/-! ## ICMP and UDP -/

def ping : RandM Session := do
  let n ← randRange 1 6
  let id := (← randNat 65536).toUInt16
  let mut ins : Array Input := #[]
  for seq in [0:n] do
    let size ← randRange 0 (mtu - 28)
    let payload ← if ← randBool then pure (Peer.pingPayload size) else randBytes size
    ins := ins.push (Peer.slip (Peer.ping id (UInt16.ofNat (seq + 1)) payload (ipId := (← randNat 65536).toUInt16)))
    if ← randBool 20 then ins := ins.push .tick
  return { kind := "icmp", inputs := ins }

def udp : RandM Session := do
  let n ← randRange 1 6
  let mut ins : Array Input := #[]
  for _ in [0:n] do
    let size ← randRange 0 (mtu - 28)
    let other ← randRange 1 65535
    let dport : UInt16 := if ← randBool 85 then echoPort else other.toUInt16
    let d ← randBytes size
    let p := Peer.udp (← randRange 1024 65535).toUInt16 dport d (ipId := (← randNat 65536).toUInt16)
    -- sometimes no checksum (RFC 768: zero means none)
    let p := if ← randBool 15 then Bytes.set16 p 26 0 else p
    ins := ins.push (Peer.slip p)
    if ← randBool 20 then ins := ins.push .tick
  return { kind := "udp", inputs := ins }

/-! ## TCP: a closed-loop client -/

structure Cli where
  st      : State := State.init {}
  ins     : Array Input := #[]
  port    : UInt16 := 40000
  cseq    : UInt32 := 0
  /-- Next sequence number expected from Ember. -/
  cack    : UInt32 := 0
  /-- Ember's last advertised window. -/
  swnd    : Nat := 0
  /-- Highest acknowledgment received from Ember. -/
  sacked  : UInt32 := 0
  sent    : ByteArray := .empty
  echoed  : ByteArray := .empty
  srvFin  : Bool := false
  reset   : Bool := false
  /-- Drop Ember's next output (a "lost" segment). -/
  loseNext : Bool := false
  lastData : Option ByteArray := none

/-- Errors keep the state, so a failing session's inputs can be saved. -/
abbrev CliM := ExceptT String (StateT Cli RandM)

def rnd (n : Nat) : CliM Nat := liftM (randNat n : RandM Nat)
def rbool (pct : Nat := 50) : CliM Bool := liftM (randBool pct : RandM Bool)
def rbytes (n : Nat) : CliM ByteArray := liftM (randBytes n : RandM ByteArray)
def r64 : CliM UInt64 := liftM (rand64 : RandM UInt64)

def cfail (msg : String) : CliM α := do
  let c ← get
  throw s!"tcp session, after {c.ins.size} inputs: {msg}"

/-- Feed an input to the Spec and process what it sends. -/
def cfeed (i : Input) : CliM Unit := do
  let c ← get
  let (st', es) := step c.st i
  set { c with st := st', ins := c.ins.push i }
  if (← get).loseNext then
    modify fun c => { c with loseNext := false }
    return
  for b in outputs es do
    for p in Slip.decodeAll b (maxLen := 65535) do
      let some (h, pl) := (Ipv4.validate p Peer.ip).toOption
        | cfail s!"Ember sent an invalid IP packet: {Pretty.ipSummary p}"
      if h.proto != Ipv4.protoTcp then cfail "non-TCP output in a TCP session"
      let some s := (Tcp.parse h.src h.dst pl).toOption | cfail "Ember sent an invalid TCP segment"
      if s.dport != (← get).port then continue
      if Tcp.has s.flags Tcp.RST then
        modify fun c => { c with reset := true }
        continue
      let c ← get
      let mut c := { c with swnd := s.wnd.toNat }
      if Tcp.has s.flags Tcp.ACK && Tcp.seqGe s.ack c.sacked then c := { c with sacked := s.ack }
      if Tcp.has s.flags Tcp.SYN then
        c := { c with cack := s.seq + 1 }
      else if s.seq == c.cack then
        c := { c with echoed := c.echoed ++ s.data, cack := c.cack + UInt32.ofNat s.data.size }
        if Tcp.has s.flags Tcp.FIN then c := { c with cack := c.cack + 1, srvFin := true }
      set c

def csend (flags : UInt8) (data : ByteArray := .empty) (seq : Option UInt32 := none)
    (mss : Option UInt16 := none) : CliM Unit := do
  let c ← get
  let sq := seq.getD c.cseq
  let pkt := Peer.tcp c.port sq (if Tcp.has flags Tcp.ACK then c.cack else 0) flags data
    (mss := mss) (ipId := (← r64).toUInt16)
  if seq.isNone then
    let l := data.size + (if Tcp.has flags Tcp.SYN then 1 else 0) + (if Tcp.has flags Tcp.FIN then 1 else 0)
    modify fun c => { c with cseq := c.cseq + UInt32.ofNat l }
  cfeed (Peer.slip pkt)

/-- A TCP session; on an expectation failure, the error and the inputs
consumed so far. -/
def tcp : RandM (Except (String × Array Input) Session) := do
  let isn := (← rand64).toUInt32
  let port := (← randRange 1024 65535).toUInt16
  let k ← randNat 4
  let small ← randRange 64 300
  let mss : Option UInt16 := if k == 0 then none else if k == 1 then some small.toUInt16 else some 1460
  let base := isn + 1
  /- Send from Ember's last acknowledgment (go-back-N), adding `fresh` new
  bytes to the stream; never more than the advertised window. -/
  let sendFrom (fresh : Nat) : CliM Unit := do
    let c ← get
    let pos := Tcp.dist c.sacked base
    let mut c := c
    if fresh > 0 then
      let d ← rbytes fresh
      c := { c with sent := c.sent ++ d }
      set c
    let avail := c.sent.size - min pos c.sent.size
    let n := min avail c.swnd
    if n == 0 then csend Tcp.ACK (seq := some c.sacked); return
    let d := c.sent.extract pos (pos + n)
    if ← rbool 15 then modify fun c => { c with loseNext := true }
    csend (Tcp.ACK ||| Tcp.PSH) d (seq := some c.sacked)
    let top := c.sacked + UInt32.ofNat n
    modify fun c => { c with lastData := some d, cseq := if Tcp.seqGe top c.cseq then top else c.cseq }
  let allAcked : CliM Bool := do
    let c ← get
    return Tcp.dist c.sacked base ≥ c.sent.size
  let body : CliM Unit := do
    modify fun c => { c with cseq := isn, port }
    csend Tcp.SYN (mss := mss)
    if (← get).cack == 0 then cfail "no SYN-ACK"
    modify fun c => { c with sacked := base }
    csend Tcp.ACK
    let rounds ← rnd 8
    for _ in [0:rounds] do
      if (← get).reset then break
      match ← rnd 10 with
      | 0 | 1 | 2 | 3 | 4 =>
        let c ← get
        let fresh ← if c.swnd > 0 then (·.succ) <$> rnd (min c.swnd 300) else pure 0
        sendFrom fresh
      | 5 => csend Tcp.ACK
      | 6 =>
        -- a segment beyond rcv.nxt (out of order); Ember ACKs and drops it
        let c ← get
        let d ← rbytes ((← rnd 20) + 1)
        csend (Tcp.ACK ||| Tcp.PSH) d (seq := some (c.cseq + UInt32.ofNat ((← rnd 10) + 1)))
      | 7 =>
        -- duplicate the last data segment as it was sent
        let c ← get
        if let some d := c.lastData then
          csend (Tcp.ACK ||| Tcp.PSH) d (seq := some (c.cseq - UInt32.ofNat d.size))
      | _ =>
        for _ in [0:(← rnd 8) + 1] do cfeed .tick
    -- deliver everything (both directions), then close
    for _ in [0:60] do
      let c ← get
      if c.reset || (c.echoed.size ≥ c.sent.size && (← allAcked)) then break
      if !(← allAcked) && c.swnd > 0 then sendFrom 0 else
        cfeed .tick
        csend Tcp.ACK (seq := some (← get).sacked)
    let finSeq := base + UInt32.ofNat (← get).sent.size
    modify fun c => { c with cseq := finSeq }
    if !(← get).reset then
      match ← rnd 10 with
      | 0 =>
        -- abort
        csend Tcp.RST
        modify fun c => { c with reset := true }
      | 1 | 2 | 3 | 4 | 5 => csend (Tcp.ACK ||| Tcp.FIN)
      | k =>
        -- wait for the idle close
        for _ in [0:idleTicks + 5] do
          if (← get).srvFin then break
          cfeed .tick
        if k == 6 then
          -- simultaneous close: our FIN does not acknowledge Ember's
          let c ← get
          let pkt := Peer.tcp c.port finSeq (c.cack - 1) (Tcp.ACK ||| Tcp.FIN) .empty
          modify fun c => { c with cseq := finSeq + 1 }
          cfeed (Peer.slip pkt)
        else
          if k == 7 then
            -- FIN-WAIT-2 for a while
            csend Tcp.ACK
            for _ in [0:(← rnd 10)] do cfeed .tick
          csend (Tcp.ACK ||| Tcp.FIN)
      for _ in [0:60] do
        if (← get).st.tcb.st == .listen || (← get).reset then break
        if (← get).srvFin then csend Tcp.ACK (seq := some (finSeq + 1))
        else if !Tcp.seqGe (← get).sacked (finSeq + 1) then
          -- our FIN may have been lost: send it again
          csend (Tcp.ACK ||| Tcp.FIN) (seq := some finSeq)
        cfeed .tick
    let c ← get
    if c.reset then
      if c.st.tcb.st != .listen then cfail s!"reset but not in LISTEN: {c.st.tcb.st.toString}"
      return
    if c.echoed.toList != c.sent.toList then
      cfail s!"echo mismatch: sent {c.sent.size} bytes, echoed {c.echoed.size}"
    if c.st.tcb.st != .listen then cfail s!"connection not closed: {c.st.tcb.st.toString}"
  let (r, c) ← body.run.run {}
  match r with
  | .ok _ => return .ok { kind := "tcp", inputs := c.ins }
  | .error e => return .error (e, c.ins)

/-! ## Mutations -/

/-- Mutate one SLIP-framed packet. -/
def mutatePacket (p : ByteArray) : RandM ByteArray := do
  if p.size == 0 then return p
  match ← randNat 6 with
  | 0 =>  -- bit flip, checksums left wrong
    let i ← randNat p.size
    return Bytes.set p i (Bytes.get p i ^^^ (1 <<< (← randNat 8).toUInt8))
  | 1 =>  -- bit flip in the IP header, header checksum fixed
    let i ← randNat (min 20 p.size)
    if i == 10 || i == 11 then return p
    return Peer.fixIpChecksum (Bytes.set p i (Bytes.get p i ^^^ (1 <<< (← randNat 8).toUInt8)))
  | 2 => return p.extract 0 (← randNat p.size)
  | 3 =>  -- bad IP checksum
    return Bytes.set p 10 (Bytes.get p 10 ^^^ 0x5A)
  | 4 =>  -- TCP sequence number far away (checksum fixed)
    if p.size < 40 || Bytes.get p 9 != Ipv4.protoTcp then return p
    let q := Bytes.set32 p 24 (Bytes.get32 p 24 + 0x40000000)
    let q := Bytes.set16 q 36 0
    let tl := q.size - 20
    return Bytes.set16 q 36 (Checksum.checksum q 20 tl (Checksum.pseudo Peer.ip Peer.ours 6 tl))
  | _ =>  -- payload byte flip with the transport checksum left wrong
    let i ← randRange (min 20 (p.size - 1)) (p.size - 1)
    return Bytes.set p i (Bytes.get p i ^^^ 0xFF)

def mutate (s : Session) : RandM Session := do
  let mut ins := s.inputs
  let k ← randRange 1 3
  for _ in [0:k] do
    let i ← randNat ins.size
    if let .rx b := ins[i]! then
      match Slip.decodeAll b with
      | [p] => ins := ins.set! i (.rx (Slip.encode (← mutatePacket p)))
      | _ => pure ()
  return { s with inputs := ins, mutated := true }

/-- Split the link byte stream at random places (ticks stay between). -/
def rechunk (s : Session) : RandM Session := do
  let mut out : Array Input := #[]
  let mut pend := ByteArray.empty
  for i in s.inputs do
    match i with
    | .tick =>
      if pend.size > 0 then out := out.push (.rx pend); pend := .empty
      out := out.push .tick
    | .rx b =>
      pend := pend ++ b
      while pend.size > 0 && (← randBool 40) do
        let k ← randRange 1 pend.size
        out := out.push (.rx (pend.extract 0 k))
        pend := pend.extract k pend.size
  if pend.size > 0 then out := out.push (.rx pend)
  return { s with inputs := out }

/-- Put ticks inside frames: some `rx` items are split in two with one to
three ticks between the halves (a tick in the middle of a frame is
deferred to its end; a second one gives the frame up). -/
def midTicks (s : Session) : RandM Session := do
  let mut out : Array Input := #[]
  for i in s.inputs do
    match i with
    | .rx b =>
      if b.size ≥ 2 && (← randBool 35) then
        let k ← randRange 1 (b.size - 1)
        out := out.push (.rx (b.extract 0 k))
        for _ in [0:(← randRange 1 3)] do out := out.push .tick
        out := out.push (.rx (b.extract k b.size))
      else out := out.push i
    | .tick => out := out.push i
  return { s with inputs := out }

/-! ## Ethernet: the same sessions in frames, with ARP around them

A generated session (possibly mutated) becomes an Ethernet session: each
packet in a frame from the peer's MAC, and between the frames ARP
requests and replies (for us, for others, malformed), frames for other
stations, other EtherTypes, truncated and oversized frames. -/

def peerMac : ByteArray := Bytes.ofList [0x02, 0x00, 0x00, 0x00, 0x00, 0x02]

def randMac : RandM ByteArray := do
  match ← randNat 4 with
  | 0 => return Arp.ourMacDefault
  | 1 => return Arp.broadcastMac
  | 2 => return peerMac
  | _ => randBytes 6

/-- A frame that is not part of the session. -/
def ethNoise (mtu : Nat) : RandM ByteArray := do
  let someIp : RandM UInt32 := do
    match ← randNat 4 with
    | 0 => return ourIpDefault
    | 1 => return peerIpDefault
    | 2 => return 0
    | _ => return 0x0A000000 + (← randNat 256).toUInt32
  match ← randNat 8 with
  | 0 | 1 =>  -- an ARP request
    let spa ← someIp
    let tpa ← someIp
    let sha ← if ← randBool 70 then pure peerMac else randBytes 6
    return Arp.frame (← randMac) sha Arp.typeArp (Arp.packet 1 sha spa (Bytes.ofList [0, 0, 0, 0, 0, 0]) tpa)
  | 2 =>  -- an ARP reply
    let sha ← randBytes 6
    return Arp.frame Arp.ourMacDefault sha Arp.typeArp (Arp.packet 2 sha (← someIp) Arp.ourMacDefault (← someIp))
  | 3 =>  -- ARP with a wrong field, or cut short
    let p := Arp.packet (← randRange 0 3).toUInt16 peerMac peerIpDefault Arp.ourMacDefault ourIpDefault
    let i ← randNat 8
    let cut ← randNat 28
    let flip ← randBool
    let p := if flip then Bytes.set p i (Bytes.get p i ^^^ 0x11) else p.extract 0 cut
    return Arp.frame Arp.broadcastMac peerMac Arp.typeArp p
  | 4 =>  -- another EtherType
    return Arp.frame Arp.ourMacDefault peerMac (← randNat 65536).toUInt16 (← randBytes (← randNat 40))
  | 5 =>  -- shorter than a header
    randBytes (← randNat 14)
  | 6 =>  -- too large for the buffer
    return Arp.frame Arp.ourMacDefault peerMac Arp.typeIpv4 (← randBytes (mtu + 1 + (← randNat 40)))
  | _ =>  -- a ping from a station not seen before, or to another address
    let src := 0x0A000000 + (← randRange 3 250).toUInt32
    let toUs ← randBool 80
    let dst := if toUs then ourIpDefault else src + 1
    return Arp.frame (← randMac) (← randBytes 6) Arp.typeIpv4
      (Peer.ping 7 1 (← randBytes (← randNat 32)) (src := src) (dst := dst))

/-- The Ethernet form of a SLIP session. -/
def toEth (s : Session) (mtu : Nat := mtuEth) : RandM Session := do
  let mut ins : Array Input := #[]
  for i in s.inputs do
    if ← randBool 12 then ins := ins.push (.rx (← ethNoise mtu))
    match i with
    | .tick =>
      -- four other stations push the peer out of the cache: what the
      -- tick then sends (a retransmission) finds no address
      if ← randBool 25 then
        for k in [0:4] do
          let src := 0x0A000064 + (← randNat 100).toUInt32 * 4 + k.toUInt32
          ins := ins.push (.rx (Arp.frame Arp.ourMacDefault (← randBytes 6) Arp.typeIpv4
            (Peer.ping 7 1 .empty (src := src))))
      ins := ins.push .tick
    | .rx b =>
      for p in Slip.decodeAll b (maxLen := 65535) do
        let dst ← if ← randBool 4 then randMac else pure Arp.ourMacDefault
        ins := ins.push (.rx (Arp.frame dst peerMac Arp.typeIpv4 p))
  if ← randBool 30 then ins := ins.push (.rx (← ethNoise mtu))
  return { s with kind := "eth-" ++ s.kind, cfg := { link := .eth, mtu }, inputs := ins }

/-! ## DHCP: a server that answers the client, not always well -/

def dhcpServer : UInt32 := 0x0A0000FE
def serverMac : ByteArray := Bytes.ofList [0x02, 0x00, 0x00, 0x00, 0x00, 0xFE]

/-- A BOOTREPLY in a frame; `opts` are raw option bytes. -/
def dhcpReply (xid : UInt32) (yi : UInt32) (chaddr : ByteArray) (opts : List UInt8) (dst : UInt32)
    (op : UInt8 := 2) (dport : UInt16 := Dhcp.clientPort) : ByteArray :=
  let fixed := [op, 1, 6, 0] ++ Bytes.be32 xid ++ [0, 0, 0x80, 0x00] ++ [0, 0, 0, 0] ++ Bytes.be32 yi ++
    Bytes.be32 dhcpServer ++ [0, 0, 0, 0]
  let m := Bytes.ofList (fixed ++ chaddr.toList ++ List.replicate 10 0 ++ List.replicate 192 0 ++
    Bytes.be32 Dhcp.magic ++ opts)
  Arp.frame Arp.broadcastMac serverMac Arp.typeIpv4
    (Ipv4.packet Ipv4.protoUdp 0x4444 dhcpServer dst (Udp.emit dhcpServer dst Dhcp.serverPort dport m))

/-- A session with the DHCP client on: ticks, and after each message of
the client an answer drawn from the right one, the wrong type, a wrong
transaction, a damaged message — and now and then traffic to the address
the client has (or had). -/
def dhcp : RandM Session := do
  let cfg : Config := { link := .eth, dhcp := true, mtu := mtuEth }
  let mut st := State.init cfg
  let mut ins : Array Input := #[]
  let steps ← randRange 4 40
  for _ in [0:steps] do
    let feed (st : State) (ins : Array Input) (i : Input) : State × Array Input := ((step st i).1, ins.push i)
    match ← randNat 11 with
    | 0 | 1 | 2 => (st, ins) := feed st ins .tick
    | 10 =>  -- silence: long enough for a timeout or a renewal
      for _ in [0:(← randRange 7 10)] do (st, ins) := feed st ins .tick
    | 3 =>  -- traffic for the address offered or bound
      let a := if st.ip != 0 then st.ip else st.dhcp.offered
      (st, ins) := feed st ins (.rx (Arp.frame Arp.ourMacDefault peerMac Arp.typeIpv4
        (Peer.ping 9 1 (← randBytes (← randNat 24)) (dst := a))))
    | 4 =>  -- who has the address?
      let a := if st.ip != 0 then st.ip else st.dhcp.offered
      (st, ins) := feed st ins (.rx (Arp.frame Arp.broadcastMac peerMac Arp.typeArp
        (Arp.packet 1 peerMac peerIpDefault (Bytes.ofList [0, 0, 0, 0, 0, 0]) a)))
    | _ =>
      -- an answer for the phase the client is in
      let ack ← randBool 85
      let any ← randRange 1 8
      let want : UInt8 := match st.dhcp.phase with
        | .selecting => 2
        | .requesting => if ack then 5 else 6
        | _ => any.toUInt8
      let right ← randBool 85
      let other ← randRange 0 8
      let mtype : UInt8 := if right then want else other.toUInt8
      let sameXid ← randBool 90
      let off ← randRange 1 3
      let xid := if sameXid then st.dhcp.xid else st.dhcp.xid + off.toUInt32
      let chaddr ← if ← randBool 92 then pure Arp.ourMacDefault else randBytes 6
      let yi := 0x0A000000 + (← randRange 2 200).toUInt32
      let lease ← match ← randNat 5 with
        | 0 => pure 0
        | 1 => pure 1
        | 2 => pure 3
        | 3 => randRange 2 40
        | _ => pure 3600
      -- options in either order, padded, sometimes without a type,
      -- sometimes cut off or with a length that runs past the end
      let tOpt : List UInt8 := [53, 1, mtype]
      let sOpt : List UInt8 := [54, 4] ++ Bytes.be32 dhcpServer
      let lOpt : List UInt8 := [51, 4] ++ Bytes.be32 lease.toUInt32
      let pad : List UInt8 := List.replicate (← randNat 3) 0
      let opts ← match ← randNat 12 with
        | 0 => pure (sOpt ++ lOpt ++ [255])
        | 1 => pure (tOpt ++ [255] ++ sOpt)
        | 2 => pure (lOpt ++ pad ++ sOpt ++ tOpt)
        | 3 => pure (tOpt ++ [54, 9, 1, 2])
        | 4 => pure ([53, 0] ++ tOpt ++ sOpt ++ [255])
        | 5 => pure (tOpt ++ [54, 2, 1, 2] ++ sOpt ++ lOpt ++ [255])
        | 6 => pure (pad ++ tOpt ++ [53, 1, 6] ++ sOpt ++ lOpt ++ [12, 3, 97, 98, 99, 255])
        | _ => pure (pad ++ tOpt ++ sOpt ++ pad ++ lOpt ++ [255])
      let toAll ← randBool 80
      let reply ← randBool 95
      let rightPort ← randBool 95
      let f := dhcpReply xid yi chaddr opts (if toAll then Ipv4.broadcast else yi)
        (op := if reply then 2 else 1) (dport := if rightPort then Dhcp.clientPort else 69)
      -- now and then damaged, or cut inside the fixed part
      let f ← match ← randNat 14 with
        | 0 => pure (f.extract 0 (← randRange 14 f.size))
        | 1 =>
          let i ← randRange 14 (f.size - 1)
          pure (Bytes.set f i (Bytes.get f i ^^^ 0x40))
        | _ => pure f
      (st, ins) := feed st ins (.rx f)
  return { kind := "dhcp", cfg, inputs := ins }

/-! ## Properties -/

/-- A transmitted packet is well-formed: IP header, lengths, and the
transport checksum all verify. -/
def wellFormed (p : ByteArray) : Option String :=
  match Ipv4.validate p (Bytes.get32 p 16) with
  | .error e => some s!"bad IP: {e}"
  | .ok (h, pl) =>
    if h.proto == Ipv4.protoIcmp then
      if Checksum.verifies (Checksum.sum pl 0 pl.size) then none else some "bad ICMP checksum"
    else if h.proto == Ipv4.protoUdp then
      match Udp.parse h.src h.dst pl with | .ok _ => none | .error e => some e
    else if h.proto == Ipv4.protoTcp then
      match Tcp.parse h.src h.dst pl with | .ok _ => none | .error e => some e
    else some "unknown protocol sent"

/-- Check the session's properties; the first violation, if any. -/
def properties (s : Session) : Option String := Id.run do
  let mut st := State.init s.cfg
  let mut idx := 0
  for i in s.inputs do
    let completes := match i with
      | .rx b => (Slip.decodeAll b).length > 0 || b.toList.contains Slip.END
      | .tick => false
    let (st', es) := step st i
    st := st'
    let accounted := es.any fun e => match e with
      | .tx _ | .drop _ | .tcb _ | .note _ => true
      | _ => false
    let framed := es.any fun e => match e with | .pkt t => t.startsWith "rx " | _ => false
    if completes && framed && !accounted then
      return some s!"input {idx}: a frame was consumed without output, drop or state change"
    for b in outputs es do
      for p in Slip.decodeAll b (maxLen := 65535) do
        if let some e := wellFormed p then return some s!"input {idx}: sent a malformed packet ({e}): {Pretty.ipSummary p}"
    idx := idx + 1
  return none

/-! ## Shrinking -/

/-- Remove inputs (halves, then one at a time) while `bad` still holds. -/
partial def shrink (bad : Array Input → Bool) (xs : Array Input) : Array Input := Id.run do
  let mut cur := xs
  let mut chunk := max 1 (cur.size / 2)
  while chunk ≥ 1 do
    let mut i := 0
    let mut progress := false
    while i < cur.size do
      let cand := cur.extract 0 i ++ cur.extract (i + chunk) cur.size
      if cand.size < cur.size && bad cand then
        cur := cand
        progress := true
      else i := i + chunk
    if !progress then
      if chunk == 1 then break
      chunk := chunk / 2
  return cur

end Ember.Spec.Gen
