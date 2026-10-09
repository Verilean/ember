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
