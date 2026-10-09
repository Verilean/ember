import Ember.Spec.Scenario

/-!
# Hand-written scenarios (corpus fixtures with stated expectations)

Each scenario's trace is written to `Tests/Ember/corpus/<dir>/<name>.trace`
by `lake exe ember-fixtures`; `lake test` re-runs the scenarios (checking
their expectations) and replays every corpus file.
-/

namespace Ember.Tests.Scenarios
open Ember Ember.Spec Ember.Spec.Scenario
open Ember.Spec.Tcp (SYN ACK FIN RST PSH)

def str := Peer.str
def AP : UInt8 := ACK ||| PSH
def AF : UInt8 := ACK ||| FIN

/-- Tick until Ember's idle close sends FIN; checks no output before. -/
def idleClose : Sc Unit := do
  for _ in [0:idleTicks - 1] do
    discard <| feed .tick
    expectNoTx
  discard <| feed .tick
  discard <| expectInSeq AF
  expectState .finWait1

def rstEach (name doc : String) (setup : Sc Unit) : Scenario :=
  { name, dir := "tcp", doc, body := do
      setup
      discard <| seg RST (advance := false)
      expectNoTx
      expectState .listen }

/-- Tick by tick until something is sent; returns the number of ticks. -/
def ticksUntilTx (limit : Nat := 200) : Sc Nat := do
  for i in [1:limit+1] do
    let out ← feed .tick
    if !out.isEmpty then return i
  fail s!"nothing sent within {limit} ticks"

def tcp : List Scenario := [
  { name := "handshake-echo-close", dir := "tcp", doc := "open, echo, peer closes", body := do
      connect
      echo (str "hello")
      discard <| seg ACK
      expectNoTx
      closeFromPeer },
  rstEach "rst-syn-rcvd" "RST in SYN-RCVD returns to LISTEN" do
    discard <| seg SYN (mss := some 1460)
    discard <| expectSeg (SYN ||| ACK),
  rstEach "rst-established" "RST in ESTABLISHED" connect,
  rstEach "rst-last-ack" "RST in LAST-ACK" do
    connect
    discard <| seg AF
    discard <| expectInSeq AF
    expectState .lastAck,
  rstEach "rst-fin-wait-1" "RST in FIN-WAIT-1" do connect; idleClose,
  rstEach "rst-fin-wait-2" "RST in FIN-WAIT-2" do
    connect; idleClose
    discard <| seg ACK
    expectState .finWait2,
  rstEach "rst-time-wait" "RST in TIME-WAIT" do
    connect; idleClose
    discard <| seg AF
    discard <| expectInSeq ACK
    expectState .timeWait,
  { name := "rst-out-of-window", dir := "tcp", doc := "RST outside the window is ignored", body := do
      connect
      discard <| seg RST (seq := some ((← get).cseq + 100000))
      expectNoTx
      expectDrop "rst-out-of-window"
      expectState .established },
  { name := "out-of-window-data", dir := "tcp", doc := "segment outside the window: ACK and drop", body := do
      connect
      discard <| seg AP (str "far") (seq := some ((← get).cseq + 100000))
      discard <| expectInSeq ACK
      expectDrop "out-of-window"
      echo (str "near") },
  { name := "out-of-order", dir := "tcp", doc := "in-window segment beyond rcv.nxt: ACK and drop", body := do
      connect
      discard <| seg AP (str "later") (seq := some ((← get).cseq + 10))
      discard <| expectInSeq ACK
      expectDrop "out-of-order"
      echo (str "first") },
  { name := "fin-out-of-order", dir := "tcp", doc := "FIN beyond rcv.nxt is not accepted", body := do
      connect
      discard <| seg AF (seq := some ((← get).cseq + 5))
      discard <| expectInSeq ACK
      expectDrop "out-of-order"
      expectState .established },
  { name := "duplicate-syn", dir := "tcp", doc := "retransmitted SYN in SYN-RCVD: SYN-ACK again", body := do
      let c ← get
      discard <| seg SYN (mss := some 1460)
      let s1 ← expectSeg (SYN ||| ACK)
      discard <| seg SYN (seq := some c.cseq) (mss := some 1460)
      let s2 ← expectSeg (SYN ||| ACK)
      expectDrop "duplicate-syn"
      expect (s1.seq == s2.seq) "same ISS on the retransmitted SYN-ACK"
      modify fun c => { c with sseq := s1.seq + 1 }
      discard <| seg ACK
      expectState .established },
  { name := "old-syn-in-established", dir := "tcp", doc := "the handshake SYN again, now outside the window", body := do
      let isn := (← get).cseq
      connect
      discard <| seg SYN (seq := some isn)
      discard <| expectInSeq ACK
      expectDrop "out-of-window"
      expectState .established },
  { name := "syn-in-window", dir := "tcp", doc := "SYN inside the window resets the connection", body := do
      connect
      discard <| seg SYN (seq := some (← get).cseq)
      let r ← expectSeg RST
      expect (r.seq == (← get).sseq) "RST at snd.nxt"
      expectDrop "syn-in-window"
      expectState .listen },
  { name := "simultaneous-close", dir := "tcp", doc := "FINs cross: FIN-WAIT-1 → CLOSING → TIME-WAIT → LISTEN", body := do
      connect; idleClose
      let c ← get
      discard <| seg AF (ack := some (c.sseq - 1))
      discard <| expectInSeq ACK
      expectState .closing
      discard <| seg ACK
      expectNoTx
      expectState .timeWait
      for _ in [0:timeWaitTicks - 1] do discard <| feed .tick
      expectState .timeWait
      discard <| feed .tick
      expectState .listen },
  { name := "active-close", dir := "tcp", doc := "idle close: FIN-WAIT-1 → FIN-WAIT-2 → TIME-WAIT; FIN retransmission in TIME-WAIT is ACKed", body := do
      connect; echo (str "x"); discard <| seg ACK
      idleClose
      discard <| seg ACK
      expectNoTx
      expectState .finWait2
      discard <| seg AF
      discard <| expectInSeq ACK
      expectState .timeWait
      let c ← get
      discard <| seg AF (seq := some (c.cseq - 1))
      discard <| expectInSeq ACK
      expectDrop "out-of-window"
      ticks timeWaitTicks
      expectState .listen },
  { name := "fin-wait-2-timeout", dir := "tcp", doc := "no FIN from the peer: FIN-WAIT-2 gives up", body := do
      connect; idleClose
      discard <| seg ACK
      expectState .finWait2
      ticks (idleTicks - 1)
      expectState .finWait2
      discard <| feed .tick
      expectNoTx
      expectDrop "fin-wait-2-timeout"
      expectState .listen },
  { name := "fin-with-data", dir := "tcp", doc := "data and FIN in one segment: echo and FIN in one segment", body := do
      connect
      discard <| seg (AP ||| FIN) (str "last words")
      discard <| expectInSeq (AP ||| FIN) (str "last words")
      expectState .lastAck
      discard <| seg ACK
      expectState .listen },
  { name := "ack-of-unsent", dir := "tcp", doc := "ACK beyond snd.nxt: ACK and drop", body := do
      connect
      discard <| seg ACK (ack := some ((← get).sseq + 1000))
      discard <| expectInSeq ACK
      expectDrop "ack-of-unsent"
      expectState .established },
  { name := "listen-ack", dir := "tcp", doc := "ACK in LISTEN: RST from the ACK number", body := do
      discard <| seg ACK (ack := some 4242)
      let r ← expectSeg RST
      expect (r.seq == 4242) "RST seq = SEG.ACK"
      expectDrop "ack-in-listen" },
  { name := "listen-no-syn", dir := "tcp", doc := "neither SYN nor ACK nor RST in LISTEN: drop", body := do
      discard <| seg PSH (str "x")
      expectNoTx
      expectDrop "no-syn-in-listen" },
  { name := "listen-rst", dir := "tcp", doc := "RST in LISTEN: ignored", body := do
      discard <| seg RST
      expectNoTx
      expectDrop "rst-in-listen" },
  { name := "closed-port", dir := "tcp", doc := "SYN to a closed port: RST-ACK", body := do
      let c ← get
      discard <| seg SYN (dport := 9)
      let r ← expectSeg (RST ||| ACK)
      expect (r.ack == c.cseq + 1) "RST acknowledges the SYN"
      expectDrop "tcp-port-closed" },
  { name := "second-connection", dir := "tcp", doc := "a second connection while busy: RST-ACK", body := do
      connect
      let c ← get
      modify fun c => { c with port := 40001, cseq := 7000 }
      discard <| seg SYN
      discard <| expectSeg (RST ||| ACK)
      expectDrop "unsupported-second-connection"
      set { (← get) with port := c.port, cseq := c.cseq, sseq := c.sseq }
      echo (str "still here") },
  { name := "syn-with-data", dir := "tcp", doc := "data on a SYN is not accepted (peer retransmits it)", body := do
      discard <| seg SYN (str "early") (mss := some 1460)
      let s ← expectSeg (SYN ||| ACK)
      expect (s.ack == 1001) "only the SYN is acknowledged"
      modify fun c => { c with cseq := 1001, sseq := s.seq + 1 }
      discard <| seg ACK
      echo (str "early") },
  { name := "options", dir := "tcp", doc := "SYN with every option kind; MSS read, others skipped", body := do
      let c ← get
      let opts := [1, 1, 4, 2, 8, 10, 0, 0, 0, 1, 0, 0, 0, 0, 3, 3, 7, 30, 6, 1, 2, 3, 4, 2, 4, 0x01, 0x00, 0]
      discard <| sendPkt (Peer.tcpOpts c.port c.cseq 0 SYN opts)
      let s ← expectSeg (SYN ||| ACK)
      expect ((← tcb).peerMss == 256) s!"MSS option read: {(← tcb).peerMss}"
      modify fun c => { c with cseq := c.cseq + 1, sseq := s.seq + 1 }
      discard <| seg ACK
      echo (str "opts") },
  { name := "malformed-option", dir := "tcp", doc := "a malformed option ends option parsing", body := do
      let c ← get
      discard <| sendPkt (Peer.tcpOpts c.port c.cseq 0 SYN [1, 30, 1, 2, 4, 1, 0])
      discard <| expectSeg (SYN ||| ACK)
      expect ((← tcb).peerMss == 536) "default MSS" },
  { name := "small-mss", dir := "tcp", doc := "peer MSS 100: window and echo limited to 100", body := do
      connect (mss := some 100)
      let d := Bytes.ofList ((List.range 150).map UInt8.ofNat)
      discard <| seg AP d (advance := false)
      let s ← expectSeg AP
      expect (s.data.size == 100 && s.wnd == 0) s!"100 bytes taken, window 0 (got {s.data.size}, {s.wnd})"
      modify fun c => { c with cseq := c.cseq + 100, sseq := c.sseq + 100 }
      discard <| seg ACK
      let u ← expectInSeq ACK
      expect (u.wnd == 100) "window update"
      echo (d.extract 100 150) },
  { name := "zero-window", dir := "tcp", doc := "with a zero window, ACKs are still processed", body := do
      connect
      let d := Bytes.ofList ((List.range 256).map fun i => UInt8.ofNat (i * 3))
      echo d
      let s ← lastSeg
      expect (s.wnd == 0) "window closed"
      let c ← get
      discard <| seg AP (str "more") (seq := some c.cseq) (ack := some (c.sseq - 256))
      let a ← expectInSeq ACK
      expect (a.wnd == 0 && a.ack == c.cseq) "data refused, window still 0"
      discard <| seg ACK
      let u ← expectInSeq ACK
      expect (u.wnd == 256) "window update after the echo is acknowledged"
      echo (str "more") },
  { name := "overlap-retransmit", dir := "tcp", doc := "retransmission overlapping rcv.nxt is trimmed", body := do
      connect
      let c ← get
      echo (str "abcdef")
      discard <| seg AP (str "abcdefgh") (seq := some c.cseq)
      modify fun c => { c with cseq := c.cseq + 2 }
      discard <| expectInSeq AP (str "gh") },
  { name := "retransmit-regenerate", dir := "timer", doc := "unacknowledged echo is regenerated after the RTO (uIP model)", body := do
      connect
      echo (str "abc")
      let first ← lastSeg
      let n ← ticksUntilTx
      expect (n == rtoInit) s!"retransmission after {rtoInit} ticks, got {n}"
      let again ← expectSeg AP
      expect (again.seq == first.seq && again.data.toList == first.data.toList) "same bytes"
      discard <| seg ACK
      expectNoTx
      for _ in [0:idleTicks - 1] do
        discard <| feed .tick
        expectNoTx
      expect (!(← tcb).outstanding) "nothing outstanding"
      expectState .established },
  { name := "backoff", dir := "timer", doc := "exponential back-off schedule, then give up with RST", body := do
      connect
      echo (str "unacked")
      let mut gaps : Array Nat := #[]
      for _ in [0:maxRetries] do
        gaps := gaps.push (← ticksUntilTx)
        discard <| expectSeg AP
      gaps := gaps.push (← ticksUntilTx)
      discard <| expectSeg (RST ||| ACK)
      expectDrop "give-up"
      expectState .listen
      let table := (List.range (maxRetries + 1)).map rto
      expect (gaps.toList == table) s!"gaps {gaps} = table {table}" },
  { name := "syn-ack-giveup", dir := "timer", doc := "SYN-ACK retransmitted on the same schedule, then reset", body := do
      discard <| seg SYN (mss := some 1460)
      discard <| expectSeg (SYN ||| ACK)
      for _ in [0:maxRetries] do
        discard <| ticksUntilTx
        discard <| expectSeg (SYN ||| ACK)
      discard <| ticksUntilTx
      discard <| expectSeg (RST ||| ACK)
      expectState .listen },
  { name := "ticks-in-listen", dir := "timer", doc := "ticks with no connection do nothing", body := do
      ticks 5
      expectNoTx
      expectState .listen },
  { name := "bad-checksum", dir := "tcp", doc := "corrupted TCP checksum", body := do
      let c ← get
      let p := Peer.tcp c.port c.cseq 0 SYN
      discard <| sendPkt (Bytes.set p 36 (Bytes.get p 36 ^^^ 0xFF))
      expectNoTx
      expectDrop "bad-tcp-checksum" },
  { name := "bad-header", dir := "tcp", doc := "short segment, data offset below 20", body := do
      let c ← get
      let p := Peer.tcp c.port c.cseq 0 SYN
      discard <| sendPkt (Peer.fixIpChecksum (Bytes.set16 (p.extract 0 36) 2 36))
      expectDrop "short-tcp"
      let q := Bytes.set p 32 0x40
      let q := Bytes.set16 q 36 0
      let q := Bytes.set16 q 36 (Checksum.checksum q 20 20 (Checksum.pseudo Peer.ip Peer.ours 6 20))
      discard <| sendPkt q
      expectDrop "bad-tcp-header" }
]

def pingP := Peer.pingPayload 56

def ipv4 : List Scenario :=
  let base := Peer.ping 7 1 pingP
  let mut1 (name doc : String) (f : ByteArray → ByteArray) (r : String) : Scenario :=
    { name, dir := "ipv4", doc, body := do
        discard <| sendPkt (f base)
        expectNoTx
        expectDrop r }
  [ mut1 "short-packet" "fewer than 20 bytes" (·.extract 0 19) "short-packet",
    mut1 "bad-version" "version 6" (fun p => Peer.fixIpChecksum (Bytes.set p 0 0x65)) "bad-version",
    mut1 "ihl-4" "IHL below 5" (fun p => Peer.fixIpChecksum (Bytes.set p 0 0x44)) "bad-ihl",
    mut1 "ihl-beyond" "IHL beyond the packet" (fun p => Peer.fixIpChecksum ((Bytes.set p 0 0x4F).extract 0 40)) "bad-ihl",
    mut1 "bad-checksum" "header checksum wrong" (fun p => Bytes.set p 11 (Bytes.get p 11 ^^^ 1)) "bad-ip-checksum",
    mut1 "length-over" "total length beyond the packet" (fun p => Peer.fixIpChecksum (Bytes.set16 p 2 200)) "bad-length",
    mut1 "length-under" "total length below the header" (fun p => Peer.fixIpChecksum (Bytes.set16 p 2 10)) "bad-length",
    mut1 "fragment-mf" "more-fragments set" (fun p => Peer.fixIpChecksum (Bytes.set16 p 6 0x2000)) "fragment",
    mut1 "fragment-offset" "non-zero fragment offset" (fun p => Peer.fixIpChecksum (Bytes.set16 p 6 0x0001)) "fragment",
    mut1 "ttl-zero" "TTL 0" (fun p => Peer.fixIpChecksum (Bytes.set p 8 0)) "ttl-zero",
    mut1 "not-for-us" "another destination" (fun _ => Peer.ping 7 1 pingP (dst := 0x0A000003)) "not-for-us",
    mut1 "broadcast-icmp" "ping to 255.255.255.255" (fun _ => Peer.ping 7 1 pingP (dst := 0xFFFFFFFF)) "broadcast",
    mut1 "unknown-protocol" "protocol 99" (fun p => Peer.fixIpChecksum (Bytes.set p 9 99)) "unsupported-protocol",
    { name := "options", dir := "ipv4", doc := "header with options: skipped, reply has IHL 5", body := do
        let icmp := base.extract 20 base.size
        let h := Ipv4.header Ipv4.protoIcmp 0x1234 Peer.ip Peer.ours (icmp.size + 4)
        let h := Bytes.set (Bytes.set16 h 0 0x4600) 1 0
        let p := Peer.fixIpChecksum (h ++ Bytes.ofList [1, 1, 1, 0] ++ icmp)
        discard <| sendPkt p
        expectTxCount 1
        let r := (← get).last.head!
        expect (Bytes.get r 0 == 0x45 && r.size == base.size) "fresh 20-byte header" },
    { name := "padding", dir := "ipv4", doc := "bytes beyond the total length are ignored", body := do
        discard <| sendPkt (base ++ Bytes.ofList [0, 0, 0, 0, 0, 0])
        expectTxCount 1
        expect ((← get).last.head!.size == base.size) "reply as long as the request" } ]

def icmp : List Scenario := [
  { name := "short", dir := "icmp", doc := "ICMP message under 8 bytes", body := do
      discard <| sendPkt (Ipv4.packet 1 1 Peer.ip Peer.ours (Bytes.ofList [8, 0, 0xf7, 0xff]))
      expectDrop "short-icmp" },
  { name := "bad-checksum", dir := "icmp", doc := "ICMP checksum wrong", body := do
      let p := Peer.ping 1 1 pingP
      discard <| sendPkt (Bytes.set p 22 (Bytes.get p 22 ^^^ 0x10))
      expectDrop "bad-icmp-checksum" },
  { name := "echo-reply-in", dir := "icmp", doc := "an echo reply is not answered", body := do
      let m := Peer.icmpEcho 1 1 pingP
      let m := Bytes.set16 (Bytes.set m 0 0) 2 0
      let m := Bytes.set16 m 2 (Checksum.checksum m 0 m.size)
      discard <| sendPkt (Ipv4.packet 1 1 Peer.ip Peer.ours m)
      expectDrop "unsupported-icmp-type" },
  { name := "odd-length", dir := "icmp", doc := "odd payload length (checksum pads the last byte)", body := do
      discard <| sendPkt (Peer.ping 3 9 (Peer.pingPayload 57))
      expectTxCount 1 },
  { name := "code-kept", dir := "icmp", doc := "a non-zero code is kept in the reply", body := do
      let m := Peer.icmpEcho 1 1 pingP
      let m := Bytes.set16 (Bytes.set m 1 5) 2 0
      let m := Bytes.set16 m 2 (Checksum.checksum m 0 m.size)
      discard <| sendPkt (Ipv4.packet 1 1 Peer.ip Peer.ours m)
      expectTxCount 1
      expect (Bytes.get (← get).last.head! 21 == 5) "code 5" },
  { name := "max-size", dir := "icmp", doc := "a ping filling the MTU", body := do
      discard <| sendPkt (Peer.ping 1 1 (Peer.pingPayload (mtu - 28)))
      expectTxCount 1 } ]

def udp : List Scenario := [
  { name := "zero-checksum", dir := "udp", doc := "checksum 0 means none; the reply has one", body := do
      let p := Peer.udp 5000 7 (str "nochk")
      discard <| sendPkt (Bytes.set16 p 26 0)
      expectTxCount 1
      expect (Bytes.get16 (← get).last.head! 26 != 0) "reply checksummed" },
  { name := "bad-checksum", dir := "udp", doc := "UDP checksum wrong", body := do
      let p := Peer.udp 5000 7 (str "x")
      discard <| sendPkt (Bytes.set16 p 26 ((Bytes.get16 p 26) ^^^ 0x0101))
      expectDrop "bad-udp-checksum" },
  { name := "length-over", dir := "udp", doc := "UDP length beyond the IP payload", body := do
      let p := Peer.udp 5000 7 (str "abc")
      discard <| sendPkt (Bytes.set16 (Bytes.set16 p 24 20) 26 0)
      expectDrop "bad-udp-length" },
  { name := "length-under", dir := "udp", doc := "UDP length below 8", body := do
      let p := Peer.udp 5000 7 (str "abc")
      discard <| sendPkt (Bytes.set16 (Bytes.set16 p 24 4) 26 0)
      expectDrop "bad-udp-length" },
  { name := "short", dir := "udp", doc := "IP payload under 8 bytes", body := do
      discard <| sendPkt (Ipv4.packet 17 1 Peer.ip Peer.ours (Bytes.ofList [0, 1, 0, 7]))
      expectDrop "short-udp" },
  { name := "closed-port", dir := "udp", doc := "no service on port 9", body := do
      discard <| sendPkt (Peer.udp 5000 9 (str "discard"))
      expectNoTx
      expectDrop "udp-port-closed" },
  { name := "trailing", dir := "udp", doc := "bytes beyond the UDP length are not echoed", body := do
      let d := Udp.emit Peer.ip Peer.ours 5000 7 (str "keep")
      discard <| sendPkt (Ipv4.packet 17 1 Peer.ip Peer.ours (d ++ str "junk"))
      expectTxCount 1
      expect ((← get).last.head!.size == 20 + 8 + 4) "only the datagram" },
  { name := "broadcast", dir := "udp", doc := "UDP echo to the broadcast address is answered from our address", body := do
      discard <| sendPkt (Peer.udp 5000 7 (str "all") (dst := 0xFFFFFFFF))
      expectTxCount 1 } ]

def slip : List Scenario := [
  { name := "escapes", dir := "slip", doc := "END and ESC inside the payload", body := do
      let pl := Bytes.ofList [0xC0, 0xDB, 0xC0, 0xDC, 0xDD, 0xDB, 0xDB, 0xC0]
      discard <| sendPkt (Peer.udp 5000 7 pl)
      expectTxCount 1
      let r := (← get).last.head!
      expect ((r.extract 28 r.size).toList == pl.toList) "payload round-trips" },
  { name := "empty-frames", dir := "slip", doc := "back-to-back END bytes are ignored", body := do
      discard <| sendRaw (Bytes.ofList [0xC0, 0xC0, 0xC0, 0xC0])
      expectNoTx
      discard <| sendPkt (Peer.ping 1 1 pingP)
      expectTxCount 1 },
  { name := "split-frame", dir := "slip", doc := "a frame split across two chunks", body := do
      let f := Slip.encode (Peer.ping 1 2 pingP)
      discard <| sendRaw (f.extract 0 30)
      expectNoTx
      discard <| sendRaw (f.extract 30 f.size)
      expectTxCount 1 },
  { name := "two-frames", dir := "slip", doc := "two frames in one chunk", body := do
      discard <| sendRaw (Slip.encode (Peer.ping 1 3 pingP) ++ Slip.encode (Peer.udp 5000 7 (str "x")))
      expectTxCount 2 },
  { name := "oversize", dir := "slip", doc := "a frame over the MTU is dropped whole", body := do
      discard <| sendRaw (Slip.encode (Peer.ping 1 4 (Peer.pingPayload (mtu - 27))))
      expectNoTx
      expectDrop "oversize-frame"
      discard <| sendPkt (Peer.ping 1 5 pingP)
      expectTxCount 1 },
  { name := "esc-other", dir := "slip", doc := "ESC before an ordinary byte keeps the byte", body := do
      let f := Slip.encode (Peer.ping 1 6 pingP)
      -- escape the first byte of the payload (0x45): ESC 0x45
      let g := Bytes.ofList [0xC0, 0xDB] ++ f.extract 1 f.size
      discard <| sendRaw g
      expectTxCount 1 },
  { name := "noise", dir := "slip", doc := "line noise between frames is a short frame", body := do
      discard <| sendRaw (Bytes.ofList [0xC0, 0x11, 0x22, 0x33, 0xC0])
      expectDrop "short-packet"
      discard <| sendPkt (Peer.ping 1 7 pingP)
      expectTxCount 1 } ]

/-! ## Ethernet + ARP (M1.11) -/

def ethCfg : Config := { link := .eth, mtu := mtuEth }
def peerMac : ByteArray := Bytes.ofList [2, 0, 0, 0, 0, 2]
def macN (n : Nat) : ByteArray := Bytes.ofList [2, 0, 0, 0, 1, UInt8.ofNat n]

def ethIp (pkt : ByteArray) (src := peerMac) (dst := Arp.ourMacDefault) : Trace.Input :=
  Trace.Input.rx (Arp.frame dst src Arp.typeIpv4 pkt)

def arpReq (spa tpa : UInt32) (sha := peerMac) : Trace.Input :=
  Trace.Input.rx (Arp.frame Arp.broadcastMac sha Arp.typeArp
        (Arp.packet 1 sha spa (Bytes.ofList [0,0,0,0,0,0]) tpa))

def arp : List Scenario := [
  { name := "request-reply", dir := "arp", doc := "who-has for us is answered; the sender is cached", cfg := ethCfg, body := do
      discard <| feed (arpReq Peer.ip Peer.ours)
      expectTxCount 1
      expect (((← get).st.arp.lookup Peer.ip).isSome) "sender cached" },
  { name := "request-other", dir := "arp", doc := "who-has for another address: not cached, not answered", cfg := ethCfg, body := do
      discard <| feed (arpReq Peer.ip 0x0A000009)
      expectNoTx
      expectDrop "arp-not-for-us"
      expect (((← get).st.arp.lookup Peer.ip).isNone) "not cached (RFC 826 merge rule)" },
  { name := "learn-from-ip", dir := "arp", doc := "a ping from an unknown host is answered (learned from the frame)", cfg := ethCfg, body := do
      discard <| feed (ethIp (Peer.ping 1 1 pingP))
      expectTxCount 1
      let f := (← get).last.head!
      expect ((f.extract 0 6).toList == peerMac.toList) "reply to the sender's MAC" },
  { name := "not-our-mac", dir := "arp", doc := "unicast to another MAC", cfg := ethCfg, body := do
      discard <| feed (ethIp (Peer.ping 1 1 pingP) (dst := macN 7))
      expectDrop "not-our-mac" },
  { name := "short-frame", dir := "arp", doc := "frame under 14 bytes", cfg := ethCfg, body := do
      discard <| feed (.rx (Bytes.ofList [1, 2, 3]))
      expectDrop "short-frame" },
  { name := "ethertype", dir := "arp", doc := "IPv6 EtherType is not handled", cfg := ethCfg, body := do
      discard <| feed (.rx (Arp.frame Arp.ourMacDefault peerMac 0x86DD (Bytes.ofList [0x60, 0, 0, 0])))
      expectDrop "unsupported-ethertype" },
  { name := "bad-arp", dir := "arp", doc := "ARP for another protocol type; short ARP", cfg := ethCfg, body := do
      let p := Arp.packet 1 peerMac Peer.ip (Bytes.ofList [0,0,0,0,0,0]) Peer.ours
      discard <| feed (.rx (Arp.frame Arp.broadcastMac peerMac Arp.typeArp (Bytes.set16 p 2 0x86DD)))
      expectDrop "bad-arp"
      discard <| feed (.rx (Arp.frame Arp.broadcastMac peerMac Arp.typeArp (p.extract 0 20)))
      expectDrop "short-arp" },
  { name := "oversize", dir := "arp", doc := "IPv4 payload over the MTU", cfg := ethCfg, body := do
      discard <| feed (ethIp (Peer.ping 1 1 (Peer.pingPayload (mtuEth - 27))))
      expectDrop "oversize-frame" },
  { name := "miss-after-eviction", dir := "arp", doc := "four other hosts evict the peer; the retransmission sends who-has instead", cfg := ethCfg, body := do
      discard <| feed (ethIp (Peer.tcp 40000 1000 0 SYN))
      let s ← expectSeg (SYN ||| ACK)
      for i in [0:4] do
        discard <| feed (arpReq (0x0A000010 + UInt32.ofNat i) Peer.ours (sha := macN i))
      let n ← ticksUntilTx
      expect (n == rtoInit) "retransmission due"
      let f := (← get).last.head!
      expect (Bytes.get16 f 12 == Arp.typeArp && Bytes.get32 f 38 == Peer.ip) "who-has the peer"
      expectDrop "arp-miss"
      discard <| feed (.rx (Arp.frame Arp.ourMacDefault peerMac Arp.typeArp
        (Arp.packet 2 peerMac Peer.ip Arp.ourMacDefault Peer.ours)))
      let n ← ticksUntilTx
      expect (n == rto 1) "next retransmission on schedule"
      let r ← expectSeg (SYN ||| ACK)
      expect (r.seq == s.seq) "same SYN-ACK" } ]

/-! ## DHCP client (M1.12) -/

def dhcpCfg : Config := { ethCfg with dhcp := true }
def server : UInt32 := 0x0A000002
def offered : UInt32 := 0x0A000032

/-- A BOOTREPLY from the server for the client's current transaction. -/
def dhcpReply (mtype : UInt8) (xid : UInt32) (lease : UInt32 := 120) (yi := offered) : Trace.Input :=
  let fixed := [2, 1, 6, 0] ++ Bytes.be32 xid ++ [0, 0, 0x80, 0] ++ Bytes.be32 0 ++ Bytes.be32 yi ++
    Bytes.be32 server ++ Bytes.be32 0
  let chaddr := Arp.ourMacDefault.toList ++ List.replicate 10 0
  let opts := [53, 1, mtype, 54, 4] ++ Bytes.be32 server ++ [51, 4] ++ Bytes.be32 lease ++
    [1, 4, 255, 255, 255, 0, 255]
  let body := Bytes.ofList (fixed ++ chaddr ++ List.replicate 192 0 ++ Bytes.be32 Dhcp.magic ++ opts)
  let u := Udp.emit server Ipv4.broadcast Dhcp.serverPort Dhcp.clientPort body
  ethIp (Ipv4.packet Ipv4.protoUdp 9 server Ipv4.broadcast u) (dst := Arp.broadcastMac)

def xid : Sc UInt32 := do return (← get).st.dhcp.xid

def expectDhcp (mtype : UInt8) : Sc Unit := do
  let f := (← get).last
  expect (f.length == 1) s!"one DHCP message, got {f.length}"
  let p := f.head!.extract 14 f.head!.size
  expect (Bytes.get p 9 == Ipv4.protoUdp && Bytes.get16 p 22 == Dhcp.serverPort) "to port 67"
  let os := Dhcp.options (p.extract 28 p.size)
  expect ((os.find? (·.1 == 53)).map (fun o => Bytes.get o.2 0) == some mtype) s!"message type {mtype}"

def bind : Sc Unit := do
  discard <| feed .tick
  expectDhcp 1
  discard <| feed (dhcpReply 2 (← xid))
  expectDhcp 3
  discard <| feed (dhcpReply 5 (← xid))
  expect ((← get).st.ip == offered) "bound to the offered address"

def dhcp : List Scenario := [
  { name := "dora-renew", dir := "dhcp", doc := "DISCOVER, OFFER, REQUEST, ACK; renewal at T1", cfg := dhcpCfg, body := do
      bind
      discard <| feed (ethIp (Peer.ping 1 1 pingP (dst := offered)))
      expectTxCount 1
      let n ← ticksUntilTx (limit := 400)
      expect (n == 120) s!"renewal at T1 = 120 ticks, got {n}"
      expectDhcp 3
      discard <| feed (dhcpReply 5 (← xid))
      expect ((← get).st.dhcp.phase == .bound) "bound again" },
  { name := "nak", dir := "dhcp", doc := "NAK returns to INIT and forgets the address", cfg := dhcpCfg, body := do
      bind
      discard <| ticksUntilTx (limit := 400)
      discard <| feed (dhcpReply 6 (← xid))
      expect ((← get).st.ip == 0 && (← get).st.dhcp.phase == .init) "back to INIT"
      discard <| feed .tick
      expectDhcp 1 },
  { name := "timeout", dir := "dhcp", doc := "no OFFER: DISCOVER again after the retry interval", cfg := dhcpCfg, body := do
      discard <| feed .tick
      expectDhcp 1
      let n ← ticksUntilTx
      expect (n == Dhcp.retryTicks + 1) s!"rediscover after {Dhcp.retryTicks}+1 ticks, got {n}"
      expectDhcp 1 },
  { name := "wrong-xid", dir := "dhcp", doc := "a reply to another transaction is ignored", cfg := dhcpCfg, body := do
      discard <| feed .tick
      discard <| feed (dhcpReply 2 ((← xid) + 7))
      expectNoTx
      expectDrop "dhcp-not-ours" },
  { name := "unexpected", dir := "dhcp", doc := "an ACK while selecting is ignored", cfg := dhcpCfg, body := do
      discard <| feed .tick
      discard <| feed (dhcpReply 5 (← xid))
      expectDrop "dhcp-unexpected"
      expect ((← get).st.ip == 0) "still unbound" } ]

def all : List Scenario := tcp ++ ipv4 ++ icmp ++ udp ++ slip ++ arp ++ dhcp

end Ember.Tests.Scenarios
