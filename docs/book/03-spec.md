# 3 · The reference stack (Spec)

`Ember.Spec` is the TCP/IP stack written as ordinary Lean: pure functions
over `ByteArray`, no I/O, no clock, no randomness. You can `#eval` it,
replay a packet capture through it, and prove things about it. Every
other implementation in the repository — the stack written in the Ember
language, the C emitted from it, the images running on the ESP32-C3 and
the Z80 — is judged by one question: *does it produce the trace the Spec
produces?* ([Chapter 4](04-testing.md) shows how that question is asked;
[Chapter 10](10-proofs.md) shows where it is answered by proof instead of
by test.)

| Module | What it is |
|---|---|
| [`Ember/Spec/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Stack.lean) | the whole stack as one step function |
| [`Ember/Spec/Config.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Config.lean) | constants shared with the Ember version: addresses, MTU, timers |
| [`Ember/Spec/Slip.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Slip.lean) | RFC 1055 framing |
| [`Ember/Spec/Arp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Arp.lean) | Ethernet II framing and ARP |
| [`Ember/Spec/Ipv4.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Ipv4.lean), [`Icmp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Icmp.lean), [`Udp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Udp.lean) | IPv4, ICMP echo, UDP (echo on port 7) |
| [`Ember/Spec/Dhcp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Dhcp.lean) | DHCP client (optional) |
| [`Ember/Spec/Tcp/`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Tcp) | TCP with one connection and the echo application built in |
| [`Ember/Spec/Checksum.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Checksum.lean) | the Internet checksum, incremental update |
| [`Ember/Spec/Srv/`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Srv) | the same stack with the application taken out of TCP: an `App` interface, `n` connections, HTTP, TLS |
| [`Ember/Spec/Peer.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Peer.lean), [`Scenario.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Scenario.lean), [`Gen.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Gen.lean) | packet builders, hand-written scenarios and random sessions used by the tests ([Chapter 4](04-testing.md)) |

## The shape: one step function

The stack is a state machine driven by two kinds of input: a chunk of
link bytes, or a timer tick. Both are defined next to the trace format in
[`Ember/Trace/Event.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Event.lean):

```lean
/-- Inputs of a stack: a chunk of link bytes, or one timer tick. -/
inductive Input where
  | rx (bytes : ByteArray)
  | tick
  deriving Inhabited
```

What a step produces is a list of trace events — `tx` lines carrying the
bytes put on the wire, interleaved with diagnostic `pkt`, `tcb`, `drop`
and `note` lines. From [`Ember/Spec/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Stack.lean):

```lean
def step (s : State) (i : Input) : State × List Event :=
  let ((), (s', es)) := (input i).run (s, #[])
  (s', es.toList)

/-- Only the observable outputs of a step. -/
def outputs (es : List Event) : List ByteArray :=
  es.filterMap fun | .tx b => some b | _ => none
```

Internally each step runs in `StackM := StateM (State × Array Event)`:
helper functions read and modify the state and append events (`ev`,
`dropR`, `txFrame`, `sendIp`). `run` folds `step` over an input sequence
and packs the result into a `Trace`, which is what the tests compare:

```lean
/-- Run a whole input sequence; the trace of the reference stack. -/
def run (cfg : Config) (inputs : Array Input) (impl := "spec") : Trace := Id.run do
  let mut s := State.init cfg
  let mut steps : Array (Input × List Event) := #[]
  for i in inputs do
    let (s', es) := step s i
    s := s'
    steps := steps.push (i, es)
  return Trace.ofSteps (cfg.header impl) steps
```

The stack is **deterministic by construction**: the IP identification
and the TCP initial sequence number come from counters in the state, and
time exists only as `tick` inputs. The same inputs always give the same
trace, byte for byte — which is what makes a recorded trace usable as a
test.

### The state

```lean
structure State where
  cfg  : Config := {}
  slip : Slip.Dec := {}
  ipId : UInt16 := 1
  ip   : UInt32 := ourIpDefault
  tcb  : Tcp.Tcb := {}
  iss  : UInt32 := issInit
  arp  : Arp.Cache := {}
  dhcp : Dhcp.St := {}
  /-- SLIP: a tick arrived while a frame was being received and waits for its end. -/
  tickDue : Bool := false
  deriving Inhabited
```

Everything is bounded: one SLIP decoder buffer (at most one MTU), one TCP
control block, an ARP cache of four entries. Nothing grows with traffic.

## Configuration

Two things are called "config". The **run-time choices** of a stack are
the `Config` structure in `Stack.lean`:

```lean
structure Config where
  link : LinkKind := .slip
  dhcp : Bool := false
  ip   : UInt32 := ourIpDefault
  mac  : ByteArray := Arp.ourMacDefault
  /-- Largest IP datagram accepted and sent (the packet buffer size). -/
  mtu  : Nat := Spec.mtu
  deriving Inhabited
```

`LinkKind` is `slip` or `eth`. With `dhcp := true` the stack starts
without an address (`State.init` sets `ip := 0`) and acquires one.
A trace header records `link`, `mtu` and `dhcp`, and
`Config.ofHeader` rebuilds the configuration from it, so a fixture
carries the configuration it must be replayed with.

The **constants** shared by the Spec and the stack written in Ember
(`Ember.Net`) live in [`Ember/Spec/Config.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Config.lean):

| Constant | Value | Meaning |
|---|---|---|
| `ourIpDefault` | `0x0A000001` | 10.0.0.1, Ember's address |
| `peerIpDefault` | `0x0A000002` | 10.0.0.2, the peer of fixtures and generators |
| `mtu` | 296 | SLIP's customary MTU; also the size of the one packet buffer |
| `mtuEth` | 576 | the Ethernet build (RFC 2131 needs 576-byte datagrams for DHCP) |
| `mssFor mtu` | `mtu - 40` | the MSS announced on SYN-ACK (256 at MTU 296) |
| `ttlDefault` | 64 | TTL of every packet sent |
| `echoPort` | 7 | UDP and TCP echo |
| `rtoInit` / `rtoMax` | 3 / 48 ticks | first retransmission timeout, cap of the back-off |
| `maxRetries` | 8 | retransmissions before the connection is reset |
| `timeWaitTicks` | 20 | TIME-WAIT (2 MSL) |
| `idleTicks` | 60 | idle close by the echo application; also the FIN-WAIT-2 limit |
| `issInit` / `issStep` | `0x00010000` / `0x00010000` | first ISN, and the step per new connection |

One tick is nominally 500 ms. The retransmission back-off is a table,
not an estimate:

```lean
/-- Back-off schedule: `rtoInit · 2^k`, capped at `rtoMax`. -/
def rto (k : Nat) : Nat := min rtoMax (rtoInit * 2 ^ (min k 16))
```

## The receive path

A received byte travels down a chain of small functions in `Stack.lean`.
On a SLIP link:

```
input (.rx bytes)
  └─ byteInput c          one byte at a time
       └─ slipByte c      Slip.Dec.feed; a complete frame →
            └─ frameInput f        `pkt rx …` line
                 └─ ipInput f      Ipv4.validate, then by protocol:
                      ├─ Icmp.reply           → sendIp (ICMP)
                      ├─ udpInput             → echo on port 7, DHCP on port 68
                      └─ Tcp.parse → runTcp (Tcp.input src seg)
```

On an Ethernet link `.rx` carries one whole frame, and `frameInput` goes
to `ethInput`, which handles ARP and passes IPv4 payloads to the same
`ipInput`. Every check that fails emits a `drop reason=…` event with a
fixed name. **The order of the checks and the names of the reasons are
part of the specification**: the Ember version performs the same checks
in the same order, so both report the same reason for a malformed packet,
and the comparison in [Chapter 4](04-testing.md) can include drop lines.

### SLIP (RFC 1055)

The decoder is a byte-at-a-time state machine, as the runtime feeds it
from the UART ring. Where RFC 1055 leaves room, it follows the Linux
driver (from the module comment of [`Slip.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Slip.lean)):

* `END` always ends a frame, even right after `ESC`;
* `ESC` followed by anything other than `ESC_END`/`ESC_ESC` stores that
  byte unchanged;
* empty frames (back-to-back `END`s) are ignored;
* a frame longer than the MTU is dropped as a whole (`oversize-frame`).

```lean
/-- Feed one byte. -/
def Dec.feed (d : Dec) (c : UInt8) (maxLen : Nat := mtu) : Dec × Result :=
  if c == END then
    let r := if d.over then Result.drop "oversize-frame"
             else if d.buf.size == 0 then Result.none
             else Result.frame d.buf
    ({}, r)
  else if d.esc then
    let v := if c == ESC_END then END else if c == ESC_ESC then ESC else c
    (d.store v maxLen, .none)
  else if c == ESC then ({ d with esc := true }, .none)
  else (d.store c maxLen, .none)
```

The encoder writes `END payload END`.

### Ethernet II and ARP

The second link layer, for raw Wi-Fi frames. Frames are not padded to 60
bytes (as with Linux on a TAP device, padding is the driver's job). The
ARP cache has `cacheSize = 4` entries, replaced round-robin. Following
RFC 826's merge rule, a request updates the sender's entry if it exists
and adds it when the request is for us; replies always update. Received
IPv4 frames also refresh the cache with their source, as uIP's `arp_ipin`
does. When a packet must be sent to an address that is not in the cache,
`sendIp` sends an ARP request instead and drops the packet (`arp-miss`);
the peer's retransmission then finds the entry.

Frame checks, in order: `short-frame`, `not-our-mac`, `oversize-frame`,
`unsupported-ethertype`; ARP checks: `short-arp`, `bad-arp`,
`arp-not-for-us`.

### IPv4

[`Ipv4.validate`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Ipv4.lean) checks a received packet in
this order — the table is the module's own:

| # | Check | Drop reason |
|---|---|---|
| 1 | fewer than 20 bytes | `short-packet` |
| 2 | version ≠ 4 | `bad-version` |
| 3 | IHL < 5 or IHL·4 > packet size | `bad-ihl` |
| 4 | header checksum wrong | `bad-ip-checksum` |
| 5 | total length < IHL·4 or > packet size | `bad-length` |
| 6 | MF set or fragment offset ≠ 0 | `fragment` |
| 7 | TTL = 0 | `ttl-zero` |
| 8 | destination neither ours nor 255.255.255.255 | `not-for-us` |

Options are skipped (the payload starts at IHL·4); bytes beyond the total
length (link padding) are ignored. Replies always carry a fresh 20-byte
header: TTL 64, identification from the `ipId` counter, and DF set
exactly where Linux sets it — on UDP and TCP, not on ICMP echo replies
(`dfFor`). A broadcast that is not UDP is dropped (`broadcast`), and a
protocol other than ICMP, UDP or TCP gives `unsupported-protocol`.

### ICMP

Only echo. The reply is the request's message with one byte changed
(type 8 → 0) and the checksum updated incrementally (RFC 1624), the way
the small targets do it:

```lean
/-- The ICMP message answering `msg`, or a drop reason. -/
def reply (msg : ByteArray) : Except String ByteArray := do
  if msg.size < 8 then throw "short-icmp"
  if !Checksum.verifies (Checksum.sum msg 0 msg.size) then throw "bad-icmp-checksum"
  if Bytes.get msg 0 != typeEchoRequest then throw "unsupported-icmp-type"
  let old := Bytes.get16 msg 0
  let new := (typeEchoReply.toUInt16 <<< 8) ||| (old &&& 0x00FF)
  let m := Bytes.set16 msg 0 new
  return Bytes.set16 m 2 (Checksum.incremental (Bytes.get16 msg 2) old new)
```

Checksums are accumulated in 16 bits with end-around carry, never in a
32-bit accumulator ([`Checksum.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Checksum.lean)) —
again the form the Ember code uses on 8-bit machines.

### UDP

`Udp.parse` checks `short-udp`, `bad-udp-length` (length field below 8
or beyond the IP payload) and `bad-udp-checksum` (a zero checksum means
"none", RFC 768). `udpInput` in `Stack.lean` then dispatches on the
destination port:

```lean
    if d.dport == echoPort then
      sendIp Ipv4.protoUdp h.src (Udp.emit s.ip h.src d.dport d.sport d.data)
    else if d.dport == Dhcp.clientPort && s.cfg.dhcp then
      dhcpApply (Dhcp.input s.dhcp s.ip s.cfg.mac (Bytes.slice p 8 (p.size - 8)))
    else dropR "udp-port-closed"
```

Replies always carry a checksum (a computed 0 is sent as `0xFFFF`).

### DHCP client

Optional (`Config.dhcp`), and meant for the Ethernet build. The phases,
from [`Dhcp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Dhcp.lean):

```
INIT → (DISCOVER) SELECTING → (OFFER, REQUEST) REQUESTING →
(ACK) BOUND → at T1 = lease/2, REQUEST again (renewing) → ACK → BOUND
```

A NAK, or no answer within `retryTicks` (8), returns to INIT and forgets
the address. Messages are broadcast with the broadcast flag set, so
replies reach the client before it has an address. The transaction id is
`xidBase + n` for the n-th exchange — a counter again, so traces stay
reproducible. DHCP is driven by `Dhcp.input` (a message on port 68) and
`Dhcp.tick`; both return an `Out` record (new state, address, an optional
message to broadcast, an optional drop reason or note) that `dhcpApply`
carries out. Checks: `bad-dhcp`, `dhcp-not-ours`, `dhcp-unexpected`.

## TCP

TCP is the largest part of the Spec, split over five files in
[`Ember/Spec/Tcp/`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Tcp): `Header` (parse and emit),
`Tcb` (the connection), `Output` (what is sent), `Input` (segment
arrival) and `Timer` (what a tick does). The subset is deliberately
small, in the style of uIP:

* **one connection**, **passive open** on port 7; CLOSED is transient,
  a closed connection is back in LISTEN;
* the states `LISTEN SYN-RCVD ESTABLISHED CLOSE-WAIT LAST-ACK FIN-WAIT-1
  FIN-WAIT-2 CLOSING TIME-WAIT`;
* **in-order data only**; a segment beyond `rcv.nxt` is ACKed and
  dropped (`out-of-order`), and the peer retransmits;
* **MSS** is the only option read (other options of valid length are
  skipped) and the only one sent, on the SYN-ACK;
* **no retransmission buffer**. The echo application owns the data, and
  a retransmission regenerates the unacknowledged part from it.

### The control block

```lean
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
```

### Windows and MSS

The echo buffer `pending` holds at most one segment. Its capacity is the
smaller of the two MSS values, and the receive window is whatever room is
left in it:

```lean
/-- Size of the echo buffer: one segment in either direction. -/
def Tcb.cap (t : Tcb) : Nat := min t.ourMss t.peerMss

/-- Current receive window. -/
def Tcb.wnd (t : Tcb) : Nat := t.cap - t.pending.size
```

So at the default MTU of 296 the SYN-ACK announces MSS 256 and window 256;
after five bytes have arrived and not yet been acknowledged by the peer,
the window is 251. The peer's own receive window is not consulted:
Ember never has more than one MSS unacknowledged. The echo application
takes new data only as the previous echo is acknowledged, and the window
says so. When the window reopens from zero, `output` sends a window
update.

### Segment arrival

`Tcp.input` follows RFC 9293 §3.10.7, reduced. Its module comment states
the order, which is again part of the specification:

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

A segment that is not for the current connection goes to `listenInput`:
a SYN opens the connection if it is in LISTEN; anything that arrives
while another connection is open gets a reset and
`drop reason=unsupported-second-connection`. A segment for any port
other than 7 gets a reset and `tcp-port-closed`.

### Output

`output` sends **at most one segment per input**: new echo data (with FIN
when the application has closed and nothing is left), otherwise a pure
ACK when one is owed, or a window update. Data segments carry `ACK|PSH`.

### Timers and retransmission

`Tcp.tick` ([`Timer.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Tcp/Timer.lean)) does, in
this order:

* TIME-WAIT counts down to LISTEN;
* while anything is outstanding the retransmission timer counts down; on
  expiry the unacknowledged part is regenerated and sent again
  (`rexmit`), and the timeout becomes `rto r` for the r-th retry; after
  `maxRetries` the connection is reset (`drop reason=give-up`);
* an ESTABLISHED connection with nothing in flight counts idle ticks; at
  `idleTicks` the echo application closes it (active close, FIN-WAIT-1);
* FIN-WAIT-2 waits at most `idleTicks` for the peer's FIN, then closes
  (`fin-wait-2-timeout`), as Linux's `tcp_fin_timeout` does.

Retransmission is the uIP model: since there is no copy of sent data,
`rexmit` rebuilds the segment from the application's buffer:

```lean
/-- Retransmission: regenerate everything unacknowledged from `snd.una`. -/
def rexmit : TcpM Unit := do
  let t := (← get).tcb
  if t.st == .synRcvd then sendSynAck
  else
    let data := Bytes.slice t.pending 0 t.sent
    let flags := ACK ||| (if t.sent > 0 then PSH else 0) ||| (if t.finSent then FIN else 0)
    sendSeg flags t.sndUna data
```

There is no RTT estimation and no congestion control: the back-off is the
fixed `rto` table. Without ticks, none of the timeouts happen.

### A tick in the middle of a frame

On a SLIP link the packet buffer holds the frame being received, and a
tick may need to send (a retransmission). So a tick that arrives in the
middle of a frame waits for the end of that frame (`tickDue`); a second
tick while one is waiting gives the incomplete frame up and runs both
ticks:

```lean
def tickArrives : StackM Unit := do
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
```

This rule was added after the proof of the Ember version's tick handler
found that a tick sent in the middle of a received frame destroyed that
frame (see the project README and
[`Tests/Ember/corpus/timer/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/timer/README.md)).

### One session, as the Spec prints it

The fixture
[`Tests/Ember/corpus/tcp/handshake-echo-close.trace`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/tcp/handshake-echo-close.trace)
is a full connection: SYN, ACK, five bytes echoed, the peer's FIN. With
the raw `rx`/`tx` bytes left out, its diagnostic lines read:

```
0      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [S] seq=1000 ack=0 win=64240 data=0
0      pkt  tx ipv4 10.0.0.1>10.0.0.2 tcp 7>40000 [S.] seq=65536 ack=1001 win=256 data=0
0      tcb  state=SYN-RCVD snd.una=65536 snd.nxt=65537 rcv.nxt=1001 pending=0 sent=0 rt=3/0
1      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [.] seq=1001 ack=65537 win=64240 data=0
1      tcb  state=ESTABLISHED snd.una=65537 snd.nxt=65537 rcv.nxt=1001 pending=0 sent=0 rt=0/0
2      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [P.] seq=1001 ack=65537 win=64240 data=5
2      pkt  tx ipv4 10.0.0.1>10.0.0.2 tcp 7>40000 [P.] seq=65537 ack=1006 win=251 data=5
2      tcb  state=ESTABLISHED snd.una=65537 snd.nxt=65542 rcv.nxt=1006 pending=5 sent=5 rt=3/0
3      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [.] seq=1006 ack=65542 win=64240 data=0
3      tcb  state=ESTABLISHED snd.una=65542 snd.nxt=65542 rcv.nxt=1006 pending=0 sent=0 rt=0/0
4      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [F.] seq=1006 ack=65542 win=64240 data=0
4      pkt  tx ipv4 10.0.0.1>10.0.0.2 tcp 7>40000 [F.] seq=65542 ack=1007 win=256 data=0
4      tcb  state=LAST-ACK snd.una=65542 snd.nxt=65543 rcv.nxt=1007 pending=0 sent=0 rt=3/0
5      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>7 [.] seq=1007 ack=65543 win=64240 data=0
5      tcb  state=LISTEN snd.una=0 snd.nxt=0 rcv.nxt=0 pending=0 sent=0 rt=0/0
```

Everything in this chapter is visible here: the ISN is `issInit` (65536);
the window is 256 (`cap`) and shrinks to 251 while five echoed bytes are
unacknowledged; the retransmission timer is armed at `rto 0 = 3` while
data or a FIN is outstanding (`rt=3/0`) and disarmed when it is ACKed;
the peer's FIN goes straight to LAST-ACK because the echo application has
nothing left to send, so the FIN rides on the ACK; and the final ACK
returns the connection to LISTEN.

## What is deliberately unsupported

The limits of the TCP subset are listed, with what the stack does about
each, in
[`Tests/Ember/corpus/tcp/UNSUPPORTED.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/tcp/UNSUPPORTED.md).
Each item is either answered with RST or dropped with a `drop reason=`:

| Not supported | Behaviour | Reason given |
|---|---|---|
| More than one connection | RST-ACK to a second SYN | `unsupported-second-connection` |
| Active open | — (Ember never connects out) | — |
| Ports other than 7 | RST-ACK | `tcp-port-closed` |
| Out-of-order reassembly | ACK and drop; the peer retransmits | `out-of-order` |
| Data on a SYN | only the SYN is acknowledged; the peer retransmits the data | — |
| Options other than MSS (window scale, SACK, timestamps) | skipped; not echoed in SYN-ACK, so the peer turns them off | — |
| Urgent data | URG ignored, data treated as normal | — |
| Peer's receive window | ignored: Ember never has more than one MSS (≤ 256 bytes) unacknowledged | — |
| Congestion control, RTT estimation | fixed back-off schedule (`rto k`) | — |
| RFC 5961 challenge ACKs | RFC 793 behaviour: RST in window closes, SYN in window resets | `syn-in-window` |
| TIME-WAIT assassination protection (RFC 1337) | RST in TIME-WAIT closes | — |
| IP options | skipped on input, never sent | — |
| Fragmented datagrams | dropped | `fragment` |

Beyond TCP: no IPv6, no fragment reassembly, ICMP echo only. The
original design document ([`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md)
§2.1) also listed ARP and DHCP as out of scope; both were added later
(plan M1.11 and M1.12) and are described above.

"Running out" is always a protocol event with a name, never a memory
error: an oversize frame is `oversize-frame`, a second connection is
`unsupported-second-connection`, a full echo buffer is a zero window.

## The server layer: `Ember.Spec.Srv`

`Ember.Spec.Tcp` has the echo application written into it: `Tcb.pending`
is the echo buffer, port 7 is everywhere, the window is the room left in
the buffer. That stack, and every proof about it, stays as it is.
[`Ember/Spec/Srv/Tcp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Tcp.lean) is the same
TCP with the application taken out and given as a parameter, and
[`Ember/Spec/Srv/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Stack.lean) is the
whole stack over it, with `n` connections.

### The `App` interface

An application is a record. The connection asks it, uIP-style, how much
it can take, hands it in-order data, and asks it for the bytes to send —
including again, on a retransmission, because the stack keeps no copy:

```lean
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
  /-- State shared by all connections (plan M9.5: the device-wide sequence
  number of control requests); `Unit` for echo and the sites of M8. -/
  G : Type := Unit
  ginit : G := by exact ()
  /-- `recv` with the shared state: in-order data of a connection may change
  it.  By default the shared state is left alone. -/
  recvG : G → σ → ByteArray → G × σ := fun g s d => (g, recv s d)
  /-- A UDP port whose datagrams go to the application (plan M9.4: the
  time), and what one does to the shared state; no answer is sent. -/
  udpPort : Option UInt16 := none
  udpG : G → ByteArray → G := fun g _ => g
```

The required fields are the first ten. The fields with defaults — a
shared state `G` across connections, and a UDP port feeding it — are used
by the control application of [Chapter 9](09-control.md); echo and the
plain HTTP sites leave them alone.

The control block of `Srv.Tcp` is `Spec.Tcp`'s with `pending` replaced by
`app : A.σ`, and its window becomes the application's answer:

```lean
def Tcb.wnd (t : Tcb A) : Nat := A.room t.app t.cap
```

### The smallest application: echo

```lean
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
```

Read it against the `Tcb` of `Spec.Tcp`: the state is the `pending`
buffer, `room` is `cap - pending.size`, `recv` appends, `acked` drops
the acknowledged prefix, and echo never closes on its own (`close _ :=
false`) but does close an idle connection (`idleClose := true`).

The connection logic of `Srv.Tcp` is `Spec.Tcp`'s, statement for
statement, with calls to the `App` where the echo buffer was. Three
changes are needed by applications that are not echo, and change nothing
for echo (from the module comment):

* a segment carries at most `cap - sent` new bytes, so no more than one
  segment's worth is in flight;
* the FIN goes with the last of the data only, not before it;
* the idle close is the application's choice (`idleClose`).

You can see the second change in `Srv.output`: the FIN is sent only when
the segment being sent carries everything the application has left.

```lean
    let unsent := A.avail t.app - t.sent
    let n := min unsent (t.cap - t.sent)
    let closing := (t.st == .closeWait || t.closeReq || A.close t.app) && !t.finSent
    let fin := closing && n == unsent
```

### Several connections

`Srv.Config` extends `Spec.Config` with a connection count, and
`Srv.State A` holds an array of control blocks instead of one:

```lean
structure Config extends Spec.Config where
  /-- Number of connections. -/
  conns : Nat := 1
  deriving Inhabited
```

Everything that is not TCP — SLIP, Ethernet and ARP, IPv4, ICMP, the UDP
echo, DHCP, ticks in the middle of a SLIP frame — is `Spec.Stack`'s,
written over this state. A segment goes to the connection whose tuple it
carries; otherwise to the first connection in LISTEN — or, when the
application allows it (`reuseTimeWait`), one in TIME-WAIT; when there is
none it is answered with RST (`unsupported-second-connection`), as the
one-connection stack does:

```lean
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
```

A tick ticks every connection, in order. With several connections the
`tcb` lines start with `conn=i `; with one they are exactly
`Spec.Stack`'s.

Running a stack with an application is one call:
`Srv.run A cfg inputs`, the same shape as `Spec.run`.

### Why the echo instance matters

Because `Srv` with `echo` and one connection is meant to *be* `Spec.Stack`,
the test suite checks it literally — every trace line, diagnostics
included — on the whole corpus and on generated sessions. From
[`Tests/Ember/SrvTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/SrvTests.lean):

```lean
/-- The two stacks' traces as text, or the first line where they differ. -/
def same (cfg : Spec.Config) (ins : Array Input) : Option String :=
  let a := (Spec.run cfg ins).print.splitOn "\n"
  let b := (Srv.run Srv.echo (srvCfg cfg) ins).print.splitOn "\n"
```

That is how a generalisation of the reference stays the reference: the
old, proved stack and the new, general one are tied together by a test
on every fixture.

### Larger applications

The same interface carries the real applications of the project:

| Application | Module | Chapter |
|---|---|---|
| HTTP/1.1, static site, one request per connection (`appM8`) | [`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean) | [6](06-http-app.md) |
| TLS 1.3 server with HTTP inside | [`Ember/Spec/Srv/Tls.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Tls.lean) | [7](07-https.md) |
| Bearer-token check on protected routes | [`Ember/Spec/Srv/Auth.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Auth.lean) | [8](08-auth.md) |
| Control requests and kept connections (`appCtl`) | [`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean) | [9](09-control.md) |

The HTTP application of a static site, for comparison with `echo`:

```lean
/-- The HTTP application of a site as in M8 (no control routes, one request per connection). -/
def appM8 (site : Site) : App where
  σ := Conn
  port := site.port
  init := {}
  room _ cap := cap
  recv := recv site
  avail c := c.resp.size
  bytes c off n := Bytes.slice c.resp off n
  acked c n := { c with resp := c.resp.extract n c.resp.size }
  close c := c.decided
  idleClose := true
  reuseTimeWait := true
```

The state is a `Conn` (the request read so far and the response built
for it); the response is the outgoing stream; the application closes once
it has decided the response, and the FIN goes out with its last byte. It
takes a TIME-WAIT connection for a new client because HTTP servers close
first.

Next: [Chapter 4](04-testing.md) — how the Spec's traces are recorded,
compared and used to test everything else.
