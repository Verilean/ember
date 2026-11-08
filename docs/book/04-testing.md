# 4 · Traces and testing

Ember has several implementations of the same stack — the reference in
Lean ([Chapter 3](03-spec.md)), the stack written in the Ember language
and run by its interpreter ([Chapter 2](02-language.md)), the C emitted
from that program, and the images on the ESP32-C3 and the Z80
([Chapter 5](05-targets.md)). They are tested in one way: **feed them the
same inputs and compare the traces they write.** Everything in this
chapter — the fixture corpus, the Linux recordings, the random sessions,
`ember-diff`, the test suites — is built on one line-oriented text
format.

| Piece | Where |
|---|---|
| Trace events, header, `Input` | [`Ember/Trace/Event.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Event.lean) |
| Printer and parser | [`Ember/Trace/Text.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Text.lean) |
| First-divergence comparison | [`Ember/Trace/Diff.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Diff.lean) |
| Fixtures | [`Tests/Ember/corpus/`](https://github.com/Verilean/ember/tree/main/Tests/Ember/corpus), [`Tests/Ember/regress/`](https://github.com/Verilean/ember/tree/main/Tests/Ember/regress) |
| Recording from Linux | [`tools/ember/record-linux.py`](https://github.com/Verilean/ember/blob/main/tools/ember/record-linux.py), [`tools/ember/record-corpus.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/record-corpus.sh) |
| Hand-written scenarios | [`Ember/Spec/Scenario.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Scenario.lean), [`Tests/Ember/Scenarios.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/Scenarios.lean) |
| Random sessions | [`Ember/Spec/Gen.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Gen.lean), [`Ember/Tools/GenRun.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/GenRun.lean) |
| C host harness | [`Tests/Ember/host/harness.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/host/harness.c) |
| Test entry point | [`Tests/AllTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/AllTests.lean), [`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md) |
| CI script, size gate | [`tools/ember/ci.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/ci.sh), [`tools/ember/size-report.py`](https://github.com/Verilean/ember/blob/main/tools/ember/size-report.py) |

## The trace format

A trace is a header line and then one event per line. Here is the start
of a real fixture,
[`Tests/Ember/corpus/tcp/closed-port.trace`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/tcp/closed-port.trace)
— a SYN to port 9, answered with a reset:

```
# ember-trace v1  impl=spec  build=dev  profile=host64  link=slip
# hand-written scenario `closed-port` (Tests/Ember/Scenarios.lean): SYN to a closed port: RST-ACK
# expected outputs are the Spec's, checked against the scenario's expectations
0      rx   c0 45 00 00 28 34 56 40 00 40 06 f2 77 0a 00 00 02 0a 00 00 01 9c 40 00 09 00 00 03 e8 00 00 00 00 50 02 fa f0 00 be 00 00 c0
0      pkt  rx ipv4 10.0.0.2>10.0.0.1 tcp 40000>9 [S] seq=1000 ack=0 win=64240 data=0
0      pkt  tx ipv4 10.0.0.1>10.0.0.2 tcp 9>40000 [R.] seq=0 ack=1001 win=0 data=0
0      tx   c0 45 00 00 28 00 01 40 00 40 06 26 cd 0a 00 00 01 0a 00 00 02 00 09 9c 40 00 00 00 00 00 00 03 e9 50 14 00 00 fb 9b 00 00 c0
0      drop reason=tcp-port-closed
```

The first column is the **step number**: the index of the input being
consumed, not a time. Traces from a fast host and a slow Z80 therefore
line up. The second column is the event kind:

```lean
inductive Event where
  | rx   (bytes : ByteArray)
  | tx   (bytes : ByteArray)
  | tick
  | pkt  (text : String)
  | tcb  (text : String)
  | drop (reason : String)
  | note (text : String)
  deriving Inhabited
```

| Kind | Class | Payload |
|---|---|---|
| `rx` | observable | link bytes received in this step, in hex (SLIP-framed, or one Ethernet frame) |
| `tick` | observable | none: one timer tick |
| `tx` | observable | link bytes transmitted |
| `pkt` | diagnostic | a one-line decode of a frame (`rx …` / `tx …`) |
| `tcb` | diagnostic | the TCP control block after the step |
| `drop` | diagnostic | `reason=<name>`, one of the fixed drop reasons of [Chapter 3](03-spec.md) |
| `note` | diagnostic | free text (DHCP progress, a reset by the peer, a trap) |

`rx`, `tx` and `tick` are **observable**: they are what any
implementation, including one running on a board, can be asked to agree
on. The `rx` and `tick` lines of a trace are also its **inputs**:
`Trace.inputs` reads them back, so every trace is at the same time a test
input and its expected output. The diagnostic kinds explain a divergence;
`pkt` lines all come from one decoder (`Ember.Util.Pretty`), so two
implementations never disagree about how a packet is *printed*.

The header carries `impl` (who wrote the trace: `spec`, `linux`,
`ember-interp`, `c`, `z80`, …), `build`, `profile`, `link`, and, when
they differ from the defaults, `mtu=N`, `dhcp=on` and `mask=…`. A
fixture therefore says which stack configuration it must be replayed on
(`Spec.Config.ofHeader`). Lines starting with `#` after the header are
comments, used for provenance.

`Trace.parse ∘ Trace.print` is the identity on every trace; the corpus
replay checks it on each fixture.

### Masking

Linux's IP identification is random, so a Linux recording cannot match
Ember's counter byte for byte. Fixtures recorded from Linux carry
`mask=ipv4.id` in their header; before comparison, `normalize` zeroes the
identification of every packet whose header checksum is valid and
recomputes the checksum (a packet with a bad checksum is left alone, so
that the error still shows):

```lean
def maskIpId (p : ByteArray) : ByteArray :=
  if p.size < 20 then p else
  let ihl := ((Bytes.get p 0) &&& 0x0F).toNat * 4
  if ihl < 20 || ihl > p.size || !Spec.Checksum.verifies (Spec.Checksum.sum p 0 ihl) then p
  else
    let q := Bytes.set16 (Bytes.set16 p 4 0) 10 0
    Bytes.set16 q 10 (Spec.Checksum.checksum q 0 ihl)
```

## `ember-diff`

```
lake exe ember-diff A.trace B.trace [--observable | --drops] [--context N] [--first-only] [--all]
```

`Trace.diff` compares two traces line by line and reports the first
difference (or all of them with `--all`). What is compared:

| Option | Lines compared |
|---|---|
| (none) | every line, diagnostics included |
| `--observable` | `rx`, `tx`, `tick` |
| `--drops` | `rx`, `tx`, `tick` and `drop` — the drop reasons are named alike in every implementation |

The report names the index of the first differing event, prints both
lines (`A:` and `B:`), shows `--context N` lines around it in each trace
(default 3), and — for two differing `rx`/`tx` payloads — decodes both
packets and lists the fields that differ, as `<field>: <a> vs <b>`, plus
the offset of the first differing byte. A divergence is explained, not
just located. The exit status is 0 when the traces agree and 1 when they
do not, so the tool sits directly in scripts. `--first-only` prints a
single line for scripts.

Two related tools: `lake exe ember-pcap X.trace > X.pcap` writes a
trace's packets for Wireshark, and `lake exe ember-replay F.trace…` runs
the inputs of each fixture through the Spec and compares observable lines
(`--write` rewrites the fixture with the Spec's full trace).

## The corpus

[`Tests/Ember/corpus/`](https://github.com/Verilean/ember/tree/main/Tests/Ember/corpus) holds one directory per
protocol, each with a `README.md` that gives the provenance of every
fixture. At the commit this book describes there are 114 fixtures:

| Directory | Fixtures | of which `linux-*` | Topic |
|---|---|---|---|
| `slip/` | 7 | 0 | framing, escapes, oversize frames, noise |
| `ipv4/` | 15 | 0 | every validation check, options, padding |
| `icmp/` | 10 | 4 | echo, sizes, malformed messages |
| `udp/` | 15 | 7 | echo, checksums, lengths, closed port |
| `tcp/` | 39 | 7 | handshake, RST in every state, windows, out-of-order, MSS, options |
| `timer/` | 8 | 1 | retransmission, back-off, TIME-WAIT, idle close, ticks mid-frame |
| `arp/` | 14 | 5 | Ethernet framing, ARP cache, `link=eth` |
| `dhcp/` | 6 | 1 | DORA, renewal, NAK, timeout |

Fixtures come from three sources.

**Linux as responder.** Linux plays Ember's role (10.0.0.1); the
fixture's inputs are crafted requests and its expected `tx` lines are
Linux's answers. These say "answer like Linux does", byte for byte up to
the IP identification. The header records it:

```
# ember-trace v1  impl=linux  build=linux-6.18.45  profile=host64  link=slip  mask=ipv4.id
# recorded by: tools/ember/record-linux.py responder icmp Tests/Ember/corpus/icmp
# Linux 6.18.45 as 10.0.0.1 answering 10.0.0.2
# IP identification is random in Linux: compared with mask=ipv4.id
```

(from [`Tests/Ember/corpus/icmp/linux-ping-s56.trace`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/icmp/linux-ping-s56.trace)).

**Linux as client.** Linux is the peer (10.0.0.2) running real programs
— `ping`, `nc`, `curl`, or the socket scenarios of
[`tools/ember/tcp-scenarios.py`](https://github.com/Verilean/ember/blob/main/tools/ember/tcp-scenarios.py) —
against `ember-host`, the Spec stack. The inputs are Linux's and the
outputs the Spec's; that the command succeeded shows that Linux accepted
those outputs. Each scenario script exits 0 only when Linux saw the
expected behaviour (echo intact, a reset on a second connection,
connection refused on another port, …).

**Hand-written scenarios.** RFC corner cases that Linux will not produce
on demand: RST in every TCP state, segments outside the window, a zero
window, every IPv4 check. Each is a small Lean program with stated
expectations (below), and its trace is generated from it.

A fourth directory, [`Tests/Ember/regress/`](https://github.com/Verilean/ember/tree/main/Tests/Ember/regress),
receives shrunk failures from the random generators; a file stays after
its bug is fixed, as a regression test. The application layers have their
own recorded sessions outside `corpus/` (`Tests/Ember/http/`,
`https/`, `http-auth/`, `https-auth/`, `http-ctl/`, `https-ctl/`; see
Chapters [6](06-http-app.md)–[9](09-control.md)).

## Recording from Linux

[`tools/ember/record-linux.py`](https://github.com/Verilean/ember/blob/main/tools/ember/record-linux.py) needs
no root. It re-executes itself under `unshare -rn` (a user and network
namespace) and creates a TUN device there (a TAP device for Ethernet),
with IPv6 disabled and the MTU set to 296 (576 on TAP).

```
tools/ember/record-linux.py responder icmp  Tests/Ember/corpus/icmp
tools/ember/record-linux.py responder udp   Tests/Ember/corpus/udp
tools/ember/record-linux.py client --name nc-echo --out Tests/Ember/corpus/tcp \
    -- sh -c 'printf "hello\n" | nc -N 10.0.0.1 7'
```

**`responder icmp|udp|arp`** — Linux is 10.0.0.1. The script writes
crafted packets into the TUN device (pings of sizes 0, 56 and 200, three
each; UDP datagrams of 0, 1, 5, 64 and 255 random bytes to an echo
server it runs on port 7), reads what Linux sends back, and writes each
packet as an `rx` line and each reply as a `tx` line, SLIP-encoded, one
step per request. `responder arp` gives Linux Ember's MAC on a TAP device
and records its ARP answers.

**`client [--name N] [--out DIR] [--host CMD] [--settle S] [--eth] [--dnsmasq RANGE] -- COMMAND`**
— Linux is 10.0.0.2. The script starts the host command (default
`lake exe ember-host`) with `--trace DIR/N.trace`, bridges the TUN device
to it — SLIP on its stdin/stdout, or, with `--eth`, Ethernet frames each
preceded by a two-byte length — runs `COMMAND` in the namespace, waits
`--settle` seconds, and exits with the command's status. The fixture is
the trace `ember-host` wrote. `--dnsmasq RANGE` runs dnsmasq on the TAP
device and starts the host with `--dhcp`. The `--host` command can be any
program speaking the same protocol on stdin/stdout — for example
`tools/ember/qemu-bridge.py` with an ESP32-C3 image, which is how the
QEMU demos of [Chapter 5](05-targets.md) are recorded.

Every Linux fixture of the corpus is re-recorded by one script,
[`tools/ember/record-corpus.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/record-corpus.sh).
Fixtures are committed; CI only replays them. A few of its lines:

```sh
python3 $R responder icmp Tests/Ember/corpus/icmp
python3 $R responder udp Tests/Ember/corpus/udp
host=.lake/build/bin/ember-host
python3 $R client --name linux-ping --out Tests/Ember/corpus/icmp --host $host -- ping -c 3 -i 0.3 -s 56 10.0.0.1
python3 $R client --name linux-nc-echo --out Tests/Ember/corpus/tcp --host $host -- sh -c 'printf "hello\n" | nc -N 10.0.0.1 7'
for s in echo bulk client-rst second-connection closed-port two-sessions; do
  python3 $R client --name linux-$s --out Tests/Ember/corpus/tcp --host $host -- python3 tools/ember/tcp-scenarios.py $s
done
```

The script ends with `lake exe ember-fixtures`, which rewrites the
hand-written fixtures.

### `ember-host`

`ember-host` ([`Ember/Tools/Host.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Host.lean)) is
the Spec stack as a process: link bytes on stdin, the stack's output on
stdout, SLIP by default or length-prefixed Ethernet frames with `--eth`.
It hands SLIP input to the stack one frame per step (the stack is a
byte-at-a-time machine, so the chunking only shapes the trace), feeds a
`tick` every `--tick-ms` milliseconds of wall time (default 500; 0
disables), and writes the trace to `--trace FILE`. Other options choose
the configuration and the application: `--dhcp`, `--mtu N`, `--http`,
`--https`, `--conns N`, and those of later chapters. `--replay TRACE`
runs a trace's inputs with no wall clock involved.

## Hand-written scenarios

A scenario drives the Spec as a peer would and states what it expects
after each step. Running it both *checks* those expectations and
*produces* the trace that is committed, so a hand-written fixture is
never just "whatever the Spec printed". The type, from
[`Ember/Spec/Scenario.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Scenario.lean):

```lean
structure Scenario where
  name : String
  dir  : String
  doc  : String
  cfg  : Config := {}
  body : Sc Unit

def Scenario.run (sc : Scenario) : Except String Trace := do
  let (_, s) ← sc.body.run { st := State.init sc.cfg }
  return Trace.ofSteps (sc.cfg.header) s.steps
```

`Sc` is a state monad over the stack state and the peer's view of the
connection, with helpers such as `seg` (send a TCP segment), `connect`,
`echo`, `expectSeg`, `expectState`, `expectNoTx` and `expectDrop`. The
scenario behind the session shown at the end of
[Chapter 3](03-spec.md#one-session-as-the-spec-prints-it), from
[`Tests/Ember/Scenarios.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/Scenarios.lean):

```lean
  { name := "handshake-echo-close", dir := "tcp", doc := "open, echo, peer closes", body := do
      connect
      echo (str "hello")
      discard <| seg ACK
      expectNoTx
      closeFromPeer },
```

and a malformed-packet one:

```lean
  { name := "bad-checksum", dir := "tcp", doc := "corrupted TCP checksum", body := do
      let c ← get
      let p := Peer.tcp c.port c.cseq 0 SYN
      discard <| sendPkt (Bytes.set p 36 (Bytes.get p 36 ^^^ 0xFF))
      expectNoTx
      expectDrop "bad-tcp-checksum" },
```

`lake exe ember-fixtures` runs every scenario of `Tests.Scenarios.all`
and writes `Tests/Ember/corpus/<dir>/<name>.trace`; with `--check` it
only checks. `lake test` re-runs the scenarios too.

## Generated sessions

[`Ember/Spec/Gen.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Gen.lean) produces random input
streams:

* `ping`, `udp`: random request streams (sizes, ids, ports, ticks);
* `tcp`: a *closed-loop* client that reacts to whatever the Spec sends —
  random segment sizes within the advertised window, delayed or
  piggybacked ACKs, lost echoes (recovered by retransmission), duplicated
  and out-of-order segments, idle periods, and every way of ending. It
  checks that every byte sent comes back, in order;
* `mutate`: bit flips (with and without fixed-up checksums), truncation,
  bad checksums, out-of-window sequence numbers;
* `rechunk`: the same link bytes split at random places (SLIP is a byte
  stream).

Every session, mutated or not, must satisfy `Gen.properties`: every step
that completes a frame is accounted for (a `tx`, `drop`, `tcb` or
`note`), and every transmitted packet is well formed (IP, ICMP, UDP and
TCP checksums, lengths).

The recorded inputs of a session are an ordinary input stream, so the
same session then becomes a test for every other implementation.
`lake exe ember-gen [icmp|udp|tcp|all] [N] [--seed S]` runs N sessions
per protocol, each as generated, mutated and re-chunked; a failing
stream is shrunk and written to `Tests/Ember/regress/` with a
`# shrunk by ember-gen: …` comment.

## Three implementations, one trace

| Implementation | Header `impl=` | How it runs |
|---|---|---|
| `Ember.Spec` | `spec` | `Spec.run cfg inputs` ([Chapter 3](03-spec.md)) |
| `Ember.Net` in the interpreter | `ember-interp` | the Ember program of the stack, run by the Ember semantics with the trace's inputs as its oracle ([Chapter 2](02-language.md)) |
| The emitted C | the input trace's header (`impl=c` when it has none) | the C of `Ember.Net`, compiled on the host with `harness.c` |

And beyond these three, the same traces are replayed on the targets
([Chapter 5](05-targets.md)): the ESP32-C3 images in Espressif's QEMU and
the Z80 images on the Lean model of the machine, both compared to the
Spec's trace.

### What is compared

The interpreter and the C know nothing of `pkt` and `tcb` lines, so they
are compared on what they can all produce: observable lines and drop
reasons. From [`Ember/Tools/NetCheck.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/NetCheck.lean):

```lean
def comparable (t : Trace) : Trace :=
  { t with lines := t.lines.filter fun l => match l.ev with
      | .rx _ | .tx _ | .tick | .drop _ => true
      | _ => false }
```

The stronger comparison is **lockstep** (`lake exe ember-lockstep`): the
Spec and the Ember interpreter consume the same inputs and their *states*
are compared after every input — the TCB fields, the echo buffer, the IP
identification, the ISS counter, the SLIP receiver — so a divergence is
caught where it starts rather than where it first reaches the wire:

```
lake exe ember-lockstep FILE.trace ...
lake exe ember-lockstep --gen [icmp|udp|tcp|eth|dhcp|slip|all] [COUNT] [--seed S] [--c] [--opt O2] [--dump DIR]
```

With `--c` the emitted C, built with the host harness under strict
warnings and UBSan/ASan, must produce the interpreter's trace too. A
fixture runs on the build its header names (SLIP, Ethernet, DHCP). A
failing stream is shrunk and saved in `regress/`.

The two Spec stacks are also compared with each other: `Spec.Srv` with
the echo application and one connection must give `Spec.Stack`'s trace
*line for line*, diagnostics included ([Chapter 3](03-spec.md#why-the-echo-instance-matters)).

### The host harness

[`Tests/Ember/host/harness.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/host/harness.c) is the
`main` for emitted C on the host. From its header comment:

```c
/* Host harness for emitted Ember code (plan M2.7).
 *
 *   harness [-p K] inputs.trace          one run, trace on stdout
 *   harness --batch LIST                 lines "K inputs.trace output.trace"
 *                                        (each run in a forked child, so
 *                                        every run starts from the initial
 *                                        globals)
 *
 * Reads the `rx`/`tick` lines of a §3.1 trace as the input oracle, calls
 * program K's entry while input remains (stopping after three calls in a
 * row that consume nothing, as `Ember.Lang.runMachine` does), and writes
 * the same trace the interpreter writes: every input line followed by
 * the events attributed to it.  A trap is reported as a final
 * `note trap (...)` line and exit status 3.
 *
 * EMBER_TRACE=0 omits drop/note lines; 2 (default) keeps them. */
```

[`Ember/Tools/Cc.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Cc.lean) writes the emitted
units next to a generated program table, compiles them with the harness
using `$CC` (default `gcc`), and runs them. The strict flags are the
design's exit criteria for the emitted C:

```lean
def strictFlags : Array String :=
  #["-std=c99", "-Wall", "-Wextra", "-Wconversion", "-Werror", "-pedantic",
    -- nix's cc wrapper defines _FORTIFY_SOURCE, whose #warning fires at -O0
    "-Wno-cpp"]
```

Tests that need a tool that is missing (gcc, sdcc, tshark, QEMU) print
"skipped" rather than fail.

## The test suites

`lake test` runs the `test` executable, whose root is
[`Tests/AllTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/AllTests.lean). It runs the IO suites
first — corpus replay, scenarios, generators, differential runs — and
then the LSpec unit tests; any failure gives a non-zero exit. One suite
can be run alone with `EMBER_ONLY`:

```
EMBER_ONLY=spec .lake/build/bin/test
```

| `EMBER_ONLY` | Suite | What it checks |
|---|---|---|
| `spec` | [`SpecTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/SpecTests.lean) | checksums, SLIP, headers, trace format and `ember-diff`; every fixture of `corpus/` and `regress/` replayed through the Spec (observable lines) with `parse ∘ print` checked; the hand-written scenarios; 1 000 generated sessions per protocol (ICMP, UDP, TCP); the corpus through the `ember-host` binary; pcaps decoded by `tshark` |
| `srv` | [`SrvTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/SrvTests.lean) (with `HttpTests`, `TlsTests`) | `Spec.Srv` with echo = `Spec.Stack`, every line; the Ember `Net.Srv` (interpreter and host C) = `Spec.Srv`; HTTP and HTTPS sessions |
| `crypto` | [`CryptoTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/CryptoTests.lean) | the crypto reference against RFC vectors and OpenSSL; the crypto in Ember against the reference |
| `auth` | [`AuthTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/AuthTests.lean), [`AuthNetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/AuthNetTests.lean) | bearer tokens in the reference and in Ember |
| `control` | [`ControlTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/ControlTests.lean), [`ControlNetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/ControlNetTests.lean) | control requests and kept connections |
| `lang` | [`LangTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/LangTests.lean) | the language: type checker, interpreter, golden C, interpreter = host C, random programs |
| `net` | [`NetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/NetTests.lean) | `Ember.Net` against the Spec: per function on random inputs; the corpus and generated sessions in lockstep, and through the host C |
| `esp32` | [`TargetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/TargetTests.lean) | `tools/ember/qemu-test.sh`: the ESP32-C3 images in QEMU, the SLIP corpus and generated sessions on the target |
| `z80` | [`Z80Tests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/Z80Tests.lean) | the Z80 model against `z88dk-ticks`; SDCC's and the own back end's images replaying the corpus |

The full description of every suite is in
[`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md). The proofs are
not a suite: `Ember/Proof` is part of the library, so `lake build` checks
them ([Chapter 10](10-proofs.md)).

The corpus replay at the heart of `spec` is short enough to quote:

```lean
/-- Replay every fixture through the Spec; also checks parse ∘ print. -/
def corpus : IO Nat := do
  let mut bad := 0
  let files := (← traceFiles "Tests/Ember/corpus") ++ (← traceFiles "Tests/Ember/regress")
  for f in files do
    let t ← Trace.readFile f
    let r := Spec.run (Spec.Config.ofHeader t.header) t.inputs
    let d := diff t r { observable := true }
    if !d.equal then
      bad := bad + 1
      IO.println s!"FAIL corpus {f}\n{d.report}"
    if !roundTrip t then
      bad := bad + 1
      IO.println s!"FAIL parse ∘ print {f}"
  IO.println s!"corpus: {files.size} fixtures replayed, {bad} failures"
  return bad
```

### `tools/ember/ci.sh`

[`tools/ember/ci.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/ci.sh) is what CI runs, inside
`nix-shell`. It always builds the library (and so checks the proofs),
evaluates the `#guard`s in `Tests.Ember.Z80Cover` and
`Tests.Ember.Z80RegressW`, and builds the tools. Then, by job:

| Job | Runs |
|---|---|
| `all` (default) | `lake test`, then `size-report.py` |
| `spec` | `ember-fixtures --check`; `ember-replay` on the corpus; `ember-gen all 1000` |
| `lang` | `ember-fuzz 1000` |
| `net` | `ember-lockstep Tests/Ember/corpus Tests/Ember/regress --gen all 1000 --c` |
| `esp32` | `tools/ember/qemu-test.sh` |
| `z80` | `tools/ember/z80-test.sh` |
| `proofs` | `lake build Ember.Proof Tests.Ember.Z80Cover Tests.Ember.Z80RegressW` |
| `size` | `size-report.py` |

Larger runs, used as milestone exit criteria and not part of `lake test`,
are listed in `Tests/Ember/README.md` — for example
`lake exe ember-lockstep --gen all 10000 --c` for Spec = interpreter = C
on ten thousand sessions per protocol.

## The size gate

[`tools/ember/size-report.py`](https://github.com/Verilean/ember/blob/main/tools/ember/size-report.py) builds
the emitted C of the stack for each target and measures it: per function
and per global with `gcc -Os` on the host; ROM, RAM and T-states per ICMP
echo for the SDCC Z80 image; code, read-only data, RAM and instructions
per echo (QEMU `-icount`) for the ESP32-C3 image; the same for the C
without bounds checks, and for the image of the own Z80 back end. Each
metric must stay within ±3 % of the committed baseline,
[`bench/ember-size.baseline`](https://github.com/Verilean/ember/blob/main/bench/ember-size.baseline), **in
either direction**; outside it the script exits 1. Its first lines:

```
# Ember stack size baseline: tools/ember/size-report.py --update
host64.code 5449
host64.ram 936
host64.rodata 1023
z80.code 7574
z80.ram 888
```

`--update` re-records the baseline, so every change in cost — up or down
— shows up as a reviewed diff of that file. ([Chapter 5](05-targets.md)
explains the targets the numbers are for.)

## Adding a fixture

**A hand-written case.** Add a `Scenario` to the right list in
[`Tests/Ember/Scenarios.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/Scenarios.lean)
(`tcp`, `ipv4`, `icmp`, `udp`, `slip`, `arp`, `dhcp` — they are joined
in `all`), with expectations for what the stack must do. Then

```
lake exe ember-fixtures            # checks every scenario, writes corpus/<dir>/<name>.trace
```

and add a line to that directory's `README.md`. `lake test` will re-run
the scenario and replay the fixture from then on.

**A Linux recording.** Run `record-linux.py` (responder or client mode)
with `--out Tests/Ember/corpus/<dir>`, add the command to
[`tools/ember/record-corpus.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/record-corpus.sh) so
the fixture can be re-recorded, and record its provenance in the
directory's `README.md`. If the recording's outputs are Linux's
(responder mode), its header carries `mask=ipv4.id`.

**A failure found by a generator.** Nothing to do: `ember-gen` and
`ember-lockstep` shrink it and write it to `Tests/Ember/regress/`, which
`lake test` replays with the corpus. Keep the file after the fix.

In every case the new fixture is replayed by the Spec in `spec`, compared
line for line against `Spec.Srv` in `srv`, run through the interpreter
and the C in `net`, and replayed on the targets by `esp32` and `z80` when
it is a SLIP fixture of the default configuration.

Next: [Chapter 5](05-targets.md) — the targets those traces are replayed on.
