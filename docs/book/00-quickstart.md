# 0 · Quickstart — from clone to a running stack

In this chapter you build Ember, run its tests, start the reference
stack on your machine, let Linux ping it and fetch a page from it, and
compare two traces. At the end you run the same stack, compiled to C,
on an ESP32-C3 in QEMU.

Every command below exists in this repository. Where a command comes
from a script or a README, the file is named.

## Prerequisites

| Tool | Why | Where it comes from |
|---|---|---|
| **Lean 4** `leanprover/lean4:v4.32.1` | everything | [`lean-toolchain`](https://github.com/Verilean/ember/blob/main/lean-toolchain); `elan` installs it on the first `lake` call |
| **LSpec** | the unit-test runner | fetched by `lake` ([`lakefile.lean`](https://github.com/Verilean/ember/blob/main/lakefile.lean) pins commit `3e23a4a`) |
| **Nix** (optional, recommended) | every external tool at once | [`shell.nix`](https://github.com/Verilean/ember/blob/main/shell.nix) |

`shell.nix` brings in `elan` and the external tools the tests use.
Here is its header, quoted from the file:

```nix
# Development shell for Ember.
#   gcc            host C differential tests (M2, M3)
#   sdcc           Z80 profile compile checks of the emitted C
#   python3        fixture recording (tools/ember/record-linux.py)
#   dnsmasq        DHCP fixtures
#   wireshark-cli  tshark checks of ember-pcap output
#   iproute2, netcat, iputils: fixture recording in a user namespace
#   z88dk          z88dk-ticks, the reference for the Z80 model (M4z, M6.1)
#   riscv32-none-elf-gcc, esptool, qemu-system-riscv32-esp, gnumake:
#                  the ESP32-C3 image and Espressif's QEMU (M4)
#   openssl        the crypto reference against OpenSSL (M8.5)
#   curl           HTTP from Linux against the stack (M8.2, M8.4)
```

`shell.nix` imports `<nixpkgs>` and pins no channel itself. Espressif's QEMU
fork is the exception: it is packaged in the repository
([`tools/ember/nix/qemu-esp32c3.nix`](https://github.com/Verilean/ember/blob/main/tools/ember/nix/qemu-esp32c3.nix))
because nixpkgs' QEMU has no ESP32 machine.

You can work without Nix. Lean, `lake build` and most of `lake test`
need only elan. A test that needs a missing tool (gcc, sdcc, tshark,
QEMU, openssl) prints "skipped" and does not fail.

## Step 1 — clone and enter the shell

```sh
git clone https://github.com/Verilean/ember.git
cd ember
nix-shell
```

The rest of this chapter runs inside `nix-shell`. You can also run one
command at a time, as the repository's READMEs do:
`nix-shell --run 'lake test'`.

## Step 2 — build

```sh
lake build
```

The default target is the `Ember` library. The library includes
`Ember/Proof`, so this command also checks every proof. It also
evaluates the `#guard`s that tie the theorems to the programs. This is
the longest build in the repository. To build only the tool you need,
name it:

```sh
lake build ember-host
```

## Step 3 — test

```sh
lake test
```

`lake test` runs `Tests/AllTests.lean`, the `@[test_driver]` in
`lakefile.lean`. The suites run in this order: Spec, Srv (HTTP and HTTPS),
crypto, auth, control, Lang, Net, the ESP32-C3 in QEMU and the Z80.
[`README.md`](https://github.com/Verilean/ember/blob/main/README.md) says the run takes about 3 minutes with every tool present.
[`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md) says about 6.

To run one suite, build the test binary and set `EMBER_ONLY`. This
comment is in `Tests/AllTests.lean`:

```lean
  -- `EMBER_ONLY=spec|srv|crypto|auth|control|lang|net|esp32|z80` runs one suite
```

```sh
lake build test
EMBER_ONLY=spec .lake/build/bin/test
```

CI runs the same suites through one script,
[`tools/ember/ci.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/ci.sh):

```sh
tools/ember/ci.sh            # all jobs: lake test, then the size gate
tools/ember/ci.sh spec       # one job: spec | lang | net | esp32 | z80 | proofs | size
```

Before it runs a job, `ci.sh` builds the library, two `#guard` modules
that `lake test` does not import (`Tests.Ember.Z80Cover`,
`Tests.Ember.Z80RegressW`) and every tool. The `size` job runs
[`tools/ember/size-report.py`](https://github.com/Verilean/ember/blob/main/tools/ember/size-report.py). That
script compares code size, RAM and cycles per ping with
[`bench/ember-size.baseline`](https://github.com/Verilean/ember/blob/main/bench/ember-size.baseline). A metric
more than ±3 % away from the baseline fails the job.

## Step 4 — the reference stack on stdin/stdout

`ember-host` runs the reference stack, `Ember.Spec`, as a process. The
stack reads link bytes on stdin and writes its output on stdout. The
default link is SLIP. With `--eth`, each Ethernet frame has a 2-byte
length in front of it. The flags below come from the doc comment and
`parseArgs` in [`Ember/Tools/Host.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Host.lean):

| Flag | Effect |
|---|---|
| *(none)* | the echo stack: ICMP echo, UDP echo and TCP echo on port 7, at 10.0.0.1, MTU 296 |
| `--eth`, `--dhcp`, `--mtu N` | Ethernet + ARP instead of SLIP; the DHCP client; the packet buffer size (default 296 on SLIP, 576 on Ethernet) |
| `--tick-ms N` | a `tick` every N ms of wall time (default 500; 0 turns ticks off) |
| `--trace FILE` | write the trace of the session to FILE (the format is in [chapter 4](04-testing.md)) |
| `--replay TRACE` | run the inputs of a trace file and print the resulting trace (no wall clock) |
| `--http` | the stack with the HTTP application and its demo site on port 80 (`Spec.Srv.Http.demo`) |
| `--https` | TLS 1.3 with the same site on port 443 (`Spec.Srv.Tls.demo`, a self-signed demo certificate) |
| `--conns N` | N connections for `--http` / `--https` (default 1) |
| `--auth`, `--now T`, `--token SCOPE` | the demo sites with protected routes; their time; print a token of the demo identity provider and exit |
| `--ctl` | the demo sites with a control route (`POST /cmd`) and kept connections |
| `--entropy HEX`, `--no-entropy` | fixed TLS randomness, for test fixtures only (see below) |

```sh
lake build ember-host
.lake/build/bin/ember-host --trace /tmp/ember.trace
```

Without a SLIP peer on stdin the process does little: it waits for
input and handles ticks. The next step connects Linux to it.

## Step 5 — let Linux talk to it

[`tools/ember/record-linux.py`](https://github.com/Verilean/ember/blob/main/tools/ember/record-linux.py) needs
no root. It runs itself in a user and network namespace
(`unshare -rn`) and creates a TUN device there. In `client` mode, Linux
is the peer at 10.0.0.2. The script bridges the TUN device over SLIP to
the `--host` command, which is the stack at 10.0.0.1. Then it runs your
command inside the namespace. The trace that `ember-host` writes becomes
a fixture: the inputs come from Linux, the outputs from the Spec.

Ping, then TCP echo. This command is from
[`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md):

```sh
python3 tools/ember/record-linux.py client --name demo --out /tmp \
    --host .lake/build/bin/ember-host -- sh -c 'ping -c 3 10.0.0.1; printf "hello\n" | nc -N 10.0.0.1 7'
```

It ends with

```
3 packets transmitted, 3 received, 0% packet loss, time 2041ms
rtt min/avg/max/mdev = 0.391/0.444/0.513/0.050 ms
hello
wrote /tmp/demo.trace (command exit 0)
```

— Linux's pings answered and `hello` echoed back by the Spec's stack.

HTTP from curl, from the same README:

```sh
python3 tools/ember/record-linux.py client --name curl --out /tmp \
    --host ".lake/build/bin/ember-host --http" \
    -- sh -c 'curl -sS http://10.0.0.1/ && curl -sS -I http://10.0.0.1/hello.txt'
```

HTTPS. By default, every handshake of `ember-host --https` takes 32
fresh bytes from the operating system
([`Ember/Tools/HostEntropy.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/HostEntropy.lean)).
If it cannot get them, the host exits with status 3. A recorded fixture
must replay the same way every time, so fixtures are recorded with
`--no-entropy`. That flag keeps the fixed seed alone. It is a test
configuration, not a secure one, and the host says so on stderr:

```sh
nix-shell --run 'python3 tools/ember/record-linux.py client --name tls --out /tmp \
    --host ".lake/build/bin/ember-host --https --no-entropy" \
    -- sh -c "curl -sS -k -v https://10.0.0.1/"'
```

The demo certificate is self-signed, so use `curl -k` or
`openssl s_client`. The `--auth` and `--ctl` sites and their tokens are
covered in [chapter 8](08-auth.md) and [chapter 9](09-control.md).

Other options of `record-linux.py client` (from its `main`):
`--settle S`, `--eth` (a TAP device and Ember's Ethernet + ARP link) and
`--dnsmasq RANGE` (runs dnsmasq and starts Ember with `--dhcp`). The
script also has a `responder` mode, in which Linux plays Ember's role.
The fixtures that say "answer as Linux does" come from that mode.
[`tools/ember/record-corpus.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/record-corpus.sh)
records the Linux fixtures of the corpus again.

If you have root and want a real SLIP interface instead,
[`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md) describes a
variant with `socat` and `slattach`. The tests do not run that variant.

## Step 6 — replay and compare traces

Every implementation writes the same line-oriented trace. These are the
first lines of a fixture recorded from Linux,
[`Tests/Ember/corpus/icmp/linux-ping.trace`](https://github.com/Verilean/ember/blob/main/Tests/Ember/corpus/icmp/linux-ping.trace)
(the `rx`/`tx` lines are cut at the right):

```
# ember-trace v1  impl=spec  build=dev  profile=host64  link=slip
0      rx   c0 45 00 00 54 b1 29 40 00 40 01 75 7d 0a 00 00 02 0a 00 00 01 08 00 …
0      pkt  rx ipv4 10.0.0.2>10.0.0.1 icmp echo-req id=21910 seq=1 len=84
0      pkt  tx ipv4 10.0.0.1>10.0.0.2 icmp echo-rep id=21910 seq=1 len=84
0      tx   c0 45 00 00 54 00 01 00 00 40 01 66 a6 0a 00 00 01 0a 00 00 02 00 00 …
1      tick
```

Run the inputs of a fixture through the Spec again, then compare the
result with the fixture:

```sh
.lake/build/bin/ember-host --replay Tests/Ember/corpus/icmp/linux-ping.trace > /tmp/ping.trace
lake exe ember-diff Tests/Ember/corpus/icmp/linux-ping.trace /tmp/ping.trace --observable
```

It prints `traces agree (9 observable events)`. `ember-diff` reports the first difference between the two traces and
decodes both differing packets field by field. It exits with 0 when the
traces agree, 1 when they differ and 2 on bad usage. The usage line in
[`Ember/Tools/Cli.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Cli.lean) lists all its
options:

```
ember-diff A.trace B.trace [--observable | --drops] [--context N] [--first-only] [--all]
```

Related tools:

```sh
lake exe ember-replay Tests/Ember/corpus/*/*.trace         # every fixture through Ember.Spec
lake exe ember-pcap /tmp/demo.trace > /tmp/demo.pcap       # the packets, for Wireshark
lake exe ember-lockstep Tests/Ember/corpus --c             # Spec = Ember interpreter = host C
lake exe ember-emit net --profile host64                   # the emitted C of the stack
```

`ember-lockstep` runs the Spec and the stack written in Ember side by
side. It compares their states after every input. With `--c`, it also
compiles the emitted C with the host harness under UBSan and ASan and
runs it. If a stream fails, the tool shrinks it and saves it in
`Tests/Ember/regress/`.

## Step 7 — the ESP32-C3 in QEMU

[`tools/ember/qemu-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-test.sh) emits the C
for the `rv32` profile, builds the bare-metal images into
`.lake/build/esp32c3/` and runs the tests in Espressif's QEMU:

```sh
tools/ember/qemu-test.sh                 # build, then every test
tools/ember/qemu-test.sh build           # the images only
tools/ember/qemu-test.sh corpus --verbose
```

To run one image, use
[`tools/ember/qemu-run.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-run.sh). These lines
are from [`runtime/esp32c3/README.md`](https://github.com/Verilean/ember/blob/main/runtime/esp32c3/README.md):

```sh
tools/ember/qemu-run.sh .lake/build/esp32c3/hello.bin --timeout 3
tools/ember/qemu-run.sh .lake/build/esp32c3/stack.bin --dir /tmp/e --gdb --log
```

With `--dir D`, UART0 (SLIP) and UART1 (the trace) are the Unix sockets
`D/uart0.sock` and `D/uart1.sock`. Without it, UART1 goes to stdout.

[`tools/ember/qemu-bridge.py`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-bridge.py) puts an
image's UART0 on stdin and stdout, the same way `ember-host` works. So
the image can be the `--host` of `record-linux.py`. From
[`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md):

```sh
python3 tools/ember/record-linux.py client --name curl-qemu --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-http.bin" \
    -- sh -c 'sleep 2; curl -sS http://10.0.0.1/big.txt'
```

Now curl gets its page from the HTTP server written in Ember, compiled
to RISC-V and running on the emulated ESP32-C3. The server has two
connections. To run the HTTPS image, use `stack-https.bin` and
`curl -sS -k https://10.0.0.1/`. All of this runs in QEMU only: no run
on a real board has been done.

The Z80 has a script of the same shape,
[`tools/ember/z80-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/z80-test.sh). It builds
the images with SDCC and with Ember's own back end, then runs them on
the Lean model of the machine. See [chapter 5](05-targets.md).

## Where next

| Want… | Read |
|---|---|
| What Ember is, what ships, what is proved | [1 · Overview](01-overview.md) |
| Write Ember code (`ember def`) | [2 · The Ember language](02-language.md) |
| The reference stack | [3 · The reference stack](03-spec.md) |
| Traces, fixtures, lockstep, fuzzing | [4 · Traces and testing](04-testing.md) |
| C, ESP32-C3, Z80 | [5 · Targets](05-targets.md) |
| Serve your own pages | [6 · Tutorial: an HTTP app](06-http-app.md) |
| How the pieces fit | [11 · Architecture](11-architecture.md) |

## Common pitfalls

- **A suite says "skipped".** A tool it needs is missing. Run it inside
  `nix-shell`.
- **`ember-host --https` exits with status 3.** The system gave no
  entropy. For a reproducible test run, pass `--no-entropy` or
  `--entropy HEX`. Never use those flags for anything else.
- **A recorded HTTPS session does not replay.** It was recorded without
  `--no-entropy`, so the server random came from the system.
- **`qemu-system-riscv32-esp: not found`.** Espressif's QEMU comes only
  from `shell.nix`.
- **A golden C file is stale.** `qemu-test.sh` and `z80-test.sh` stop
  when the emitted C differs from `Tests/Ember/golden/`. If the change is
  intended, rewrite the golden files with `lake exe ember-emit --golden`
  and review the diff.
