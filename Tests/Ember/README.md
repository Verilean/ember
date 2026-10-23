# Ember tests

`lake test` runs everything below; tests that need a tool (gcc, sdcc,
tshark) say "skipped" when it is missing.  The full set of tools comes
with `nix-shell` (see `shell.nix`):

```
nix-shell --run 'lake test'          # ≈ 6 minutes; EMBER_ONLY=spec|lang|net|esp32|z80 .lake/build/bin/test runs one suite
```

## What `lake test` checks

| Suite | Milestone | Contents |
|---|---|---|
| `Tests/Ember/SpecTests.lean` | M1 | checksum (RFC 1071/1624), SLIP, headers, trace format and `ember-diff`; **corpus replay** (`corpus/`, `regress/`); hand-written **scenarios** with their expectations; **1 000 generated sessions** per protocol, each also mutated and re-chunked, against the properties of `Ember.Spec.Gen`; the corpus through the `ember-host` binary; pcaps decoded by `tshark` |
| `Tests/Ember/LangTests.lean` | M2, M5.4, M5.7 | **the total semantics** `Lang.Sem` (what the proofs unfold) = interpreter, on random programs, the examples and every build of the stack on the corpus; **the emitted C under the C semantics** `Ember.C.Sem` = `Lang.Sem`, same programs, three profiles, never undefined, and a planted emitter bug noticed; type checker (one negative test per rule, with spans), interpreter (every construct, traps, fuel), surface syntax = hand-built AST, profiles, **golden C** (`golden/`), examples vs Lean references, **interpreter = host C** (−O0/−O2, UBSan/ASan, strict warnings), **SDCC** `--Werror`, **1 000 random programs** (`ember-fuzz`) |
| `Tests/Ember/NetTests.lean` | M3 | `Ember.Net` functions vs `Ember.Spec` on 10 000 random inputs; the corpus (SLIP and Ethernet fixtures) and **1 000 generated sessions** per protocol × 3 variants, plus 1 000 Ethernet and 1 000 DHCP sessions: Spec = Ember interpreter (**lockstep**) = host C |
| `Tests/Ember/TargetTests.lean` | M4 | `tools/ember/qemu-test.sh`: the bare-metal ESP32-C3 images in Espressif's QEMU — boot, trap handler, UART, interrupt-driven echo of 10 000 bytes, SLIP loopback, the SLIP corpus and **100 generated sessions** per protocol × 3 variants (target trace = Spec trace), SYSTIMER tick |
| `Tests/Ember/Z80Tests.lean` | M4z, M6.1 | the Z80 CPU model (interrupt modes, `EI` delay, `HALT`, `R`; random instruction streams against `z88dk-ticks`); SDCC's code on the model of the machine: the examples (interpreter = Z80), echo, SLIP loopback, the corpus and generated sessions (target trace = Spec trace), random programs; the **own back end** (M6): assembler vs `z88dk-z80asm`, runtime routines vs their specifications, random programs through the IR and through generated code, index-check programs that must still trap, the corpus and sessions on the image it builds (`tools/ember/z80-test.sh`) |
| `lake build` | M5 | `Ember/Proof` is part of the library: the proofs are checked by building — properties of the Spec (M5.1–M5.3), refinement of the stack in Ember against it (M5.4–M5.6), the emitted C against the Ember semantics (M5.8), the IR of the Z80 back end against it (M7.1, M7.2), and the Z80 encoder against the CPU model (M7.4); the build also evaluates the `#guard`s that tie the theorems to the programs (the checked stack is the program the theorems are about; the checkers accept every build of the stack: `progOkB` for every profile of the C, `progOkB` and `irOkB` for the IR).  `Ember/Proof/README.md` lists the theorems and which links to the running code are tests, not theorems |

The target suites are skipped, with a line saying so, when their tools
are missing; inside `nix-shell` everything runs.

## Tools

| Command | Purpose |
|---|---|
| `lake exe ember-diff A B [--observable] [--context N] [--first-only] [--all]` | first difference of two traces, packets decoded field by field |
| `lake exe ember-pcap X.trace > X.pcap` | a trace's packets for Wireshark |
| `lake exe ember-replay [--write] F.trace…` | replay fixtures through `Ember.Spec` |
| `lake exe ember-host [--eth] [--dhcp] [--mtu N] [--tick-ms N] [--trace F]` | the Spec stack on stdin/stdout (SLIP, or length-prefixed Ethernet frames) |
| `lake exe ember-fixtures [--check]` | run the hand-written scenarios, (re)write their fixtures |
| `lake exe ember-gen [icmp\|udp\|tcp\|all] [N] [--seed S]` | generated sessions against the Spec's properties; failures shrunk into `regress/` |
| `lake exe ember-emit NAME [--profile P] [--ember] [--dropped] \| --golden` | emitted C of a registered program; `--dropped`: without its bounds checks, the SLIP build (`net`) only (M5.9); `--golden` rewrites `golden/` |
| `lake exe ember-fuzz [N] [--seed S] [--opt O0\|O2\|both] [--plant]` | random programs: interpreter vs C; `--plant` checks the fuzzer finds a planted emitter bug |
| `lake exe ember-lockstep FILES… \| --gen [P] [N] [--c]` | Spec = Ember interpreter (lockstep) [= host C]; `P`: `icmp udp tcp` (SLIP), `eth`, `dhcp` (the Ethernet builds), `slip`, `all`; a fixture runs on the build its header names; `--dropped`: the SLIP build's C without its bounds checks |
| `tools/ember/record-corpus.sh` | re-record the Linux fixtures (user namespace + TUN/TAP, no root) |
| `tools/ember/size-report.py [--update]` | code/RAM per function, ±3 % gate against `bench/ember-size.baseline` |
| `lake exe ember-z80 asm-check\|rt-check\|ir-fuzz\|ir-replay\|own-fuzz\|own-build\|own-size …` | the own Z80 back end: its checks; `own-build net` writes the image (`.ihx`), a listing with the IR between the instructions (`.lst`) and symbols; `own-size` the bytes per function; `--plain`: without the passes on the assembly (the image the proofs of M7.3 speak of) |
| `lake exe ember-z80 profile\|stack IMAGE …` | T-states per function for one ping; deepest stack over fixtures |
| `lake exe ember-z80 check\|replay\|echo\|slip\|ping\|fuzz\|run …` | the Z80 model: against `z88dk-ticks`; fixtures, echo and SLIP on an SDCC image; T-states per ping; random programs (interpreter vs SDCC's code, `--u64` to see SDCC's 64-bit bugs); instruction trace with symbols |
| `tools/ember/qemu-run.sh IMAGE [--gdb] [--log]`, `tools/ember/esp32.py TEST` | one ESP32-C3 image in QEMU; one test against it |
| `tools/ember/ci.sh [JOB]` | what CI runs (the plan's `ember-spec`, `ember-lang`, `ember-net`, `ember-esp32`, `ember-z80`, `ember-proofs` jobs) |

## Exit-criteria runs (not part of `lake test`)

```
nix-shell --run 'lake exe ember-gen all 10000 --seed 7'          # M1: 30 000 sessions per protocol
nix-shell --run 'lake exe ember-fuzz 10000 --seed 42 --all'      # M2: 10 000 programs, −O0 and −O2
nix-shell --run 'lake exe ember-fuzz 1000 --plant --opt O0'      # M2: planted bug found and shrunk
nix-shell --run 'lake exe ember-lockstep --gen all 10000 --c'    # M3: Spec = interpreter = C
```

## Manual demo: ping and TCP echo from Linux (M1 exit criterion)

`ember-host` is the reference stack speaking SLIP on stdin/stdout.
Attach it to a pseudo-terminal and let Linux's SLIP driver use it (needs
root for `slattach` and `ip`, so this variant is not exercised by the
tests; the user-namespace variant below is):

```
lake build ember-host
socat -d -d pty,raw,echo=0,link=/tmp/ember-pty \
      exec:'.lake/build/bin/ember-host --trace /tmp/ember.trace',pty,raw,echo=0 &
sudo slattach -s 115200 -p slip /tmp/ember-pty &
sudo ip addr add 10.0.0.2 peer 10.0.0.1 dev sl0
sudo ip link set sl0 up mtu 296
ping -c 3 10.0.0.1
printf 'hello\n' | nc -N 10.0.0.1 7
lake exe ember-pcap /tmp/ember.trace > /tmp/ember.pcap    # open in Wireshark
```

Without root the same exchange runs in a user namespace with a TUN
device bridged to `ember-host` — that is how the `linux-*` fixtures of
the corpus were recorded:

```
python3 tools/ember/record-linux.py client --name demo --out /tmp \
    --host .lake/build/bin/ember-host -- sh -c 'ping -c 3 10.0.0.1; printf "hello\n" | nc -N 10.0.0.1 7'
```

(Recorded here: `ping` 0 % loss, `nc` echoed the line, Linux 6.18.)
