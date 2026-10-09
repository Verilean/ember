# Ember tests

`lake test` runs everything below; tests that need a tool (gcc, sdcc,
tshark) say "skipped" when it is missing.  The full set of tools comes
with `nix-shell` (see `shell.nix`):

```
nix-shell --run 'lake test'          # ≈ 3 minutes
```

## What `lake test` checks

| Suite | Milestone | Contents |
|---|---|---|
| `Tests/Ember/SpecTests.lean` | M1 | checksum (RFC 1071/1624), SLIP, headers, trace format and `ember-diff`; **corpus replay** (`corpus/`, `regress/`); hand-written **scenarios** with their expectations; **1 000 generated sessions** per protocol, each also mutated and re-chunked, against the properties of `Ember.Spec.Gen`; the corpus through the `ember-host` binary; pcaps decoded by `tshark` |
| `Tests/Ember/LangTests.lean` | M2 | type checker (one negative test per rule, with spans), interpreter (every construct, traps, fuel), surface syntax = hand-built AST, profiles, **golden C** (`golden/`), examples vs Lean references, **interpreter = host C** (−O0/−O2, UBSan/ASan, strict warnings), **SDCC** `--Werror`, **1 000 random programs** (`ember-fuzz`) |
| `Tests/Ember/NetTests.lean` | M3 | `Ember.Net` functions vs `Ember.Spec` on 10 000 random inputs; the corpus and **1 000 generated sessions** per protocol × 3 variants: Spec = Ember interpreter (**lockstep**) = host C |

## Tools

| Command | Purpose |
|---|---|
| `lake exe ember-diff A B [--observable] [--context N] [--first-only] [--all]` | first difference of two traces, packets decoded field by field |
| `lake exe ember-pcap X.trace > X.pcap` | a trace's packets for Wireshark |
| `lake exe ember-replay [--write] F.trace…` | replay fixtures through `Ember.Spec` |
| `lake exe ember-host [--eth] [--dhcp] [--mtu N] [--tick-ms N] [--trace F]` | the Spec stack on stdin/stdout (SLIP, or length-prefixed Ethernet frames) |
| `lake exe ember-fixtures [--check]` | run the hand-written scenarios, (re)write their fixtures |
| `lake exe ember-gen [icmp\|udp\|tcp\|all] [N] [--seed S]` | generated sessions against the Spec's properties; failures shrunk into `regress/` |
| `lake exe ember-emit NAME [--profile P] [--ember] \| --golden` | emitted C of a registered program; `--golden` rewrites `golden/` |
| `lake exe ember-fuzz [N] [--seed S] [--opt O0\|O2\|both] [--plant]` | random programs: interpreter vs C; `--plant` checks the fuzzer finds a planted emitter bug |
| `lake exe ember-lockstep FILES… \| --gen [P] [N] [--c]` | Spec = Ember interpreter (lockstep) [= host C] |
| `tools/ember/record-corpus.sh` | re-record the Linux fixtures (user namespace + TUN/TAP, no root) |
| `tools/ember/size-report.py [--update]` | code/RAM per function, ±3 % gate against `bench/ember-size.baseline` |
| `tools/ember/ci.sh` | what CI runs (the plan's `ember-spec`, `ember-lang`, `ember-net` jobs) |

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
