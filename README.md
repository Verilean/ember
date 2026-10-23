# Ember

A TCP/IP stack in Lean, a Lean-hosted DSL that emits C without undefined
behaviour, and the stack written in that DSL — three implementations
checked against each other through one trace format, on the way to
small machines (ESP32-C3, Z80) and to proofs.

* Design: [`docs/Ember-design.md`](docs/Ember-design.md) — §2.7: what of the resources is fixed, what is bounded, what is not
* Plan and progress: [`docs/Ember-plan.md`](docs/Ember-plan.md) — M1–M3 (host), M4 (ESP32-C3 in QEMU), M4z (Z80, on a Lean model of the machine), proofs M5.1–M5.4 and the refinement proofs (M5.5: SLIP, IPv4, ICMP, UDP per received byte against the Spec; TCP — `tcp_input` and `tcp_tick` as the Ember semantics runs them do what `Spec.Tcp.parse`/`input`/`tick` do; M5.6: per received byte, per tick, per call of `main`, and from the initial state for any input — the SLIP build never traps and transmits and drops what the Spec does.  The tick proof found a defect, now fixed: a tick that sent in the middle of a received frame destroyed that frame); the emitted C proved against the Ember semantics (M5.8: expressions, statements, calls, programs, for programs without by-reference parameters — with M5.6, the C of the SLIP build under the C semantics `Ember.C.Sem` transmits and drops what the Spec does), Ethernet/ARP/DHCP in Ember, and the own Z80 back end (M6) done; of the back end's proof (M7) the frame validator, `Lang → IR` and the encoder are done, and `IR → Z80` is done for the SLIP build's test-harness image on the Lean model of the machine: the image as built by default (with the passes on the assembly) and without them, loaded and stepped as the tests run them, halts for any input having transmitted and dropped what the Spec does, prints the Spec's trace with no trap, and its `tcb` observer's lines, when it gives them, are the Spec's control block after each item (that the observer always gives lines is not proved).  What the theorems take of the program is that it is the checked SLIP build (`StackSrc`); that the items and bytes are those `build` gives is checked by evaluation (`#guard`).  This is not a proof of the back end for every IR program: the board runtime and interrupts, and the routines and operations the stack does not use, are outside it; no run on real hardware yet
* Tests and tools: [`Tests/Ember/README.md`](Tests/Ember/README.md)
* The stack in Ember: [`Ember/Net/README.md`](Ember/Net/README.md)

| Directory | |
|---|---|
| `Ember/Spec` | reference stack: SLIP, IPv4, ICMP, UDP, TCP (one connection), Ethernet + ARP, DHCP client |
| `Ember/Lang` | the DSL: AST, type checker, interpreter (= semantics), `ember def` syntax, profiles, random programs |
| `Ember/C` | Clight-like C AST, `Lang → C`, printer, a semantics for that C subset |
| `Ember/Net` | the stack in Ember (SLIP build) |
| `Ember/Proof` | proofs about the reference stack (checksum algebra, round trips, TCP invariants), that the stack in Ember (SLIP build: IPv4, ICMP, UDP, TCP, `main`) does what it does, that the emitted C does what the Ember semantics does, and that the IR of the Z80 back end does |
| `Ember/Z80` | Z80 CPU model (checked against `z88dk-ticks`) and the machine the Z80 builds are tested on; the own back end: assembler, IR, static frames, code generator, runtime routines — Ember to a Z80 image without a C compiler |
| `Ember/Trace`, `Ember/Util` | trace format, `ember-diff`, packet decoder, pcap |
| `runtime/common` | C runtime interface and SPSC ring |
| `runtime/esp32c3`, `runtime/z80` | bare-metal runtimes: start-up, interrupts, UART |
| `Tests/Ember` | corpus (recorded from Linux and hand-written), golden C, host harness, test suites |
| `tools/ember` | fixture recording, size gate, CI script |

```
nix-shell                  # gcc, sdcc, z88dk, riscv32 gcc, Espressif's QEMU, python3, dnsmasq, tshark
lake build
lake test                  # ≈ 3 minutes with every tool present
tools/ember/ci.sh          # lake test + size gate
```
