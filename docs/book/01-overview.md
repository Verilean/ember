# 1 · Overview — what Ember is

Ember is a TCP/IP stack in Lean. Lean holds the specification, the code
and the proofs. Ember goes from Lean to C and to Z80 machine code, never
the other way.

Ember has four parts:

| Part | Where | What it is |
|---|---|---|
| **The reference stack** | [`Ember/Spec`](https://github.com/Verilean/ember/tree/main/Ember/Spec) | ordinary Lean functions: SLIP, IPv4, ICMP, UDP, TCP, Ethernet + ARP, a DHCP client; with an application interface: HTTP/1.1, TLS 1.3, token checks, control requests. You can `#eval` and test them |
| **The Ember language** | [`Ember/Lang`](https://github.com/Verilean/ember/tree/main/Ember/Lang) | a small language embedded in Lean (`ember def`): an AST, a type checker, an interpreter that is its semantics. Every operation is total and defined |
| **The stack written in Ember** | [`Ember/Net`](https://github.com/Verilean/ember/tree/main/Ember/Net) | the reference stack again, function for function, in the language: no heap, fixed buffers, no recursion |
| **Back ends** | [`Ember/C`](https://github.com/Verilean/ember/tree/main/Ember/C), [`Ember/Z80`](https://github.com/Verilean/ember/tree/main/Ember/Z80) | Ember to C without undefined behaviour; Ember to a Z80 image without a C compiler |

The reference stack, the stack in Ember and the emitted C are three
implementations of one stack. A target build adds a fourth. They are
checked against each other through **one trace format**. Every
implementation writes the same line-oriented trace, so a disagreement
is always "the first line where two traces differ".

> **Want to run it first?** → [Chapter 0 · Quickstart](00-quickstart.md)
> goes from `git clone` to Linux pinging the stack.

## One function, three forms

The one's-complement addition of the checksum, in the reference stack
([`Ember/Spec/Checksum.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Checksum.lean)), is
ordinary Lean. In the stack written in Ember it is an `ember def`
([`Ember/Net/Buffer.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Buffer.lean)):

```lean
/-- One's-complement addition. -/
ember def add16 (a : u16) (b : u16) : u16 := do
  let s : u16 := a + b
  if s < a then
    return s + 1
  return s
```

This is the C the emitter produces for it, for the `host64` profile
([`Tests/Ember/golden/net.host64.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/golden/net.host64.c)):

```c
uint16_t e_add16(uint16_t v_a, uint16_t v_b) {
#line 30 "Ember/Net/Buffer.lean"
  ((void)v_a);
  ((void)v_b);
#line 31 "Ember/Net/Buffer.lean"
  uint16_t v_s = ((uint16_t)(((unsigned)v_a) + ((unsigned)v_b)));
  ((void)v_s);
#line 32 "Ember/Net/Buffer.lean"
  if ((v_s < v_a)) {
#line 33 "Ember/Net/Buffer.lean"
    return ((uint16_t)(((unsigned)v_s) + ((unsigned)((uint16_t)1u))));
  }
#line 34 "Ember/Net/Buffer.lean"
  return v_s;
}
```

Every operation is done in an unsigned type at least as wide as `int`,
then cast back explicitly. This avoids C's promotion to signed `int`.
The widths come from a target profile (`host64`, `rv32` and `sdcc-z80`
in [`Ember/Lang/Profile.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Profile.lean)). The
`#line` directives point back at the Ember source. The language is
described in [chapter 2](02-language.md) and the back ends in
[chapter 5](05-targets.md).

## Targets

| Target | How | State |
|---|---|---|
| Host (Linux) | emitted C with gcc, or the reference stack itself (`ember-host`) | tested against Linux clients: `ping`, `nc`, curl, `openssl s_client`, headless Chromium |
| **ESP32-C3** (RISC-V) | emitted C with `riscv32-none-elf-gcc`, bare-metal runtime [`runtime/esp32c3`](https://github.com/Verilean/ember/tree/main/runtime/esp32c3) | runs in Espressif's QEMU; **not run on a board** |
| **Z80** | emitted C with SDCC and [`runtime/z80`](https://github.com/Verilean/ember/tree/main/runtime/z80), or Ember's own back end ([`Ember/Z80`](https://github.com/Verilean/ember/tree/main/Ember/Z80)) | runs on a Lean model of the CPU and the machine (the CPU is checked against `z88dk-ticks`); **not run on hardware** |

HTTP runs on the host, the ESP32-C3 and the Z80. HTTPS runs on the host
and the ESP32-C3 only. The plan gives two reasons: SDCC miscompiles
`u64`, and X25519 takes minutes on a Z80
([`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md), M8).

## What ships

The executables are the `lean_exe` entries of
[`lakefile.lean`](https://github.com/Verilean/ember/blob/main/lakefile.lean). Their drivers are in
`Tests/Ember/Drivers/`.

| Binary | Purpose |
|---|---|
| `lake test` (`test`) | every suite (`Tests/AllTests.lean`); `EMBER_ONLY=…` runs one |
| `lake exe ember-host` | the reference stack on stdin/stdout: echo, `--http`, `--https`, `--auth`, `--ctl`, `--eth`, `--dhcp` |
| `lake exe ember-diff` | the first difference between two traces, with packets decoded field by field |
| `lake exe ember-pcap` | a trace's packets as a pcap file, for Wireshark |
| `lake exe ember-replay` | fixtures through `Ember.Spec`; `--write` rewrites them |
| `lake exe ember-fixtures` | run the hand-written scenarios; write their fixtures again, or `--check` them |
| `lake exe ember-gen` | generated sessions against the Spec's properties; failures shrunk into `Tests/Ember/regress/` |
| `lake exe ember-lockstep` | Spec = Ember interpreter (states compared after every input) [= host C with `--c`] |
| `lake exe ember-emit` | the emitted C of a registered program (`--profile`, `--ember`, `--dropped`, `--golden`) |
| `lake exe ember-fuzz` | random Ember programs: interpreter against emitted C; `--plant` checks that a planted emitter bug is found |
| `lake exe ember-z80` | the Z80 model and the own back end: `check`, `replay`, `ping`, `fuzz`, `own-build`, `own-size`, `rt-check`, … |
| `lake exe ember-passcert` | the certificate for the passes on the Z80 assembly of the stack's two images, and the files of its check (written into `Ember/Proof`) |

Scripts in [`tools/ember`](https://github.com/Verilean/ember/tree/main/tools/ember):

| Script | Purpose |
|---|---|
| `ci.sh [JOB]` | what CI runs: `lake test` and the size gate, or one job (`spec`, `lang`, `net`, `esp32`, `z80`, `proofs`, `size`) |
| `record-linux.py` | record fixtures from Linux in a user namespace with a TUN/TAP device, no root (`client`, `responder`) |
| `record-corpus.sh` | record every Linux fixture of the corpus again |
| `tcp-scenarios.py` | client-side TCP scenarios that `record-linux.py client` runs |
| `size-report.py [--update]` | code, RAM and cycles per ping against `bench/ember-size.baseline`, ±3 % |
| `qemu-test.sh` | build the ESP32-C3 images and run every QEMU test |
| `qemu-run.sh` | run one ESP32-C3 image in Espressif's QEMU (`--gdb`, `--log`, `--icount`) |
| `qemu-bridge.py` | an ESP32-C3 image on stdin/stdout, the same way `ember-host` works (the `--host` of `record-linux.py`) |
| `esp32.py` | one QEMU test: `boot`, `trap`, `hello`, `echo`, `slip`, `corpus`, `tick`, `ping` |
| `z80-test.sh` | build the Z80 images (SDCC and the own back end) and run every Z80 test on the model |

## What each directory covers

| Directory | Contents |
|---|---|
| `Ember/Spec` | the reference stack: SLIP, IPv4, ICMP, UDP, TCP (one connection), Ethernet + ARP, DHCP client; generators and scenarios |
| `Ember/Spec/Srv` | the stack with an application interface and `n` connections; HTTP/1.1, TLS 1.3, OIDC access tokens, control requests |
| `Ember/Spec/Crypto` | the crypto reference: SHA-2, ChaCha20-Poly1305, Curve25519 (X25519, Ed25519), P-256 |
| `Ember/Lang` | the language: AST, type checker, interpreter (= semantics), total semantics for the proofs, `ember def` syntax, profiles, random programs |
| `Ember/C` | a Clight-like C AST, `Lang → C`, the printer, a semantics for that C subset, removal of the bounds checks |
| `Ember/Net` | the stack in Ember: the SLIP build, the Ethernet build, the server with an application (`Srv`), `Http`, `Tls`, `Auth`, `Ctl` |
| `Ember/Net/Crypto` | the crypto in Ember |
| `Ember/Z80` | the Z80 CPU model and the machine; the own back end: IR, static frames, code generator, assembler, runtime routines |
| `Ember/Proof` | the proofs; [`Ember/Proof/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Proof/README.md) lists every theorem |
| `Ember/Trace`, `Ember/Util` | the trace format, its parser and diff; the packet decoder, pcap, a seeded PRNG |
| `Ember/Tools` | the code behind the executables |
| `runtime/common` | the C runtime interface (`ember_rt.h`) and the SPSC ring |
| `runtime/esp32c3`, `runtime/z80` | bare-metal runtimes: start-up, interrupts, UART |
| `Tests/Ember` | the corpus (recorded from Linux and hand-written), golden C, the host harness, the test suites |
| `tools/ember` | the scripts above |
| `bench` | the size baseline |
| `docs` | [`Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md) (why), [`Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md) (how, and progress) |

## What is proved, and what is only tested

The proofs are part of the library. `lake build` checks them. The proof
directory has no `sorry`, no `axiom`, no `native_decide` and no
`bv_decide`. Where the statements name their axioms, the axioms are the
standard ones (`propext`, `Classical.choice`, `Quot.sound`). The exact
statements and their hypotheses are in
[`Ember/Proof/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Proof/README.md) and in
[chapter 10](10-proofs.md). In short:

**Proved** (for the **SLIP echo build** of the stack, `Net.prog`, unless a
line says otherwise):

| | |
|---|---|
| Properties of the Spec | checksum algebra and RFC 1624, SLIP and header round trips, TCP invariants (M5.1–M5.3) |
| The stack in Ember refines the Spec | function by function. Then for each received byte, each tick, each call of `main`, and from the initial state for any input: the stack never traps, and it transmits and drops what `Spec.step` does (M5.4–M5.6) |
| The emitted C | does what the Ember semantics does, under the C semantics `Ember.C.Sem` (expressions, statements, calls, programs), for programs without by-reference parameters. With the result above: the C of the SLIP build transmits and drops what the Spec does (M5.8) |
| The C without bounds checks | the same C with all 17 bounds checks removed does the same. This holds for the SLIP build only (M5.9, first part) |
| The Z80 back end | the frame validator, `Lang → IR`, and the encoder against the CPU model (M7.1, M7.2, M7.4). `IR → Z80` is proved for **the SLIP build's test-harness image** on the Lean model of the machine, built by default and without the passes on the assembly. For any input, the image halts having transmitted and dropped what the Spec does (M7.3, for that image only) |

**Tested, not proved:**

- The link between the theorems and the running code. For example, that
  the items and bytes of an image are those `build` gives. Evaluation
  (`#guard`) checks this, not a theorem.
- Everything in M8 and M9: the application interface, HTTP, TLS 1.3, the
  crypto, the token check and the control requests. The plan decided
  this on 2026-11-06. These are checked by lockstep runs (Spec = Ember
  interpreter = host C under UBSan/ASan = QEMU), RFC test vectors,
  runs against OpenSSL and recorded sessions with real clients.
- The Ethernet/ARP/DHCP build.
- The runtimes (start-up, interrupts, UART, timer, ring). They are
  hand-written and trusted.
- The stack-depth bound of the Z80 images. It comes from an analysis
  (`Ember.Z80.StackBound`), not a theorem
  ([`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md) §2.7).

**Not claimed at all:**

- That the Z80 back end is correct for every IR program.
- Anything about the board runtime and interrupts.
- Response times.
- Side channels in the crypto. The crypto is written without
  secret-dependent branches, but it has not been audited.

The trusted base is Lean's kernel, the C printer, the C compiler, the
assumption that `Ember.C.Sem` agrees with the compiler's reading of the
printed C, and the runtime. On the Z80, the trusted base is also the
Lean model of the machine.

## Current limits

From [`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md) §2.7 and
[`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md):

- **No hardware yet.** The ESP32-C3 runs in QEMU and the Z80 on a Lean
  model. The board steps (M4.8, M4z.5) and Wi-Fi (M4w on a board) are
  not done. QEMU says nothing about the quality of the ESP32-C3's RNG;
  only a board can check that.
- **Capacities are build constants.** These include the MTU (296 on
  SLIP), the number of connections (one in the echo stack; `n`, chosen
  when the program is built, in the server), the request and record
  buffers, and the ARP cache of four entries. To change one, you build
  the stack again, and for the proved build you check the proofs again.
- **Protocol scope.** The stack has no IPv6, no fragment reassembly, no
  TCP options beyond MSS and no congestion control. TLS has one cipher
  suite (`TLS_CHACHA20_POLY1305_SHA256` with X25519), runs only as a
  server, and has no client authentication, 0-RTT or resumption.
- **Keys.** The keys and certificates are in the image, and the demo
  ones are in the source. Tokens are not revoked, and the device never
  fetches keys (it has no TLS client).
- **Sizes.** On the Z80, the echo stack meets the 8 KB code budget with
  both back ends. It misses the 1 KB RAM budget by about 40 bytes once
  the stack is counted
  ([`Ember/Net/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Net/README.md), "Size").

## What this book covers

```text
 0. Quickstart              ── clone, build, test, run, compare traces
 1. Overview                ── you are here
 2. The Ember language      ── ember def, types, effects, the checker
 3. The reference stack     ── Ember.Spec, step, Spec.Srv
 4. Traces and testing      ── the trace format, corpus, lockstep, fuzzing
 5. Targets                 ── C, the ESP32-C3, the Z80 and its own back end
 6. Tutorial: an HTTP app   ── a site on the application interface
 7. HTTPS and TLS 1.3       ── the TLS server, certificates, entropy
 8. Protected routes        ── OIDC/JWT access tokens
 9. Control and status      ── POST, kept connections, time, RNG
10. What is proved          ── the theorems and their hypotheses
11. Architecture            ── the system map
```
