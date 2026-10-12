# Ember — design (M0)

Ember is a small embedded-software track inside the Sparkle repository:

1. a **TCP/IP stack written in Lean 4** (the reference: pure functions you
   can `#eval` and test),
2. a **Lean-hosted DSL that emits C** for bare-metal targets (no heap,
   fixed-size buffers, no recursion, interrupts),
3. the stack **written in that DSL, compiled to C and run** on small
   machines — the **ESP32-C3** (RISC-V; serial link first, then Wi-Fi)
   and a **Z80-class 8-bit CPU**, the target that shows what the approach
   is worth: a few kilobytes of code, a few hundred bytes of RAM,
4. eventually **proofs that connect the three**, CompCert style: the DSL
   program refines the reference, and the DSL → C translation preserves
   its meaning.

Sparkle proves things about hardware generated from Lean.  Ember is the
same idea for the software that runs on it: one source of truth in Lean,
generated low-level code, and proofs instead of trust where it counts.
It goes from Lean *to* C, never the other way (see the 2026-10 direction:
no C/Rust → DSL translation).

Status (2026-10-09): M1–M3 implemented on the host — the reference
stack, the DSL with its interpreter and C emitter, and the stack in
Ember, cross-checked against each other; see `Ember-plan.md`
("Progress").  Ember lives in its own repository rather than inside
Sparkle.

---

## 1. Decisions taken at M0

These are the defaults chosen when the project started; each is cheap to
revisit before M2.

| Question | Decision | Why |
|---|---|---|
| Where | `Ember/` in the Sparkle repo, its own `lean_lib`, no dependency on Sparkle's hardware libraries | reuses the toolchain, `firmware/`'s cross build, and later the RV32 SoC simulator |
| Targets (2026-10-09) | **ESP32-C3** and **Z80** | ESP32-C3: RISC-V (CompCert has a back end), Espressif's QEMU emulates it, a board costs little and has Wi-Fi; Z80: the impact target.  Classic ESP32 (Xtensa) only through gcc |
| Link layer | SLIP over the UART first; Ethernet II + ARP over Wi-Fi raw frames on the ESP32-C3 later | SLIP: one interrupt source, no driver, small trusted base; Wi-Fi: the demonstration, at the cost of the vendor's driver blob |
| DSL style | deep embedding: an AST, a type checker and an executable semantics written in Lean, with a surface syntax that reads like Lean `do` code | the proofs in M5 need the DSL's semantics as an object; a reflection of arbitrary Lean terms is what made Sparkle's elaborator hard ("not inlinable") |

## 2. Layers

```
Ember.Spec   reference stack, ordinary Lean           ← properties (P1)
   ▲ refines (P2)
Ember.Lang   DSL: AST, types, interpreter (= semantics)
   │ compile (P3: preserves semantics)
Ember.C      a Clight-like C subset: AST + semantics
   │ print (trusted, small)
C text  →  gcc / CompCert  →  RISC-V binary + Ember runtime (trusted)
```

### 2.1 `Ember.Spec` — the reference stack

Pure Lean over `ByteArray` / `List UInt8`.  A step function

```
step : StackState → Input → StackState × List Output
Input  = rxByte UInt8 | tick       -- a byte from the link, a timer tick
Output = txByte UInt8
```

Scope, in this order: SLIP framing; IPv4 (no fragmentation, options
skipped, header checksum checked); ICMP echo; UDP echo; TCP with one
connection, passive open, in-order data, fixed window, then
retransmission on the timer.  Not in scope: IPv6, ARP (SLIP is
point-to-point), DHCP, fragment reassembly, TCP options beyond MSS,
congestion control, more than one connection.

`IP/Net/` holds hardware versions of the same protocols (Ethernet, ARP,
IPv4, ICMP, TCP header, TCP state machine, SLIP, CRC32); they are a
reference for field layouts and corner cases, not a dependency.

### 2.2 `Ember.Lang` — the DSL

Every operation is **total and defined**, so the language has no
undefined behaviour and the C it produces must not either:

- **Types**: `u8 u16 u32 u64 bool`; fixed arrays `[τ; n]`; records of
  those.  No pointers.  A function may take an array *by reference*
  (`buf : ref [u8; 1500]`); two references in one call may not name the
  same array (checked), so there is no aliasing to reason about.
- **Expressions** are side-effect free: literals, variables, arithmetic
  modulo 2^w, comparisons, zero-extend / truncate, array reads.  A shift
  by ≥ width is 0 and division by zero is 0 — defined here, guarded in
  the emitted C.  Array reads out of range are an error in the semantics;
  the emitter inserts a check that traps unless the index is provably in
  range.
- **Statements**: local `let`, assignment, array store, `if`, bounded
  loops (`for i in [0, n)`, `loop (max := n)`), `break`, `return`, calls.
  No recursion: the call graph is acyclic, so stack depth is static.
- **Effects** are explicit: `mmio.read32 addr`, `mmio.write32 addr v`,
  and the runtime's ring buffer (`ring.pop`).  The semantics records them
  as a trace of events and reads inputs from an oracle.
- **Interrupts** (v1): the UART receive ISR lives in the runtime and only
  pushes bytes into a single-producer / single-consumer ring.  The main
  loop, written in Ember, pops from it.  The program's semantics is then
  a function of the received byte sequence; the interleaving is
  abstracted by the ring's specification.  Writing ISRs in Ember comes
  later, with an explicit model of where interrupts may occur.

The semantics is an **executable interpreter** in Lean
(`exec : Prog → Env → Fuel → Result × Trace`).  The same interpreter is
the oracle for differential tests (against `Ember.Spec`, and against the
emitted C compiled on the host) and the object of the proofs.

Surface syntax: an `ember` command whose body reads like Lean `do`
notation and elaborates to the AST, e.g.

```lean
ember def ip_checksum (buf : ref [u8; 1500]) (off len : u16) : u16 := do
  let mut sum : u32 := 0
  for i in [0, len / 2) do
    sum := sum + ((buf[off + 2*i] : u32) <<< 8) + (buf[off + 2*i + 1] : u32)
  ...
```

### 2.3 `Ember.C` — the C subset and the emitter

The emitter produces C99 close to CompCert's Clight: no side effects
inside expressions, explicit temporaries, `stdint.h` types only.

Integer promotion is the main trap, and it depends on the target.  C
promotes anything narrower than `int` to (signed) `int`: with a 32-bit
`int`, `a * b` on two `uint16_t` can overflow a signed int — undefined
behaviour; with SDCC's 16-bit `int` on the Z80, the same happens already
for `uint8_t * uint8_t` (255·255 > 32767).  The emitter is therefore
parameterised by a **target profile** (width of `int`, register width,
cost of each operation width) and emits every operation in the narrowest
*unsigned* type that is at least as wide as `int` and as the operands,
truncating by an explicit cast: `(uint8_t)((unsigned)a * (unsigned)b)`.
On a 32-bit target that is `uint32_t`; on the Z80 it stays 16-bit, which
matters, because 32-bit arithmetic there is a library call.  Shifts and
divisions get the guards of §2.2.

`Ember.C` is an AST with its own semantics in Lean.  The compiler
`Lang → C AST` is what P3 proves; the printer `C AST → text` and
everything after it are trusted (§4).

### 2.4 Runtime and target

Hand-written, kept small, part of the trusted base.  On the ESP32-C3,
bare metal: `start.S` (stack, trap vector, watchdogs off), the UART
driver and its receive ISR through the interrupt matrix, the SYSTIMER as
the TCP retransmission `tick`, and the ring buffer.  On Wi-Fi, an ESP-IDF
component that hands raw Ethernet frames from the driver to the same ring
and transmits Ember's frames, bypassing lwIP — the Wi-Fi blob, ESP-IDF
and FreeRTOS then join the trusted base, and the bare-metal SLIP build
remains the small-trusted-base configuration.

Host side for tests: QEMU's (Espressif fork, `-M esp32c3`) serial port on
a socket, driven by a test program that speaks SLIP and sends crafted IP
packets; no root needed.  Attaching to the host's network with
`slattach` is a manual step for demos.

Budget on the ESP32-C3 (SLIP build): under 16 KB of code and 8 KB of RAM.

### 2.5 The Z80 target

The point of a Z80 port is that it is hard: 64 KB of address space, no
multiply or divide instruction, 16-bit arithmetic built from 8-bit
pieces, 32-bit arithmetic as library calls.  uIP (Dunkels, 2002) showed
that a TCP/IP stack fits machines of this class in about 5 KB of code and
a few hundred bytes of RAM.  Ember aims for the same footprint, with the
code generated from Lean and checked against a specification.

What makes that achievable is the DSL's shape, not cleverness in the
emitter:

- **one packet buffer**, used for receive and transmit; replies are built
  in place (an ICMP echo reply swaps addresses and changes one byte);
- **checksums updated incrementally** (RFC 1624) instead of recomputed,
  and accumulated in 16 bits with end-around carry, never 32;
- **no retransmission buffer**: as in uIP, the application regenerates
  unacknowledged data on request;
- **small MTU** (SLIP's usual 296 bytes), one TCP connection, MSS
  announced accordingly;
- **static everything**: no heap, a call graph without recursion, so the
  stack depth is known at compile time;
- **narrow arithmetic** from the target profile (§2.3), and bounds checks
  removed where P2 proves the index in range — the proofs pay for speed,
  not only for safety.

Toolchain: SDCC 4.6 (`nix-shell -p sdcc`) and z88dk (`nix-shell -p
z88dk`), whose `z88dk-ticks` simulator counts cycles exactly — the Z80
analogue of `bench/gate`'s instruction count.  Hardware: an RC2014-class
machine with a 68B50 ACIA or Z80 SIO in interrupt mode, SLIP over the
serial port.

The proof chain is shorter on the Z80 as long as it goes through C:
CompCert has no Z80 back end, so SDCC stays in the trusted base, backed
by differential testing against the interpreter.  §2.6 removes it.

### 2.6 Ember's own Z80 back end (later)

Ember is small enough to compile to the Z80 directly, and the
restrictions that make it UB-free also make a back end simple:

- no recursion → every local and temporary gets a **fixed address**
  (static frames, overlaid along the call graph); no frame pointer, no
  calling convention to honour;
- no pointers → array accesses are `base + index` with a known base;
- known widths → 8-bit operations stay 8-bit, 16-bit ones use `HL`/`DE`,
  32-bit ones call a handful of runtime routines written once;
- whole-program compilation → no ABI, no linker relocations beyond the
  program itself.

Pipeline: `Ember.Lang → linear IR (three-address, explicit widths) → Z80
assembly → bytes`, all in Lean.  The Z80 side needs an **executable
semantics of the instruction subset the back end emits** (on the order of
60 instructions), which doubles as the test oracle: the same program runs
in the Lang interpreter, in the Lean Z80 model, and under `z88dk-ticks`,
and the three must agree.  Proving the back end correct is then the
CompCert argument on a much smaller machine — and the result is a chain
from the specification to Z80 machine code with no C compiler in it.

The C path stays: it is the portable back end (RISC-V, the host), the
baseline the Z80 back end is measured against (cycles under
`z88dk-ticks`, bytes of code), and a second implementation to test
against.

A further step, natural in this repository: a Z80 core written in
Sparkle, so that the CPU, the network stack, and the code between them
all come from Lean.

### 2.7 Resources: what is fixed, what is bounded, what is not

"Static everything" is easy to overstate.  What holds, for one
configuration of the stack (the globals, the functions, the profile):

- **Memory is laid out before the program runs.**  No heap; every
  global, parameter, local and temporary has a fixed address (§2.6), so
  the static RAM of an image is a number the build prints — for the SLIP
  build on the board 1061 bytes: 273 of the runtime (its cells and the
  256-byte receive ring), 623 of globals (the packet buffer, the TCB, the
  application's buffer), 165 of frames and temporaries.  The build
  refuses an image whose code does not fit below the RAM or whose static
  RAM does not fit below `0xFF00`.
- **The stack is bounded, not constant.**  The call graph has no cycle
  and a call pushes only its return address, so the deepest stack follows
  from the items of the image (`Ember.Z80.StackBound`: start-up, the
  program, the routines of the runtime, one interrupt — the interrupt
  routine does not let another in): 24 bytes for the SLIP build, against
  16 seen on the corpus and more than 31 KB of room.  `ember-z80
  own-size` fails when the bound exceeds the room.  That bound is an
  analysis, not a theorem; proved so far is only that the routines of the
  loopback image for the test harness use no stack at all (§4, M7.3).
- **Time is not fixed.**  How long a call of `main` takes depends on the
  input: the loops are bounded (`for`, `loop (max := n)`), so each call
  ends, and the proofs give a number of steps of the Ember semantics that
  suffices for any input (`n + 4716` for the SLIP build) — a bound on the
  *fuel* of a semantics, not on T-states, and nothing is proved about
  response times or about interrupts arriving while `main` runs.  What is
  sent, and how often it is sent again, depends on the peer.

What this buys: no leak and no fragmentation, because nothing is
allocated; a footprint that can be read off before deployment; and a
state small and fixed enough to state invariants about.  What it costs,
as things are today:

- capacities are constants of the build — the MTU, **one** TCP
  connection, one segment of echoed data awaiting its acknowledgement, an
  ARP cache of four entries (Spec and the Ethernet build) — and changing
  one means generating and building again, and for the proved build,
  checking the proofs again;
- no recursion, no data structure that grows, no pointers;
- a function added to the stack is a function added to the proofs.

**Running out is a protocol matter, not a memory matter**, and each case
has its behaviour written down in the Spec and replayed from the corpus:
a frame longer than the buffer is dropped (`drop
reason=oversize-frame`), the decoder recovering at the next frame end; a
segment for a second connection is answered with a reset (`drop
reason=unsupported-second-connection`); the echo application takes new
data only when the last echo is acknowledged and advertises its window
accordingly; on the board, the receive ring raises RTS at 224 of 256
bytes and counts what still overruns.  The one connection is given back
on a close, on a reset, after `maxRetries` (8) retransmissions without an
acknowledgement, after `idleTicks` without traffic, and from FIN-WAIT-2
after the same wait — all driven by `tick`; without ticks none of the
timeouts happen.

What is proved and what is only tested or checked is in
`Ember/Proof/README.md`; in short: the Spec-to-IR chain is proved for the
SLIP build; of the Z80 code, the functions of the loopback image built
*without* the passes on the assembly; of the images as built by default,
nothing — they are tested.

## 3. Milestones and exit criteria

| | Deliverable | Done when |
|---|---|---|
| M0 | this document | agreed |
| M1 | `Ember.Spec`: SLIP, IPv4, ICMP echo, UDP echo, TCP (one connection) | `lake test` replays packet captures (ping, UDP echo, a TCP session from `nc`) and the replies match byte for byte |
| M2 | `Ember.Lang` core: AST, type checker, interpreter, `ember` syntax, C emitter | a suite of small programs (checksum, SLIP decode, ring buffer) gives the same trace in the interpreter and as host-compiled C; the C compiles warning-free with `-Wall -Wextra -Wconversion` and runs clean under `-fsanitize=undefined` |
| M3 | the stack in Ember | for the M1 captures, interpreter = `Ember.Spec`, and host-compiled C = interpreter |
| M4 | ESP32-C3, bare metal, SLIP (QEMU, then board) | ping, UDP echo and TCP echo answered through the UART ISR; code/RAM size reported and tracked in CI like `bench/gate` |
| M4w | ESP32-C3 on Wi-Fi | ping and TCP echo from a laptop on the same network, through raw frames below lwIP |
| M4z | on the Z80 (`z88dk-ticks`, then hardware) | the same exchanges; code ≤ 8 KB, RAM ≤ 1 KB; cycles per ping tracked in CI |
| M5 | proofs | see §4 |
| M6 | own Z80 back end (§2.6) | the M4z exchanges with code generated by Ember itself; agreement of interpreter, Lean Z80 model and `z88dk-ticks`; code size and cycles reported against the SDCC build |
| M7 | back-end proof | Lang → IR → Z80 simulation proof over the Lean Z80 model; trusted base on the Z80 reduced to the Z80 model and the runtime |

M4 is optionally followed by the Sparkle RV32 SoC under the JIT simulator
(own CPU, own stack); M4z by an RC2014-class machine.  The detailed,
step-by-step plan is [`Ember-plan.md`](Ember-plan.md).

## 4. Proof plan

- **P1 — properties of `Ember.Spec`**: the checksum algebra (one's
  complement, incremental update), header round trips (parse ∘ emit),
  TCP state-machine invariants (sequence numbers within the window,
  no data accepted before ESTABLISHED, …).
- **P2 — the Ember program refines `Ember.Spec`**: per function at first
  (`exec ip_checksum … = Spec.checksum …`), with a symbolic-execution
  tactic to keep it cheap; then the main loop as a simulation of `step`.
- **P3 — `Lang → C` preserves semantics**: a forward simulation between
  the interpreter and the `Ember.C` semantics, CompCert style.  Defining
  `Ember.C`'s semantics in Lean is part of the work; CompCert's Clight
  semantics lives in Coq and cannot be linked formally.

**Trusted base**, explicitly: Lean's kernel; the C printer; the C
compiler (gcc in practice, CompCert where the claim matters); the
assumption that `Ember.C`'s semantics agrees with the compiler's
reading of the printed C; the runtime (start-up, UART/interrupt/timer drivers,
ring buffer — specified, not proven, at first).

## 5. Open questions

- How far the ring-buffer abstraction of interrupts carries once ISRs are
  written in Ember: an explicit interleaving semantics, or a restriction
  to SPSC structures with a proven specification.
- Whether `Ember.C` should be close enough to Clight that a translation
  validator on the CompCert side can check the printed C against it.
- Timer granularity for TCP retransmission, and how time appears in
  `Ember.Spec` (`tick` inputs vs a clock value).
