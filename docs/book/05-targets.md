# 5 · C and the targets

An Ember program ([chapter 2](02-language.md)) reaches a machine by one
of two roads:

```
                    ┌── Ember.C.compile ──▶ C ──▶ gcc            host harness   (tests)
checked Prog ───────┤                        ├──▶ riscv32 gcc    ESP32-C3       (runtime/esp32c3)
                    │                        └──▶ SDCC           Z80            (runtime/z80)
                    └── Ember.Z80: IR.lower ▶ IR ▶ Codegen ▶ Asm ──────────▶ Z80 (no C compiler)
```

The C road is the main one: one emitter, parameterised by a target
profile, whose output has no undefined behaviour on any input. The
second road is Ember's own Z80 back end, which takes the C compiler out
of the picture.

Every snippet in this chapter is copied from the tree, with its path.

## `Lang → C`

| File | What |
|---|---|
| [`Ember/C/Ast.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Ast.lean) | the C subset, close to CompCert's Clight |
| [`Ember/C/Compile.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Compile.lean) | `Lang → C` (`compile`, `emitC`) |
| [`Ember/C/Print.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Print.lean) | C AST to text (trusted, kept small: every compound expression parenthesised) |
| [`Ember/C/Sem.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Sem.lean) | a semantics for that C subset, in which "undefined" is a result |
| [`Ember/C/DropChecks.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/DropChecks.lean) | the C without its bounds checks (M5.9) |

The emitter's input is a checked program; `emitC` checks it first
(`Ember/C/Compile.lean`):

```lean
def emitC (p : Prog) (o : Opts := {}) : Except String String := do
  let p ← match p.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let u ← compile p o
  return u.print ++ "\n" ++ tables p o
```

```lean
structure Opts where
  profile : Profile := .host64
  namePrefix : String := ""
  lines   : Bool := true
  /-- Planted bug for the fuzzer's self-test: drop the truncating cast of `+`. -/
  bugDropCast : Bool := false
```

Names in the C: functions `e_f`, globals `g_x`, records `s_T`, locals
and parameters `v_x`, temporaries `t<n>`. `namePrefix` goes in front of
the global ones so that many programs can share one C file (the fuzzer
and the Z80 harness image do this).

### What the C looks like

The checksum example (`Ember/Lang/Examples.lean`):

```lean
ember def csum_add (acc w : u16) : u16 := do
  let s : u16 := acc + w
  if s < acc then
    return s + 1
  return s
```

becomes, in [`Tests/Ember/golden/checksum.host64.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/golden/checksum.host64.c):

```c
uint16_t e_csum_add(uint16_t v_acc, uint16_t v_w) {
#line 28 "Ember/Lang/Examples.lean"
  ((void)v_acc);
  ((void)v_w);
#line 29 "Ember/Lang/Examples.lean"
  uint16_t v_s = ((uint16_t)(((unsigned)v_acc) + ((unsigned)v_w)));
  ((void)v_s);
#line 30 "Ember/Lang/Examples.lean"
  if ((v_s < v_acc)) {
#line 31 "Ember/Lang/Examples.lean"
    return ((uint16_t)(((unsigned)v_s) + ((unsigned)((uint16_t)1u))));
  }
#line 32 "Ember/Lang/Examples.lean"
  return v_s;
}
```

`#line` directives map every statement back to its Ember source line, so
a compiler error or a debugger points into the `.lean` file.

## No undefined behaviour

The emitter's header comment (`Ember/C/Compile.lean`) lists how:

- every arithmetic operation is computed in the profile's `opType` and
  truncated with an explicit cast;
- shifts are guarded (`s >= w ? 0 : …`), divisions too
  (`b == 0 ? 0 : …`);
- array reads and writes are bounds-checked unless the index is
  provably in range by its form;
- `#line` directives for every statement.

### Integer promotion and profiles

C converts any operand narrower than `int` to *signed* `int` before an
operation. With a 32-bit `int`, `u16 * u16` can overflow a signed int;
with SDCC's 16-bit `int`, `u8 * u8` already can (255·255 > 32767). So the
emitter computes in plain `unsigned` when the width fits in `int`, and in
the operand's own `uintN_t` otherwise ([`Ember/Lang/Profile.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Profile.lean)):

```lean
/-- The unsigned C type an operation of width `w` is computed in. -/
def Profile.opType (p : Profile) (w : Width) : String :=
  if w.bits ≤ p.intBits then "unsigned" else cTypeOf w
```

| Profile | `int` | registers | used for |
|---|---|---|---|
| `host64` | 32 | 64 | the host harness, the size gate's `host64` rows |
| `rv32` | 32 | 32 | ESP32-C3 |
| `sdcc-z80` | 16 | 8 | Z80 with SDCC |

Unsigned arithmetic wraps, so no operation can overflow.

### Guards

From the program that uses every construct
(`Ember/Lang/Examples.lean`, lines 240 and 243):

```lean
  out.byte((200 : u8) / (b - b))
```
```lean
  out.byte((128 : u8) >>> (b &&& 7))
```

and their C ([`Tests/Ember/golden/constructs.host64.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/golden/constructs.host64.c)):

```c
  uint8_t t0 = ((uint8_t)(((unsigned)v_b) - ((unsigned)v_b)));
  ((void)t0);
  ember_out_byte(((uint8_t)((t0 == 0u) ? ((uint8_t)0u) : ((uint8_t)(((unsigned)((uint8_t)200u)) / ((unsigned)t0))))));
```
```c
  uint8_t t2 = ((uint8_t)(((unsigned)v_b) & ((unsigned)((uint8_t)7u))));
  ((void)t2);
  ember_out_byte(((uint8_t)((t2 >= 8u) ? ((uint8_t)0u) : ((uint8_t)(((unsigned)((uint8_t)128u)) >> t2)))));
```

The divisor and the shift amount go into a temporary first. A
subexpression without variables is evaluated by the semantics at emit
time and emitted as a constant: line 242, `out.byte((1 : u8) <<< 9)`,
becomes `ember_out_byte(((uint8_t)0u));`.

### Bounds checks

An index is left unchecked only if it is a literal in range or a `u8`
index into an array of at least 256 elements (`indexSafe`,
`Ember/C/Compile.lean`):

```lean
def indexSafe (i : Expr) (iw : Width) (n : Nat) : Bool :=
  match i with
  | .lit v _ => v < n
  | _ => iw == .w8 && n ≥ 256
```

Everything else gets a check, hoisted into a temporary before the
statement, in the interpreter's evaluation order. `get16` of the stack
(`Ember/Net/Buffer.lean`)

```lean
ember def get16 (o : u16) : u16 := do
  return ((buf[o] : u16) <<< 8) ||| (buf[o + 1] : u16)
```

emits ([`Tests/Ember/golden/net.host64.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/golden/net.host64.c)):

```c
uint16_t e_get16(uint16_t v_o) {
#line 13 "Ember/Net/Buffer.lean"
  ((void)v_o);
#line 14 "Ember/Net/Buffer.lean"
  uint16_t t0 = v_o;
  if ((t0 >= 296u)) {
    ember_trap("fn=get16 at stmt 1: index out of bounds [0, 296)");
  }
  uint16_t t1 = ((uint16_t)(((unsigned)v_o) + ((unsigned)((uint16_t)1u))));
  if ((t1 >= 296u)) {
    ember_trap("fn=get16 at stmt 1: index out of bounds [0, 296)");
  }
  return ((uint16_t)(((unsigned)((uint16_t)(((unsigned)((uint16_t)g_buf[t0])) << ((uint8_t)8u)))) | ((unsigned)((uint16_t)g_buf[t1]))));
}
```

The trap message is the interpreter's error location
(`fn=get16 at stmt 1`), so a trap on a target and an error in the
interpreter name the same place. `ember_trap` does not return
([`runtime/common/ember_rt.h`](https://github.com/Verilean/ember/blob/main/runtime/common/ember_rt.h)); with
`EMBER_TRAP_TERSE` the place strings are not compiled in.

### What "no undefined behaviour" means here

[`Ember/C/Sem.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Sem.lean) gives the emitted subset a
meaning only where C gives it one *and* that meaning does not depend on
a signed type: an operation that C would do in signed `int`, a shift by
the width or more, a division by zero, an index outside its array — all
have no meaning (`Res.undef`). "The emitted C has no undefined
behaviour" is the statement that running it never yields `Res.undef`.
`Tests/Ember/LangTests.lean` runs the emitted C of the examples, of
random programs and of the stack under this semantics against
`Ember.Lang.Sem`, for every profile; M5.8 proves it for programs without
by-reference parameters (the stack is one) — see
[chapter 10](10-proofs.md).

Besides, on the host the C is compiled with
`-std=c99 -Wall -Wextra -Wconversion -Werror -pedantic` and run under
UBSan and ASan (`Ember/Tools/Cc.lean`, [chapter 4](04-testing.md)).

### Dropping the bounds checks (M5.9)

The checks cost code. For the SLIP build of the stack the refinement
proofs show every index in range, so none of its checks can fire.
[`Ember/C/DropChecks.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/DropChecks.lean) removes them —
every `if (t >= n) ember_trap(…)` the emitter put before an access, and
nothing else:

```lean
/-- A bounds check as `placeIndex` emits it. -/
def isCheck : CStmt → Bool
  | .ite (.bin ">=" _ _) [.expr (.call "ember_trap" [.str _])] [] => true
  | _ => false
```

This is not a pass of `compile`, and nothing runs it by default. Its
justification is a theorem: `Ember.Proof.CDrop.stack_c_dropped` — the
SLIP build's C without any bounds check, under the C semantics, never
traps, is never undefined, and transmits and drops what the Spec does,
for any input (plan M5.9; there are 17 checks in that C). The tools
allow it for that program only ([`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean)):

```lean
/-- The programs whose C may go without bounds checks: `stack_c_dropped`
is about the SLIP build (`Net.prog`), and no other. -/
def dropped : List String := ["net"]
```

The same `get16` in
[`Tests/Ember/golden/net.dropped.host64.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/golden/net.dropped.host64.c)
keeps its temporaries and loses only the checks:

```c
  uint16_t t0 = v_o;
  uint16_t t1 = ((uint16_t)(((unsigned)v_o) + ((unsigned)((uint16_t)1u))));
  return ((uint16_t)(((unsigned)((uint16_t)(((unsigned)((uint16_t)g_buf[t0])) << ((uint8_t)8u)))) | ((unsigned)((uint16_t)g_buf[t1]))));
```

Other programs (the Ethernet builds, HTTP, HTTPS, the examples) keep
their checks, and the boards build the C with its checks. Per-check
elimination from a range lemma is not done.

## `ember-emit`

[`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean) prints the C of a
registered program:

```
lake exe ember-emit NAME [--profile host64|rv32|sdcc-z80] [--ember] [--dropped]
lake exe ember-emit --golden
```

| Flag | Effect |
|---|---|
| `--profile P` | `host64` (default), `rv32`, `sdcc-z80` |
| `--ember` | print the program as Ember source instead (`Prog.pretty`) |
| `--dropped` | the C without bounds checks; refused for every program but `net` |
| `--golden` | rewrite `Tests/Ember/golden/<name>.<profile>.c` (and `net.dropped.<profile>.c`) for every registered program and profile |

The registered programs — those with golden files — are:

```lean
def registry : IO (List (String × Prog)) :=
  pure (Examples.all ++ [("net", Net.prog), ("sliploop", Net.Loop.prog),
    ("net-eth", Net.Eth.prog), ("net-eth-dhcp", Net.Eth.progDhcp)])
```

with `Examples.all` = `checksum`, `slip`, `ring`, `crc32`,
`constructs`. Some more can be emitted by name, without a golden file:
`trapnote`, `http` (the HTTP server on two connections), `crypto`,
`https`, `https-ctl` (as shipped), `https-ctl-test`, `https-auth-test`.

The golden files are what the tests compare the emitter's output with;
after a deliberate change to the emitter or to a program, regenerate
them with `--golden` and review the diff. The target scripts also check
that the golden `net.rv32.c` / `net.sdcc-z80.c` are current before they
build an image.

## The host harness

[`Tests/Ember/host/harness.c`](https://github.com/Verilean/ember/blob/main/Tests/Ember/host/harness.c) runs
emitted C on the host:

```
harness [-p K] inputs.trace          one run, trace on stdout
harness --batch LIST                 lines "K inputs.trace output.trace"
```

It reads the `rx`/`tick` lines of a trace as the input oracle, calls
program K's entry while input remains (stopping after three calls in a
row that consume nothing, as `Ember.Lang.runMachine` does), and writes
the same trace the interpreter writes. A trap is reported as a final
`note trap (...)` line and exit status 3. In `--batch` mode each run is
a forked child, so every run starts from the initial globals.

[`Ember/Tools/Cc.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Cc.lean) writes the emitted
units next to the harness and compiles them with `$CC` (default `gcc`)
and the strict flags:

```lean
def strictFlags : Array String :=
  #["-std=c99", "-Wall", "-Wextra", "-Wconversion", "-Werror", "-pedantic",
    -- nix's cc wrapper defines _FORTIFY_SOURCE, whose #warning fires at -O0
    "-Wno-cpp"]
```

This is what the differential tests, the fuzzer (`ember-fuzz`) and
`ember-lockstep --c` use; tests skip it when no C compiler is installed.
How they compare traces is [chapter 4](04-testing.md).

The runtime interface the emitted code calls is the same on every target,
[`runtime/common/ember_rt.h`](https://github.com/Verilean/ember/blob/main/runtime/common/ember_rt.h):

```c
/* Next input item: 0x00..0xFF a byte, 0x0100 a tick, 0xFFFF nothing. */
uint16_t ember_input_next(void);
uint16_t ember_ring_pop(void);
/* On a link that delivers whole frames: as ember_input_next, and 0x0200
 * after the last byte of each frame. */
uint16_t ember_input_frame(void);

/* Transmit: bytes of the current frame, then end of frame. */
void ember_out_byte(uint8_t b);
void ember_out_end(void);

/* Diagnostics (drop reasons and notes are tables in the emitted code). */
void ember_drop(uint8_t code);
void ember_note(uint8_t code, uint32_t value);

uint32_t ember_mmio_read32(uint32_t addr);
void ember_mmio_write32(uint32_t addr, uint32_t value);
```

One function per effect of the language. The runtime is hand-written and
part of the trusted base; on a target it is start-up code, the UART
interrupt feeding an SPSC ring ([`runtime/common/ring.h`](https://github.com/Verilean/ember/blob/main/runtime/common/ring.h)),
and the timer.

## ESP32-C3, bare metal

[`runtime/esp32c3`](https://github.com/Verilean/ember/blob/main/runtime/esp32c3/README.md): the emitted C with
a runtime of three files — no ESP-IDF, no RTOS, no C library.

| File | Contents |
|---|---|
| `start.S` | reset entry (stack, `mtvec`, `.bss`), the vector table, trap entry |
| `link.ld` | code in IRAM from `0x40380000`, data in DRAM from `0x3FC90000` (64 KB each), 4 KB stack |
| `soc.h` | the registers used: UART0/1, interrupt matrix, SYSTIMER, watchdogs, clock gates, GPIO matrix |
| `rt.c` | watchdogs off, UART0 receive interrupt → SPSC ring, polled transmit, SYSTIMER tick, the trace on UART1, trap handler, main loop |
| `Makefile` | `NAME.elf`, `NAME.map`, `NAME.img` (ESP image) and `NAME.bin` (padded to a 4 MB flash image for QEMU) |

UART0 carries SLIP and nothing else; UART1 is the debug channel (the
trace). Build-time switches are listed at the top of `rt.c`:
`EMBER_TRACE` (0 silent but traps, 1 `tick`/`tx N`/`# idle` lines,
2 also `drop`/`note`, the default), `EMBER_TICK_HOST` (a tick when the
host asks, so fixtures replay deterministically), `EMBER_ICOUNT`,
`EMBER_ENTROPY`, and `APP` (`APP_STACK`, `APP_ECHO`, `APP_HELLO`,
`APP_TRAP`, `APP_BOOT`).

Building an image (`runtime/esp32c3/Makefile`):

```
make OUT=dir NAME=stack PROG=path/to/net.rv32.c [DEFS="-DEMBER_TICK_HOST=1"]
make OUT=dir NAME=echo  DEFS="-DAPP=APP_ECHO"
```

The compiler flags are `-march=rv32imc_zicsr -mabi=ilp32 -Os -std=c99
-ffreestanding -fno-builtin … -Wall -Wextra -Werror`.

### In QEMU

Inside `nix-shell` (Espressif's QEMU fork comes from
`tools/ember/nix/qemu-esp32c3.nix`):

```
tools/ember/qemu-test.sh                 # build all images, run all tests
tools/ember/qemu-test.sh corpus --verbose
tools/ember/qemu-run.sh .lake/build/esp32c3/hello.bin --timeout 3
tools/ember/qemu-run.sh .lake/build/esp32c3/stack.bin --dir /tmp/e --gdb --log
```

[`tools/ember/qemu-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-test.sh) emits the
programs with `ember-emit … --profile rv32`, builds every image, then
runs the tests of [`tools/ember/esp32.py`](https://github.com/Verilean/ember/blob/main/tools/ember/esp32.py):
`boot`, `trap`, `hello`, `echo`, `slip`, `corpus`, `tick`, then
generated sessions, and the HTTP, crypto and HTTPS sessions on their
images. [`tools/ember/qemu-run.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-run.sh) runs
one image: UART0 and UART1 on unix sockets in `--dir`, `--gdb` waits on
`:1234`, `--icount` makes virtual time a function of executed
instructions.

The stack images differ only in build flags (from the runtime's README
and `qemu-test.sh`):

| Image | Flags | Use |
|---|---|---|
| `stack` | — | 500 ms tick from SYSTIMER, full trace |
| `stack-test` | `EMBER_TICK_HOST=1` | ticks on request, for fixture replay |
| `stack-icount` | + `EMBER_ICOUNT=1` | instruction counter in the idle line |
| `stack-quiet` | `EMBER_TRACE=0` | what a board runs, and what the size gate measures |
| `stack-http`, `stack-https`, `stack-https-ctl`, … | | the servers of chapters [6](06-http-app.md)–[9](09-control.md) |

A fixture is replayed by sending a step's `rx` bytes on UART0 (or `t` on
UART1 for a tick); the target answers on UART1 with `tx N` per frame, its
`drop`/`note` lines and an idle line; the driver rebuilds a trace and
`ember-diff` compares it with the fixture.

No run on a real board yet: the README's flashing steps (M4.8) are
untested.

## Z80

The Z80 is the hard target: 64 KB of address space, no multiply or
divide, 32-bit arithmetic as library calls. It is tested on a Lean model
of the machine (`Ember/Z80/Machine.lean`, CPU checked against
`z88dk-ticks`), not on hardware. Two roads lead there.

### With SDCC

[`runtime/z80`](https://github.com/Verilean/ember/blob/main/runtime/z80/README.md):

| File | What |
|---|---|
| `crt0.s` | reset, `IM 1`, clearing of the data area, SDCC's initialisers; the receive interrupt in assembly with its 256-byte ring on a page boundary at `0x8000` |
| `rt.c` | the Ember effects on the ACIA and the debug port; the main loop: drain the ring, run the program, `ei; halt` when idle |
| `mmio.c` | `mmio.read32/write32` for programs that use them |
| `echo.c` | byte echo without Ember code |
| `harness.c` | runs one of several programs on inputs from the model's harness ports |
| `Makefile` | `make -f runtime/z80/Makefile NAME=stack PROG=net.c [DEFS=…] [MMIO=1]` → `.ihx`, `.map`, `.noi` |

The machine is the RC2014 layout with its 68B50 serial module: ROM
`0x0000`–`0x7FFF`, RAM `0x8000`–`0xFFFF`, the ACIA at `0x80`/`0x81`, the
debug port at `0xC0`. Every compile uses
(`runtime/z80/Makefile`):

```make
ALLOCS := --max-allocs-per-node 10000
CFLAGS := -mz80 --std-c99 --opt-code-size $(ALLOCS) --Werror \
          -I$(HERE)../common $(DEFS)
```

Two cautions from the README: SDCC's warnings 110 and 126 ("unreachable
code") are errors, because SDCC 4.6.0 gives them when it has deleted
live code; and `--max-allocs-per-node 10000` is validated for SDCC 4.6.0
#16555 only — with 30000 and 100000 that version miscompiles the C
without checks. On another SDCC, run `tools/ember/z80-test.sh` with
larger counts before trusting it. The size build adds
`-DEMBER_TRACE=0 -DEMBER_TRAP_TERSE -DEMBER_NO_NAMES`.

### Ember's own back end

[`Ember/Z80`](https://github.com/Verilean/ember/blob/main/Ember/Z80/README.md) compiles Ember to a Z80 image
without a C compiler:

```
Ember (checked) ──IR.lower──▶ IR ──Codegen.genProg──▶ Asm items ──Asm.assemble──▶ bytes
                               │          ▲                 ▲
                         IRInterp.run   Frame.layout    Runtime.select
                        (its semantics) (+ validate)   (the routines used)
```

| File | |
|---|---|
| `IR.lean` | the IR and `Lang → IR`; every variable has a fixed place; an index check is part of the address it guards; `dropChecks` drops a check a comparison on the path already made |
| `IRInterp.lean` | the IR's semantics, executable |
| `Frame.lean` | static frames overlaid along the call graph, and `validate`, the independent check of a layout |
| `Asm.lean` | instructions as data, the encoder, a two-pass assembler |
| `Runtime.lean` | the routines generated code calls (wide arithmetic, multiply, divide, shifts, the index check), the test harness, a board's runtime |
| `Codegen.lean` | IR → Z80, and the image |

Because Ember has no recursion, frames are static: a local is an absolute
address and the stack holds return addresses only. Division by zero and
over-wide shifts give 0 inside the runtime routines, so the generated
code needs no guard.

The tool is `ember-z80` ([`Ember/Tools/Z80.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Z80.lean)):

```
ember-z80 own-build net|sliploop|trapnote [--trace 0|1|2] [--out DIR]    image, listing, symbols
ember-z80 own-size net|sliploop [--trace 0|1|2]      bytes per function
```

(`own-build` also accepts `http`.) `own-build net --out DIR` writes
`DIR/net-own.ihx`, `.lst` (the listing, with the IR between the
instructions) and `.noi`; `--plain` builds without the passes on the
assembly — the image the proofs of M7 speak of (`net-own-plain.ihx`).
`own-size` also prints a static bound on the stack and fails if it
exceeds the room above the static RAM.

### Z80 tests

[`tools/ember/z80-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/z80-test.sh) (in
`lake test` inside `nix-shell`) builds the SDCC images (`stack`,
`stack-dropped`, `sliploop`, `echo`, `stack-http`, `trapnote`) and the
own back end's, then runs on the model: the CPU against `z88dk-ticks`,
byte echo, SLIP loopback, the corpus and generated sessions with the
target trace compared to the Spec's, random programs through SDCC
(`ember-z80 fuzz`) and through the own back end (`rt-check`, `ir-fuzz`,
`own-fuzz`), the HTTP sessions, and the stack bounds.

## The size gate

[`tools/ember/size-report.py`](https://github.com/Verilean/ember/blob/main/tools/ember/size-report.py) builds
the stack for each target, measures it, and compares with the committed
[`bench/ember-size.baseline`](https://github.com/Verilean/ember/blob/main/bench/ember-size.baseline):

```
tools/ember/size-report.py            report, compare with the baseline
tools/ember/size-report.py --update   re-record bench/ember-size.baseline
```

- **host64**: `gcc -Os -c` of `Tests/Ember/golden/net.host64.c`, sizes
  from `nm -S`;
- **z80** (SDCC, no trace) and **z80own** (own back end): ROM and RAM
  (without the stack), the deepest stack seen on the corpus, and T-states
  per ICMP echo on the Z80 model (`ember-z80 ping`); for the own back end
  also the static bound on the stack (`stack_bound`);
- **esp32c3**: the bare-metal image without tracing, code, read-only
  data and RAM (the 4 KB stack included), and instructions per ICMP echo
  in QEMU with `-icount`;
- the same for `net.dropped.*.c` (rows `*.dropped.*`), and for the HTTP,
  HTTPS and HTTPS-with-control servers.

Each metric must stay within ±3 % of the baseline, in either direction
(`TOL = 0.03`); outside that the script exits 1. A metric whose tool is
missing is reported as "not measured here". So a change in cost is a
reviewed diff of the baseline file. `tools/ember/ci.sh` runs it after
`lake test`.

Some rows of the baseline as committed:

| Metric | Value |
|---|---|
| `host64.code` | 5449 |
| `host64.dropped.code` | 5147 |
| `esp32c3.code` | 7076 |
| `esp32c3.ram` | 5028 |
| `esp32c3.ping_instructions` | 16892 |
| `z80.code` (SDCC) | 7574 |
| `z80.dropped.code` | 6848 |
| `z80.ping_tstates` | 188460 |
| `z80.dropped.ping_tstates` | 179694 |
| `z80own.code` (own back end) | 6011 |
| `z80own.stack` (deepest on the corpus) | 16 |
| `z80own.stack_bound` (static bound) | 24 |
| `z80.stack` (SDCC, deepest on the corpus) | 177 |
| `esp32c3.http.code` | 9840 |
| `esp32c3.https.code` | 34076 |
| `esp32c3.https-ctl.code` | 47604 |
| `esp32c3.https-ctl.ram` | 30848 |

Read off it: the echo stack is about 7 KB of code on the ESP32-C3 and on
the Z80, well under the plan's ESP32-C3 budget of 16 KB code and 8 KB
RAM; dropping the proved-unnecessary bounds checks saves 726 bytes on
the Z80 (−9.6 %) and 4.7 % of T-states per ping; the own back end's code
is smaller than SDCC's, and its deepest stack on the corpus is 16 bytes
(statically bounded by 24) against SDCC's 177. A
ping on the ESP32-C3 costs 16 892 instructions with the checks and
16 964 without — no gain in cycles there. (The READMEs of the runtimes
and of `Ember/Z80` carry earlier measurements; the baseline file is the
current one.)
