# Ember.Z80 — the Z80: a model, and a back end without a C compiler

Two things live here (plan M4z.0, M6).

**The model** — what Z80 code is tested on, in place of an emulator:

| File | |
|---|---|
| `Cpu.lean` | the CPU: every documented instruction and the undocumented ones compilers use, all flags, `R`, interrupt modes, T-states.  `step` is a total function of the state |
| `Check.lean` | random instruction streams against `z88dk-ticks`, every register after every instruction (`ember-z80 check`) |
| `Machine.lean` | the machine around the CPU: ROM/RAM, a 68B50 ACIA with its timing and RTS, debug and tick ports; and the test-harness ports (an input oracle, an event recorder) |
| `Target.lean` | running fixtures and harness programs on it, as traces |

**The back end** — Ember to a Z80 image:

```
Ember (checked) ──IR.lower──▶ IR ──Codegen.genProg──▶ Asm items ──Asm.assemble──▶ bytes
                               │          ▲                 ▲
                         IRInterp.run   Frame.layout    Runtime.select
                        (its semantics) (+ validate)   (the routines used)
```

| File | |
|---|---|
| `IR.lean` | the intermediate representation and the translation into it.  Sizes are explicit; every variable has a fixed place (a global, or an offset in its function's frame); an index check is part of the address it guards.  Also: checks a comparison already made are dropped (`dropChecks`), dead code is swept (`cleanup`), calls can be replaced by bodies (`inlineCalls`, off by default) |
| `IRInterp.lean` | the IR's semantics, executable, on 64 KB of bytes laid out as the frames say |
| `Frame.lean` | static frames overlaid along the call graph, and `validate`, the independent check of a layout |
| `Asm.lean` | instructions as data, the encoder (it rejects operand combinations the Z80 does not have), a two-pass assembler, `jp` → `jr` where near, and a parser for the text the runtime is written in |
| `Runtime.lean` | the routines generated code calls (wide arithmetic, multiply, divide, shifts, the index check), the test harness, and the runtime of a board: start-up, receive interrupt with ring and RTS, ACIA, trace on the debug port |
| `RtCheck.lean` | every routine against its specification, on the model |
| `Codegen.lean` | IR → Z80, and the image: code, runtime, literal pool, constants in ROM, initial values, RAM layout |

## How the generated code works

* One byte is computed in `A`, two in `HL`; four and eight bytes in a
  memory accumulator (`rt_acc`) through routines that take the other
  operand's address in `HL`.  Wide constants are in a literal pool.
* No register allocator.  The generator tracks which operands `A`,
  `HL` and the accumulator currently hold, across forward joins too, and
  skips a load when the value is at hand.  A first pass notes which
  temporaries and locals are ever read *from memory*; the second pass
  stores only those.
* Frames are static (Ember has no recursion): a local is an absolute
  address.  The stack holds return addresses only — 14 bytes at most for
  the whole stack over the corpus.
* The last one- or two-byte parameter is passed in `A`/`HL`; results
  come back in `A`, `HL` or the accumulator.
* Division and remainder by zero give 0 and shifts by the width or more
  give 0 in the routines themselves, so the Ember semantics needs no
  guard in the generated code.

## Numbers (the stack, no trace; `tools/ember/size-report.py`)

| | code + constants | RAM (variables + stack) | T-states per ping |
|---|---|---|---|
| SDCC 4.6.0 `--opt-code-size` | 7 481 B | 887 + 179 B | 184 850 |
| own back end | 5 859 B | 1 051 + 14 B | 183 136 |

A ping is mostly the wire (86 bytes each way, 640 T-states a byte), so
the T-states say little about code quality: `ember-z80 profile` gives
the split by function.

## Tests

`tools/ember/z80-test.sh` (in `lake test`): `asm-check`, `rt-check`,
`ir-fuzz`, `own-fuzz`, the corpus and generated sessions on the image of
`own-build net`.  `Tests/Ember/Z80Tests.lean` adds the examples and the
programs whose index checks must not be dropped.

Not done: any run on hardware; the proofs of M7 (the IR interpreter and
`validate` are written to be their starting point).
