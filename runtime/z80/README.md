# Ember on the Z80 (SDCC)

The runtime of the Z80 build (plan M4z): what is not Ember and not SDCC's
library.  It is tested on the Lean model of the machine
(`Ember/Z80/Machine.lean`), not yet on hardware (M4z.5).

| File | What |
|---|---|
| `crt0.s` | reset, `IM 1`, clearing of the data area, SDCC's initialisers; the receive interrupt in assembly (about 285 T-states per byte) with its 256-byte ring on a page boundary at `0x8000` |
| `rt.c` | the Ember effects (`ember_rt.h`) on the ACIA and the debug port; the main loop: drain the ring, run the program, `ei; halt` when there is nothing to do |
| `mmio.c` | `mmio.read32/write32` for programs that use them (the stack does not) |
| `echo.c` | byte echo without Ember code: the interrupt and ring test |
| `harness.c` | runs one of several programs on inputs given by the model's harness ports (the examples and the random programs of `ember-z80 fuzz`) |
| `Makefile` | `make -f runtime/z80/Makefile NAME=stack PROG=net.c [DEFS=…] [MMIO=1]` → `.ihx`, `.map`, `.noi` |

## The machine

| | |
|---|---|
| ROM | `0x0000`–`0x7FFF`, code from `0x0100` (`0x0038` is the interrupt) |
| RAM | `0x8000`–`0xFFFF`; the ring first, the stack down from the top |
| `0x80`/`0x81` | 68B50 ACIA, control/status and data: receive interrupt, `RTS` as flow control (raised when the ring holds 224 bytes, dropped at 128) |
| `0xC0` | debug output: the §3.1 trace, as text |
| `0xC1` | reading it acknowledges a pending tick |

This is the RC2014 layout with its 68B50 serial module; the debug and
tick ports are the model's and need a counterpart on a board (a second
serial port, a timer interrupt).

## Build options

* `-DEMBER_TRACE=0|1|2` — no trace, `tx N` only, every event (default);
* `-DEMBER_TRAP_TERSE` — a trap prints no message (saves the strings);
* `-DEMBER_NO_NAMES` — the tables of drop and note names are left out (for `EMBER_TRACE` < 2).

The size build is `-DEMBER_TRACE=0 -DEMBER_TRAP_TERSE -DEMBER_NO_NAMES`
(`tools/ember/size-report.py`).

SDCC's warnings are errors, including 110 and 126 ("unreachable code"):
SDCC 4.6.0 gives them when it has deleted live code (see the decision log
of `docs/Ember-plan.md`), and the stack draws none.

Every compile passes `--max-allocs-per-node 10000` (SDCC's default is
3000): the Makefile, `ember-z80`'s harness images (`sdccFlags`) and the
compile check of `lake test`.  This is validated for **SDCC 4.6.0
#16555** only (`shell.nix` does not pin nixpkgs: check `sdcc
--version`), by the tests below on the C with its bounds checks and on
the C without them (M5.9).  With 30000 and 100000 that version
miscompiles the C without checks (the payload of a TCP segment is
zeroed): the setting is not a free knob.  On any other SDCC, run
`tools/ember/z80-test.sh` with larger counts (`SESSIONS`, `FUZZ`) before
keeping it.

## Tests

`tools/ember/z80-test.sh` (part of `lake test` inside `nix-shell`):
the CPU model against `z88dk-ticks`, byte echo (10 000 bytes at line
rate), SLIP loopback, the corpus and generated sessions with the target
trace compared to the Spec's, and random programs.  `ember-z80 run
IMAGE FIXTURE --itrace FILE` writes an instruction trace with symbols.
