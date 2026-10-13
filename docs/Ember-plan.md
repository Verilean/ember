# Ember — implementation plan

This is the working plan for Ember.  The *why* and the architecture are in
[`Ember-design.md`](Ember-design.md); this document is the *how*: what is
built in which order, how each step is tested, how a failure is located,
and when a milestone counts as done.

Status (2026-10-11): M0 done (design).  **M1, M2 and M3 done on the host;
M4 done in QEMU (not on a board); M4z done on a Lean model of the machine
(not on hardware); M5.1–M5.8 done (the stack in Ember, SLIP build, is proved against the Spec: function by function, per received byte and per tick, per call of `main`, and from the initial state for any input — it never traps and transmits and drops what `Spec.step` does, input by input.  Outside the theorems: the `while` of the driver `Sem.run`, the printing of the trace, the Ethernet build.  The proof of the tick found a defect — a tick that sent in the middle of a received frame destroyed that frame — which is fixed: such a tick now waits for the end of the frame.  M5.7: a semantics for the emitted C, against which the emitted code is run; it found an evaluation-order defect in the emitter, fixed.  M5.8: the emitted C is proved to do what the Ember semantics does — expressions, statements, calls, programs — for programs without by-reference parameters, which the stack is; so the C of the SLIP build, under the C semantics, transmits and drops what the Spec does); M6 done — the own Z80 back end
compiles the stack without a C compiler, smaller than SDCC's build and as
fast** (see "Progress" below).
The stack in Ember also has its Ethernet/ARP/DHCP link layer now (what
M4w needs on the host side).
To do: the board and hardware steps (M4.8, M4z.5), Wi-Fi on a board (M4w:
the ESP-IDF component), the Sparkle SoC (M4s), the rest of the P2/P3
proofs (by-reference parameters in M5.8, M5.9) and the rest of the
proof of the back end (M7.3 `IR → Z80`; M7.1, M7.2 and M7.4 are done).

**Targets: the Z80 and the ESP32.**  The ESP32 variant is the
**ESP32-C3** (RISC-V, rv32imc): it keeps the RISC-V path that CompCert
supports, Espressif's QEMU emulates it, and it has Wi-Fi.  The classic
ESP32 (Xtensa) is reachable through the same C with Espressif's gcc, but
has no CompCert back end and is not the primary target.  See §7.

Progress (2026-10-11)

| Step | State | Where / notes |
|---|---|---|
| M1.0 | done | `Ember/Trace`, `Ember/Util`, `ember-diff`, `ember-pcap` (checked with `tshark`); corpus with a provenance README per directory |
| M1.1–M1.6 | done | `Ember/Spec`; ICMP and UDP replies byte-equal to Linux's (recorded on a TUN device; IP identification masked) |
| M1.7–M1.9 | done | one connection, passive open, uIP-style regeneration, RTO back-off; RFC 9293 scenarios hand-written *with expectations* (`Tests/Ember/Scenarios.lean`); out of scope listed in `corpus/tcp/UNSUPPORTED.md` |
| M1.10 | done | `ember-host`; corpus through the binary = in process |
| M1.11 | done | Ethernet II + ARP; fixtures from Linux on a **TAP** device (not a veth pair: same frames, one namespace) |
| M1.12 | done | DHCP client, against dnsmasq; needs `mtu=576` on Ethernet (see decision log) |
| M1 exit | met | corpus passes; 10 000 generated sessions per protocol (×3: as generated, mutated, re-chunked) without panic and with every frame accounted for; ping and TCP echo from Linux through `ember-host` (user-namespace variant recorded; `slattach` variant documented) |
| M2.1–M2.6 | done | `Ember/Lang`, `Ember/C`; surface syntax `ember def/global/const/struct` |
| M2.7–M2.8 | done | host harness; `ember-fuzz` (random programs, shrinker, planted bug found and shrunk to 5 statements) |
| M2.9 | done | checksum, SLIP decoder, SPSC ring, CRC-32, and one program using every construct |
| M2 exit | met | 10 000 random programs: interpreter = C at −O0 and −O2 under UBSan/ASan; warning-free with gcc `-Wall -Wextra -Wconversion -Werror -pedantic` and SDCC `--Werror` (two optimiser notes disabled, see decision log) |
| M3.1–M3.7 | done | `Ember/Net` (layout in `Ember/Net/README.md`); `ember-lockstep` |
| M3 exit | met | corpus and 10 000 generated sessions per protocol: Spec = Ember interpreter = host C, lockstep states equal; size baseline committed (`bench/ember-size.baseline`) |
| M4.0–M4.2 | done | Espressif's QEMU packaged for nix (`tools/ember/nix/qemu-esp32c3.nix`); `runtime/esp32c3` (start-up, vectored traps, linker script, both UARTs); `tools/ember/qemu-run.sh` |
| M4.3–M4.4 | done | UART0 receive interrupt → ring, pause/resume when full; 10 000 bytes echoed; SLIP loopback through the Ember SLIP code (`Ember/Net/Loop.lean`) |
| M4.5–M4.6 | done | `tools/ember/esp32.py` replays fixtures over QEMU's UART sockets: the whole SLIP corpus and generated sessions, target trace = Spec trace; SYSTIMER tick (ticks on the host's request during replay, see decision log) |
| M4.7 | done | 7.0 KB code, 0.8 KB constants, 5.0 KB RAM (4 KB of it the stack); 16 634 instructions per ping (QEMU `-icount`), in the baseline |
| M4.8 | **not done** | needs a board; the image is the one QEMU loads, untested on silicon |
| M4 exit | met in QEMU | `tools/ember/qemu-test.sh` (in `lake test`); board run open |
| M4w (host part) | done | `Ember/Net/Eth.lean`: Ethernet frames, ARP (cache of 4), DHCP client, in Ember; IP, ICMP and TCP are the SLIP build's functions unchanged.  The 20 Ethernet fixtures (Linux-recorded ARP, ping, TCP echo, DHCP against dnsmasq) and 1 000 generated Ethernet and 1 000 DHCP sessions: Spec = interpreter (states compared after every input) = host C.  A planted bug (cache replacement modulo 3) is caught by 104 of 500 sessions |
| M4w.0–M4w.4 | **not done** | ESP-IDF, the raw-frame component and a board: nothing of it exists |
| M4z.0 | done | `z88dk-ticks` cannot raise interrupts from host-driven input, so the machine is the Lean model (`Ember/Z80/Machine.lean`: 68B50 ACIA, debug and tick ports) around the CPU model of M6.1 |
| M4z.1 | done | examples and fuzz regressions: interpreter = SDCC's code on the model (`Tests/Ember/Z80Tests.lean`); random programs with `ember-z80 fuzz` |
| M4z.2 | done | `runtime/z80`: `crt0.s` with the receive interrupt in assembly (a C one was too slow for line rate), RTS flow control; 10 000 bytes echoed with no overrun |
| M4z.3 | done | whole SLIP corpus and generated sessions on the model: target trace = Spec trace |
| M4z.4 | done, RAM target missed by 42 B | **7.5 KB code** (no trace), 184 850 T-states per ping (46 ms at 4 MHz), in the baseline.  RAM: 887 B of variables, within 1 KB — but the stack reaches 179 B over the corpus (`ember-z80 stack`), **1 066 B in all**.  (An earlier version of this line counted the variables only.) |
| M4z.5 | **not done** | needs hardware; the debug and tick ports of the model need a counterpart on a board |
| M5.1–M5.3 | done | `Ember/Proof` (checksum algebra and RFC 1624, SLIP and header round trips, TCP invariants over `Spec.step`); no `sorry`, no `native_decide`, standard axioms only; statements and their hypotheses in `Ember/Proof/README.md` |
| M5.4 | done | `Ember/Lang/Sem.lean`: the semantics as total functions (fuel for loops and calls), tested equal to the interpreter on random programs, the examples and every build of the stack on the corpus; `Ember/Proof/Symex.lean`: symbolic execution by one equation per statement form, calls through the callee's theorem; `checked_fn%` inserts a function's checked AST as a term |
| M5.5 | done | functions of the stack refine the Spec's (`Ember/Proof/Refine*.lean`): checksums (`add16`, `verifies`, `csum_update`, `pseudo`, `csum` — the loop by induction), field access (`get16/32`, `set16/32`), SLIP (`slip_store` = `Slip.Dec.store`, `slip_send` transmits `Slip.encode`), `ip_send` transmits `Spec.Ipv4.packet`, `icmp_input` = `Icmp.reply` + `sendIp`, `udp_input` = `Udp.parse` + echo with `Udp.emit`, `ip_input` = `Ipv4.validate` + the dispatch of `Spec.ipInput` (with the loop that skips IP options).  Drop reasons and reply bytes are the Spec's.  TCP: the *raw layer* is done — each of the 18 functions of `Ember/Net/Tcp.lean` (three of them with loops) is proved to compute a Lean function on one state value, `tcp_emit` sends `Spec.Tcp.emit`, and under the size hypotheses no TCP function traps (`RefineTcp*.lean`).  The *second layer* is done too (`TcpSim.lean`, `TcpSimParse.lean`): under a relation between the two control blocks (`TcbRel`: machine integers and a fixed echo buffer against naturals and a `ByteArray`) those Lean functions are the Spec's — `tcp_input` is `Tcp.parse` then `Tcp.input` (`tcp_input_sim`), `tcp_tick` is `Tcp.tick` (`tcp_tick_sim`, under `Tcp.Inv` and counters below 255): same transmissions, same drops, related states again.  The two layers are joined (`tcp_input_refines`, `tcp_tick_refines`): the calls, run by the Ember semantics from a state that agrees with the Spec's, do not trap and end in a state that agrees again.  **Not done** (M5.6): TCP inside `ip_input`/`slip_rx`; the Spec's `tcb` and note lines are not compared; the counter bound the tick theorem assumes |
| M5.6 | done | per input item, TCP included (`TcpRx.lean`, `NetStep.lean`): an invariant `NetInv` between the stack's globals and the Spec's stack state (SLIP decoder, TCP control block, counters); **one received byte** through `slip_rx` keeps it and adds the Spec's transmissions and drops (`slip_rx_step`, from `frame_refines`: a frame through `ip_input` is a frame through `Spec.ipInput`, every protocol); **one tick between frames** likewise (`tick_step`).  Also the whole SLIP loopback program (`loop_main_refines`, `loop_initial`, `loop_safe`).  **A defect found by the proof, fixed:** a tick that sent while a frame was half received overwrote the shared packet buffer and the frame was lost; now a tick in the middle of a frame waits for its end, in the stack and in the Spec (`Spec.tickArrives`; a second tick gives the frame up), with fixtures `corpus/timer/midframe-tick-*` and a `-midtick` variant of the generated lockstep sessions (cost: about 60–90 bytes of code, 1 byte of RAM, +1.6 % per ping).  **`main` and its repetition** (`TcpBound.lean`, `Main.lean`, `Driver.lean`): the tick counters are bounded in every reachable state (`reach_bnd`); one call of `main` is one input item of the Spec — nothing, a tick as `Spec.tickArrives` treats it, a byte as `Spec.byteInput` does (`main_step`; so `tcp_tick` is only called between frames); the first call boots into the invariant (`boot_call`, `boot_inv`); `Spec.input` is its items (`input_items`); any number of calls from the initial state does not trap, and once the input is read the stack's transmissions and drops are those of `Spec.step`, input by input, and its state agrees with `Spec.reach` (`main_run_all`).  For this the per-byte body of `Spec.input` got names (`slipByte`, `byteInput`) and `Prog.framed` became structurally recursive.  **Outside the theorems:** the `while` loop of `Sem.run` (core's `partial` loop) and how it prints the trace; that the checker's output is the program the theorems are about (`#guard`s); the Ethernet build |
| M5.7 | done | `Ember/C/Sem.lean`: a semantics for the C subset the emitter produces — total functions in the style of `Lang.Sem` (expressions by structural recursion, statements by fuel), unsigned integers with widths, the profile's `int` width, by-reference arguments as pointers to storage (aliasing modelled), `ember_*` as the effects on the same `World`.  A program has a meaning only where C gives one that does not depend on a signed type: an operation that C's promotions would do in signed `int`, a shift by the width or more, a division by zero, an index out of range, and `l = f()` when `l` names different storage before and after the call are all `undef`.  Test (`lake test`): the emitted C of 1 000 random programs, the examples and regressions, and the stack on the 114 fixtures, for the three profiles, runs under it to the trace of `Lang.Sem`, never `undef`; a planted emitter bug (dropped cast) is noticed.  **A defect found, fixed:** `a[i] = f();` with an index that needs no check (`u8` into ≥ 256 elements) and a callee that changes `i` — C leaves the order open; the call's result now goes through a temporary (`regress_call_changes_index`).  For M5.8 the emitter is now made of total functions (no `partial`; `closedVal` is `Sem.evalE`), with byte-identical output |
| M5.8 | done, without by-reference parameters | `Ember/Proof/C*.lean`, `LangFrame.lean` — **the emitted C does what `Lang.Sem` does**, proved through the emitter itself against `Ember.C.Sem`.  Expressions (`expr_ok`, `place_ok`): the hoisted statements run and the C expression has the value of `evalE`, or they end in `ember_trap` exactly when `evalE` has no value; every operator with its guards, folds, casts and the SDCC helpers.  Statements (`stmt_ok`, `block_ok`): every construct — declarations, assignments, `if`, both loops, `break`, `return`, the nine effects, calls, the destination of a result — ends as `Lang.Sem.execS` ends, in related states, or traps when it traps.  Functions (`fn_sim`), programs (`compile_unit`, `init_rel`, `iter_sim`): the entry function called again and again from the initial state.  A checker for what the theorems assume of a program, proved right (`progOkB_sound`), accepts every build of the stack for the three profiles.  **With M5.6 (`stack_c`): the C emitted for the SLIP build, run under the C semantics from its initial state, never traps, is never undefined, and transmits and drops what the Spec does**, for any input.  For any profile with `int` of 16 bits or more.  Emitter changes for the proof, output byte-identical: `assignResult` compiles the destination again after the call's temporary; `compileFn`/`compile` are made of named functions.  **Not covered:** by-reference parameters (`Lang.Sem` copies in and out, C passes a pointer — needs the no-aliasing rules as a theorem; the stack has none, the checker rejects them); the C semantics is a definition and the printer is trusted (gcc/SDCC agreement is tested, not proved) |
| M5.9 | **not done** | |
| M6.1 | done | `Ember/Z80/Cpu.lean`: every documented instruction and the undocumented ones SDCC and z88dk use, flags with X/Y, `R`, IM 0–2, T-states; 1 000 000 random instructions equal to `z88dk-ticks` register for register (`ember-z80 check`) |
| M6.2 | done | `Ember/Z80/Asm.lean`: instructions as data, encoder that rejects operand combinations the Z80 does not have, two-pass assembler with labels; the 1 748 forms it accepts assemble to the same bytes with `z88dk-z80asm` (`ember-z80 asm-check`) |
| M6.3 | done | `Ember/Z80/IR.lean` (three-address, explicit sizes, static storage, checks in the address) and its interpreter `IRInterp.lean`; 5 000 random programs and the corpus: Ember interpreter = IR interpreter (`ember-z80 ir-fuzz`, `ir-replay`) |
| M6.4 | done | `Ember/Z80/Frame.lean`: frames overlaid along the call graph; `validate` checks every layout used (no frame overlaps the frame of a function it can reach, nor a global) — the IR interpreter and the image builder both refuse a layout that fails it |
| M6.5 | done | `Ember/Z80/Codegen.lean`: 8 bits in `A`, 16 in `HL`, 32/64 in a memory accumulator; registers tracked across forward joins; temporaries and locals that are always at hand never touch memory.  20 000 random programs: interpreter = generated code on the model (`ember-z80 own-fuzz`); a planted bug (8-bit `sub` as `add`) is found and shrunk to 3 statements |
| M6.6 | done | `Ember/Z80/Runtime.lean`: the routines in assembly, each against its specification on the model (`ember-z80 rt-check`): every operand pair for 8 bits, edge and random values for 16/32/64 — 279 551 cases |
| M6.7 | done | the stack by the own back end with a board runtime in assembly (`Runtime.board`): corpus and generated sessions, target trace = Spec trace.  Against SDCC (both without trace): **code 5 859 B vs 7 481 B (−22 %), ping 183 136 vs 184 850 T-states (−0.9 %), RAM with the stack 1 065 B vs 1 066 B** (static 1 051 + 14 of stack, against 887 + 179) |
| M7 (begun) | M7.1, M7.2, M7.4 done; M7.3 **in progress** | **groundwork:** `Ember/Z80/IRSem.lean` — the IR's semantics as total functions (recursion on fuel; finished, trapped, out of fuel or malformed), which is to M7 what `Lang.Sem` and `C.Sem` are to M5; run against the IR interpreter in `lake test` (the examples, 2 000 random programs, the stack on the fixtures: same traces).  The lowering `IR.lower` is made of total functions now (`place`/`expr`/`exprTo` by well-founded recursion, statements structurally, `cleanup` with a bound; only `inlineCalls`, off by default, is still `partial`), with identical IR for every build of the stack, the examples and 400 random programs.  **M7.2** (`Ember/Proof/Z80Frame.lean`): the frame validator is right — `validate_sound`: a layout it accepts keeps every function's frame inside the RAM given, apart from every global and from the frame of every function reachable through calls (`Reach`, the transitive closure), and no function reaches itself; the validator is now a pure function (`valid`) that also checks that the reachable set it computed is closed, so the bound on its rounds is not trusted.  **M7.1** (`Ember/Proof/IR*.lean`): `Lang → IR` — expressions, conditions, statements, calls, effects, functions (`fn_sim`), the program as lowered with its initial memory (`iter_sim`, `init_rel`), and the passes `cleanup` and `dropChecks` (`tidy_ref`), so for the program `IR.lower` returns: if the calls of the entry function end in `Lang.Sem` they end in `IR.Sem` with the same world, and a trap is a trap (`lower_iter`, `lower_trap`); with M5.6, **the IR of the SLIP build never traps and transmits and drops what the Spec does** (`stack_ir`).  Assumptions are checked, not trusted: `progOkB` (typing, no by-reference parameters) and `irOkB` (the layout, by the frame validator; the slots `dropChecks` reasons about; initial values) accept every build of the stack (`#guard`).  The proofs found a defect in the lowering (`&&`/`||` skipped an operand that traps: an element at a constant, non-literal index out of range), fixed with a regression test.  Outside M7.1: by-reference parameters, `inlineCalls`.  **M7.4** (`Ember/Z80/AsmSem.lean`, `Ember/Proof/Z80Encode.lean`, `Z80Asm.lean`): what an instruction does, by its mnemonic and operands (`Asm.exec`), and `step_encode` — the CPU model stepping on the bytes `Asm.encode` gives does exactly that (whole state), for every form without `IX`/`IY`; `assemble_ok` — the assembler puts every item's encoding at its address and resolves labels to the addresses of their items (the assembler is two recursive passes now, same images; that sizes do not change between the passes is checked by the second).  **M7.3, in progress** (`Ember/Proof/Z80Run.lean` … `Z80FnGen.lean`): the setting — an instruction of an assembled image runs as `Asm.exec` says (`step_item`), a relation `Rel` between CPU and IR states (shared bytes, slots of temporaries, what the register tracker claims, the stack as the function found it, nothing written outside the function's footprint), a wp calculus for the generator, and the CPU in a machine (`ZCtx.W`, its bus and what I/O does to it; `wrel`: the machine stands for the IR's world) — and, through the generator itself, **every instruction the stack's IR has**: `mov`, `bin` (every operation), `not`, `neg`, `ext`, shifts by a constant, `cmp`, `br`, `jmp`, labels, `ret`, `trap`, `call`, on one and two bytes in `A` and `HL` and on four bytes in the runtime's accumulator (`loadAcc_ok`, `storeAcc_ok`, the literal pool); **addresses** (`genAddr_ok`: static root, index of one or two bytes checked in line or by `rt_bound`, scaled; a failed check gets to `rt_trap`) with `lea`, `load`, `store`; and **effects** (`out.byte`, `out.end`, `drop`, `note`, `input.next`, `ring.pop`), gathered in one statement (`ins_ok`: for whatever `IR.Sem.step` says the instruction does, the code does it — instructions without effects are proved to do no I/O, whatever the bus would answer, and lifted to the machine); then **functions**: the generator's states along a body (`genBody_ok`), `exec_ok` — from any instruction of a body with the states agreeing, the code returns as the IR's `exec` does with the machine standing for the world it leaves, or reaches `rt_trap` when that traps — by induction on the fuel with the functions called, `fn_ok`/`genFn_ok` for a whole function from its entry, and `prog_ok` — in an image that holds the items `genProg` gives, every function does what `IR.Sem.callF` does (`genProg` is a recursion now; same images).  Registers across jumps are not proved but checked: the generator records what it held at every jump and what it assumed after every label, and `jumpsOk` compares the two for every function generated (translation validation; same images).  The runtime's routines are taken with specifications (`RtOK`: arithmetic and shifts, `rt_bound`, the accumulator routines, the routines of the effects).  For the proofs the generator's early returns and loops became conditionals and recursion (same images), and an index of the IR carries the bound it is known to be below (`Index.bound`), kept when `dropChecks` drops the check.  The instruction theorems cover all 1073 instructions of the SLIP build's IR, all 79 of the loopback program, and 1559 of the 1562 of the Ethernet builds (a `load` and a `store` of four bytes through an address, and `input.frame`, are left).  **What the theorems assume of the layout is decided** (`Z80Plan`, `Z80Check`): a `Plan` gives the shared bytes, the bytes a function may write and the slots it uses as data; `okB`/`fnStaticB` decide `ZCtx.OK`/`FnStatic` of it (`plan_ok`, `fnStaticB_sound`), for each function in the environment its second pass ran in (`progEnvs`).  A review found the assumptions contradictory as first stated (a slot read from a register only was asked to be a shared byte, a store left out asked it not to be) — `Rd` now asks for shared bytes only where the generator may read memory, which the generator checks in its second pass.  Two changes to the generator followed (tests and size gate pass): **the temporaries have an area of their own** (+9 bytes of RAM in the SLIP build), and **a store to a byte another function's frame shares is not left out** (+91 bytes of code); with them the plans of the SLIP build and of the loopback program pass (`#guard`).  What is taken of the runtime is taken where the image calls it (`Uses`).  **The loopback image** (`Z80Loop`, `Z80LoopImage`): for the image without the passes on the assembly (`build (passes := false)`, `ember-z80 --plain`; SLIP build 7159 bytes against 6856) the kernel computes the environments, the checks, the assembly and the symbols, and `loop_image_ok` says every function of the image does what the IR's does, given `RtOK` and a machine quiet without I/O — the IR and the items are terms written out, tied to `IR.lower` and `build` by `#guard`.  **Routines of the runtime, proved from their items** (`Z80Rt`): `rt_bound`, and the effects of the test harness (`rt_input`, `rt_out_byte`, `rt_out_end`, `rt_drop`) against a machine that is the world behind the harness's ports; with them `loopH_ok` — the loopback image for the harness, nothing taken of the runtime, `rtK = 0` — and, with start-up (`boot_ok`: the stack pointer, the RAM cleared by `ldir`) and the harness's loop (`loop_iter`) proved from their items, composed with `loop_safe`/`loop_main_refines` (M5.5) and `lower_iter` (M7.1), and carried to the machine the tests run (`step_sim`: `Ember.Z80.Machine.step` in harness mode is a step of the proofs' machine): `loopH_halts` — **the loopback image, loaded and run as the tests do, processes all its input and stops, the machine standing for the world the Ember semantics has**.  On the way: the harness asks the machine whether a call moved the position in the input (port `0xD9`) instead of counting in a byte of its own, as the interpreter's driver does (so the loop is left only with the input used up, and the routines write no memory); the layout `build` returns has the constants at their addresses in ROM (M7.1 takes every global to be in the layout); `Machine.normalize` and `Cpu.load` are recursions.  A static bound on the stack of an image (`Ember.Z80.StackBound`, an analysis: 24 bytes for the SLIP build, 16 seen) is printed by `own-size`, checked against the room above the static RAM, and in the size gate.  **More routines proved from their items** (`Z80Note`, `Z80Wide`, `Z80Bytes`): the harness's `rt_note` (its value goes out with it: port `0xDA`), `rt_ld32`, `rt_st32`, `rt_acc_a`, `rt_acc_hl`, `rt_or32`, `rt_add32`, `rt_sub32`, `rt_shr8`, `rt_cmp32` — the routines on four bytes at `HL` under `HLApart` (those bytes apart from the accumulator and the stack; without it the specifications taken before were not true of the routines), which the generated code is shown to meet.  **The image of the stack (SLIP build) for the harness** (`Z80StackH`): the literal pool is checked on the assembled bytes (`litB`); the kernel cannot run the generator over the 1073 instructions in one evaluation (over 40 GB), so it runs it a function and a pass at a time (`Z80ImageParts`; at most about 11 GB); `stackH_ok` — every function of the image does what the IR's does, nothing taken of the runtime (`rtK = 2`).  **Not done:** for the stack's image, start-up (the copy of the initial values), the harness's loop and the composition with `stack_ir` and the Spec (it is not run from reset in a theorem); the runtime routines the stack does not call (multiplication, division, …) and the board's — which need interrupts in the machine of the proofs; the passes on the assembly (`peephole`, `sweep`, …: nothing is proved of the images as built by default); variable shifts, `not`/`neg` and `zero` on wide values, eight-byte values (not in the stack) |

Findings worth knowing before M4:

* the Ember stack was SLIP-only after M3; Ethernet, ARP and DHCP are now
  in Ember too (`Ember/Net/Eth.lean`, the host part of M4w) — what M4w
  still needs is the ESP-IDF component and a board;
* host64 build: 5.4 KB code, 935 B RAM; SDCC Z80 build: 7.5 KB code,
  887 B of variables plus 179 B of stack — the code within the M4z
  target, the RAM 42 B over 1 KB once the stack is counted.  (An earlier version of this
  document said 24.8 KB, "3× over": the size script added up the
  linker map's area lines, which the map repeats on every page.  The
  script now reads the linker's `l__AREA` symbols.)
* **SDCC 4.6.0 miscompiles** (found by `ember-z80 fuzz`, each confirmed
  outside the Lean model): 64-bit shifts by a variable and 64-bit
  comparisons; a guarded division moved above its guard, where SDCC's
  own division routine does not return for a zero divisor; and a dead
  local in an `if` in a loop deleting the rest of the function.  It also
  stops with an internal error on some valid programs.  What Ember does
  about each is in the decision log; the stack uses no `u64` and draws
  none of SDCC's "unreachable code" warnings.  This is the case for M6;
* the emitter had to learn more than §2.3 of the design says: GCC's
  `-Wtype-limits`/`-Wtautological-compare` see through casts and
  constants, so closed subexpressions are folded *by the interpreter* and
  comparison operands, divisors and shift amounts are hoisted into typed
  temporaries (`Ember/C/Compile.lean`).

Contents

1. Principles
2. Repository layout
3. Debugging infrastructure (built first, used everywhere)
4. Milestones M1–M7, step by step
5. Continuous integration and gates
6. Risk register
7. Decision log
8. Glossary

---

## 1. Principles

These apply to every milestone.  They are what keeps the project
debuggable when four implementations of the same stack exist side by
side.

1. **One trace format for everything.**  The reference stack, the DSL
   interpreter, the host-compiled C, the QEMU run and the Z80 run all
   write the same line-oriented event trace (§3.1).  A disagreement is
   always "first differing line of two traces", never "it doesn't work".
2. **Deterministic by construction.**  No randomness and no wall clock in
   the stack: the TCP initial sequence number comes from a counter, time
   is an input (`tick`).  The same input stream gives the same trace,
   byte for byte, on every run and every implementation.
3. **Every layer is runnable on the host.**  Each milestone produces
   something that runs under `lake exe` or as a host binary before it
   runs on a target.  A target only ever adds the runtime (start-up,
   drivers, interrupts) — never new protocol logic.
4. **Differential testing before proofs.**  Each new implementation is
   checked against the previous one on the full corpus and on generated
   inputs before any theorem about it is attempted.  Proofs then confirm
   what the tests already showed, and a failing proof attempt is not the
   first sign of a bug.
5. **Small steps with a test each.**  Every step below ends with a test
   that fails before the step and passes after it.  A step without a test
   is not done.
6. **Errors carry locations.**  Interpreter errors name the function and
   the statement path; emitted C carries `#line` directives back to the
   Ember source; target crashes print the trap cause and PC on a debug
   UART.
7. **Gates, not dashboards.**  Code size, RAM, instructions and cycles
   per exchange are measured by scripts that fail CI outside a tolerance
   against a committed baseline, as `bench/gate` does for the CSim JIT.

## 2. Repository layout

Ember lives in its own repository (decided 2026-10-09; the layout below is
unchanged, rooted at the repository instead of inside Sparkle), with the
same Lean toolchain as Sparkle (v4.32.1) and LSpec at Sparkle's pin.
Nothing in `Ember/` depends on Sparkle; the RV32-SoC milestone (M4s) will
*use* its simulator.

```
Ember/
  Util/           Bytes, hex dump, pretty printers, pcap writer
  Trace/          event type, text format, parser, diff
  Spec/           reference stack (ordinary Lean)
    Checksum.lean  Slip.lean  Ipv4.lean  Icmp.lean  Udp.lean
    Tcp/  (Header.lean  Tcb.lean  Input.lean  Output.lean  Timer.lean)
    Stack.lean     -- step : State → Input → State × List Output
  Lang/           the DSL
    Syntax.lean    -- AST
    Types.lean     -- type checker
    Eval.lean      -- interpreter (= semantics), traces
    Surface.lean   -- `ember def` syntax → AST
    Profile.lean   -- target profiles (host64, rv32, sdcc-z80)
  C/              C subset
    Ast.lean  Sem.lean  Compile.lean (Lang → C AST)  Print.lean
  Net/            the stack written in Ember (M3)
  Z80/            own back end (M6): Isa.lean  Model.lean  Ir.lean  Isel.lean  Asm.lean
  Proof/          P1, P2, P3, back-end proofs
runtime/
  common/         ring buffer, trace output (C)
  esp32c3/        bare-metal: start.S  link.ld  uart.c  intr.c  systimer.c  Makefile   (M4)
  esp32c3-idf/    ESP-IDF component: Wi-Fi raw frames ↔ ring, Ember task          (M4w)
  rv32-sparkle/   (M4s) Sparkle RV32 SoC variant
  z80/            crt0.s  acia.c / sio.c  Makefile (SDCC)  (M4z)
Tests/Ember/
  corpus/         *.trace fixtures with provenance (README per directory)
  Drivers/        *Main.lean wrappers for lean_exe
  host/           host C harness
tools/ember/      ember-diff, ember-pcap, qemu-run.sh, z80-run.sh, gates
```

Conventions, following the repo's `CLAUDE.md`: test modules are
namespaced and called from `Tests/AllTests.lean`; each `lean_exe` has a
one-line driver under `Tests/Ember/Drivers/`; heavy jobs run under
`systemd-run --user --scope -p MemoryMax=…`.

## 3. Debugging infrastructure

Built in M1.0 and extended as layers arrive.  It is listed first because
every later step depends on it.

### 3.1 The trace format

One event per line, ASCII, stable, diffable:

```
# ember-trace v1  impl=spec  build=<git sha>  profile=host64
0      rx   c0 45 00 00 54 ...           # raw link bytes (SLIP-framed)
0      pkt  rx ipv4 10.0.0.2>10.0.0.1 icmp echo-req id=1 seq=1 len=84
0      tcb  state=LISTEN snd.nxt=0 rcv.nxt=0
0      pkt  tx ipv4 10.0.0.1>10.0.0.2 icmp echo-rep id=1 seq=1 len=84
0      tx   c0 45 00 00 54 ...
17     tick
17     drop reason=bad-ip-checksum
```

- `rx` / `tx` / `tick` are the **observable** events: the only ones the
  comparison between implementations requires.
- `pkt`, `tcb`, `drop`, `note` are **diagnostic** events: emitted by
  implementations that can (the Lean ones always; C builds with
  `EMBER_TRACE=2`); ignored by the observable comparison, used to explain
  a divergence.
- The first column is the step number (number of inputs consumed), not
  time, so traces from fast and slow implementations line up.

Every implementation has a writer; Lean has a parser.  `pkt` lines are
produced by one decoder (`Ember.Util.Pretty`) so that two
implementations never disagree about how a packet is *printed*.

### 3.2 `ember-diff`

`lake exe ember-diff A.trace B.trace [--observable] [--context 5]`

- aligns the two traces on observable events, reports the first
  difference with context, and decodes both differing packets field by
  field (`ipv4.ttl: 64 vs 63`, `tcp.ack: 1001 vs 1000`);
- exit status 0/1 so it can sit in tests and CI;
- `--first-only` for scripts, `--all` for a full report.

### 3.3 Packet corpus and pcap

- `Tests/Ember/corpus/<protocol>/<name>.trace`: input-and-expected-output
  traces.  Each directory has a `README.md` with the provenance of every
  fixture (RFC example, hand-written, recorded from Linux — with the
  command line used).
- `lake exe ember-pcap X.trace > X.pcap` writes the `rx`/`tx` packets as
  a pcap (link type `RAW`/IPv4), so any trace can be opened in Wireshark.
- Recording fixtures from Linux without root: `unshare -rn` gives a user
  network namespace with its own loopback where `ping`, `nc` and
  `tcpdump` work; a small script converts the capture to a trace.  The
  recorded responses of Linux are the expected outputs for the cases
  where Ember is meant to behave the same way.

### 3.4 Generators and shrinking

- `Ember.Spec.Gen`: random but valid packet streams (pings with random
  sizes and ids, UDP payloads, TCP sessions with random segmentation), and
  mutations (flip a bit, truncate, bad checksum, out-of-window sequence
  number).  Used against every implementation.
- `Ember.Lang.Gen`: random well-typed Ember programs for the emitter
  (M2.6).
- A shrinker for both: on a disagreement, remove packets/bytes or
  statements while the disagreement persists, and write the minimal case
  to `Tests/Ember/regress/` as a new fixture.

### 3.5 Target-side debugging

- **Debug channel**: targets have a second output channel (UART1 or the
  USB-Serial-JTAG port on the ESP32-C3, a reserved port on the Z80) where
  the runtime writes the trace in the §3.1 format.  The main link carries
  only network traffic.
- **Trap handler** prints `cause`, `pc`, `mtval` and the last trace step
  number on the debug UART, then halts.
- **`#line` directives** in the emitted C point at the Ember source in
  the Lean file, so gdb and compiler errors show Ember lines.
- **QEMU** (Espressif's fork, `-M esp32c3`): `tools/ember/qemu-run.sh
  --gdb` starts with `-s -S`; `--log` adds `-d int,guest_errors,unimp`.
- **ESP32-C3 board**: built-in USB-Serial-JTAG gives OpenOCD + gdb without
  extra hardware; the panic handler's register dump goes to the debug
  channel.
- **Z80**: the emulator writes a symbol-annotated instruction trace on
  request (`--trace-from <step>`), and a `.map` file maps addresses back
  to Ember functions.
- **Size reports**: `tools/ember/size-report` prints code and RAM per
  Ember function from the linker map, so a size regression points at a
  function.

## 4. Milestones

Each milestone lists: **Goal**, **Steps** (each with its test),
**Debug aids** it adds, **Exit criteria**, and **Risks / fallback**.
Effort is given as S (≤ 1 day), M (a few days), L (a week or more).

---

### M0 — Design  ✅

`docs/Ember-design.md`.  Decisions in §7.

---

### M1 — Reference stack in Lean (`Ember.Spec`)

**Goal.** A complete, deterministic TCP/IP stack as ordinary Lean
functions, with the step interface
`step : State → Input → State × List Output`, replaying the corpus.

**Steps**

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M1.0 | Debug infrastructure: `Bytes`, hex dump, trace type + writer + parser, `ember-diff`, `ember-pcap`, corpus directory layout | round trip: parse ∘ print = id on hand-written traces; `ember-diff` on two traces differing in one byte reports exactly that byte; pcap of a fixture opens in `tshark` with the expected fields | M |
| M1.1 | Internet checksum: full, incremental (RFC 1624), pseudo-header | RFC 1071 / 1624 examples; random check incremental = recompute | S |
| M1.2 | SLIP encode/decode (RFC 1055) as a byte-at-a-time state machine | escapes (`END`, `ESC`) in payload, empty frames, back-to-back `END`, oversize frame dropped; decode ∘ encode = id on random payloads | S |
| M1.3 | IPv4 parse/emit, validation (version, IHL, length, checksum, TTL), drop reasons | header fixtures; mutated headers each produce the right `drop reason=` | M |
| M1.4 | ICMP echo reply, built in place (swap addresses, type 8→0, incremental checksum) | `ping -c 3 -s {0,56,200}` fixtures recorded from Linux; reply bytes equal Linux's | S |
| M1.5 | UDP: parse/emit, checksum (including the zero-checksum case), echo on a fixed port | `nc -u` fixtures; random payloads | S |
| M1.6 | TCP header parse/emit, MSS option emitted on SYN-ACK, other options skipped | header fixtures incl. options of every length | S |
| M1.7 | TCP state machine, one connection, passive open: LISTEN → SYN-RCVD → ESTABLISHED → CLOSE-WAIT → LAST-ACK → CLOSED; RST handling; in-order data only; out-of-order segments dropped with ACK | `nc` session fixtures (connect, send, echo, close from either side); RFC 793 / 9293 scenario traces written by hand: simultaneous FIN, RST in each state, segment outside the window, duplicate SYN | L |
| M1.8 | Echo application (TCP port 7, UDP port 7) on the uIP model: no retransmission buffer, the application is asked to regenerate unacknowledged data | session with a dropped segment: the retransmission carries the same bytes | M |
| M1.9 | Timers from `tick`: retransmission with exponential back-off, TIME-WAIT, give-up after N retries | hand-written traces with ticks; back-off schedule checked against a table | M |
| M1.10 | `lake exe ember-host`: the Spec stack on stdin/stdout as SLIP, so the host harness of later milestones can talk to it directly | the corpus replayed through the binary equals the in-process replay | S |
| M1.11 | Ethernet II framing and ARP (request/reply, a small cache) as a second link layer, selected at build time — needed for Wi-Fi on the ESP32 (M4w) | ARP fixtures recorded from Linux on a veth pair in a user namespace; the IP corpus replayed over Ethernet framing gives the same IP-level trace | M |
| M1.12 | DHCP client (DISCOVER/OFFER/REQUEST/ACK, lease renewal by `tick`) — optional; a static address is the default | fixtures against `dnsmasq` in a user namespace | M |

**Debug aids added:** `pkt`/`tcb`/`drop` diagnostic events from every
Spec function; `Ember.Spec.Gen` packet generator with mutations; the
shrinker.

**Exit criteria**

- all corpus fixtures pass (`lake test` includes them);
- 10 000 generated sessions per protocol run without a Lean panic, and
  every mutated packet is either answered correctly or dropped with a
  reason;
- the Spec stack answers `ping` and TCP echo from Linux through
  `ember-host` attached to a pty (manual demo, documented in
  `Tests/Ember/README.md`).

**Risks / fallback**

- *TCP corner cases eat time.*  Keep scope to the table in the design
  (one connection, passive open, in-order).  Anything else is answered
  with RST or dropped, with a `drop reason=unsupported-…` event, and
  listed in `Tests/Ember/corpus/tcp/UNSUPPORTED.md`.
- *Recording fixtures without root fails on the CI runner.*  Fixtures are
  recorded once and committed; CI only replays.

---

### M2 — The DSL core (`Ember.Lang`, `Ember.C`)

**Goal.** Write small programs in Ember, run them in the interpreter,
emit C, and get the same trace from the C compiled on the host — with no
undefined behaviour.

**Steps**

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M2.1 | AST (`Syntax.lean`): types, expressions, statements, functions, programs; source spans on every node | constructing the AST of each example by hand compiles | S |
| M2.2 | Type checker: widths, array bounds of literals, `ref` non-aliasing at call sites, acyclic call graph, every path returns | one positive and one negative `#guard_msgs` test per rule, error messages naming the span | M |
| M2.3 | Interpreter (`Eval.lean`): total arithmetic (shift ≥ width = 0, div by 0 = 0), bounds errors with the statement path, fuel, effect trace (`mmio`, `ring`, `trace`) | unit programs per construct; an out-of-bounds read reports `fn=… at stmt 3.2.1` | M |
| M2.4 | Surface syntax `ember def …` (`Surface.lean`): `do`-style body → AST, spans from the Lean source | each example written in surface syntax elaborates to the hand-built AST of M2.1 (`#guard` equality) | M |
| M2.5 | Target profiles (`Profile.lean`): `host64`, `rv32`, `sdccZ80` — `int` width, preferred operation width | unit tests of the width-selection function, incl. `u8 * u8` on `sdccZ80` | S |
| M2.6 | C AST + emitter (`Compile.lean`, `Print.lean`): temporaries, explicit casts per profile, guarded shifts/divisions, bounds checks calling `ember_trap()`, `#line` directives | golden C for each example; compiles with `gcc -std=c99 -Wall -Wextra -Wconversion -Werror` | M |
| M2.7 | Host differential harness: a C `main` that feeds the same input oracle and writes the trace; `ember-diff` against the interpreter | every example: interpreter trace = C trace | M |
| M2.8 | Random program generator + shrinker for the emitter (`Lang.Gen`) | 10 000 random programs: interpreter = C under `-fsanitize=undefined,address`, at `-O0` and `-O2`; a planted emitter bug (dropped cast) is found and shrunk to ≤ 5 statements | M |
| M2.9 | Example library: checksum, SLIP decoder, SPSC ring buffer, CRC32 | each is also compared with the corresponding `Ember.Spec` function on random inputs | S |

**Debug aids added:** span-carrying interpreter errors; `#line` in C;
`EMBER_TRACE` levels in the C runtime; the program shrinker.

**Exit criteria**

- the M2.8 fuzz run is clean at both optimisation levels with UBSan and
  ASan, and is part of CI at a reduced count (1 000);
- emitted C is warning-free with `-Wall -Wextra -Wconversion` on gcc and
  on SDCC (`--std-c99`, `--Werror`);
- each Lang construct has an interpreter test, an emitter golden test and
  a differential test (the repo's "every construct: sim + synth"
  rule, transposed).

**Risks / fallback**

- *Surface syntax takes longer than expected.*  M3 can start on the
  hand-built AST with small helper functions; the syntax is sugar.
- *SDCC rejects some C99 construct.*  The emitter avoids them from the
  start (no compound literals, no VLAs, no designated initialisers); the
  SDCC compile is in the M2 exit criteria so this is found early.

---

### M3 — The stack in Ember (`Ember.Net`)

**Goal.** The M1 stack rewritten in Ember, agreeing with `Ember.Spec`
on every input, as interpreter and as host C.

**Steps** — one protocol at a time, each compared function by function
before the whole stack is compared:

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M3.1 | Data layout: one packet buffer (`[u8; MTU]`), TCB as a record, constants | `sizeof` report; layout doc in `Ember/Net/README.md` | S |
| M3.2 | Checksum, SLIP (from M2.9) wired into the buffer layout | function-level: = Spec on 10 000 random inputs | S |
| M3.3 | IPv4 + ICMP in place | function-level vs Spec; corpus `icmp/` through the Ember step | M |
| M3.4 | UDP echo | corpus `udp/` | S |
| M3.5 | TCP input/output, state machine, application callback | corpus `tcp/`; generated sessions | L |
| M3.6 | Timers | corpus with ticks | M |
| M3.7 | Main loop: `poll` (drain the ring, run `step`, emit SLIP) in Ember | whole corpus: Ember interpreter = Spec; host C = interpreter | M |

**Debug aids added:** a *lockstep* mode in the host harness: Spec and
Ember interpreter consume the same input and their **states** are
compared after every step (TCB fields, buffer contents), so a divergence
is caught where it starts, not where it becomes visible on the wire.

**Exit criteria**

- whole corpus and 10 000 generated sessions: Spec = interpreter = host
  C (observable traces), lockstep states equal;
- host C size report: code and RAM per function, first baseline
  committed.

**Risks / fallback**

- *Ember is too restrictive for some protocol logic.*  Extend the
  language (with M2-style tests for the new construct) rather than work
  around it in the runtime; the runtime stays protocol-free.

---

### M4 — ESP32-C3, bare metal, SLIP over the UART

**Goal.** The emitted stack answers ping, UDP echo and TCP echo on an
ESP32-C3, first in Espressif's QEMU and then on a board, over SLIP on
UART0, receiving through an interrupt.  No ESP-IDF, no FreeRTOS: a
bare-metal runtime, so that what runs is only Ember and a small runtime.

**Steps** — the hardware path first, then the protocols, so that a
failure is always in the newest piece:

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M4.0 | **Spike / toolchain**: Espressif's QEMU (`qemu-system-riscv32 -M esp32c3`, from ESP-IDF's tools or built from source; packaged for nix if missing), `riscv32-none-elf-gcc` with `-march=rv32imc`, `esptool.py` for images; `tools/ember/qemu-run.sh` with UART0 on a socket, UART1 to a file, `--gdb`, `--log` | a bare `while(1)` image boots in QEMU and exits cleanly on timeout | M |
| M4.1 | `start.S`, `link.ld` (IRAM/DRAM layout of the C3), watchdogs disabled, trap handler printing `mcause`/`mepc`/`mtval` on UART1 | an illegal instruction prints `cause=2 pc=…` | M |
| M4.2 | UART0/UART1 polled TX, "hello" on UART1 | host sees the string | S |
| M4.3 | Interrupt matrix + UART0 RX FIFO interrupt → SPSC ring; main loop echoes bytes | host sends 10 000 random bytes, gets them back in order; interrupt count printed | M |
| M4.4 | SLIP loopback through the Ember SLIP code | random frames echoed | S |
| M4.5 | Ember stack linked in; host test driver replays the corpus over the socket | `icmp/` corpus: target trace = Spec trace | M |
| M4.6 | UDP, then TCP, then the SYSTIMER as `tick` | `udp/`, `tcp/` corpora and timer traces | M |
| M4.7 | Size and instruction gate: code/RAM from the map, instructions per ping via QEMU `-icount` | gate script with committed baseline | S |
| M4.8 | Board (ESP32-C3 DevKit): same image flashed with `esptool.py`; SLIP over the USB-UART bridge; `slattach` on a Linux host, `ping` and `nc` | documented steps and a recorded session; corpus replay on the board through the serial port | S |

**Debug aids added:** the target trace on UART1 (same §3.1 format), so
`ember-diff target.trace spec.trace` works directly; QEMU interrupt log;
OpenOCD/gdb over USB-Serial-JTAG on the board.

**Exit criteria**

- `tools/ember/qemu-test.sh` replays the whole corpus in QEMU and all
  traces match (CI job);
- the same on the board, run manually and recorded;
- code < 16 KB, RAM < 8 KB, recorded in the gate baseline.

**Risks / fallback**

- *Espressif's QEMU unavailable or incomplete for the peripherals used.*
  Fallback for CI: generic QEMU `virt` riscv32 with a 16550 UART (the
  runtime's driver layer is the only difference); the board stays the
  reference for the C3 peripherals.
- *Interrupt bugs (lost bytes, ring races).*  M4.3 isolates them before
  any protocol code runs; the ring has its own stress test (bursts at
  line rate, random gaps).
- *Timing differs between QEMU and the board.*  The protocol layer never
  depends on timing other than `tick`.

---

### M4w — ESP32-C3 on Wi-Fi

**Goal.** The same stack on Wi-Fi: ping and TCP echo from a laptop on
the same network.  This is the demonstration that matters to most people,
and it is the one place where Ember runs next to code it does not
control: Espressif's Wi-Fi driver is a binary blob that needs ESP-IDF.

**Design.** An ESP-IDF component registers a raw receive callback on the
station interface (`esp_wifi_internal_reg_rxcb`) and transmits with
`esp_wifi_internal_tx`, bypassing lwIP entirely.  Received Ethernet frames
go into the same SPSC ring as the UART bytes did; an Ember task runs the
main loop.  The Ember stack uses the Ethernet + ARP link layer of M1.11
and a static address (DHCP from M1.12 if available).

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M4w.0 | Spike: ESP-IDF (via a nix flake for ESP development or ESP-IDF's installer), a station connecting to an AP, raw RX callback counting frames, lwIP disabled for the interface | frame counter on the debug channel | M |
| M4w.1 | Frame ring and TX path; frames mirrored to the debug channel as pcap-over-serial (`ember-pcap --serial`) | Wireshark shows the frames the board sees | M |
| M4w.2 | Ember stack with Ethernet + ARP; static IP | `arping` and `ping` from a laptop | M |
| M4w.3 | UDP and TCP echo | `nc` sessions; traces recorded and compared with the Spec replaying the same frames | M |
| M4w.4 | DHCP (if M1.12 is done) | address obtained from the AP | S |

**Exit criteria:** ping, UDP echo and TCP echo from a laptop over Wi-Fi;
the board's trace of a session, replayed through `Ember.Spec`, gives the
same outputs.

**Risks / fallback**

- *The raw RX/TX hooks are internal ESP-IDF APIs and change between
  versions.*  Pin the ESP-IDF version; keep the component small; the
  UART path (M4) does not depend on it.
- *The trusted base grows* (Wi-Fi blob, ESP-IDF, FreeRTOS).  Stated
  plainly: proofs (M5) cover the stack, not the radio.  The bare-metal
  UART build (M4) is the one with the small trusted base.
- *Classic ESP32 (Xtensa) wanted for its Ethernet MAC.*  Same component
  with `xtensa-esp32-elf-gcc`; no CompCert claim on that path.

---

### M4s — Sparkle's own RV32 SoC (optional, after M4)

**Goal.** The M4 code on the Sparkle RV32 SoC under the CSim JIT: own
CPU, own stack (a different runtime layer; the Ember code is the same).

| # | Step | Test | Effort |
|---|---|---|---|
| M4s.1 | Check the SoC's UART: RX interrupt path, interrupt controller; add what is missing (as a Sparkle PR with sim + synth tests per `CLAUDE.md`) | UART RX interrupt test program | M |
| M4s.2 | Runtime variant `runtime/rv32-sparkle/` | M4.3 byte-echo test on the SoC | S |
| M4s.3 | Corpus replay through the JIT-simulated UART | traces = Spec | M |

---

### M4z — Z80 via SDCC

**Goal.** The same exchanges on a Z80, with code ≤ 8 KB and RAM ≤ 1 KB.

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M4z.0 | **Spike**: pick the emulator.  Check whether `z88dk-ticks` can feed input bytes and raise interrupts (IM 1) from a host-driven port.  If not, use the Lean Z80 model started early from M6.1, or an existing emulator library with a scriptable ACIA | a 20-line program receives bytes by interrupt and echoes them in the chosen emulator | S |
| M4z.1 | `sdccZ80` profile end to end: the M2 example library compiled with SDCC, run in the emulator, traces = interpreter | M2 examples | M |
| M4z.2 | `crt0.s`, ACIA (68B50) or SIO driver, IM 1 ISR → ring; debug output port | byte-echo stress test as M4.3 | M |
| M4z.3 | Stack linked; corpus replay | all corpora | M |
| M4z.4 | Footprint work: MTU 296, one buffer, 16-bit checksums; size/cycle gate with `z88dk-ticks` | code ≤ 8 KB, RAM ≤ 1 KB; cycles per ping in the baseline | M |
| M4z.5 | Hardware (RC2014-class): same binary, SLIP to a Linux host | manual demo, recorded session | S |

**Risks / fallback**

- *Code does not fit 8 KB with SDCC.*  The size report points at the
  functions; options in order: narrower arithmetic in the profile,
  restructure the Ember code, and finally M6 (own back end) — which is
  the planned answer anyway.

---

### M5 — Proofs

Proofs follow the tests; each item is small enough to finish on its own.

| # | Statement | Notes | Effort |
|---|---|---|---|
| M5.1 | P1: checksum algebra — incremental update (RFC 1624) equals recomputation; one's-complement sum is order-independent | pure `BitVec 16` / `Nat` lemmas | M |
| M5.2 | P1: SLIP decode ∘ encode = id; IPv4/UDP/TCP header parse ∘ emit = id | structural | M |
| M5.3 | P1: TCP invariants — `snd.una ≤ snd.nxt`, no data delivered outside ESTABLISHED/CLOSE-WAIT, accepted segments lie in the receive window | state-machine induction over `step` | L |
| M5.4 | P2 tooling: a symbolic-execution tactic for `Lang.exec` on straight-line code and bounded loops | measured on the checksum function first | L |
| M5.5 | P2: function-level refinement for checksum, SLIP, IPv4, ICMP, UDP | uses M5.4 | L |
| M5.6 | P2: the main loop as a simulation of `Spec.step` | the TCP part last | L |
| M5.7 | P3: `Ember.C` semantics (the subset the emitter produces) | as built: big-step with fuel, like `Lang.Sem`, so that M5.8 relates two functions of the same shape; C11 §6.3 and §6.5 as the reference for what has no meaning | L |
| M5.8 | P3: `Lang → C AST` forward simulation | per construct, then whole programs | L |
| M5.9 | Bounds-check elimination: the emitter drops a check when a P2 lemma proves the index in range; size/cycle gates record the gain | ties proofs to performance | M |

**Debugging proofs:** every lemma is first checked on the generators
with `#eval` over random inputs (or `decide`/`native_decide` on small
instances) before a proof is attempted — a false statement is found by a
counterexample, not by a stuck proof.

---

### M6 — Own Z80 back end

**Goal.** Ember → Z80 machine code without a C compiler, at least as
small and fast as the SDCC build of M4z.

| # | Step | Test that closes it | Effort |
|---|---|---|---|
| M6.1 | Lean Z80 model of the instruction subset (registers, flags, memory, I/O ports, IM 1 interrupts) | differential against the emulator on random instruction sequences (10 000 sequences of 50 instructions, all registers and flags compared after each instruction) | L |
| M6.2 | Encoder/assembler in Lean (`Asm.lean`), checked against z88dk's assembler | byte-identical output for every instruction form used | M |
| M6.3 | Linear IR (three-address, explicit widths) and `Lang → IR` | IR interpreter = Lang interpreter on the M2 fuzz corpus | M |
| M6.4 | Static frame allocation (overlay along the call graph) | no two live locals share an address — checked by a separate validator on every compiled program | M |
| M6.5 | Instruction selection: 8-bit in `A`, 16-bit in `HL`/`DE`, runtime routines for 32-bit and multiply/divide | Lang interpreter = Lean Z80 model = emulator on the fuzz corpus | L |
| M6.6 | Runtime routines in assembly, each with a Lean specification | exhaustive tests for 8-bit operands, random for 16/32-bit | M |
| M6.7 | Whole stack on the own back end; compare with SDCC | corpus replay; size and cycles vs the M4z baseline | M |

**Debug aids added:** the three-way comparison (interpreter, Lean Z80
model, emulator) with first-divergence reporting at instruction level,
and a listing that interleaves Ember source, IR and Z80 instructions.

---

### M7 — Back-end proof

| # | Statement | Effort |
|---|---|---|
| M7.1 | `Lang → IR` preserves semantics | L |
| M7.2 | Frame allocation is sound (validator proven, translation-validation style) | M |
| M7.3 | `IR → Z80` preserves semantics over the M6.1 model | L |
| M7.4 | Encoder correctness: decode ∘ encode = id on the subset | M |

Result: a chain from `Ember.Spec` to Z80 machine code whose trusted base
is Lean's kernel, the Z80 model, and the hand-written runtime (start-up,
ISR, ring buffer).

## 5. Continuous integration and gates

| Job | Runs | From |
|---|---|---|
| `ember-spec` | corpus replay, 1 000 generated sessions per protocol | M1 |
| `ember-lang` | interpreter tests, golden C, differential with gcc + UBSan/ASan, 1 000 fuzz programs | M2 |
| `ember-net` | whole corpus: Spec = interpreter = host C | M3 |
| `ember-esp32` | corpus on QEMU `-M esp32c3`; size/instruction gate | M4 |
| `ember-z80` | CPU model vs `z88dk-ticks`; corpus on the Z80 model; random programs; size/cycle gate | M4z |
| `ember-proofs` | `lake build Ember.Proof` | M5 |

Gate scripts follow `bench/gate/run.sh`: the measurement is compared
against a committed baseline produced by the same script; outside ±3 %
in either direction fails; `--update` re-records, so every change in
cost is a reviewed diff.

## 6. Risk register

| Risk | Where | Mitigation |
|---|---|---|
| TCP scope creep | M1.7, M3.5 | fixed scope; unsupported cases answered with RST and listed |
| Interrupt and ring races | M4.3, M4z.2 | isolated stress tests before protocol code; SPSC ring with a single writer per index |
| Z80 emulator lacks scriptable I/O/interrupts | M4z.0 | spike first; Lean Z80 model as fallback |
| Espressif QEMU missing or incomplete | M4.0 | generic QEMU `virt` for CI; the board as reference |
| ESP-IDF internal Wi-Fi APIs change | M4w | pinned ESP-IDF; UART path independent of it |
| Trusted base on Wi-Fi includes the radio blob and ESP-IDF | M4w | stated; proofs claim the stack, the bare-metal UART build is the small-TCB configuration |
| SDCC code too large for 8 KB | M4z.4 | size report per function; M6 own back end |
| Surface syntax effort | M2.4 | M3 can start on the AST |
| Proofs slower than code | M5 | proofs never block milestones; each M5 item is independent |
| Divergent behaviour hidden by trace formatting | all | one decoder for `pkt` lines; observable comparison on raw bytes only |

## 7. Decision log

| Date | Decision | Reason |
|---|---|---|
| 2026-10-05 | Name: Ember | embedded + Sparkle |
| 2026-10-05 | `Ember/` inside the Sparkle repo, own `lean_lib` | shared toolchain and simulator |
| 2026-10-05 | QEMU riscv32 first, then Z80 | debuggability first, impact second |
| 2026-10-09 | Targets: **Z80 and ESP32**; the ESP32 variant is the ESP32-C3 (RISC-V) | user's choice of targets; C3 keeps RISC-V (CompCert, one toolchain with the rest of the repo) and is emulated by Espressif's QEMU; classic ESP32 (Xtensa) only via gcc |
| 2026-10-09 | ESP32-C3 bare metal over SLIP first (M4), Wi-Fi through ESP-IDF raw frames second (M4w) | small trusted base and full debuggability first; Wi-Fi needs the vendor blob |
| 2026-10-05 | SLIP over UART | one interrupt source, no NIC driver |
| 2026-10-05 | Deep embedding with an executable semantics | needed for P2/P3; avoids reflection of arbitrary Lean terms |
| 2026-10-05 | Own Z80 back end as M6, C path kept | removes SDCC from the trusted base; C stays the portable back end and the baseline |
| 2026-10-09 | One trace format and first-divergence diffing for all implementations | debuggability across four implementations |
| 2026-10-09 | Ember in its own repository, not inside Sparkle | user's choice; no dependency on Sparkle's libraries anyway |
| 2026-10-09 | Implementation pass 1 = M1–M3 on the host | everything that runs without target hardware or emulators |
| 2026-10-09 | `Input = rx chunk \| tick`; one trace step per input; the SLIP decoder still sees one byte at a time | traces stay readable (a frame per line) without changing the byte-level state machine |
| 2026-10-09 | One tick = 500 ms; RTO 3·2^k ticks capped at 48, 8 retries; TIME-WAIT 20; the echo application closes after 60 idle ticks | small integers on small targets; idle close makes the active-close states reachable from tests |
| 2026-10-09 | DF set on UDP and TCP, not on ICMP echo replies; Ethernet frames not padded to 60 bytes | what Linux does (recorded fixtures); padding is the driver's job |
| 2026-10-09 | MTU 576 for the Ethernet build, 296 for SLIP | dnsmasq's OFFER is 328 bytes; RFC 2131 requires 576 |
| 2026-10-09 | Fixtures from Linux through TUN/TAP devices in a user namespace (`tools/ember/record-linux.py`); Linux-responder fixtures masked on `ipv4.id` | no root, no tcpdump; Linux's IP identification is random |
| 2026-10-09 | Hand-written fixtures are scenarios with stated expectations, not Spec output | a fixture must not be "whatever the Spec printed" |
| 2026-10-09 | Ember evaluates every operand (strict `&&`, `\|\|`, `if-then-else`); the destination of a call is evaluated after the call | one evaluation order for the interpreter and the hoisted C; found by the fuzzer |
| 2026-10-09 | Emitter folds closed subexpressions with the interpreter and hoists comparison operands, divisors and shift amounts into temporaries | GCC's front-end range warnings otherwise fire on legal Ember; found by the fuzzer |
| 2026-10-09 | SDCC warnings 110 and 126 ("conditional flow changed by optimizer", "unreachable code") disabled in the `--Werror` check | they report what SDCC's optimiser proved, not a property of the C |
| 2026-10-11 | …but they are **errors in the Z80 build of the stack** (`runtime/z80/Makefile`) | SDCC 4.6.0 gives them when it deletes live code: `for (t = 0; t < 5; t++) { if (g == 0) { uint8_t x = 1; } } f();` compiles to `ret`.  The stack draws none; random programs draw them almost always (constant conditions), so the fuzzer runs them and counts a divergence of a flagged program apart |
| 2026-10-11 | ESP32-C3 fixture replay requests each tick from the host (a byte on UART1 arms a one-shot SYSTIMER alarm); the shipped image ticks every 500 ms | a fixture says where ticks fall between bytes; a free-running timer cannot reproduce that |
| 2026-10-11 | The Z80 machine for tests is a Lean model (CPU of M6.1 + 68B50 ACIA + debug/tick ports), not `z88dk-ticks` | ticks has no host-driven input with interrupts; the CPU model is checked against ticks instruction by instruction instead |
| 2026-10-11 | Known differences of `z88dk-ticks` from a real Z80, excluded from the comparison: `DD CB` adds 3 to `R`; `LD IXH,IXL` copies the wrong register; `ADC A,H` takes 7 T-states; X/Y flags of `BIT n,(HL)` | found by the differential test; the model follows the documented behaviour |
| 2026-10-11 | On `sdcc-z80`, division and remainder by a non-literal go through emitted helpers `ember_divN`/`ember_modN` | SDCC hoists `d == 0 ? 0 : a / d` out of a loop, above the test, and `__divulong`/`__modulong` loop for ever on `d = 0` |
| 2026-10-11 | `u64` is not tested on `sdcc-z80` (`ember-z80 fuzz --u64` shows why) | SDCC 4.6.0: `1ULL >> n` and `x > 0xC000000000000000ULL` give wrong results; the stack has no `u64` |
| 2026-10-11 | `--nogenconstprop` and `--nolabelopt` not used | the first avoids SDCC's internal errors but costs 5 % code; the second avoids the dead-local bug but brings many more wrong results |
| 2026-10-11 | Z80 size build: `-DEMBER_TRACE=0 -DEMBER_TRAP_TERSE -DEMBER_NO_NAMES` | trap messages and the drop/note name tables are 0.9 KB of strings that a board without a debug port never prints |
| 2026-10-11 | A second input effect, `input.frame`: bytes, ticks, and `0x0200` at the end of each frame; a program uses it or `input.next` | Ethernet has no in-band frame boundary; the byte-stream semantics of `input.next` (and everything tested on it) stays untouched.  Implemented in the interpreter, the IR interpreter and the host harness; no target runtime has it yet |
| 2026-10-11 | The Ethernet build shares the SLIP build's functions by name: a program is a list of functions and globals, and `Eth.progFor` puts `buf : [u8; 576]`, `MTU`, `OUR_MSS` and a *variable* `OUR_IP` in place of the SLIP build's | no change to the SLIP build (its size gates do not move), no duplicated IP/TCP code; only `ip_send` and `udp_input` exist twice |
| 2026-10-11 | Three Ethernet builds: MTU 576 static, MTU 576 with DHCP, MTU 296 static | the fixtures' headers name these; the buffer size is a compile-time constant in Ember |
| 2026-10-11 | Proofs about Ember code use a second, total semantics (`Lang.Sem`: fuel, association lists, copy-in/copy-out for references) rather than the interpreter | the interpreter's loops are `partial`, which the kernel cannot unfold; the two are tested against each other, and the proofs README says that this link is a test, not a theorem |
| 2026-10-11 | The checked AST of a function enters a proof as a literal made at elaboration time (`checked_fn%`), re-checked by `#guard` | the type checker is `partial` too; the alternative — proving about unchecked ASTs — would not be about the program that runs |
| 2026-10-11 | RAM is reported with the deepest stack over the corpus (`z80.stack`, `z80own.stack` in the baseline) | SDCC keeps locals on the stack (179 B), the own back end in static frames (14 B of return addresses): variables alone do not compare |
| 2026-10-11 | Own back end: no register allocator — a fixed register per size and a tracker of what each holds; all storage static | Ember has no recursion, so frames need no stack pointer arithmetic (costly on a Z80), and the tracker removes most loads; simple enough for the proofs of M7 |
| 2026-10-11 | Own back end: an index check is dropped when a comparison on the straight path to it already established it (`IR.dropChecks`) | a static fact, not a proof obligation (M5.9 remains for the checks that need reasoning); `Tests/Ember/LangPrograms.lean` (`Guard`) has the cases where the check must stay |
| 2026-10-11 | Own back end: the last one- or two-byte parameter travels in `A`/`HL`; the others are stored into the callee's frame by the caller | one store in the callee instead of one per call site, and the value is at hand on entry |
| 2026-10-11 | Inlining (`IR.inlineCalls`) is implemented and tested on the IR, but off | with static frames it made the stack larger and no faster: a call costs little here, and a copy loses the tail call |
| 2026-10-11 | The runtime of the own back end is assembly written as Lean data (`Runtime.lean`), assembled by `Asm.lean` | no external assembler or C compiler in the Z80 path; the routines are checked on the model against one-line specifications |
| 2026-10-11 | M5.8 is proved for programs without by-reference parameters; a checker (`progOkB`, proved right) decides whether a program is covered | the stack has no by-reference parameter, and with pointers the relation between the states needs the type checker's no-aliasing rules as theorems (the checker is `partial` code); the C semantics models the pointers, and the differential tests cover the examples that use them |
| 2026-10-11 | M5.8 goes through the emitter itself (`wpc` over its monad), not through a second, proof-friendly translation | a theorem about another function would say nothing about the C that is shipped; the price was making the emitter total and splitting it into small functions, with byte-identical output |

## 8. Glossary

- **Observable event**: `rx`, `tx`, `tick` — what two implementations
  must agree on.
- **Diagnostic event**: `pkt`, `tcb`, `drop`, `note` — explanation only.
- **Lockstep**: two implementations run side by side with their internal
  states compared after every input.
- **Profile**: target description used by the emitter (int width,
  operation widths).
- **P1/P2/P3**: properties of the reference / refinement of the reference
  by the Ember program / semantics preservation of `Lang → C`.
- **Trusted base**: what is assumed, not proven (design §4).
