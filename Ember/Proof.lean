import Ember.Proof.Bytes
import Ember.Proof.Checksum
import Ember.Proof.Icmp
import Ember.Proof.Slip
import Ember.Proof.Headers
import Ember.Proof.Tcp
import Ember.Proof.Stack
import Ember.Proof.Symex
import Ember.Proof.Refine
import Ember.Proof.RefineSlip
import Ember.Proof.RefineIp
import Ember.Proof.RefineIcmp
import Ember.Proof.RefineUdp
import Ember.Proof.RefineIpInput
import Ember.Proof.RefineRx
import Ember.Proof.RefineTcp
import Ember.Proof.RefineTcpSt
import Ember.Proof.RefineTcpOut
import Ember.Proof.RefineTcpIn
import Ember.Proof.RefineTcpParse
import Ember.Proof.RefineTcpTick
import Ember.Proof.TcpSim
import Ember.Proof.TcpSimParse
import Ember.Proof.TcpRx
import Ember.Proof.NetStep
import Ember.Proof.TcpBound
import Ember.Proof.Main
import Ember.Proof.Driver
import Ember.Proof.CSem
import Ember.Proof.CTypes
import Ember.Proof.CArith
import Ember.Proof.CExpr
import Ember.Proof.CFuel
import Ember.Proof.CPlace
import Ember.Proof.LangFrame
import Ember.Proof.CRel
import Ember.Proof.CStmt
import Ember.Proof.CCall
import Ember.Proof.CSim
import Ember.Proof.CVoid
import Ember.Proof.CFn
import Ember.Proof.CProgram
import Ember.Proof.CCheck
import Ember.Proof.CNet
import Ember.Proof.Z80Frame
import Ember.Proof.IRFuel
import Ember.Proof.IRMem
import Ember.Proof.IRTypes
import Ember.Proof.IRRel
import Ember.Proof.IRPlace
import Ember.Proof.IRWp
import Ember.Proof.IRArith
import Ember.Proof.IRExpr
import Ember.Proof.IRJump
import Ember.Proof.IRStmt
import Ember.Proof.IRCall
import Ember.Proof.IRBlock
import Ember.Proof.IRSim
import Ember.Proof.IRProgram
import Ember.Proof.IRCheck
import Ember.Proof.IRInit
import Ember.Proof.IRPass
import Ember.Proof.IRLower
import Ember.Proof.IRNet
import Ember.Proof.Z80Encode
import Ember.Proof.Z80Asm
import Ember.Proof.Z80Run
import Ember.Proof.Z80Wp
import Ember.Proof.Z80Rel
import Ember.Proof.Z80Attr
import Ember.Proof.Z80Fields
import Ember.Proof.Z80Load
import Ember.Proof.Z80Store
import Ember.Proof.Z80Instr
import Ember.Proof.Z80Call
import Ember.Proof.Z80Alu
import Ember.Proof.Z80Mul
import Ember.Proof.Z80Bits
import Ember.Proof.Z80Rep
import Ember.Proof.Z80Bin16
import Ember.Proof.Z80Una
import Ember.Proof.Z80Flags
import Ember.Proof.Z80Cmp
import Ember.Proof.Z80Jump
import Ember.Proof.Z80CmpI
import Ember.Proof.Z80Ctl
import Ember.Proof.Z80Ret
import Ember.Proof.Z80Ext
import Ember.Proof.Z80Addr
import Ember.Proof.Z80After
import Ember.Proof.Z80Mem
import Ember.Proof.Z80Eff
import Ember.Proof.Z80Shift
import Ember.Proof.Z80Acc
import Ember.Proof.Z80AccOps
import Ember.Proof.Z80ExtW
import Ember.Proof.Z80CallFn
import Ember.Proof.Z80Ins
import Ember.Proof.Z80Fn
import Ember.Proof.Z80FnGen
import Ember.Proof.Z80Prog
import Ember.Proof.Z80Shape
import Ember.Proof.Z80Plan
import Ember.Proof.Z80Check
import Ember.Proof.Z80PlanOf
import Ember.Proof.Z80LoopIR
import Ember.Proof.Z80Loop
import Ember.Proof.Z80BoardPlan
import Ember.Proof.Z80LoopItems
import Ember.Proof.Z80LoopImage
import Ember.Proof.Z80Rt
import Ember.Proof.Z80Boot
import Ember.Proof.Z80Note
import Ember.Proof.Z80Wide
import Ember.Proof.Z80Bytes
import Ember.Proof.Z80HarnessW
import Ember.Proof.Z80ImageParts
import Ember.Proof.Z80GenChunks
import Ember.Proof.Z80GenOut
import Ember.Proof.Z80AsmChunks
import Ember.Proof.Z80StackIR
import Ember.Proof.Z80StackHItems
import Ember.Proof.Z80StackHAsm
import Ember.Proof.Z80StackHGen
import Ember.Proof.Z80StackHPlan
import Ember.Proof.Z80StackH
import Ember.Proof.Z80BootInit
import Ember.Proof.Z80HarnessLoop
import Ember.Proof.Z80StackHRun
import Ember.Proof.Z80StackHSpec
import Ember.Proof.Z80StackHMachine
import Ember.Proof.Z80StackHTrace
import Ember.Proof.SemTrapped
import Ember.Proof.Z80SimCheck
import Ember.Proof.TcbCheckpoint
import Ember.Proof.Z80StackHTcb
import Ember.Proof.Z80StackHTcbObs
import Ember.Proof.Z80PassLocal
import Ember.Proof.Z80PassSim
import Ember.Proof.Z80PassStep
import Ember.Proof.Z80PassCtl
import Ember.Proof.Z80PassTaint
import Ember.Proof.Z80PassRun
import Ember.Proof.Z80PassSeg
import Ember.Proof.Z80PassBlock
import Ember.Proof.Z80PassCheck
import Ember.Proof.Z80StackDAsm
import Ember.Proof.Z80World
import Ember.Proof.Z80Image
import Ember.Proof.Z80LoopHItems
import Ember.Proof.Z80LoopH
import Ember.Proof.Z80LoopHSpec
import Ember.Proof.Z80Machine

/-!
# Ember.Proof — proofs (plan M5): about the reference stack (P1), and that Ember code refines it (P2)

* `Checksum`, `Icmp`: the checksum algebra (M5.1);
* `Slip`, `Headers`: decode ∘ encode and parse ∘ emit (M5.2);
* `Tcp`, `Stack`: invariants of the TCP state machine, for `Tcp.input`
  and `Tcp.tick` and by induction over `Spec.step` (M5.3);
* `Symex`: symbolic execution of Ember code over the total semantics
  `Ember.Lang.Sem` (M5.4);
* `Refine`: functions of the stack in Ember compute the Spec's functions
  (M5.5: the checksum functions, 16-bit fields);
* `RefineSlip`: 32-bit fields; the SLIP receiver and transmitter with
  their effects; the SLIP loopback program as a whole — one call of its
  `main` is one step of the Spec's decoder, and it never traps;
* `RefineIp`: `ip_send` transmits the Spec's IPv4 packet;
* `RefineIcmp`: `icmp_input` is the Spec's ICMP echo handling;
* `RefineUdp`: `udp_input` is the Spec's UDP validation and echo;
* `RefineIpInput`: `ip_input` is the Spec's IPv4 validation and dispatch (TCP apart);
* `RefineRx`: `slip_rx`, the stack's receive path per byte, is the Spec's decoder step
  followed by `Spec.ipInput` (TCP apart);
* `RefineTcp`, `RefineTcpSt`, `RefineTcpOut`, `RefineTcpIn`, `RefineTcpParse`, `RefineTcpTick`: TCP, the
  raw layer — every function of `Ember/Net/Tcp.lean` computes a Lean function on one state value
  (`tcpInputW` for a segment, `tickW` for a tick); `tcp_emit` sends `Spec.Tcp.emit`;
* `TcpSim`, `TcpSimParse`: TCP against the Spec — `tcpInputW` is `Spec.Tcp.parse` then `Spec.Tcp.input`,
  `tickW` is `Spec.Tcp.tick`: from states that agree, the same transmissions and drops and states that agree
  again (`tcp_input_sim`, `tcp_tick_sim`); joined with the raw layer into statements about the calls
  (`tcp_input_refines`, `tcp_tick_refines`);
* `TcpRx`: TCP inside `ip_input` — a frame through `ip_input` is a frame through `Spec.ipInput`, every
  protocol (`frame_refines`);
* `NetStep`: one input item, TCP included — a received byte through `slip_rx` (`slip_rx_step`) and a tick
  between frames (`tick_step`) keep the invariant `NetInv` between the stack's globals and the Spec's stack
  state, with the same transmissions and drops;
* `TcpBound`: the tick counters of the Spec's control block stay within their limits;
* `Main`: one call of `main` is one input item of the Spec (`main_step`); boot;
* `Driver`: `main` called again and again from the initial state never traps and transmits and drops
  what `Spec.step` does, input by input (`main_run_all`).

P3, the emitted C (M5.8) — `Ember.C.Sem` is the semantics of the C subset:

* `CSem`, `CFuel`, `CVoid`: facts about that semantics (more variables in scope change nothing; statements
  run as the beginning of a block; more fuel changes nothing; `(void)x;` changes nothing);
* `CTypes`, `CPlace`: values and their types, well-typed expressions, `evalE` yields a value of the type;
  a place as a variable and a path, `update` as a change along the path;
* `CArith`: the operators as functions on natural numbers;
* `CExpr`: **expressions** — what `C.expr` emits for a well-typed scalar expression runs, from related
  states, to the value `Lang.Sem.evalE` gives, or ends in `ember_trap` exactly when `evalE` has no value
  (`expr_ok`, `place_ok`); for every profile;
* `LangFrame`: what a statement of `Lang.Sem` leaves alone (a `for` counter the body does not write);
* `CRel`: the relation statements keep (locals position by position, globals, the world), and
  `Lang.Sem.assign` as `C.Sem.write` (`assign_sim`);
* `CStmt`, `CCall`, `CSim`: **statements** — what `C.stmt` emits does what `Lang.Sem.execS` does, every
  construct: declarations, assignments, `if`, both loops, `break`, `return`, effects, calls and where their
  results go (`stmt_ok`, `block_ok`);
* `CFn`: **functions** — a compiled function called with the values of its arguments (`fn_sim`);
* `CProgram`: **programs** — `C.compile`'s unit, the initial state, the entry function called again and
  again (`compile_unit`, `init_rel`, `iter_sim`);
* `CCheck`: a checker for what these theorems assume of a program, proved right (`progOkB_sound`);
* `CNet`: **the emitted C of the stack transmits and drops what the Spec does** (`stack_c`) — M5.6 and M5.8
  together; the checker accepts every build of the stack, for every profile.

By-reference parameters are outside M5.8 (the stack has none).

The Z80 back end (M7, begun) — `Ember.Z80.IR.Sem` is the semantics of its IR:

* `Z80Frame`: **the frame validator is right** (M7.2) — a layout `IR.validate` accepts keeps every
  function's frame apart from the globals and from the frame of every function it can reach through
  calls (`validate_sound`);
* `IRFuel`, `IRMem`, `IRTypes`, `IRRel`, `IRPlace`, `IRWp`, `IRArith`: the IR's semantics without counting
  fuel, memory, values as bytes, the relation statements keep, and a weakest-precondition calculus for
  the lowering monad;
* `IRExpr`, `IRJump`, `IRStmt`, `IRCall`, `IRBlock`, `IRSim`: **`Lang → IR`** (M7.1) — what the lowering
  emits for an expression, a condition, a statement, a call, a function does what `Lang.Sem` does
  (`expr_ok`, `condJump_ok`, `stmt_ok`, `fn_sim`);
* `IRProgram`, `IRInit`, `IRCheck`: the program as lowered, its initial state, the entry function called
  again and again (`iter_sim`, `init_rel`), and a checker for what is assumed (`progOkB_sound`);
* `IRPass`, `IRLower`: the passes `cleanup` and `dropChecks` keep what a function does (`tidy_ref`), so
  the program `IR.lower` returns does what `Lang.Sem` does (`lower_iter`, `lower_trap`);
* `IRNet`: **the IR of the stack transmits and drops what the Spec does** (`stack_ir`) — M5.6 and M7.1
  together; the checkers accept every build of the stack.

* `Z80Encode`, `Z80Asm`: **the encoder** (M7.4) — the CPU model, stepping on the bytes `Asm.encode`
  gives for an instruction, does what `Asm.exec` says the instruction does (`step_encode`; every form
  without `IX`/`IY`), and `Asm.assemble` puts every item's encoding at its address with the labels
  resolved to the addresses of their items (`assemble_ok`).

* `Z80Run`, `Z80Wp`, `Z80Rel`, `Z80Fields`, `Z80Load`, `Z80Store`, `Z80Instr`: **`IR → Z80`** (M7.3), in
  progress — an instruction of an assembled image as `Asm.exec` (`step_item`); a wp calculus for the
  generator's monad; the relation between a CPU state and an IR state (`Rel`: the shared bytes, the slots
  of the temporaries, what the generator's tracker says the registers hold, the stack and the
  function's footprint); loading an operand into `A` or `HL` and storing them (`loadA_ok`, `loadHL_ok`,
  `storeA_ok`, `storeHL_ok`); `mov`;
* `Z80Call`, `Z80Alu`, `Z80Mul`, `Z80Bits`, `Z80Rep`, `Z80Bin16`, `Z80Una`: calls of the runtime's
  routines (`Routine`, `call_rule`, `RtOK`), and `bin`, `not`, `neg` of one and two bytes;
* `Z80Flags`, `Z80Cmp`, `Z80Jump`, `Z80CmpI`, `Z80Ctl`: flags after a comparison, jumps to labels, `cmp`,
  `br`, `jmp` and labels — what the registers hold across a jump is checked by `Codegen.jumpsOk`
  (`arrive`);
* `Z80Ext`, `Z80Shift`, `Z80Addr`, `Z80Mem`: `ext`, shifts by a constant; an address into `HL` with its
  index check (`genAddr_ok`); `lea`, `load`, `store`;
* `Z80Acc`, `Z80AccOps`, `Z80ExtW`: values of four bytes in the runtime's accumulator — `loadAcc_ok`,
  `storeAcc_ok`, `mov`, `bin`, `cmp`, `br`, `ext`, by routines taken with specifications (`RtW`);
* `Z80Ret`, `Z80CallFn`, `Z80After`, `Z80Eff`, `Z80Ins`: `ret`, `trap`, `call` of a function of the
  program, effects through the runtime's routines (`RtEff`), and every covered instruction in one
  statement (`ins_ok`), in the machine around the CPU (`WSteps`, `ZCtx.wrel`) — every instruction of the
  SLIP build's IR is covered;
* `Z80Fn`, `Z80FnGen`: **a function's code has the outcome of the IR's function** — it returns as
  `IR.Sem.callF` does, the machine standing for the world, or reaches `rt_trap` (`exec_ok`, `fn_ok`, by
  induction on the fuel; `genFn_ok`);
* `Z80Prog`, `Z80Shape`: in an image that holds the items `genProg` gives, every function does what
  `IR.Sem.callF` does (`prog_ok`), given `FnStatic` of each in the environment its second pass ran in
  (`progEnvs`); the part of the assumptions about a body alone is checked on the SLIP build and the
  loopback program (`shapeB_sound`);
* `Z80Plan`, `Z80Check`, `Z80PlanOf`: **what the theorems assume of the layout, decided** — a `Plan`
  gives the shared bytes, the bytes a function may write and the slots it uses as data; `okB` decides
  `ZCtx.OK` of it (`plan_ok`) and `fnStaticB` decides `FnStatic` (`fnStaticB_sound`);
* `Z80BoardPlan`: the plans of the SLIP build and of the loopback program for the board pass (`#guard`);
* `Z80LoopIR`, `Z80Loop`, `Z80LoopItems`, `Z80LoopImage`: **the loopback image** — the IR and the items of
  the image without the passes on the assembly written out; the environments of its functions, the checks
  of its plan, the assembly and the symbols computed by the kernel: every function of the image does what
  the IR's does (`loop_static`, `loop_image_ok`).

* `Z80Rt`, `Z80Image`, `Z80LoopHItems`, `Z80LoopH`: **routines of the runtime** (`rt_bound`, the effects of
  the test harness) proved from their items, and the loopback image for the harness with nothing taken of
  the runtime (`loopH_ok`);
* `Z80Boot`, `Z80World`, `Z80LoopHSpec`, `Z80Machine`: start-up from reset and the harness's loop, from
  their items; the loop is left only with the input used up; composed with the Ember semantics (`loop_safe`,
  `lower_iter`) and carried to the machine the tests run (`Ember.Z80.Machine`, `step_sim`): **the loopback
  image, loaded and run as the tests do, processes all its input and stops with the world the Ember
  semantics has** (`loopH_spec_halt`, `loopH_halts`).

* `Z80Note`, `Z80Wide`, `Z80Bytes`: the harness's `rt_note`, and the routines on the accumulator, `rt_shr8`,
  proved from their items;
* `Z80HarnessW`, `Z80ImageParts`, `Z80GenChunks`, `Z80GenOut`, `Z80AsmChunks`, `Z80StackIR`, `Z80StackHItems`,
  `Z80StackHGen` (and `Z80StackHGen/`), `Z80StackHAsm`, `Z80StackHPlan`, `Z80StackH`: **the image of the stack
  (SLIP build) for the harness** — the literal pool checked, the generator run by the kernel a function at a
  time (a long one a stretch at a time, each stretch by its own items), the assembler a stretch of items at a time: every function does what
  the IR's does, nothing taken of the runtime (`stackH_ok`);
* `Z80BootInit`, `Z80HarnessLoop`, `Z80StackHRun`: the copy of an initial value at start-up, the harness's
  loop for any image, and the image of the stack from reset (`stackH_run`);
* `Z80StackHSpec`, `Z80StackHMachine`: composed with the Ember semantics and the Spec, and carried to the
  machine the tests run: **the image of the stack, loaded and run as the tests do, processes all its input
  and stops, having transmitted and dropped what the Spec does** (`stackH_spec_halt`, `stackH_halts`);
* `Z80StackHTrace`: **the trace `Target.runHarness` prints of it has the transmissions and drops of
  `Spec.run`'s, input by input, and the inputs as its input lines** (`stackH_trace`); **the whole trace
  is the inputs each followed by its events in the world the Ember semantics leaves, notes included, and
  nothing else** (`stackH_trace_lines`); **the harness records no trap** (`stackH_no_trap`; `SemTrapped`:
  the Ember semantics never sets `World.trapped`; `Z80SimCheck`: `Sim` on small machines, `#guard`);
* `TcbCheckpoint`, `Z80StackHTcb`: **between input items the connection record the program holds is the
  Spec's control block after the same items** — in the Ember semantics (`tcb_checkpoint`), in the IR's
  memory (`stackH_tcb_ir`) and in the RAM of the machine the tests run at the head of its loop
  (`stackH_tcb_ram`); `RawTcb.describe` writes of it what the Spec's `tcb` lines write.  The lines
  themselves are not written by the program;
* `Z80StackHTcbObs`: **the observer's lines** (`Ember.Z80.TcbObs`, `ember-z80 tcb-obs`: the record read
  from the RAM at every head of the harness's loop) **are, when it gives lines, one per item, at the
  number of its input, the Spec's control block after it** (`stackH_tcb_obs`: sound given the
  observer's own count check, that it gives lines is not proved; what runs, `scan`, is what the proof
  reads, `obsList`: `run_eq`).  Not the Spec's `tcb` lines: an item can write two, or one that is not
  the state after it;
* `Z80PassLocal`: **the passes on the assembly, begun** — what each rewrites and what its soundness
  needs (a table); the rewrites on `Asm.exec`, from one CPU state: `packHigh`'s (`packHigh_agree`),
  `Asm.relax`'s (`exec_jp_to`, `exec_jr_to`, `exec_jpcc_to`, `exec_jrcc_to`), `retThreading`'s
  (`jp_ret`, `jpcc_ret`), `peephole`'s conditional return (`exec_retcc`, `cond_invert`);
* `Z80PassSim`: two images side by side on the machine of the proofs (`wstep`: the harness's, no
  interrupt, the code in ROM): `packHigh_steps` — four steps of the image without the passes and two
  of one with `packHigh`, from states equal but for `pc`, `R`, the T-states and memory, at the items
  of the rewrite, to such states at the items after it;
* `Z80PassStep`: one ordinary instruction in the two machines (`ord_eqv`): the 75 forms of the stack's
  images that neither jump, call, return nor touch the stack (`Form`), from CPUs equal but for `pc`,
  `R`, the T-states and memory, their memories equal on a range of RAM (`Eqv`), with the same operands
  and bytes read or written in that range (a hypothesis about the addresses), give such CPUs;
* `Z80PassTaint`: an ordinary instruction where `H` or `L` may differ between the two machines (after a
  routine of the runtime read a literal through `HL`, each machine's `HL` points into its own ROM):
  `EqvT`, the relation with those free, kept by an instruction that reads none of them (`ord_eqvT`;
  `h_comm`, `l_comm`: what reads neither does the same with any);
* `Z80PassSeg`: the relation of the two machines (`Sync`: CPUs equal but for `pc`, `R`, the T-states,
  memory and the stack pointer, `H` and `L` free where the relation says; the RAM below the stack
  equal; the stacks holding the same calls, `Stk`: the return addresses of both images, or of `A`
  alone for a call that is a jump in `B`; the devices in the same state), and segments that keep it:
  an ordinary instruction (`seg_ord`), a jump (`seg_jump`), a call (`seg_call`: each pushes its own
  return address, a frame more on the stacks), a return (`seg_ret`: each to its own return point, the
  frame popped; with a condition, both taken or both not), `djnz`, `ld sp,0` (`seg_ldsp0`: both stacks
  empty), `halt` (`seg_halt`: both halted, `Done`), `packHigh`'s rewrite (`seg_pack`: four steps of `A`
  against two of `B`), `push af` and `pop af` (`seg_push_af`, `seg_pop_af`: a frame of data, the
  same word in both), a round of `ldir` (`seg_ldir`: the byte each reads the same — from the RAM kept
  equal, or a literal of each image's ROM with `H`, `L` free — written in the RAM kept equal), and with
  `H`, `L` free: a literal's address into `HL` (`seg_ldhl`), `inc hl` (`seg_inchl_free`), an operation on `A`
  with the byte at each one's `(HL)` (`seg_aluM`); `seg_gen`: an instruction that goes on, in general;
* `Z80PassBlock`: a call of a routine of the runtime that works through `HL`, as one segment of the two
  runs: `blk_ld32` (`rt_ld32`, the four bytes at `HL` in the RAM kept equal: eight steps of each from
  the call to the item after it), `blk_st32` (`rt_st32`, the accumulator's first four bytes to those at `HL`),
  `blk_bytes` (`rt_add32`, `rt_sub32`, `rt_or32`: the loop over the bytes, `loop_eq_rounds`), `blk_cmp32`
  (`rt_cmp32`, its loop keeping `AF` on the stack, `loop_cmp_rounds`);
  `ldir_eq_rounds`: all the rounds of an `ldir` within that RAM;
* `Z80PassRun`: two machines side by side to the end (`sim_halts`: a relation kept by segments of
  the two runs, the first machine taking at least one step, under which the first halted means the
  second halted with the same devices — then when the first halts so does the second);
* `Z80PassCtl`: jumps (`jp`, `jr`, with a condition or not), calls and returns as steps of the machine
  in one image (`jump_mstep`, `call_mstep`, `ret_mstep`: the state after, the item the CPU is at);
* `Z80PassCheck`: the items of the image without the passes matched with those of one with them
  (`align`: a kind for each — the same item, a rewrite of a pass, an item dropped — computed by the
  kernel as at run time); what the match means is not proved yet;
* `Z80StackDItems`, `Z80StackDAsm`: the image of the stack for the harness **as built by default**
  (with the passes), written out (`#guard`: what `build` gives) and assembled by the kernel
  (`StackD.assemble_items`).  Nothing yet of what it does: the relation between it and the image
  without the passes is not proved.

By-reference parameters and `inlineCalls` are outside M7.1; of `IR → Z80` (M7.3) not proved: the routines
of the runtime the stack's image for the harness does not call; interrupts and the board's runtime and
start-up; the passes on the assembly (the images as built by default); of the trace `Target.runHarness`
prints, the notes and the line of a trap.

Every statement is about the definitions of `Ember.Spec` as they are;
`Ember/Proof/README.md` lists the theorems, the hypotheses they need and
what is not proven.  `lake build Ember.Proof` is the gate.
-/
