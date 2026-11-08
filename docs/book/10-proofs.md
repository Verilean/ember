# 10 · What is proved

Ember is tested in many ways (see [Chapter 4](04-testing.md)). Part of
it is also **proved**, in Lean, with no `sorry`. This chapter says which
parts are proved, quotes the main theorem of each layer, lists what each
theorem assumes, and lists what is **not** proved.

> **What this chapter is for**: telling you exactly how far the proofs
> go. A claim like "the stack is verified" is too broad. Each section
> below names the theorem, the file it is in, and where it stops. The
> full list of theorems, with one row per theorem, is
> [`Ember/Proof/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Proof/README.md). The milestones
> are in [`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md) (M5, M7).

Every statement quoted below is copied from the tree. Proofs are left
out. The names are fully qualified where the namespace is not obvious.

---

## 1 · The chain in one picture

The proofs connect five descriptions of the same TCP/IP stack:

```
Ember.Spec            the reference stack, plain Lean          (Chapter 3)
   ▲  M5.5, M5.6      "does what the Spec does"
Ember.Lang.Sem        the stack in Ember, under a total semantics
   ▲  M5.8, M5.9      "the emitted C does what Lang.Sem does"
Ember.C.Sem           the emitted C, under a C semantics
   ▲  M7.1            "the IR does what Lang.Sem does"         (from Lang.Sem)
Ember.Z80.IR.Sem      the Z80 back end's IR
   ▲  M7.3, M7.4      "the image does what the IR does"
Ember.Z80.Machine     the Lean model of the Z80 and the test harness
```

The C and the IR are two separate branches. Both start from
`Lang.Sem`. M5.1 to M5.3 are about the Spec alone.

All of this is for the **echo stack over SLIP**, the program
`Ember.Net.prog` (the "SLIP build"). The HTTP, HTTPS and authentication
layers (Chapters [6](06-http-app.md), [7](07-https.md), [8](08-auth.md),
[9](09-control.md)) are tested, not proved (§10).

---

## 2 · How the proofs keep themselves honest

From [`Ember/Proof/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Proof/README.md):

> There is no `sorry`, no `axiom`, no `native_decide` and no
> `bv_decide` in this directory.

Every file ends with its axioms pinned. If a proof starts to depend on
a new axiom, the build fails. For example, at the end of
`Ember/Proof/Driver.lean`:

```lean
/-- info: 'Ember.Proof.Refine.main_run_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_run_all
```

The main theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. `Lean.ofReduceBool` (which `native_decide` would bring in)
does not occur.

Two more rules, also from the README and the plan:

* **Statements are tested before they are proved.** Each statement was
  first run on random inputs. The ones that were false as first written
  are listed under "Hypotheses that are needed" in the proofs README
  (§3 below gives examples).
* **Two kinds of evaluation check, kept apart.** Some facts are checked by
  Lean's kernel with `decide +kernel`. These are part of the proofs. For
  example, in `Ember/Proof/Z80StackHRun.lean`:

  ```lean
  theorem rcItems_true : rcItems = true := by decide +kernel
  ```

  Other facts are checked with `#guard`. Lean runs `#guard` as compiled
  code when it builds the file. A false `#guard` fails the build, but it
  is not a kernel proof. The README always says which kind a fact is.
  A typical `#guard` checks that a term written out in a proof file is
  the same as what the tool produces (for example, the IR that
  `IR.lower` returns, or the bytes that `build` gives).

---

## 3 · The Spec on its own (M5.1 – M5.3)

These theorems are about `Ember.Spec` only. No Ember code is involved.

### Checksum algebra (M5.1)

`Ember/Proof/Checksum.lean` shows that one's-complement addition is a
commutative monoid, that the Internet checksum does not depend on the
order of the words (`sum_perm`), and that the RFC 1624 incremental update
gives the same result as recomputing:

```lean
-- Ember/Proof/Checksum.lean  (namespace Ember.Spec.Checksum)
theorem incremental_eq_recompute {b : ByteArray} {off len k : Nat} (hk : 2 * k + 1 < len)
    (hb : off + 2 * k + 1 < b.size) (m' init : UInt16)
    (hnz : sum (Bytes.set16 b (off + 2 * k) m') off len init ≠ 0) :
    incremental (checksum b off len init) (Bytes.get16 b (off + 2 * k)) m' =
      checksum (Bytes.set16 b (off + 2 * k) m') off len init
```

The hypothesis `hnz` is needed. One's complement has two zeros. For
all-zero data the update gives `0x0000` but recomputation gives `0xFFFF`.
The theorem without that hypothesis is `incremental_eq_checksum`, which
states both cases. `Icmp.reply_verifies` (in `Ember/Proof/Icmp.lean`)
uses this to show that the ICMP echo reply the Spec builds has a valid
checksum.

### Round trips (M5.2)

`Ember/Proof/Slip.lean` and `Ember/Proof/Headers.lean` prove
"parse ∘ emit = id" for SLIP, IPv4, UDP and TCP:

```lean
-- Ember/Proof/Slip.lean  (namespace Ember.Spec.Slip)
theorem decodeAll_encode (p : ByteArray) (maxLen : Nat) (h0 : 0 < p.size) (hmax : p.size ≤ maxLen) :
    decodeAll (encode p) maxLen = [p]
```

```lean
-- Ember/Proof/Headers.lean  (namespace Ember.Spec.Ipv4)
theorem validate_packet (proto : UInt8) (id : UInt16) (src dst : UInt32) (payload : ByteArray)
    (ourIp : UInt32) (hlen : 20 + payload.size ≤ 65535) (hdst : dst = ourIp ∨ dst = broadcast) :
    validate (packet proto id src dst payload) ourIp = .ok
      ({ ihl := 20, totalLen := 20 + payload.size, id, ttl := ttlDefault, proto, src, dst }, payload)
```

```lean
-- Ember/Proof/Headers.lean  (namespace Ember.Spec.Tcp)
theorem parse_emit (src dst : UInt32) (s : Seg) (hflags : s.flags &&& 0x3F = s.flags) :
    parse src dst (emit src dst s) = .ok s
```

Each hypothesis is there because the statement is false without it. An
empty SLIP frame is ignored and a frame longer than `maxLen` is dropped.
A length field is 16 bits, so a 65 536-byte payload wraps. The TCP
parser keeps six flag bits, but `emit` writes eight.

### TCP invariants (M5.3)

`Ember/Proof/Tcp.lean` defines the invariant of the TCP control block
(doc comments left out):

```lean
-- Ember/Proof/Tcp.lean  (namespace Ember.Spec.Tcp)
structure Inv (t : Tcb) : Prop where
  peerMss : t.peerMss ≤ 65535
  pendingCap : t.pending.size ≤ t.cap
  sentPending : t.sent ≤ t.pending.size
  flight : dist t.sndNxt t.sndUna = t.sent + ctl t.st
  holds : 0 < t.pending.size → t.st = .established ∨ t.st = .closeWait ∨ t.st = .lastAck
  fresh : t.st = .synRcvd ∨ t.st = .established → t.closeReq = false ∧ t.finSent = false
```

`input_inv` and `tick_inv` show that every segment and every tick keep
it. `Ember/Proof/Stack.lean` then lifts it to every state the whole
Spec can reach:

```lean
-- Ember/Proof/Stack.lean  (namespace Ember.Spec)
theorem reach_inv (cfg : Config) (inputs : List Input) : Tcp.Inv (reach cfg inputs).tcb

theorem reach_seqGe (cfg : Config) (inputs : List Input) :
    Tcp.seqGe (reach cfg inputs).tcb.sndNxt (reach cfg inputs).tcb.sndUna = true
```

`reach_seqGe` is "`snd.una ≤ snd.nxt` in every reachable state". There
are also per-segment theorems about delivery (`input_delivery`: bytes are
added to the buffer only from ESTABLISHED, or from SYN-RCVD when the
same segment completes the handshake) and about the window
(`input_window`).

The window theorem is weaker than the plan first said. The plan said
"accepted segments lie in the receive window". The proof showed that the
Spec trims a segment after it processes the segment's ACK, which frees
space. So the bound that holds is: the window, plus the bytes the same
segment acknowledges, plus one for a FIN.

**Not proved for the Spec** (from the README, "Not proven"):

* emit ∘ parse (the other direction). It is false as an equality of
  bytes.
* parsers on packets the Spec's own emitters do not make: IPv4 options,
  TCP options other than MSS, link padding.
* SLIP on arbitrary byte streams. Only "any decoder state, then one
  encoded frame" (`feed_encode`) is covered.
* round trips for ICMP, ARP, DHCP and Ethernet.
* TCP beyond the invariants: that every byte is echoed in order,
  retransmission and timer behaviour, the closing handshake.
* the delivery and window theorems are per segment. Only the state
  invariants are lifted to `Spec.step`.

---

## 4 · The stack in Ember does what the Spec does (M5.4 – M5.6)

This is the "refinement" part. The stack written in Ember
(`Ember/Net`) is run by `Ember.Lang.Sem`. This is a second, total
semantics of the language: loops and calls run on fuel. The proofs show
that it computes what `Ember.Spec` computes.

### Function by function (M5.5)

Each function of the stack gets a theorem that relates it to a Spec
function. For example, the checksum loop:

```lean
-- Ember/Proof/Refine.lean
theorem csum_refines (p : Prog) (hc : p.fn? "csum" = some csum) (hg : p.fn? "get16" = some get16)
    (ha : p.fn? "add16" = some add16) (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (o n ini : UInt16)
    (hr : o.toNat + n.toNat ≤ b.size) (hsz : b.size ≤ 65536) (d : Nat) :
    Sem.call (d + n.toNat / 2 + 60) p st "csum" [u16 o, u16 n, u16 ini]
      = .ok (some (u16 (Spec.Checksum.sum b o.toNat n.toNat ini))) st
```

Read it as: in any program that contains these functions, from any
state whose `buf` holds the bytes `b`, with enough fuel, `csum` returns
the Spec's sum and does not change the state. There are theorems of this
kind for SLIP (`slip_store_refines`, `slip_send_refines`), IPv4
(`ip_send_refines`, `ip_input_refines`), ICMP (`icmp_input_refines`),
UDP (`udp_input_refines`), and TCP (`tcp_input_refines`,
`tcp_tick_refines`). The drop reasons and the reply bytes are the
Spec's, byte for byte.

### The whole program, for any input (M5.6)

`main_step` (`Ember/Proof/Main.lean`) proves that one call of `main`
reads one input item and does what the Spec does with that item.
`Ember/Proof/Driver.lean` puts the calls together, from the initial
state:

```lean
-- Ember/Proof/Driver.lean  (namespace Ember.Proof.Refine)
theorem main_run_all (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (inputs : Array Trace.Input) (n j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ (st' : St) (w' : TW), mainIter (n + 4716) p (j + 1) (Sem.initial Net.prog inputs) = some st' ∧
      MainInv st' (Spec.reach {} inputs.toList) w' 296 Spec.ourIpDefault 296 ∧
      kept st'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems st'.world = []
```

`specKept` is the list of transmissions and drops that `Spec.step`
makes, input by input:

```lean
-- Ember/Proof/Driver.lean
def specKept : List Trace.Input → Nat → Spec.State → List (Nat × Trace.Event)
  | [], _, _ => []
  | x :: t, j, s => ((Spec.step s x).2.filter keep).map (fun e => (j, e)) ++ specKept t (j + 1) (Spec.step s x).1
```

So, for every input sequence, the stack in Ember (as `Lang.Sem` runs
it, in the SLIP configuration `{}`: 10.0.0.1, MTU 296, no DHCP) **never
traps**, and it **transmits and drops exactly what the Spec does**, at
the same inputs. "Never traps" means `mainIter … = some st'`: every call
ends normally. So every array index is in range and the fuel
(`n + 4716` per call) is enough.

**A defect found by this proof.** The first form of `tick_step` (one
timer tick) was false. The stack builds what a tick sends in the same
buffer that holds a frame being received. A tick that arrived in the
middle of a frame and sent something destroyed that frame. No test had a
tick inside a frame. Now a tick in the middle of a frame waits for the
frame to end, both in the stack and in the Spec. The corpus has tests
for it (`corpus/timer/midframe-tick-*.trace`).

### What M5.4 – M5.6 assume and leave out

* **`Lang.Sem` is not the interpreter.** The interpreter has `partial`
  loops that the kernel cannot unfold. The two are *tested* equal
  (random programs, the examples, every build of the stack on the
  corpus), not proved equal.
* **The program is taken as given.** The hypotheses `TcpAll p`,
  `TcpReasons p` and `p.fn? "main" = some main_fn` say that `p` has the
  functions of the checked stack. The type checker is `partial` too. So
  "the checker's output for `Net.prog` is such a `p`" is checked by
  `#guard`, function by function, not by a theorem.
* **The driver loop is not in the theorem.** `Sem.run` calls `main` in a
  `while` loop and prints `Trace` lines. That loop and the printing are
  not proved. The theorems are about `j` calls of `main` (`mainIter`).
  On the Spec side, `Spec.run` likewise.
* **Only transmissions and drops are compared.** The Spec's `pkt`, `tcb`
  and note lines are not.
* **Only the SLIP configuration.** The Ethernet build (Ethernet, ARP,
  DHCP) has no refinement proofs.
* **Counters**: the TCP layer needs the idle and retry counters below
  255. This is proved for every reachable state (`Spec.reach_bnd` in
  `TcpBound.lean`), so `main_run_all` itself takes no such hypothesis.

---

## 5 · The emitted C (M5.7, M5.8)

`Ember/C/Sem.lean` (M5.7) gives a meaning to the C subset that the
emitter writes. It has no meaning for what C leaves undefined, or for
anything that would be computed in a signed type. So "the C has a
meaning" already rules out undefined behaviour **in this model**.

The proofs relate `Ember.C.Sem` to `Ember.Lang.Sem` through the emitter
itself (`Ember/C/Compile.lean`). The general results:

* `expr_ok` (`CExpr.lean`): a well-typed expression's code has the
  value `Lang.Sem` gives it, or ends in `ember_trap` when it has none.
* `stmt_ok`, `block_ok` (`CSim.lean`): every statement form.
* `fn_sim` (`CFn.lean`): a compiled function, for any fuel.
* `iter_sim`, `iter_trap` (`CProgram.lean`): for any program the checker
  `progOkB` accepts, calls that end in `Lang.Sem` end in `C.Sem` in a
  related state, and a trap is a trap.

With M5.6 this gives the result for the stack:

```lean
-- Ember/Proof/CNet.lean  (namespace Ember.Proof.CSim)
theorem stack_c (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (hentry : p.entry = "main") (hg : p.globals = Net.prog.globals) (hs : p.structs = Net.prog.structs)
    (hf : p.framed = Net.prog.framed) (o : Opts) (hpre : o.namePrefix = "") (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hok : progOkB p o = true) (u : CUnit) (hc : compile p o = .ok u)
    (inputs : Array Trace.Input) (j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ m cst', cIter m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) (j + 1)
        (C.Sem.initial (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) inputs p.framed)
          = some cst' ∧
      kept cst'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems cst'.world = []
```

In words: for the checked SLIP build, with emitter options that have no
name prefix and without the planted bug of the fuzzer's self-test
(`bugDropCast`, `Ember/C/Compile.lean`, which drops the truncating cast
of `+`), on any profile whose `int` has 16 bits or more, the
emitted C (under `C.Sem`) ends every call normally, with no
`ember_trap` and nothing undefined. Once the input is read, its
transmissions and drops are the Spec's, input by input.

`progOkB` is a checker, and `progOkB_sound` (`CCheck.lean`) proves it
right. It is run on the SLIP, loopback, Ethernet and Ethernet+DHCP
builds for the three profiles (`#guard`s in `CNet.lean`). All are
accepted.

**Not proved for the C** (from the README):

* **by-reference parameters.** `Lang.Sem` copies an array or record in
  and out, and the C passes a pointer. `progOkB` rejects such programs.
  The stack has none. The examples that have them are covered by tests
  only.
* **name prefixes.** The fuzzer's programs use one. `iter_sim` takes "no
  name collisions" as a hypothesis, and it is proved only for the empty
  prefix.
* **the C semantics itself.** It is a definition, not derived from the C
  standard. The printer from the C AST to text is trusted. That gcc and
  SDCC give the printed text the meaning `Ember.C.Sem` gives the AST is
  checked by the differential tests, not proved.
* the `while` loops of the drivers (`C.Sem.run`, `Lang.Sem.run`), as in
  M5.6.

---

## 6 · Bounds checks taken out (M5.9, first part)

When the emitter cannot see from the form of an index that it is in
range, it writes `if (t >= n) { ember_trap("…"); }` before the access.
The SLIP build has 17 such checks. `C.dropUnit`
(`Ember/C/DropChecks.lean`) removes them. `Ember/Proof/CDrop.lean`
proves two things:

* `drop_sim`: under `C.Sem`, anything that **ends normally** with the
  checks ends the same way without them. A check that does not trap does
  nothing.
* `stack_c_dropped`: what `stack_c` says, of the C without checks.

```lean
-- Ember/Proof/CDrop.lean  (namespace Ember.Proof.CDrop)
theorem stack_c_dropped (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (hentry : p.entry = "main") (hg : p.globals = Net.prog.globals) (hs : p.structs = Net.prog.structs)
    (hf : p.framed = Net.prog.framed) (o : Opts) (hpre : o.namePrefix = "") (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hok : progOkB p o = true) (u : CUnit) (hc : compile p o = .ok u)
    (inputs : Array Trace.Input) (j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ m cst', cIter m (C.Sem.CProg.ofUnit (dropUnit u) o.profile o.entryName p.dropReasons p.notes) (j + 1)
        (C.Sem.initial (C.Sem.CProg.ofUnit (dropUnit u) o.profile o.entryName p.dropReasons p.notes) inputs
          p.framed) = some cst' ∧
      kept cst'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems cst'.world = []
```

This works because M5.6 already shows that no call of `main` traps, so
every index is in range. The C without checks is a separate output
(`ember-emit net --dropped`, golden files
`Tests/Ember/golden/net.dropped.*.c`). The normal C still has the checks.
The tools refuse `--dropped` for any program other than the SLIP build.
The README explains why: `drop_sim` says nothing about a run that traps.
In such a run the check is what turns an out-of-range index into a trap
instead of undefined behaviour. The top-level [`README.md`](https://github.com/Verilean/ember/blob/main/README.md)
sums up the gain as 5 % less code on the Z80 and the ESP32-C3, and no
fewer cycles per ping. The plan's M5.9 row has the measured numbers,
which depend on SDCC's settings.

**Not done:** dropping one check at a time, from a range lemma about
its index, in programs that have no whole-program "never traps" theorem
(the Ethernet builds, the examples). The Z80 back end's own check removal
(`IR.dropChecks`) is a different pass, covered in §7.

---

## 7 · The Z80 back end (M7)

Ember has its own Z80 back end (M6): Ember → IR → Z80 assembly → bytes,
with no C compiler ([Chapter 5](05-targets.md)). M7 has four parts.

### Frame validator (M7.2)

Locals live in static frames, overlaid along the call graph. A
validator checks every layout before it is used. Its soundness:

```lean
-- Ember/Proof/Z80Frame.lean  (namespace Ember.Z80.IR)
theorem validate_sound {p : Prog} {l : Layout} {frameSize : String → Nat} {lo hi : Nat}
    (h : validate p l frameSize lo hi = .ok ()) : Sound p l frameSize lo hi
```

`Sound` (same file) says: the globals lie in `[lo, hi)` and do not
overlap. Every function's frame lies in `[lo, hi)`, apart from every
global and from the frame of every function it can reach. No function
reaches itself. This is translation validation: the allocator is not
proved, but every layout it makes is checked.

### `Lang → IR` (M7.1)

`Ember/Z80/IRSem.lean` is a semantics for the IR, as total functions.
The proofs follow the same plan as for the C, through the lowering
`Ember/Z80/IR.lean` itself, and include the passes `cleanup` and
`dropChecks` (`tidy_ref`):

```lean
-- Ember/Proof/IRLower.lean  (namespace Ember.Proof.IRSim)
theorem lower_iter {lp : Prog} {q' : IR.Prog} (hl : lower lp = .ok q') (l : Layout) (hok : progOkB lp = true)
    (hir : irOkB lp l = true) (inputs : Array Trace.Input) (k j : Nat) (st' : Lang.Sem.St)
    (hi : callIter k lp j (Lang.Sem.initial lp inputs) = some st') :
    ∃ m ist', irIter m (irCtx lp q' l) j (irInit lp q' l inputs) = some ist' ∧ ist'.world = st'.world
```

`lower_trap` is the trap case. With M5.6, `stack_ir` (`IRNet.lean`)
says: the IR of the SLIP build never traps and transmits and drops what
the Spec does. The checkers `progOkB` and `irOkB` are proved sound and
accept every build of the stack (`#guard`).

The proof found a defect in the lowering: `a && b` skipped `b` when `b`
was an element at a constant, non-literal index out of range, where the
interpreter traps. It is fixed and has a regression test
(`regress_strict_and`).

**Not covered:** by-reference parameters; `inlineCalls` (off by
default); the IR semantics against the `partial` IR interpreter (tested,
not proved equal).

### The encoder (M7.4)

`Ember/Z80/AsmSem.lean` gives every assembler instruction a meaning by
its mnemonic and operands (`Asm.exec`). The CPU model
(`Ember/Z80/Cpu.lean`) decodes bytes. The theorem connects them:

```lean
-- Ember/Proof/Z80Encode.lean  (namespace Ember.Proof.Z80Enc)
theorem step_encode (i : Instr) (he : encode i env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env i s inp = some s') : s.step inp = s' ∧ (Instr.falls i = true → s'.pc = s.pc + UInt16.ofNat bs.length)
```

If the encoded bytes are at the program counter, one CPU step does what
`exec` says, for the whole state (registers, flags, memory, T-states,
`R`). `assemble_ok` (`Z80Asm.lean`) proves that the assembler puts every
item's encoding at its address and resolves labels correctly.

**Not covered:** forms with `IX`/`IY` (`exec` is `none` for them, so the
hypothesis `hx` cannot hold; the back end uses none); `Asm.relax`; the
text parser for the runtime's assembly. The block instructions are
covered, but their meaning is the model's own `execBlock`.

### `IR → Z80` for the SLIP harness image (M7.3)

This is the largest part, and its scope is narrow. It is proved **for
one program**: the SLIP build of the stack, in its image for the **test
harness** (`Runtime.harness`: effects are I/O ports of the model; there
are no interrupts), on the **Lean model of the machine**
(`Ember.Z80.Machine`). It covers two images: the one without the passes
on the assembly (`StackH`) and the one `build` makes by default, with
the passes (`StackD`).

What the theorems take of the program is one structure:

```lean
-- Ember/Proof/Z80StackHSpec.lean  (namespace Ember.Proof.Z80Gen.StackH)
structure StackSrc (p : Lang.Prog) : Prop where
  all : TcpAll p
  reasons : TcpReasons p
  main : p.fn? "main" = some main_fn
  entry : p.entry = "main"
  globals : p.globals = Net.prog.globals
  structs : p.structs = Net.prog.structs
  framed : p.framed = false
  lowered : IR.lower p = .ok Stack.ir
  okP : progOkB p = true
  okIR : irOkB p layout = true
  drops : p.dropReasons = img.dropReasons
  notes : p.notes = img.notes
```

The parts that can be computed are checked by a `#guard` on
`Net.prog.check` in the same file.

The headline theorem for the default image:

```lean
-- Ember/Proof/Z80PassStack.lean  (namespace Ember.Proof.PassSim.Stack)
theorem stackD_halts (p : Lang.Prog) (S : StackH.StackSrc p) (inputs : Array Input) :
    ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW),
      mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
      (LoopH.mrun n (harnessMachine StackD.asm inputs)).cpu.halted = true ∧
      Sim StackH.img.ctx (LoopH.mrun n (harnessMachine StackD.asm inputs)) w' ∧ w'.1 = sti.world ∧
      kept w'.1 = specKept inputs.toList 0 (Spec.State.init {})
```

In words: load the default image into the model as the tests do, give it
any input, and step it. After some number of steps the CPU is halted.
At that point the machine stands for the world that some number of
calls of `main` leave in the Ember semantics with no input left. Its
transmissions and drops are those of `Spec.step`.

`stackH_halts` (`Z80StackHMachine.lean`) says the same of `StackH`.
Around these theorems there are more:

* `stackH_trace`, `stackD_trace`: the trace that `Target.runHarness`
  prints has the Spec's transmissions and drops, input by input.
* `stackH_no_trap`, `stackD_no_trap`: the harness records no trap.
* `stackH_trace_lines`, `stackD_trace_lines`: the whole printed trace,
  notes included, is the Ember semantics' trace and nothing else.
* `stackH_tcb_obs`, `stackD_tcb_obs`: the lines of the `tcb` observer
  (`ember-z80 tcb-obs`), **when it gives them**, are the Spec's control
  block after each item. That the observer always gives lines is not
  proved.

How the proof is built, in short:

* Every instruction of the stack's IR (all 1073) has an instruction
  theorem, through the code generator itself (`ins_ok`), then functions
  (`fn_ok`), then the program (`prog_ok`).
* The image's IR and its 2924 items are written out as terms in proof
  files. Kernel checks (`decide +kernel`, cut into small parts to keep
  memory down) show that the proofs' setting holds for that image. A
  `#guard` checks that the written-out terms are what `IR.lower` and
  `build` give.
* The runtime routines that the image calls (fifteen of them) are
  proved from their items, so `stackH_ok` takes nothing from the
  runtime. Start-up and the harness loop are proved from their items too
  (`stackH_run`).
* The assembly passes (`retThreading`, `sweep`, `peephole`, `packHigh`,
  `relax`) are proved **for this image only**. `StackD` and `StackH` run
  side by side under a relation. The meeting points come from a
  certificate made outside the proofs by `ember-passcert`, and the kernel
  checks it (`certD_ok`). This gives `passes_halt`.
* Registers across jumps are **checked, not proved**: `jumpsOk`
  compares, for each generated function, what the generator assumed
  after a label with what registers held at each jump to it.

Smaller programs get the same treatment: the loopback program
(`loopH_halts`), `crc32` (`crc32H_harness_halts`), `regress_wide_store`
(`regressH_harness_halts`) and the small program `Ember.Z80.Wide`
(`wideH_harness_halts`). For these programs the theorems are about the
image without the passes, and not about the trace `runHarness` prints.

### What M7 does not prove

From the README and the plan's M7 row:

* **Not the back end for every IR program.** Other programs' images are
  tested (random programs, the loopback, the corpus). The assembly
  passes are proved for `StackD` only.
* **Not the board runtime or interrupts.** The proofs' machine has no
  interrupts. Start-up, the interrupt routine, the ring buffer and the
  loop that calls `main` on the board are not proved. For the board
  build, the layout checks pass by `#guard` (not the kernel), and its
  image is not connected to the theorems.
* **Not the routines and operations the stack does not use:**
  multiplication, division, variable shifts, wide `not`/`neg`/`zero`,
  eight-byte values, MMIO effects, `input.frame`. These routines are
  tested by `ember-z80 rt-check`.
* **Not real hardware.** Everything is on the Lean model of the CPU,
  which is checked against `z88dk-ticks` by tests (M6.1). The plan's
  hardware step M4z.5 is not done.
* **Not the `tcb` lines themselves.** The program writes none. The
  observer theorems are soundness only.
* The `#guard`s that tie the written-out IR, items and bytes to the
  real `IR.lower` and `build` are evaluation, not kernel proofs.

---

## 8 · The trust base

Putting §4 – §7 together, a reader has to trust:

* Lean's kernel, and the three standard axioms;
* `Ember.Spec` as the meaning of "correct" (it is checked against Linux
  by recorded traces, see [Chapter 3](03-spec.md) and
  [Chapter 4](04-testing.md));
* that `Lang.Sem` agrees with the interpreter (tested);
* that the type checker's output for `Net.prog` is the term the proofs
  use (`#guard`);
* for the C: `Ember.C.Sem` as the meaning of C, the printer, and gcc or
  SDCC (differential tests);
* for the Z80: the CPU model (tested against `z88dk-ticks`), and, on a
  board, everything the harness proofs leave out (§7).

The plan's goal for M7 was a chain whose trusted base is "Lean's kernel,
the Z80 model, and the hand-written runtime (start-up, ISR, ring
buffer)". The harness image is proved without trusting its runtime.
The board's runtime is still trusted.

---

## 9 · How to check the proofs yourself

The proofs are an ordinary Lean library. `Ember.lean` imports
`Ember.Proof`, so the default build checks them:

```sh
nix-shell                  # the tools (see Chapter 0)
lake build                 # builds Ember, Ember.Proof included
```

To build only the proofs, plus the two `Tests` modules that carry
`#guard`s on programs in `Tests` (`Ember` does not import `Tests`):

```sh
lake build Ember.Proof Tests.Ember.Z80Cover Tests.Ember.Z80RegressW
```

This is the `proofs` job of `tools/ember/ci.sh`. Note that
`tools/ember/ci.sh proofs` first runs `lake build` and builds the tool
binaries, as every job does, and then runs the line above.

The build is heavy. The README measured building `Ember.Proof` from
nothing in a pod limited to 8 GB: about 16 minutes, with the largest
Lean process at about 3.6 GB (`Z80StackHAsm`). Limit the memory and the
number of jobs on a shared machine.

To confirm the "no `sorry`, no `native_decide`" claim yourself:

```sh
grep -rn -E 'sorry|native_decide|bv_decide|^axiom' Ember/Proof --include='*.lean'
```

This should find nothing. A `sorry` would also show as a warning in the
build. To see which axioms a theorem uses, look at the `#print axioms`
lines at the end of its file. Each is pinned with `#guard_msgs`, so the
build fails if the list changes.

To see where kernel evaluation is used, as opposed to `#guard`:

```sh
grep -rn 'decide +kernel' Ember/Proof --include='*.lean'
grep -rn '^#guard ' Ember/Proof --include='*.lean'
```

---

## 10 · Tested, not proved: HTTP, HTTPS and authentication

The HTTP server, TLS 1.3, the crypto and the OIDC access-token checks
(M8 and M9) are **not proved**. The plan records the decision for M8
(2026-11-06):

> The echo stack and its proofs (`Net.prog`, M5–M7) are unchanged. M8
> is checked by tests (lockstep of Spec, interpreter, C and QEMU; RFC
> test vectors; differential runs against OpenSSL). Proofs of M8, such
> as the crypto functions against a Lean reference, come after M8

and for M9: "As M8: tests (RFC vectors, Lean = Ember = C, OpenSSL,
negative cases)." There is no file about HTTP, TLS, crypto or
authentication in `Ember/Proof`.

These layers are built on a new application stack (`Spec.Srv`,
`Net.Srv`), not on `Net.prog`. So none of the theorems in this chapter
applies to them, not even the TCP ones. The plan also says that no claim
is made about side channels in the crypto.

---

## 11 · Summary

| Layer | Key theorem | File | Scope | Main limits |
|---|---|---|---|---|
| Checksum | `incremental_eq_recompute` | `Checksum.lean` | Spec | new range must not sum to 0 |
| Round trips | `decodeAll_encode`, `validate_packet`, `parse_emit` | `Slip.lean`, `Headers.lean` | Spec | parse ∘ emit only |
| TCP | `reach_inv`, `reach_seqGe` | `Tcp.lean`, `Stack.lean` | Spec | invariants, not full TCP behaviour |
| Ember vs Spec | `main_run_all` | `Driver.lean` | SLIP build, `Lang.Sem` | driver loop, `Lang.Sem` = interpreter tested |
| C | `stack_c` | `CNet.lean` | SLIP build, `C.Sem` | C semantics, printer, compiler trusted |
| No bounds checks | `stack_c_dropped` | `CDrop.lean` | SLIP build only | no per-check elimination |
| Frames | `validate_sound` | `Z80Frame.lean` | any layout validated | — |
| IR | `lower_iter`, `stack_ir` | `IRLower.lean`, `IRNet.lean` | programs `progOkB` accepts | no by-reference, no `inlineCalls` |
| Encoder | `step_encode`, `assemble_ok` | `Z80Encode.lean`, `Z80Asm.lean` | all forms without `IX`/`IY` | `relax` |
| Z80 image | `stackH_halts`, `stackD_halts` | `Z80StackHMachine.lean`, `Z80PassStack.lean` | SLIP harness image, Lean model | no board, no interrupts, no hardware |
| HTTP/TLS/auth | — | — | — | tested only |

For every row, the full list of theorems and hypotheses is in
[`Ember/Proof/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Proof/README.md). The design
reasons are in [`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md) §4 and in the
decision log of [`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md).
