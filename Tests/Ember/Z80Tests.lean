import Ember.Tools.Z80
import Tests.Ember.TargetTests
import Tests.Ember.LangTests

/-!
# M4z / M6.1 tests: the Z80

* the Lean model of the CPU (`Ember.Z80.Cpu`): interrupts, `EI` delay,
  `HALT`, the `R` register — and, in `tools/ember/z80-test.sh`, random
  instruction streams against `z88dk-ticks`;
* SDCC's code for the emitted C on the model of the machine
  (`Ember.Z80.Machine`): the examples (interpreter = Z80), byte echo and
  SLIP loopback under interrupts, the corpus and generated sessions
  (target trace = Spec trace), random programs.

The SDCC parts are skipped when `sdcc` or `make` is not installed (they
come with `nix-shell`).
-/

namespace Ember.Tests.Z80Tests
open Ember Ember.Lang Ember.Trace Ember.Z80
open Ember.Tests.LangPrograms Ember.Tests.LangTests

/-- A CPU with the code at 0 and everything above 0x8000 writable. -/
def cpuOf (code : List UInt8) : Cpu :=
  (Cpu.load {} 0 (ByteArray.mk code.toArray))

def run (c : Cpu) (n : Nat) : Cpu := Id.run do
  let mut c := c
  for _ in [0:n] do c := c.step (fun _ => 0xFF)
  return c

/-- Unit tests of what random instruction streams do not reach. -/
def modelTests : IO Nat := do
  let mut bad := 0
  let check (name : String) (ok : Bool) : IO Nat := do
    if !ok then IO.println s!"FAIL z80 model: {name}"
    return if ok then 0 else 1
  -- HALT stays put until an interrupt; IM 1 goes to 0x38 and pushes the
  -- address after the HALT
  let c := run (cpuOf [0x31, 0x00, 0x90, 0xED, 0x56, 0xFB, 0x76]) 6   -- ld sp,9000h; im 1; ei; halt
  bad := bad + (← check "halt" (c.halted && c.pc == 7))
  bad := bad + (← check "interruptible after ei; halt" c.interruptible)
  let i := c.interrupt 0xFF
  bad := bad + (← check "im 1 vector" (i.pc == 0x38 && !i.halted && !i.iff1 && i.sp == 0x8FFE))
  bad := bad + (← check "im 1 return address" (i.mem[0x8FFE]! == 7 && i.mem[0x8FFF]! == 0))
  -- EI takes effect after the next instruction
  let c := run (cpuOf [0xFB, 0x00, 0x00]) 1
  bad := bad + (← check "ei delay" (!c.interruptible))
  bad := bad + (← check "ei delay over" (run c 1).interruptible)
  -- DI: no interrupt
  bad := bad + (← check "di" (!(run (cpuOf [0xFB, 0x00, 0xF3, 0x00]) 3).interruptible))
  -- R counts opcode fetches (two for a prefixed instruction), bit 7 kept
  let c := run (cpuOf [0x00, 0x00, 0xED, 0x44, 0xDD, 0x23]) 4
  bad := bad + (← check "r register" (c.r &&& 0x7F == 6))
  -- IM 2: the vector comes from I and the bus
  let c := run (cpuOf [0x31, 0x00, 0x90, 0x3E, 0x80, 0xED, 0x47, 0xED, 0x5E, 0xFB, 0x00]) 6
  let c := { c with mem := (c.mem.set! 0x8010 0x34).set! 0x8011 0x12 }
  bad := bad + (← check "im 2 vector" ((c.interrupt 0x10).pc == 0x1234))
  if bad == 0 then IO.println "z80 model: HALT, EI delay, DI, IM 1, IM 2, R: ok"
  return bad

/-- M4z.1: the examples and the regressions, interpreter = SDCC's code on
the model, with the inputs of the host differential test. -/
def examples : IO Nat := do
  let regress : List (String × Prog × Array Input) := Regress.progs
  let progs := Examples.all ++ regress.map fun (r : String × Prog × Array Input) => (r.1, r.2.1)
  let mut cases : Array (String × Prog × Array Input) := #[]
  for (n, p) in progs do
    for seed in [0:(if n == "constructs" || n.startsWith "regress" then 1 else 5)] do
      let ins := if n == "constructs" then constructsInputs
        else if let some (_, _, i) := regress.find? (fun (r : String × Prog × Array Input) => r.1 == n) then i
        else if n == "slip" then #[.rx ((randBytes 400).run' (Rng.ofSeed seed))]
        else roundInputs (rounds seed 4 40)
      cases := cases.push (n, p, ins)
  let o ← Tools.Z80.compareWithInterp ".lake/ember-z80-examples" cases 64
  IO.println (s!"z80 examples: {o.ran - o.bad.size - o.refused.size} of {cases.size} runs of {progs.length} programs: interpreter = Z80" ++
    (if o.refused.isEmpty then "" else s!"; differ where SDCC warned of unreachable code: {o.refused}") ++
    (if o.crashed.isEmpty then "" else s!"; SDCC internal error: {o.crashed}"))
  return o.bad.size

/-- M6.5: the examples, the regressions and the index-check programs
through the own back end: interpreter = IR interpreter = generated code
on the model. -/
def ownExamples : IO Nat := do
  let regress : List (String × Prog × Array Input) := Regress.progs
  let mut cases : Array (String × Prog × Array Input) := #[]
  for (n, p) in Examples.all do
    for seed in [0:(if n == "constructs" then 1 else 5)] do
      let ins := if n == "constructs" then constructsInputs
        else if n == "slip" then #[.rx ((randBytes 400).run' (Rng.ofSeed seed))]
        else roundInputs (rounds seed 4 40)
      cases := cases.push (n, p, ins)
  for (n, p, ins) in regress do cases := cases.push (n, p, ins)
  for (n, p) in Guard.progs do
    for ins in Guard.inputs do cases := cases.push (n, p, ins)
  let mut bad := 0
  let mut traps := 0
  for (n, p, ins) in cases do
    match Tools.Fuzz.interp p ins with
    | .error e => IO.println s!"FAIL {n}: interpreter: {e}"; bad := bad + 1
    | .ok it =>
      if Tools.Cc.trapped it then traps := traps + 1
      for (what, r) in [("IR", IR.run p ins), ("IR with inlining", IR.run p ins (inline := true)),
                        ("IR semantics", IR.Sem.run p ins), ("IR semantics with inlining", IR.Sem.run p ins (inline := true)),
                        ("own back end", Tools.Z80.ownRun p ins)] do
        match r with
        | .ok t =>
          if !Tools.Fuzz.agree it t then
            bad := bad + 1
            IO.println s!"FAIL {n}: interpreter vs {what}\n{(diff it t { observable := false }).report}"
        | .error e => bad := bad + 1; IO.println s!"FAIL {n}: {what}: {e}"
  IO.println s!"z80 own back end: {cases.size} runs of the examples, regressions and index-check programs ({traps} of them trap): interpreter = IR = IR semantics = generated code; {bad} failures"
  return bad

/-- Traces agree only when the program's notes do — names, values, how
many — and the note of a trap, which each implementation words its own
way, is the one line left out.  A note of the program is never taken
for a trap, whatever its name (`Trace.isTrapNote`): shown on made-up
traces, and on a program whose note is named `trap counter`, run by the
interpreter and by the own back end. -/
def noteAgreeTests : IO Nat := do
  let tr (notes : List String) : Trace :=
    { lines := #[⟨0, .tick⟩] ++ (notes.map fun s => (⟨0, .note s⟩ : Line)).toArray }
  let agree (a b : List String) := Tools.Fuzz.agree (tr a) (tr b)
  let trapped (s : String) := Tools.Cc.trapped (tr [s])
  let big := "tick 4294967295"
  -- names a program may give a note: none of them makes its note a trap
  let names := ["trap", "trapdoor", "trapCount", "trap counter", "trap (z80)", "trap (", "trap ()", "trap (x) y",
    "trap fn=main at stmt", "", " ", "trap "]
  let namesOk := names.all fun n => [0, 1, 42, 4294967295].all fun (v : Nat) =>
    !trapped s!"{n} {v}" && !agree [s!"{n} {v}"] [s!"{n} {v + 1}"] && agree [s!"{n} {v}"] [s!"{n} {v}"]
  -- what the implementations write for a trap
  let traps := [trapNote "", trapNote "z80", trapNote "sem", trapNote "trap", trapNote "out of fuel",
    trapNote "fn=main at stmt 3 (x.lean:1:2): index 7 out of bounds [0, 4)", trapNote "index 3", trapNote "7",
    trapNote "trap: index 7 out of bounds [0, 4) in f_1", trapNote "trap in main"]
  let trapsOk := traps.all fun t => trapped t && traps.all fun u => agree ["tick 1", t] ["tick 1", u]
  let mut cases : List (String × Bool) := [
    ("same note", agree ["tick 42"] ["tick 42"]),
    ("value differs", !agree ["tick 1"] ["tick 2"]),
    ("name differs", !agree ["tick 1"] ["tock 1"]),
    ("note missing", !agree ["tick 1"] []),
    ("no name makes a note a trap", namesOk),
    ("several notes, the largest value", agree ["a 0", big, "b 7"] ["a 0", big, "b 7"]),
    ("several notes, one differs", !agree ["a 0", big, "b 7"] ["a 0", "tick 4294967294", "b 7"]),
    ("several notes, one missing", !agree ["a 0", big, "b 7"] ["a 0", "b 7"]),
    ("several notes, order", !agree ["a 0", "b 7"] ["b 7", "a 0"]),
    ("a trap, however worded", trapsOk),
    ("a trap after notes that differ", !agree ["tick 1", "trap (z80)"] ["tick 2", "trap (sem)"]),
    ("a trap against none", !agree ["tick 1", "trap (z80)"] ["tick 1"]),
    ("a trap against a note that begins with trap", !agree ["trap (z80)"] ["trap (z80) 1"]),
    ("a trap is the last line only", !agree ["trap (z80)", "tick 1"] ["trap (sem)", "tick 1"])]
  -- a program that type-checks, its note named `trap counter`
  let p : Prog := { Examples.Constructs.prog with notes := ["trap counter"] }
  let ins : Array Input := #[.tick]
  let swap (t : Trace) : Trace :=
    { t with lines := t.lines.map fun l => match l.ev with
        | .note "trap counter 42" => { l with ev := .note "trap counter 99" }
        | _ => l }
  let hasNote (t : Trace) := t.lines.any fun l => match l.ev with | .note "trap counter 42" => true | _ => false
  match p.check, Tools.Fuzz.interp p ins, Tools.Z80.ownRun p ins, IR.Sem.run p ins with
  | .ok _, .ok it, .ok zt, .ok st =>
    cases := cases ++ [
      ("program: the note is there", hasNote it && hasNote zt && hasNote st),
      ("program: not a trap", !Tools.Cc.trapped it && !Tools.Cc.trapped zt),
      ("program: interpreter = own back end = IR semantics", Tools.Fuzz.agree it zt && Tools.Fuzz.agree it st),
      ("program: another value is seen", !Tools.Fuzz.agree it (swap it) && !Tools.Fuzz.agree it (swap zt))]
  | _, _, _, _ => cases := cases ++ [("program: checks and runs", false)]
  -- and one that traps: every implementation's trace ends in a trap, and they agree
  let q := Examples.Constructs.prog
  let qins : Array Input := #[.rx (ByteArray.mk #[7])]
  match Tools.Fuzz.interp q qins, Tools.Z80.ownRun q qins, IR.Sem.run q qins, IR.run q qins with
  | .ok it, .ok zt, .ok st, .ok rt =>
    cases := cases ++ [
      ("a real trap: seen in all", [it, zt, st, rt].all Tools.Cc.trapped),
      ("a real trap: they agree", [zt, st, rt].all (Tools.Fuzz.agree it))]
  | _, _, _, _ => cases := cases ++ [("a real trap: runs", false)]
  let mut bad := 0
  for (n, okc) in cases do
    unless okc do
      bad := bad + 1
      IO.println s!"FAIL note agreement: {n}"
  IO.println s!"trace agreement on notes: {cases.length} cases (values, names, missing notes, any name against a trap, traps however worded, a program with a note named `trap counter`); {bad} failures"
  return bad

/-- The static bound on the stack answers only for images of the shape
it models: the counter-examples of the review (a jump to a label plus an
offset, a stack pointer set elsewhere than at the top, an interrupt
routine that lets another interrupt in) are refused. -/
def stackBoundTests : IO Nat := do
  let asm (src : String) : List Asm.Item := match Asm.parse src with | .ok l => l | .error _ => []
  let cases : List (String × String × Option (Nat × Nat)) := [
    ("plain", "rt_start: ld sp,0\n call f\nstop: jp stop\nf: push af\n pop af\n ret\n", some (4, 0)),
    ("di first", "rt_start: di\n ld sp,0\n call f\nstop: jp stop\nf: ret\n", some (2, 0)),
    ("isr", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n nop\n jp loop\nrt_isr: push af\n pop af\n ei\n reti\n", some (2, 4)),
    ("jump to a label plus an offset", "rt_start: ld sp,0\n jp target+1\ntarget: ret\ngrow: push af\n jp grow\n", none),
    ("call to a label plus an offset", "rt_start: ld sp,0\n call f+1\nstop: jp stop\nf: nop\n ret\n", none),
    ("stack pointer not at the top", "rt_start: ld sp,0x8002\n call f\nstop: jp stop\nf: push af\n pop af\n ret\n", none),
    ("stack pointer from a register", "rt_start: ld sp,hl\n call f\nstop: jp stop\nf: ret\n", none),
    ("code before the stack pointer is set", "rt_start: push af\n ld sp,0\nstop: jp stop\n", none),
    ("interrupt routine that can be entered again", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n nop\n jp loop\nrt_isr: ei\n nop\n reti\n", none),
    ("interrupt routine that calls a routine with ei", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n nop\n jp loop\nrt_isr: push af\n call enable\n pop af\n reti\nenable: ei\n ret\n", none),
    ("ei two calls below the interrupt routine", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: call fa\n reti\nfa: call fb\n ret\nfb: ei\n ret\n", none),
    ("ei before a conditional return", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: ei\n ret z\n nop\n reti\n", none),
    ("ei before retn", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: ei\n retn\n", none),
    ("interrupt routine ending by a tail jump", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: push af\n jp out\nout: pop af\n ei\n reti\n", some (2, 4)),
    ("interrupt routine calling a routine without ei", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: call hlp\n ei\n reti\nhlp: push af\n pop af\n ret\n", some (4, 6)),
    ("the same two calls deep, no ei", "rt_start: ld sp,0\n jp rt_isr\nloop: ei\n jp loop\nrt_isr: call fa\n ei\n reti\nfa: call fb\n ret\nfb: nop\n ret\n", some (4, 6)),
    ("interrupts without a routine", "rt_start: ld sp,0\nloop: ei\n jp loop\n", none),
    ("computed jump", "rt_start: ld sp,0\n jp (hl)\n", none),
    ("unbalanced pop", "rt_start: ld sp,0\n call f\nstop: jp stop\nf: pop af\n ret\n", none),
    ("stack that grows in a loop", "rt_start: ld sp,0\ngrow: push af\n jp grow\n", none),
    ("running off the end", "rt_start: ld sp,0\n nop\n", none)]
  let mut bad := 0
  for (name, src, want) in cases do
    let items := asm src
    let got := (StackBound.ofItems items).map fun b => (b.main, b.interrupt)
    if items.isEmpty || got != want then
      bad := bad + 1
      IO.println s!"FAIL stack bound: {name}: {got}, expected {want}"
  IO.println s!"z80 stack bound: {cases.length} small images, the unsupported shapes refused; {bad} failures"
  return bad

def main : IO UInt32 := do
  let mut bad ← modelTests
  bad := bad + (← stackBoundTests)
  bad := bad + (← noteAgreeTests)
  bad := bad + (← ownExamples)
  for t in ["sdcc", "make"] do
    if !(← Ember.Tests.TargetTests.installed t) then
      IO.println s!"z80: {t} not installed, the SDCC tests are skipped"
      return if bad == 0 then 0 else 1
  bad := bad + (← examples)
  let r ← IO.Process.output { cmd := "tools/ember/z80-test.sh" }
  IO.print r.stdout
  if r.exitCode != 0 then
    IO.eprint r.stderr
    IO.println "FAIL z80: tools/ember/z80-test.sh"
    bad := bad + 1
  return if bad == 0 then 0 else 1

end Ember.Tests.Z80Tests
