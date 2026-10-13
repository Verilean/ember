import Ember.Z80.Machine
import Ember.Trace.Text
import Ember.Trace.Diff

/-!
# Ember.Z80.Target — an Ember image on the Z80 machine, driven by a trace

The host side of plan M4z: inputs go in through the ACIA (`rx` chunks)
and the tick device, and what comes back is cut into trace events with
the lines the runtime writes on the debug port (`tx N` after each frame,
`drop reason=…`, `note …`).  A step is over when the machine is idle:
halted, with every byte delivered and no interrupt pending.
-/

namespace Ember.Z80.Target
open Ember Ember.Trace

/-- Events since the last call: debug lines in order, each `tx N` taking
the next `N` transmitted bytes. -/
def collect (m : Machine) : Except String (Machine × List Event) := do
  let (txb, m) := m.takeTx
  let (dbg, m) := m.takeDbg
  let mut evs : List Event := []
  let mut pos := 0
  for line in dbg.splitOn "\n" do
    if line.isEmpty then continue
    if line.startsWith "tx " then
      let some n := (line.drop 3).toString.toNat? | throw s!"bad debug line: {line}"
      if pos + n > txb.size then throw s!"`{line}` but only {txb.size - pos} bytes were transmitted"
      evs := evs ++ [.tx (txb.extract pos (pos + n))]
      pos := pos + n
    else if line.startsWith "drop reason=" then evs := evs ++ [.drop (line.drop 12).toString]
    else if line.startsWith "note " then evs := evs ++ [.note (line.drop 5).toString]
    else throw s!"unexpected debug line: {line}"
  if pos != txb.size then throw s!"{txb.size - pos} bytes transmitted outside any frame"
  return (m, evs)

/-- Run to idle and collect; an error when the image stops for good. -/
def settle (m : Machine) (maxSteps : Nat) : Except String (Machine × List Event) := do
  let (m, done) := m.runIdle maxSteps
  let (m', evs) ← collect m
  if !done then throw s!"not idle after {maxSteps} machine steps (pc={m.cpu.pc})"
  if evs.any (fun e => match e with | .note t => isTrapNote t | _ => false) then
    throw s!"trap: {evs.filterMap fun e => match e with | .note t => some t | _ => none}"
  if m.dead then throw s!"the CPU halted with nothing able to wake it (pc={m.cpu.pc}, iff1={m.cpu.iff1})"
  return (m', evs)

/-- Reset and run the start-up code until the image waits for input. -/
def boot (m : Machine) (maxSteps : Nat := 2000000) : Except String Machine := do
  let (m, _) ← settle m maxSteps
  return m

def feed (m : Machine) (i : Input) (maxSteps : Nat := 50000000) : Except String (Machine × List Event) :=
  match i with
  | .rx b => settle (m.send b) maxSteps
  | .tick => settle m.tick maxSteps

structure Result where
  trace : Trace
  error : Option String := none
  machine : Machine

/-- Replay inputs on a booted machine: the target's trace. -/
def replay (m : Machine) (h : Header) (inputs : Array Input) : Result := Id.run do
  let mut m := m
  let mut lines : Array Line := #[]
  for i in [0:inputs.size] do
    let inp := inputs[i]!
    lines := lines.push ⟨i, match inp with | .rx b => .rx b | .tick => .tick⟩
    match feed m inp with
    | .ok (m', evs) =>
      m := m'
      for e in evs do lines := lines.push ⟨i, e⟩
    | .error e =>
      return { trace := { header := h, lines := lines.push ⟨i, .note s!"trap {e}"⟩ }, error := some e, machine := m }
  return { trace := { header := h, lines }, machine := m }

/-! ## The test harness (`runtime/z80/harness.c`) -/

/-- Run program `k` of a harness image on the inputs, as the interpreter's
`runMachine` and the host harness do; the trace they would write. -/
def runHarness (m : Machine) (k : Nat) (h : Header) (inputs : Array Input)
    (dropNames noteNames : Array String) (maxSteps : Nat := 200000000) : Except String Trace := do
  let mut m := { m with harness := true, inputs := inputs, program := UInt8.ofNat k }
  let mut n := 0
  while !m.cpu.halted do
    if n ≥ maxSteps then throw s!"still running after {maxSteps} instructions (pc={m.cpu.pc})"
    m := m.step
    n := n + 1
  let mut lines : Array Line := #[]
  let mut trapped := false
  for i in [0:inputs.size] do
    lines := lines.push ⟨i, match inputs[i]! with | .rx b => .rx b | .tick => .tick⟩
    for (j, e) in m.events do
      if j == i then
        match e with
        | .tx b => lines := lines.push ⟨i, .tx b⟩
        | .drop c => lines := lines.push ⟨i, .drop (dropNames.getD c.toNat s!"code-{c}")⟩
        | .note c v => lines := lines.push ⟨i, .note s!"{noteNames.getD c.toNat s!"note-{c}"} {v}"⟩
        | .trap => trapped := true
  if trapped then lines := lines.push ⟨m.cur, .note "trap (z80)"⟩
  return { header := h, lines }

end Ember.Z80.Target
