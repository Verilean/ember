import Ember.Proof.Z80Machine
import Ember.Z80.Target

/-!
# Ember.Proof.Z80SimCheck — the relation on small machines (plan M7.3)

`Sim` ties the machine the tests run to the proofs' machine (`hbus`,
`hdev`).  Here both are run side by side on small programs and inputs —
none, a tick, an empty chunk, bytes and a tick — and after every step
the two are compared as `Sim` compares them: the input position, the
events (`evsOf`), the trap (`trapIn` against `World.trapped`).  The
programs read all the input, write notes (one of the largest value,
`0xFFFFFFFF`), and one writes the trap port.  And `Target.runHarness`
prints a trap as its last line (when there is an input), which `stackH_no_trap` rules out for
the stack.  Checks (`#guard`), not proofs.
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember Ember.Z80 Ember.Z80.Cpu
open Ember.Trace (Input Line Event)

/-- A context with the names of two notes. -/
def ckCtx : IR.Ctx := { prog := default, layout := default, notes := ["first", "second"] }

def ckMachine (bytes : List UInt8) (inputs : Array Input) : Machine :=
  { cpu := { (({} : Cpu).load 0 (ByteArray.mk bytes.toArray)) with ramStart := 0x8000 },
    harness := true, inputs := inputs, program := 0 }

def ckWorld (inputs : Array Input) : HW := ({ inputs, framed := false }, 0, (0, 0), (0, 0))

/-- The two compared as `Sim` compares them. -/
def ckRel (m : Machine) (w : HW) : Bool :=
  m.inputs.size == w.1.inputs.size && m.ipos == w.1.pos && m.ioff == w.1.off && m.cur == w.1.cur &&
    m.latch == w.2.1 && m.mark == w.2.2.1 && m.nval == w.2.2.2 && m.frame.toList == w.1.frame.toList &&
    evsOf ckCtx m.events == w.1.events && trapIn m.events == w.1.trapped

/-- Run both `n` steps, the relation checked after each; the machine's
CPU steps as the proofs' does.  The machine and world at the end. -/
def ckRun (dev : HW → IoEvent → HW) : Nat → Machine → HW → Option (Machine × HW)
  | 0, m, w => some (m, w)
  | n + 1, m, w =>
    let c := m.cpu.step (hbus w)
    let m' := m.step
    let w' := dev w c.io
    if m'.cpu.pc == c.pc && m'.cpu.halted == c.halted && ckRel m' w' then ckRun dev n m' w' else none

/-- `in a,(0xD1)` five times (all the input of the cases below and then
the end), a note of `0xFFFFFFFF` (`first`), a note of `0x01020304`
(`second`), then `halt` — or with `trap`, `out (0xD7),a` first. -/
def ckProg (trap : Bool) : List UInt8 :=
  [0xF3] ++ (List.replicate 5 [0xDB, 0xD1]).flatten ++
  [0x3E, 0xFF, 0xD3, 0xDA, 0xD3, 0xDA, 0xD3, 0xDA, 0xD3, 0xDA, 0x3E, 0x00, 0xD3, 0xD6] ++
  [0x3E, 0x04, 0xD3, 0xDA, 0x3E, 0x03, 0xD3, 0xDA, 0x3E, 0x02, 0xD3, 0xDA, 0x3E, 0x01, 0xD3, 0xDA,
   0x3E, 0x01, 0xD3, 0xD6] ++
  (if trap then [0x3E, 0x00, 0xD3, 0xD7] else []) ++ [0x76]

def ckInputs : List (Array Input) :=
  [#[], #[.tick], #[.rx .empty], #[.rx (ByteArray.mk #[1, 2]), .tick]]

/-- The run reaches the halt with the relation kept, and at the end the
notes and the trap are as written. -/
def ckCaseWith (dev : HW → IoEvent → HW) (trap : Bool) (inputs : Array Input) : Bool :=
  match ckRun dev 60 (ckMachine (ckProg trap) inputs) (ckWorld inputs) with
  | some (m, w) =>
    m.cpu.halted && w.1.trapped == trap && trapIn m.events == trap &&
      (w.1.events.toList.map (·.2)) == [.note "first 4294967295", .note "second 16909060"]
  | none => false

def ckCase := ckCaseWith (hdev ckCtx)

#guard ckInputs.all (ckCase false)
#guard ckInputs.all (ckCase true)

-- The check sees the trap: with the device as it was before the trap was
-- recorded (a write to `0xD7` ignored), the relation fails at that write.
def hdevNoTrap (w : HW) : IoEvent → HW
  | .write p v => if lo p = 0xD7 then w else hdev ckCtx w (.write p v)
  | e => hdev ckCtx w e

#guard ckInputs.all (ckCaseWith hdevNoTrap false)
#guard ckInputs.all fun i => !ckCaseWith hdevNoTrap true i

/-- The trace `runHarness` prints: a trap is its last line. -/
def ckLines (trap : Bool) (inputs : Array Input) : Option (List Line) :=
  (Target.runHarness (ckMachine (ckProg trap) #[]) 0 {} inputs #[] #["first", "second"] 1000).toOption.map
    (·.lines.toList)

-- with an input, the trap is the last line; with none, `runHarness` prints no line at all
-- (it keeps the trap only when recorded at an input, `j < inputs.size`)
#guard (ckInputs.drop 1).all fun i => ((ckLines true i).bind (·.getLast?)).map (·.ev) == some (.note "trap (z80)")
#guard ckLines true #[] == some []
#guard ckInputs.all fun i => ((ckLines false i).map fun ls => ls.any (·.ev == .note "trap (z80)")) == some false
#guard (ckLines false #[.rx (ByteArray.mk #[1, 2]), .tick]).map (·.map (·.ev)) ==
  some [.rx (ByteArray.mk #[1, 2]), .tick, .note "first 4294967295", .note "second 16909060"]

-- The proofs' machine records a write to `0xD7` only: the other ports
-- leave `trapped` as it was.
#guard (hdev ckCtx (ckWorld #[]) (.write 0x00D7 0)).1.trapped
#guard (List.range 256).all fun p => p == 0xD7 ||
  !(hdev ckCtx (ckWorld #[]) (.write (UInt16.ofNat p) 0)).1.trapped

end Ember.Proof.Z80Gen.LoopH
