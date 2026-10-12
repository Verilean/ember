import Ember.Z80.Cpu
import Ember.Trace.Event

/-!
# Ember.Z80.Machine — a small Z80 computer around the CPU model (M4z.0)

An RC2014-class machine, as far as the Ember runtime (`runtime/z80`)
uses it: ROM below `ramStart`, RAM above, interrupt mode 1, and

| Port | Device |
|---|---|
| `0x80` | 68B50 ACIA control (write) / status (read) |
| `0x81` | ACIA data |
| `0xC0` | debug output: a byte written here is a character of the trace |
| `0xC1` | tick status: bit 0 set when a tick is pending; reading clears it |

The ACIA is the SLIP link.  Bytes queued by the host arrive one per
`rxGap` T-states while the target holds RTS low (control bits 6–5 ≠ 10);
a byte that arrives while the previous one is still unread is lost and
counted (`overruns`), as on the chip.  A transmitted byte keeps TDRE low
for `txTime` T-states.  The interrupt line is the ACIA's (RDRF with the
receive interrupt enabled) or the tick's.

`z88dk-ticks` cannot raise an interrupt when a byte arrives, which is why
this machine exists (plan M4z.0); its CPU is checked against
`z88dk-ticks` (`Ember.Z80.Check`).

A second set of ports is the *test harness* (`runtime/z80/harness.c`),
for running any Ember program exactly as the interpreter and the host
harness do — an input oracle and an event recorder, no interrupts:

| Port | |
|---|---|
| `0xD0` in | 1 while input remains |
| `0xD1` in | take the next input item: 0 a byte, 1 a tick, 2 nothing |
| `0xD2` in | the byte just taken |
| `0xD3` out | a byte of the frame being transmitted |
| `0xD4` out | end of the frame |
| `0xD5` out | drop, with its code |
| `0xD6` out | note, with its code |
| `0xD7` out | trap |
| `0xD8` in | which program of the image to run |
| `0xD9` in | 1 when the position in the input has moved since this port was last read |
-/

namespace Ember.Z80
open Ember.Trace (Input)

/-- What the test harness recorded. -/
inductive HEvent where
  | tx (bytes : ByteArray)
  | drop (code : UInt8)
  | note (code : UInt8)
  | trap
  deriving Inhabited

structure Machine where
  cpu : Cpu := {}
  /-- ACIA control register. -/
  ctrl : UInt8 := 0
  rdr : UInt8 := 0
  rdrf : Bool := false
  ovrn : Bool := false
  txBusyUntil : UInt64 := 0
  /-- Bytes from the host not yet delivered. -/
  rxQueue : ByteArray := ByteArray.empty
  rxPos : Nat := 0
  /-- Earliest time of the next delivery. -/
  rxNext : UInt64 := 0
  /-- Bytes the host may still send after RTS went high (one in flight). -/
  rtsGrace : Nat := 1
  tickPending : Bool := false
  /-- Bytes transmitted on the ACIA, and written to the debug port. -/
  tx : ByteArray := ByteArray.empty
  dbg : ByteArray := ByteArray.empty
  overruns : Nat := 0
  interrupts : Nat := 0
  /-- T-states per received byte and per transmitted byte: 115 200 baud at 7.3728 MHz. -/
  rxGap : UInt64 := 640
  txTime : UInt64 := 640
  /-- Times the target raised RTS. -/
  holds : Nat := 0
  /-- The test harness: inputs, position (item, byte within a chunk), the
  item last consumed, and the events with the item they belong to. -/
  harness : Bool := false
  inputs : Array Input := #[]
  ipos : Nat := 0
  ioff : Nat := 0
  cur : Nat := 0
  latch : UInt8 := 0
  /-- The position in the input (item, byte) when port `0xD9` was last read. -/
  mark : Nat × Nat := (0, 0)
  program : UInt8 := 0
  frame : ByteArray := ByteArray.empty
  events : Array (Nat × HEvent) := #[]
  deriving Inhabited

namespace Machine

@[inline] def rie (m : Machine) : Bool := m.ctrl &&& 0x80 != 0
/-- RTS high: the target asks the host to stop sending. -/
@[inline] def rtsHigh (m : Machine) : Bool := m.ctrl &&& 0x60 == 0x40
@[inline] def irq (m : Machine) : Bool := (m.rdrf && m.rie) || m.tickPending

@[inline] def status (m : Machine) : UInt8 :=
  (if m.rdrf then 0x01 else 0) ||| (if m.cpu.cycles ≥ m.txBusyUntil then 0x02 else 0) |||
  (if m.ovrn then 0x20 else 0) ||| (if m.rdrf && m.rie then 0x80 else 0)

/-- Skip exhausted chunks (as `normalize` in the host harness, and as
`Ember.Lang.World.normalize`: a recursion, so that proofs can follow it). -/
def normalize (m : Machine) : Machine :=
  if h : m.ipos < m.inputs.size then
    match m.inputs[m.ipos] with
    | .rx b => if m.ioff ≥ b.size then normalize { m with ipos := m.ipos + 1, ioff := 0 } else m
    | .tick => m
  else m
termination_by m.inputs.size - m.ipos

/-- Kind of the next input item (0 byte, 1 tick, 2 nothing) and its byte. -/
def peekInput (m : Machine) : UInt8 × UInt8 :=
  let m := m.normalize
  if m.ipos ≥ m.inputs.size then (2, 0)
  else match m.inputs[m.ipos]! with
    | .tick => (1, 0)
    | .rx b => (0, b[m.ioff]!)

def takeInput (m : Machine) : Machine :=
  let m := m.normalize
  if m.ipos ≥ m.inputs.size then m
  else match m.inputs[m.ipos]! with
    | .tick => ({ m with cur := m.ipos, ipos := m.ipos + 1, ioff := 0 }).normalize
    | .rx b => ({ m with cur := m.ipos, latch := b[m.ioff]!, ioff := m.ioff + 1 }).normalize

/-- The effect of the I/O the CPU has just done. -/
def applyIo (m : Machine) : Machine :=
  match m.cpu.io with
  | .none => m
  | .read port =>
    match port.toUInt8 with
    | 0x81 => { m with rdrf := false, ovrn := false }
    | 0xC1 => { m with tickPending := false }
    | 0xD1 => m.takeInput
    | 0xD9 => { m with mark := (m.ipos, m.ioff) }
    | _ => m
  | .write port v =>
    match port.toUInt8 with
    | 0xD3 => { m with frame := m.frame.push v }
    | 0xD4 => { m with events := m.events.push (m.cur, .tx m.frame), frame := ByteArray.empty }
    | 0xD5 => { m with events := m.events.push (m.cur, .drop v) }
    | 0xD6 => { m with events := m.events.push (m.cur, .note v) }
    | 0xD7 => { m with events := m.events.push (m.cur, .trap) }
    | 0x80 =>
      if v &&& 3 == 3 then { m with ctrl := v, rdrf := false, ovrn := false }      -- master reset
      else { m with ctrl := v, rtsGrace := if v &&& 0x60 == 0x40 then m.rtsGrace else 1,
                    holds := if v &&& 0x60 == 0x40 && !m.rtsHigh then m.holds + 1 else m.holds }
    | 0x81 => { m with tx := m.tx.push v, txBusyUntil := m.cpu.cycles + m.txTime }
    | 0xC0 => { m with dbg := m.dbg.push v }
    | _ => m

/-- Is a byte from the host due? -/
@[inline] def rxDue (m : Machine) : Bool :=
  m.rxPos < m.rxQueue.size && m.cpu.cycles ≥ m.rxNext && (!m.rtsHigh || m.rtsGrace > 0)

def deliver (m : Machine) : Machine :=
  let b := m.rxQueue[m.rxPos]!
  let m := { m with rxPos := m.rxPos + 1, rxNext := m.cpu.cycles + m.rxGap,
                    rtsGrace := if m.rtsHigh then m.rtsGrace - 1 else m.rtsGrace }
  if m.rdrf then { m with ovrn := true, overruns := m.overruns + 1 }
  else { m with rdr := b, rdrf := true }

/-- Apply `f` to the CPU, in place. -/
@[inline] def modifyCpu (m : Machine) (f : Cpu → Cpu) : Machine :=
  let c := m.cpu
  let m := { m with cpu := Cpu.hole }
  { m with cpu := f c }

/-- One step: deliver a due byte, take a pending interrupt, or execute an
instruction.  A halted CPU waiting for a byte that is still on the wire
skips the wait. -/
def step (m : Machine) : Machine :=
  let m := if m.rxDue then m.deliver else m
  if m.irq && m.cpu.interruptible then
    let n := m.interrupts + 1
    { (m.modifyCpu (·.interrupt)) with interrupts := n }
  else if m.cpu.halted && m.rxPos < m.rxQueue.size && m.cpu.cycles < m.rxNext && !m.rtsHigh then
    let t := m.rxNext
    m.modifyCpu fun c => { c with cycles := t }
  else
    let st := m.status
    let rdr := m.rdr
    let tk : UInt8 := if m.tickPending then 1 else 0
    if m.harness then
      let (kind, _) := m.peekInput
      let latch := m.latch
      let prog := m.program
      let moved : UInt8 := if (m.ipos, m.ioff) != m.mark then 1 else 0
      (m.modifyCpu fun c => c.step fun p =>
        match p.toUInt8 with
        | 0xD0 => if kind == 2 then 0 else 1
        | 0xD1 => kind
        -- the byte taken by the read of 0xD1 that came before
        | 0xD2 => latch
        | 0xD8 => prog
        | 0xD9 => moved
        | _ => 0xFF).applyIo
    else
      (m.modifyCpu fun c => c.step fun p =>
        match p.toUInt8 with
        | 0x80 => st
        | 0x81 => rdr
        | 0xC1 => tk
        | _ => 0xFF).applyIo

/-- Nothing more will happen without the host: the CPU is halted, no
interrupt is pending or possible, and every queued byte was delivered. -/
def idle (m : Machine) : Bool :=
  m.cpu.halted && !m.irq && m.rxPos ≥ m.rxQueue.size

/-- Halted with interrupts disabled, or RTS held high with nothing to
read: no input can wake it. -/
def dead (m : Machine) : Bool :=
  m.cpu.halted && (!m.cpu.iff1 || (!m.irq && m.rxPos < m.rxQueue.size && m.rtsHigh && m.rtsGrace == 0))

/-- Run until idle (or dead); `none` when `maxSteps` did not suffice. -/
def runIdle (m : Machine) (maxSteps : Nat := 50000000) : Machine × Bool := Id.run do
  let mut m := m
  for _ in [0:maxSteps] do
    if m.idle || m.dead then return (m, true)
    m := m.step
  return (m, false)

def send (m : Machine) (b : ByteArray) : Machine :=
  { m with rxQueue := (m.rxQueue.extract m.rxPos m.rxQueue.size) ++ b, rxPos := 0,
           rxNext := max m.rxNext m.cpu.cycles }

def tick (m : Machine) : Machine := { m with tickPending := true }

/-- Take what was transmitted since the last call. -/
def takeTx (m : Machine) : ByteArray × Machine := (m.tx, { m with tx := ByteArray.empty })
def takeDbg (m : Machine) : String × Machine :=
  (String.ofList (m.dbg.toList.map fun b => Char.ofNat b.toNat), { m with dbg := ByteArray.empty })

/-! ## Loading an image -/

def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The data records of an Intel HEX file: (address, bytes). -/
def parseIhx (text : String) : Except String (Array (Nat × ByteArray)) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    let cs := (line.trimAscii.toString).toList
    match cs with
    | ':' :: rest =>
      let mut bytes : Array UInt8 := #[]
      let mut r := rest
      while r.length ≥ 2 do
        match hexNibble r[0]!, hexNibble r[1]! with
        | some h, some l => bytes := bytes.push (UInt8.ofNat (h * 16 + l))
        | _, _ => throw s!"bad hex in {line}"
        r := r.drop 2
      if bytes.size < 5 then throw s!"short record {line}"
      let n := bytes[0]!.toNat
      if bytes.size != n + 5 then throw s!"record length in {line}"
      if bytes[3]! == 0 then
        out := out.push (bytes[1]!.toNat * 256 + bytes[2]!.toNat, ByteArray.mk (bytes.extract 4 (4 + n)))
    | _ => pure ()
  return out

/-- A machine with the image in memory, ROM below `ramStart`. -/
def ofIhx (text : String) (ramStart : Nat := 0x8000) : Except String Machine := do
  let recs ← parseIhx text
  let mut c : Cpu := {}
  for (a, b) in recs do c := c.load a b
  return { cpu := { c with ramStart := UInt16.ofNat ramStart } }

/-- Bytes of the image, and its end: the ROM a board would need. -/
def ihxExtent (text : String) : Except String (Nat × Nat) := do
  let recs ← parseIhx text
  return (recs.foldl (fun n r => n + r.2.size) 0, recs.foldl (fun n r => max n (r.1 + r.2.size)) 0)

end Machine
end Ember.Z80
