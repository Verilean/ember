import Ember.Z80.Cpu
import Ember.Util.Rand
import Ember.Util.Bytes

/-!
# Ember.Z80.Check — the Z80 model against `z88dk-ticks` (plan M6.1)

Random programs of straight-line instructions (with jumps, calls and
returns whose targets are fixed by construction) are run by both: the
registers must agree before every instruction, the memory at the end,
and the T-state total.  A disagreement is reported with the instruction
and both states.

Not generated: `IN`/`OUT` (the devices differ), `HALT`, the block I/O
instructions, and `LD A,R` — `z88dk-ticks` adds 3 to `R` for a `DD CB`
instruction where the Z80 adds 2 (two opcode fetches), so `R` is tested
by itself in `Tests/Ember/Z80Tests.lean`.

One deliberate difference is masked: after `BIT n,(HL)` the undocumented
flags (bits 3 and 5 of `F`) come from an internal register of the Z80
that this model does not have; the generator follows that instruction
with `OR A`, which defines every flag, and the comparison in between
ignores the two bits.
-/

namespace Ember.Z80.Check
open Ember Ember.Z80

def codeStart : Nat := 0x0100
/-- The programs run with memory below this address write-protected, so
that no stray store can change the code. -/
def ramStart : Nat := 0x4000

abbrev Instr := List UInt8

def lo8 (n : Nat) : UInt8 := UInt8.ofNat (n % 256)
def hi8 (n : Nat) : UInt8 := UInt8.ofNat (n / 256 % 256)

def randByte : RandM UInt8 := do return UInt8.ofNat (← randNat 256)

/-- An address in RAM, away from its ends. -/
def randRam : RandM Nat := randRange 0x4100 0xEF00

/-- `DD`/`FD` prefix or none. -/
def randPrefix : RandM (List UInt8) := do
  let k ← randNat 10
  return if k == 0 then [0xDD] else if k == 1 then [0xFD] else []

/-- A main-page opcode that runs straight on. -/
def plainOp (op : UInt8) : Bool :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  if op == 0x76 then false
  else if op == 0x8C then false                                  -- ADC A,H: 7 T-states in z88dk-ticks, 4 on a Z80
  else if g == 0 && z == 0 && y ≥ 2 then false                    -- DJNZ, JR
  else if g == 3 && (z == 0 || z == 2 || z == 4 || z == 7) then false   -- RET cc, JP cc, CALL cc, RST
  else if op == 0xC9 || op == 0xE9 || op == 0xC3 || op == 0xCD then false
  else if op == 0xD3 || op == 0xDB then false                    -- OUT, IN
  else if op == 0xCB || op == 0xDD || op == 0xED || op == 0xFD then false
  else true

/-- Does the instruction address memory through `(HL)` — under a prefix,
through `(IX+d)`, with a displacement byte? -/
def usesMem (op : UInt8) : Bool :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  (g == 0 && (z == 4 || z == 5 || z == 6) && y == 6) ||
  (g == 1 && (y == 6 || z == 6) && op != 0x76) || (g == 2 && z == 6)

/-- Immediate operand bytes of a main-page opcode. -/
def immBytes (op : UInt8) : Nat :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  let q := y &&& 1
  if g == 0 && z == 1 && q == 0 then 2
  else if g == 0 && z == 2 && y ≥ 4 then 2
  else if g == 0 && z == 6 then 1
  else if g == 3 && z == 6 then 1
  else 0

def genPlain : RandM (List Instr) := do
  let mut op ← randByte
  while !plainOp op do op ← randByte
  let mut pre ← randPrefix
  -- `LD IXH,IXL` and `LD IXL,IXH` (and the IY forms): z88dk-ticks takes
  -- the source from the other index register
  if op == 0x65 || op == 0x6C then pre := []
  let mut out := pre ++ [op]
  if !pre.isEmpty && usesMem op then out := out ++ [← randByte]
  for _ in [0:immBytes op] do out := out ++ [← randByte]
  -- `INC`/`DEC` of a memory byte: z88dk-ticks computes the flags from
  -- what was stored, which is not the result in write-protected memory,
  -- so the operand is put in RAM
  if op == 0x34 || op == 0x35 then
    let a ← randRam
    let load : Instr := match pre with
      | [] => [0x21, lo8 a, hi8 a]
      | p => p ++ [0x21, lo8 a, hi8 a]
    return [load, out]
  return [out]

/-- `BIT n,(HL)`, whose undocumented flags are not modelled. -/
def isBitHL (op : UInt8) : Bool := op &&& 0xC7 == 0x46

def genCB : RandM (List Instr) := do
  let pre ← randPrefix
  let op ← randByte
  -- a memory operand is put in RAM (see `genPlain`)
  let a ← randRam
  if pre.isEmpty then
    let i : Instr := [0xCB, op]
    return if isBitHL op then [i, [0xB7]] else if op &&& 7 == 6 then [[0x21, lo8 a, hi8 a], i] else [i]
  else return [pre ++ [0x21, lo8 a, hi8 a], pre ++ [0xCB, ← randByte, op]]

def edOps : Array UInt8 :=
  #[0x44, 0x4A, 0x5A, 0x6A, 0x7A, 0x42, 0x52, 0x62, 0x72, 0x43, 0x53, 0x63, 0x73, 0x4B, 0x5B, 0x6B, 0x7B,
    0x46, 0x56, 0x5E, 0x47, 0x4F, 0x57, 0x67, 0x6F]

def genED : RandM Instr := do
  let op ← randPick edOps
  let nn := (op &&& 0xC7) == 0x43
  if nn then return [0xED, op, ← randByte, ← randByte] else return [0xED, op]

/-- Load a register pair with a RAM address (keeps the memory operands
of later instructions where they have an effect). -/
def genPointer : RandM Instr := do
  let a ← randRam
  let k ← randNat 6
  let nn := [lo8 a, hi8 a]
  return match k with
    | 0 => [0x01] ++ nn
    | 1 => [0x11] ++ nn
    | 2 => [0x21] ++ nn
    | 3 => [0x31] ++ nn
    | 4 => [0xDD, 0x21] ++ nn
    | _ => [0xFD, 0x21] ++ nn

def ldSP : RandM Instr := do
  let a ← randRam
  return [0x31, lo8 a, hi8 a]

/-- Control flow whose every path ends at the next instruction; `pc` is
the address of the first byte. -/
def genFlow (pc : Nat) : RandM (List Instr) := do
  let cc ← randNat 8
  let k ← randNat 12
  let sp ← ldSP
  let rel (n : Nat) : List UInt8 := [lo8 (pc + n), hi8 (pc + n)]
  match k with
  | 0 => return [[0x20 + 8 * UInt8.ofNat (cc % 4), 1], [0x04]]       -- JR cc over INC B
  | 1 => return [[0x18, 1], [0x0C]]                                -- JR over INC C
  | 2 => return [[0x10, 1], [0x14]]                                -- DJNZ over INC D
  | 3 => return [[0xC2 + 8 * UInt8.ofNat cc] ++ rel 4, [0x1C]]        -- JP cc over INC E
  | 4 => return [[0xC3] ++ rel 4, [0x3C]]                           -- JP over INC A
  | 5 => return [sp, [0xC4 + 8 * UInt8.ofNat cc] ++ rel 6]            -- CALL cc to the next instruction
  | 6 => return [sp, [0xCD] ++ rel 6]                               -- CALL
  | 7 =>
    -- LD HL,T; PUSH HL; RET cc; POP HL; T:
    return [sp, [0x21] ++ rel 9, [0xE5], [0xC0 + 8 * UInt8.ofNat cc], [0xE1]]
  | 8 =>
    let ret : List UInt8 := if cc < 3 then [0xC9] else if cc < 6 then [0xED, 0x45] else [0xED, 0x4D]
    return [sp, [0x21] ++ rel (7 + ret.length), [0xE5], ret]
  | 9 => return [sp, [0xC7 + 8 * UInt8.ofNat cc]]                    -- RST: a RET at every vector
  | 10 => return [[0x21] ++ rel 4, [0xE9]]                          -- JP (HL)
  | _ => return [[0xDD, 0x21] ++ rel 6, [0xDD, 0xE9]]               -- JP (IX)

/-- A block instruction with its registers set up: 1 to 5 iterations in RAM. -/
def genBlock : RandM (List Instr) := do
  let n ← randRange 1 5
  let h ← randRam
  let d ← randRam
  let op ← randPick #[0xA0, 0xA8, 0xB0, 0xB8, 0xA1, 0xA9, 0xB1, 0xB9]
  return [[0x01, lo8 n, 0], [0x21, lo8 h, hi8 h], [0x11, lo8 d, hi8 d], [0xED, op]]

/-- A program of about `n` instructions: the image from address 0 (a `RET`
at every `RST` vector, the code from `codeStart`) and the end address. -/
def genProgram (n : Nat) : RandM (ByteArray × Nat) := do
  let mut code : Array UInt8 := #[]
  let emit (code : Array UInt8) (is : List Instr) : Array UInt8 := is.foldl (fun c i => c ++ i.toArray) code
  -- every register pair starts as a RAM pointer
  code := emit code [[0x31, 0x00, 0xF0], [0x21, 0x00, 0x80], [0x01, 0x00, 0x90], [0x11, 0x00, 0xA0],
                     [0xDD, 0x21, 0x00, 0xB0], [0xFD, 0x21, 0x00, 0xC0]]
  let mut count := 0
  while count < n do
    let k ← randNat 100
    let is ← if k < 55 then genPlain
      else if k < 70 then genCB
      else if k < 78 then (fun i => [i]) <$> genED
      else if k < 86 then (fun i => [i]) <$> genPointer
      else if k < 96 then genFlow (codeStart + code.size)
      else genBlock
    code := emit code is
    count := count + is.length
  let mut img := ByteArray.mk (Array.replicate codeStart 0)
  for v in [0:8] do img := img.set! (v * 8) 0xC9
  return (img ++ ByteArray.mk code, codeStart + code.size)

/-! ## Running both -/

structure Regs where
  pc : Nat
  sp : Nat
  af : Nat
  bc : Nat
  de : Nat
  hl : Nat
  ix : Nat
  iy : Nat
  af' : Nat
  bc' : Nat
  de' : Nat
  hl' : Nat
  deriving BEq, Inhabited

def hex4 (n : Nat) : String := Bytes.hex8 (hi8 n) ++ Bytes.hex8 (lo8 n)

def Regs.show (r : Regs) : String :=
  s!"pc={hex4 r.pc} sp={hex4 r.sp} af={hex4 r.af} bc={hex4 r.bc} de={hex4 r.de} hl={hex4 r.hl} " ++
  s!"ix={hex4 r.ix} iy={hex4 r.iy} af'={hex4 r.af'} bc'={hex4 r.bc'} de'={hex4 r.de'} hl'={hex4 r.hl'}"

def regsOf (s : Cpu) : Regs :=
  { pc := s.pc.toNat, sp := s.sp.toNat, af := s.af.toNat, bc := s.bc.toNat, de := s.de.toNat, hl := s.hl.toNat,
    ix := s.ix.toNat, iy := s.iy.toNat, af' := (Cpu.mk16 s.a' s.f').toNat, bc' := (Cpu.mk16 s.b' s.c').toNat,
    de' := (Cpu.mk16 s.d' s.e').toNat, hl' := (Cpu.mk16 s.h' s.l').toNat }

/-- The four hex digits after `key` in a line of the ticks trace. -/
def field (line key : String) : Option Nat := do
  let rest ← (line.splitOn key)[1]?
  let b ← Bytes.ofHex (rest.take 4).toString
  if b.size != 2 then none else some (b[0]!.toNat * 256 + b[1]!.toNat)

/-- The register lines of `z88dk-ticks -trace`: the state before each instruction. -/
def parseTrace (out : String) : Array Regs := Id.run do
  let mut rs : Array Regs := #[]
  let mut cur : Option Regs := none
  for line in out.splitOn "\n" do
    if line.startsWith "pc=" then
      cur := do
        return { pc := ← field line "pc=", sp := 0, af := ← field line "af=", bc := ← field line "bc=",
                 de := ← field line "de=", hl := ← field line "hl=", ix := ← field line "ix=",
                 iy := ← field line "iy=", af' := 0, bc' := 0, de' := 0, hl' := 0 }
    else if line.startsWith "sp=" then
      if let some r := cur then
        let full : Option Regs := do
          return { r with sp := ← field line "sp=", af' := ← field line "af'=", bc' := ← field line "bc'=",
                          de' := ← field line "de'=", hl' := ← field line "hl'=" }
        if let some f := full then rs := rs.push f
      cur := none
  return rs

def ticksAvailable : IO Bool := do
  try
    let r ← IO.Process.output { cmd := "z88dk-ticks", args := #[] }
    return r.stdout.contains "z88dk-ticks" || r.stderr.contains "z88dk-ticks"
  catch _ => return false

/-- The model's initial state: as `z88dk-ticks` starts. -/
def initial (img : ByteArray) : Cpu :=
  ({ f := 0x40, f' := 0x40, pc := UInt16.ofNat codeStart, ramStart := UInt16.ofNat ramStart } : Cpu).load 0 img

/-- Run one program on both; `none` when they agree. -/
def checkProgram (dir : System.FilePath) (img : ByteArray) (stop : Nat) : IO (Option String) := do
  let bin := dir / "prog.bin"
  let dump := dir / "mem.bin"
  IO.FS.writeBinFile bin img
  let r ← IO.Process.output { cmd := "z88dk-ticks", args := #["-mz80", "-trace", "-rom", "4000", "-pc", "100",
    "-start", "100", "-end", hex4 stop, "-output", dump.toString, bin.toString] }
  let ticks := parseTrace r.stdout
  if ticks.isEmpty then return some s!"no trace from z88dk-ticks: {r.stdout.take 300}{r.stderr.take 300}"
  let cycles := ((r.stdout.splitOn "\n").filter (· != "")).getLast?.bind (·.trimAscii.toString.toNat?)
  let mut s := initial img
  let mut k := 0
  let instrAt (s : Cpu) : String :=
    " ".intercalate ((List.range 4).map fun i => Bytes.hex8 (s.rd (s.pc + UInt16.ofNat i)))
  let mut prev := ""
  let mut maskXY := false
  -- (pc, T-states) after every instruction, to locate a difference in the totals
  let mut marks : Array (Nat × Nat × String) := #[]
  while s.pc.toNat != stop do
    if k ≥ ticks.size then return some s!"z88dk-ticks stopped after {k} instructions, the model is at pc={hex4 s.pc.toNat}"
    let mine := regsOf s
    let noXY (r : Regs) : Regs := if maskXY then { r with af := r.af / 64 * 64 + r.af % 8 + (r.af / 16 % 2) * 16 } else r
    maskXY := s.rd s.pc == 0xCB && isBitHL (s.rd (s.pc + 1))
    if noXY mine != noXY ticks[k]! then
      return some s!"registers differ before instruction {k}, after executing {prev}\n  model {mine.show}\n  ticks {ticks[k]!.show}"
    prev := s!"[{hex4 s.pc.toNat}] {instrAt s}"
    s := s.step
    marks := marks.push (s.pc.toNat, s.cycles.toNat, prev)
    k := k + 1
    if k > 200000 then return some "the model did not reach the end address"
  if k != ticks.size then return some s!"the model ran {k} instructions, z88dk-ticks {ticks.size}"
  match cycles with
  | some c =>
    if c != s.cycles.toNat then
      -- rerun z88dk-ticks to each address reached for the first time,
      -- up to the first one where the totals differ
      let mut seen : Array Nat := #[]
      for (pc, cyc, ins) in marks do
        if seen.contains pc then continue
        seen := seen.push pc
        let r ← IO.Process.output { cmd := "z88dk-ticks", args := #["-mz80", "-rom", "4000", "-pc", "100",
          "-start", "100", "-end", hex4 pc, bin.toString] }
        let t := ((r.stdout.splitOn "\n").filter (· != "")).getLast?.bind (·.trimAscii.toString.toNat?)
        if t != some cyc then
          return some s!"T-states differ after {ins}: model {cyc}, z88dk-ticks {t}"
      return some s!"T-states differ: model {s.cycles}, z88dk-ticks {c}"
  | none => return some s!"no cycle count from z88dk-ticks: {r.stdout.takeEnd 100}"
  let mem ← IO.FS.readBinFile dump
  -- the 64 KB of memory come first in the dump, the registers after them
  if mem.size < 65536 then return some s!"memory dump of {mem.size} bytes"
  for a in [0:65536] do
    if mem[a]! != s.mem[a]! then
      return some s!"memory differs at {hex4 a}: model {Bytes.hex8 s.mem[a]!}, z88dk-ticks {Bytes.hex8 mem[a]!}"
  return none

structure Summary where
  programs : Nat := 0
  instructions : Nat := 0
  failures : Nat := 0

/-- `count` random programs of `len` instructions each. -/
def run (count len seed : Nat) (verbose := true) : IO Summary := do
  let dir : System.FilePath := ".lake/ember-z80-check"
  IO.FS.createDirAll dir
  let mut rng := Rng.ofSeed seed
  let mut sum : Summary := {}
  for i in [0:count] do
    let ((img, stop), r) := (genProgram len).run rng
    rng := r
    sum := { sum with programs := sum.programs + 1, instructions := sum.instructions + len }
    match ← checkProgram dir img stop with
    | none => pure ()
    | some why =>
      sum := { sum with failures := sum.failures + 1 }
      if verbose then
        IO.println s!"FAIL program {i} (seed {seed}): {why}"
        IO.FS.writeBinFile (dir / s!"fail-{seed}-{i}.bin") img
  return sum

end Ember.Z80.Check
