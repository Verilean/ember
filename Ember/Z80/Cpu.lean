/-!
# Ember.Z80.Cpu — a model of the Z80 (plan M6.1, used from M4z on)

The documented instruction set, the undocumented instructions compilers
and other emulators agree on (`IXH`/`IXL`, `SLL`, the `DD CB` forms that
also store into a register), all flags including the two undocumented
ones (bits 3 and 5 of `F`) for everything but the block I/O
instructions, the refresh register, interrupt modes 0–2 and T-state
counts.

`step` executes one instruction and is a total function of the state:
memory is a 64 KB array, and I/O is kept outside — an `IN` reads its
value from the function passed to `step`, and every `IN`/`OUT` is
reported in `io` so that the machine around the CPU (`Ember.Z80.Machine`)
can apply its effect on the devices.

Checked against `z88dk-ticks` on random instruction sequences: every
register after every instruction, the memory at the end and the T-state
total (`Tests/Ember/Z80Tests.lean`).
-/

namespace Ember.Z80

/-- What an instruction did on the I/O bus. -/
inductive IoEvent where
  | none
  | read (port : UInt16)
  | write (port : UInt16) (value : UInt8)
  deriving Inhabited, BEq, Repr

structure Cpu where
  a : UInt8 := 0
  f : UInt8 := 0
  b : UInt8 := 0
  c : UInt8 := 0
  d : UInt8 := 0
  e : UInt8 := 0
  h : UInt8 := 0
  l : UInt8 := 0
  a' : UInt8 := 0
  f' : UInt8 := 0
  b' : UInt8 := 0
  c' : UInt8 := 0
  d' : UInt8 := 0
  e' : UInt8 := 0
  h' : UInt8 := 0
  l' : UInt8 := 0
  ix : UInt16 := 0
  iy : UInt16 := 0
  sp : UInt16 := 0
  pc : UInt16 := 0
  i : UInt8 := 0
  r : UInt8 := 0
  iff1 : Bool := false
  iff2 : Bool := false
  im : UInt8 := 0
  halted : Bool := false
  /-- `EI` takes effect after the instruction that follows it. -/
  eiDelay : Bool := false
  /-- T-states executed. -/
  cycles : UInt64 := 0
  io : IoEvent := .none
  /-- Memory below this address is ROM: writes to it are ignored. -/
  ramStart : UInt16 := 0
  mem : ByteArray := ByteArray.mk (Array.replicate 65536 0)
  deriving Inhabited

namespace Cpu

/-! ## Flags -/

def FC : UInt8 := 0x01
def FN : UInt8 := 0x02
def FPV : UInt8 := 0x04
def FX : UInt8 := 0x08
def FH : UInt8 := 0x10
def FY : UInt8 := 0x20
def FZ : UInt8 := 0x40
def FS : UInt8 := 0x80
def FXY : UInt8 := 0x28

@[inline] def flag (s : Cpu) (m : UInt8) : Bool := s.f &&& m != 0

@[inline] def bit (c : Bool) (m : UInt8) : UInt8 := if c then m else 0

/-- Even parity. -/
def parity (v : UInt8) : Bool :=
  let v := v ^^^ (v >>> 4)
  let v := v ^^^ (v >>> 2)
  let v := v ^^^ (v >>> 1)
  v &&& 1 == 0

/-- `S`, `Z` and the undocumented copies of bits 5 and 3 of a result. -/
@[inline] def szxy (v : UInt8) : UInt8 := (v &&& 0xA8) ||| bit (v == 0) FZ

@[inline] def szxyp (v : UInt8) : UInt8 := szxy v ||| bit (parity v) FPV

/-! ## Memory and registers -/

@[inline] def rd (s : Cpu) (a : UInt16) : UInt8 := s.mem.get! a.toNat

/-- Write a byte (ignored in ROM).  The array is taken out of the record
first so that it is updated in place. -/
@[inline] def wr (s : Cpu) (a : UInt16) (v : UInt8) : Cpu :=
  if a < s.ramStart then s
  else
    let m := s.mem
    let s := { s with mem := ByteArray.empty }
    { s with mem := m.set! a.toNat v }

@[inline] def rd16 (s : Cpu) (a : UInt16) : UInt16 :=
  (s.rd a).toUInt16 ||| ((s.rd (a + 1)).toUInt16 <<< 8)

@[inline] def wr16 (s : Cpu) (a : UInt16) (v : UInt16) : Cpu :=
  (s.wr a v.toUInt8).wr (a + 1) (v >>> 8).toUInt8

@[inline] def mk16 (hi lo : UInt8) : UInt16 := (hi.toUInt16 <<< 8) ||| lo.toUInt16
@[inline] def hi (v : UInt16) : UInt8 := (v >>> 8).toUInt8
@[inline] def lo (v : UInt16) : UInt8 := v.toUInt8

@[inline] def bc (s : Cpu) : UInt16 := mk16 s.b s.c
@[inline] def de (s : Cpu) : UInt16 := mk16 s.d s.e
@[inline] def hl (s : Cpu) : UInt16 := mk16 s.h s.l
@[inline] def af (s : Cpu) : UInt16 := mk16 s.a s.f
@[inline] def setBC (s : Cpu) (v : UInt16) : Cpu := { s with b := hi v, c := lo v }
@[inline] def setDE (s : Cpu) (v : UInt16) : Cpu := { s with d := hi v, e := lo v }
@[inline] def setHL (s : Cpu) (v : UInt16) : Cpu := { s with h := hi v, l := lo v }

@[inline] def tick (s : Cpu) (n : UInt64) : Cpu := { s with cycles := s.cycles + n }

@[inline] def fetch (s : Cpu) : UInt8 × Cpu := (s.rd s.pc, { s with pc := s.pc + 1 })

@[inline] def fetch16 (s : Cpu) : UInt16 × Cpu := (s.rd16 s.pc, { s with pc := s.pc + 2 })

/-- One more opcode fetch: the low seven bits of `R` count them. -/
@[inline] def bumpR (s : Cpu) : Cpu := { s with r := (s.r &&& 0x80) ||| ((s.r + 1) &&& 0x7F) }

@[inline] def push (s : Cpu) (v : UInt16) : Cpu :=
  let sp := s.sp - 2
  ({ s with sp := sp }).wr16 sp v

@[inline] def pop (s : Cpu) : UInt16 × Cpu := (s.rd16 s.sp, { s with sp := s.sp + 2 })

@[inline] def sext (d : UInt8) : UInt16 := if d < 0x80 then d.toUInt16 else d.toUInt16 ||| 0xFF00

/-- Which register pair plays `HL`: selected by the `DD`/`FD` prefixes. -/
inductive Idx where
  | hl | ix | iy
  deriving BEq, Inhabited

@[inline] def idxGet (s : Cpu) : Idx → UInt16
  | .hl => s.hl
  | .ix => s.ix
  | .iy => s.iy

@[inline] def idxSet (s : Cpu) (x : Idx) (v : UInt16) : Cpu :=
  match x with
  | .hl => s.setHL v
  | .ix => { s with ix := v }
  | .iy => { s with iy := v }

/-- Register `i` of the encoding `B C D E H L (HL) A`; `H` and `L` are the
halves of the index register under a prefix.  Index 6 is not a register. -/
@[inline] def reg (s : Cpu) (x : Idx) (i : UInt8) : UInt8 :=
  match i with
  | 0 => s.b
  | 1 => s.c
  | 2 => s.d
  | 3 => s.e
  | 4 => hi (s.idxGet x)
  | 5 => lo (s.idxGet x)
  | _ => s.a

@[inline] def setReg (s : Cpu) (x : Idx) (i : UInt8) (v : UInt8) : Cpu :=
  match i with
  | 0 => { s with b := v }
  | 1 => { s with c := v }
  | 2 => { s with d := v }
  | 3 => { s with e := v }
  | 4 => s.idxSet x (mk16 v (lo (s.idxGet x)))
  | 5 => s.idxSet x (mk16 (hi (s.idxGet x)) v)
  | _ => { s with a := v }

/-- The address of the `(HL)` operand: `HL`, or `IX+d`/`IY+d` with the
displacement fetched (8 T-states more). -/
@[inline] def memAddr (s : Cpu) (x : Idx) : UInt16 × Cpu :=
  match x with
  | .hl => (s.hl, s)
  | _ =>
    let (d, s) := s.fetch
    (s.idxGet x + sext d, s.tick 8)

/-- Register pairs `BC DE HL SP`. -/
@[inline] def rp (s : Cpu) (x : Idx) (p : UInt8) : UInt16 :=
  match p with
  | 0 => s.bc
  | 1 => s.de
  | 2 => s.idxGet x
  | _ => s.sp

@[inline] def setRp (s : Cpu) (x : Idx) (p : UInt8) (v : UInt16) : Cpu :=
  match p with
  | 0 => s.setBC v
  | 1 => s.setDE v
  | 2 => s.idxSet x v
  | _ => { s with sp := v }

/-- Condition `NZ Z NC C PO PE P M`. -/
@[inline] def cond (s : Cpu) (y : UInt8) : Bool :=
  match y with
  | 0 => !s.flag FZ
  | 1 => s.flag FZ
  | 2 => !s.flag FC
  | 3 => s.flag FC
  | 4 => !s.flag FPV
  | 5 => s.flag FPV
  | 6 => !s.flag FS
  | _ => s.flag FS

/-! ## Arithmetic -/

/-- `a + b + carry`: result and flags. -/
@[inline] def add8 (a b : UInt8) (cin : Bool) : UInt8 × UInt8 :=
  let w := a.toUInt16 + b.toUInt16 + (if cin then 1 else 0)
  let r := w.toUInt8
  (r, szxy r ||| ((a ^^^ b ^^^ r) &&& FH) ||| bit ((a ^^^ r) &&& (b ^^^ r) &&& 0x80 != 0) FPV |||
      bit (w > 0xFF) FC)

/-- `a - b - carry`: result and flags. -/
@[inline] def sub8 (a b : UInt8) (cin : Bool) : UInt8 × UInt8 :=
  let w := a.toUInt16 - b.toUInt16 - (if cin then 1 else 0)
  let r := w.toUInt8
  (r, szxy r ||| ((a ^^^ b ^^^ r) &&& FH) ||| bit ((a ^^^ b) &&& (a ^^^ r) &&& 0x80 != 0) FPV |||
      FN ||| bit (w > 0xFF) FC)

/-- The eight accumulator operations `ADD ADC SUB SBC AND XOR OR CP`. -/
def alu (s : Cpu) (op : UInt8) (v : UInt8) : Cpu :=
  match op with
  | 0 => let (r, f) := add8 s.a v false; { s with a := r, f := f }
  | 1 => let (r, f) := add8 s.a v (s.flag FC); { s with a := r, f := f }
  | 2 => let (r, f) := sub8 s.a v false; { s with a := r, f := f }
  | 3 => let (r, f) := sub8 s.a v (s.flag FC); { s with a := r, f := f }
  | 4 => let r := s.a &&& v; { s with a := r, f := szxyp r ||| FH }
  | 5 => let r := s.a ^^^ v; { s with a := r, f := szxyp r }
  | 6 => let r := s.a ||| v; { s with a := r, f := szxyp r }
  | _ =>
    -- CP: the undocumented flags come from the operand
    let (_, f) := sub8 s.a v false
    { s with f := (f &&& ~~~FXY) ||| (v &&& FXY) }

@[inline] def inc8 (s : Cpu) (v : UInt8) : UInt8 × Cpu :=
  let r := v + 1
  (r, { s with f := (s.f &&& FC) ||| szxy r ||| bit (v &&& 0x0F == 0x0F) FH ||| bit (v == 0x7F) FPV })

@[inline] def dec8 (s : Cpu) (v : UInt8) : UInt8 × Cpu :=
  let r := v - 1
  (r, { s with f := (s.f &&& FC) ||| szxy r ||| bit (v &&& 0x0F == 0) FH ||| bit (v == 0x80) FPV ||| FN })

/-- `ADD HL,rr` (and the index forms): `S`, `Z`, `P/V` unchanged. -/
@[inline] def add16 (s : Cpu) (a b : UInt16) : UInt16 × Cpu :=
  let w := a.toUInt32 + b.toUInt32
  let r := w.toUInt16
  (r, { s with f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (hi r &&& FXY) |||
                    bit ((a ^^^ b ^^^ r) &&& 0x1000 != 0) FH ||| bit (w > 0xFFFF) FC })

def adc16 (s : Cpu) (b : UInt16) : Cpu :=
  let a := s.hl
  let w := a.toUInt32 + b.toUInt32 + (if s.flag FC then 1 else 0)
  let r := w.toUInt16
  let f : UInt8 := (hi r &&& (FS ||| FXY)) ||| bit (r == 0) FZ |||
    bit ((a ^^^ b ^^^ r) &&& 0x1000 != 0) FH |||
    bit ((a ^^^ r) &&& (b ^^^ r) &&& 0x8000 != 0) FPV ||| bit (w > 0xFFFF) FC
  { (s.setHL r) with f := f }

def sbc16 (s : Cpu) (b : UInt16) : Cpu :=
  let a := s.hl
  let w := a.toUInt32 - b.toUInt32 - (if s.flag FC then 1 else 0)
  let r := w.toUInt16
  let f : UInt8 := (hi r &&& (FS ||| FXY)) ||| bit (r == 0) FZ |||
    bit ((a ^^^ b ^^^ r) &&& 0x1000 != 0) FH |||
    bit ((a ^^^ b) &&& (a ^^^ r) &&& 0x8000 != 0) FPV ||| FN ||| bit (w > 0xFFFF) FC
  { (s.setHL r) with f := f }

/-- The `CB` rotates and shifts `RLC RRC RL RR SLA SRA SLL SRL`. -/
def rot (s : Cpu) (op : UInt8) (v : UInt8) : UInt8 × Cpu :=
  let cin : UInt8 := if s.flag FC then 1 else 0
  let (r, c) : UInt8 × Bool :=
    match op with
    | 0 => ((v <<< 1) ||| (v >>> 7), v &&& 0x80 != 0)
    | 1 => ((v >>> 1) ||| (v <<< 7), v &&& 1 != 0)
    | 2 => ((v <<< 1) ||| cin, v &&& 0x80 != 0)
    | 3 => ((v >>> 1) ||| (cin <<< 7), v &&& 1 != 0)
    | 4 => (v <<< 1, v &&& 0x80 != 0)
    | 5 => ((v >>> 1) ||| (v &&& 0x80), v &&& 1 != 0)
    | 6 => ((v <<< 1) ||| 1, v &&& 0x80 != 0)
    | _ => (v >>> 1, v &&& 1 != 0)
  (r, { s with f := szxyp r ||| bit c FC })

/-- `BIT n`: `xy` supplies the undocumented flags. -/
@[inline] def bitTest (s : Cpu) (n : UInt8) (v : UInt8) (xy : UInt8) : Cpu :=
  let t := v &&& ((1 : UInt8) <<< n)
  { s with f := (s.f &&& FC) ||| FH ||| (t &&& FS) ||| bit (t == 0) (FZ ||| FPV) ||| (xy &&& FXY) }

def daa (s : Cpu) : Cpu :=
  let a := s.a
  let low := s.flag FH || (a &&& 0x0F) > 9
  let high := s.flag FC || a > 0x99
  let corr : UInt8 := (if low then 0x06 else 0) ||| (if high then 0x60 else 0)
  let r := if s.flag FN then a - corr else a + corr
  let h := if s.flag FN then s.flag FH && (a &&& 0x0F) < 6 else (a &&& 0x0F) > 9
  { s with a := r, f := szxyp r ||| (s.f &&& FN) ||| bit high FC ||| bit h FH }

/-! ## Instructions -/

@[inline] def jr (s : Cpu) (taken : Bool) : Cpu :=
  let (d, s) := s.fetch
  if taken then ({ s with pc := s.pc + sext d }).tick 12 else s.tick 7

/-- An instruction of the `CB` page without a prefix, its opcode fetched. -/
def cbOp (s : Cpu) (op : UInt8) : Cpu :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  if z == 6 then
    let a := s.hl
    let v := s.rd a
    match g with
    | 0 => let (r, s) := s.rot y v; (s.wr a r).tick 15
    -- the undocumented flags of BIT n,(HL) come from an internal
    -- register; this model takes them from H
    | 1 => (s.bitTest y v s.h).tick 12
    | 2 => (s.wr a (v &&& ~~~((1 : UInt8) <<< y))).tick 15
    | _ => (s.wr a (v ||| ((1 : UInt8) <<< y))).tick 15
  else
    let v := s.reg .hl z
    match g with
    | 0 => let (r, s) := s.rot y v; (s.setReg .hl z r).tick 8
    | 1 => (s.bitTest y v v).tick 8
    | 2 => (s.setReg .hl z (v &&& ~~~((1 : UInt8) <<< y))).tick 8
    | _ => (s.setReg .hl z (v ||| ((1 : UInt8) <<< y))).tick 8

/-- The `CB` page (`cbOp`); under a prefix the operand is `(IX+d)` and
the displacement comes before the opcode. -/
def execCB (s : Cpu) (x : Idx) : Cpu :=
  match x with
  | .hl =>
    let (op, s) := s.fetch
    cbOp s.bumpR op
  | _ =>
    let (d, s) := s.fetch
    let (op, s) := s.fetch
    let g := op >>> 6
    let y := (op >>> 3) &&& 7
    let z := op &&& 7
    let a := s.idxGet x + sext d
    let v := s.rd a
    if g == 1 then (s.bitTest y v (hi a)).tick 16
    else
      let (r, s) : UInt8 × Cpu :=
        match g with
        | 0 => s.rot y v
        | 2 => (v &&& ~~~((1 : UInt8) <<< y), s)
        | _ => (v ||| ((1 : UInt8) <<< y), s)
      let s := s.wr a r
      -- undocumented: the result also goes to a register
      let s := if z == 6 then s else s.setReg .hl z r
      s.tick 19

/-- The block instructions `LDI CPI INI OUTI` and their decrementing and
repeating forms (`ED A0`–`ED BB`). -/
def execBlock (s : Cpu) (inp : UInt16 → UInt8) (y z : UInt8) : Cpu :=
  let dec : Bool := y &&& 1 == 1
  let rep : Bool := y ≥ 6
  let step (v : UInt16) : UInt16 := if dec then v - 1 else v + 1
  match z with
  | 0 =>
    let v := s.rd s.hl
    let s := s.wr s.de v
    let s := (s.setHL (step s.hl)).setDE (step s.de)
    let s := s.setBC (s.bc - 1)
    let more : Bool := s.bc != 0
    let n : UInt8 := s.a + v
    let y5 : Bool := n &&& 2 != 0
    let f : UInt8 := (s.f &&& (FS ||| FZ ||| FC)) ||| bit more FPV ||| (n &&& FX) ||| bit y5 FY
    let s := { s with f := f }
    if rep && more then ({ s with pc := s.pc - 2 }).tick 21 else s.tick 16
  | 1 =>
    let v := s.rd s.hl
    let (r, f) := sub8 s.a v false
    let s := s.setHL (step s.hl)
    let s := s.setBC (s.bc - 1)
    let more : Bool := s.bc != 0
    let hb : Bool := f &&& FH != 0
    let n : UInt8 := if hb then r - 1 else r
    let y5 : Bool := n &&& 2 != 0
    let f' : UInt8 := (s.f &&& FC) ||| (f &&& (FS ||| FZ ||| FH)) ||| FN ||| bit more FPV ||| (n &&& FX) ||| bit y5 FY
    let s := { s with f := f' }
    if rep && more && r != 0 then ({ s with pc := s.pc - 2 }).tick 21 else s.tick 16
  | 2 =>
    let port := s.bc
    let v := inp port
    let s := s.wr s.hl v
    let s := s.setHL (step s.hl)
    let b := s.b - 1
    let s := { s with b := b, f := (s.f &&& FC) ||| szxy b ||| FN, io := .read port }
    if rep && b != 0 then ({ s with pc := s.pc - 2 }).tick 21 else s.tick 16
  | _ =>
    let v := s.rd s.hl
    let b := s.b - 1
    let s := { s with b := b }
    let port := s.bc
    let s := s.setHL (step s.hl)
    let s := { s with f := (s.f &&& FC) ||| szxy b ||| FN, io := .write port v }
    if rep && b != 0 then ({ s with pc := s.pc - 2 }).tick 21 else s.tick 16

/-- An instruction of the `ED` page, its opcode fetched. -/
def edOp (s : Cpu) (inp : UInt16 → UInt8) (op : UInt8) : Cpu :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  let p := y >>> 1
  let q := y &&& 1
  if g == 1 then
    match z with
    | 0 =>
      let port := s.bc
      let v := inp port
      let s := { s with f := (s.f &&& FC) ||| szxyp v, io := .read port }
      (if y == 6 then s else s.setReg .hl y v).tick 12
    | 1 => ({ s with io := .write s.bc (if y == 6 then 0 else s.reg .hl y) }).tick 12
    | 2 => (if q == 0 then s.sbc16 (s.rp .hl p) else s.adc16 (s.rp .hl p)).tick 15
    | 3 =>
      let (nn, s) := s.fetch16
      (if q == 0 then s.wr16 nn (s.rp .hl p) else s.setRp .hl p (s.rd16 nn)).tick 20
    | 4 => let (r, f) := sub8 0 s.a false; ({ s with a := r, f := f }).tick 8
    | 5 => let (a, s) := s.pop; ({ s with pc := a, iff1 := s.iff2 }).tick 14
    | 6 => ({ s with im := match y &&& 3 with | 2 => 1 | 3 => 2 | _ => 0 }).tick 8
    | _ =>
      match y with
      | 0 => ({ s with i := s.a }).tick 9
      | 1 => ({ s with r := s.a }).tick 9
      | 2 => ({ s with a := s.i, f := (s.f &&& FC) ||| szxy s.i ||| bit s.iff2 FPV }).tick 9
      | 3 => ({ s with a := s.r, f := (s.f &&& FC) ||| szxy s.r ||| bit s.iff2 FPV }).tick 9
      | 4 =>
        -- RRD
        let v := s.rd s.hl
        let a : UInt8 := (s.a &&& 0xF0) ||| (v &&& 0x0F)
        let s := s.wr s.hl ((s.a <<< 4) ||| (v >>> 4))
        ({ s with a := a, f := (s.f &&& FC) ||| szxyp a }).tick 18
      | 5 =>
        -- RLD
        let v := s.rd s.hl
        let vh : UInt8 := v >>> 4
        let a : UInt8 := (s.a &&& 0xF0) ||| vh
        let s := s.wr s.hl ((v <<< 4) ||| (s.a &&& 0x0F))
        ({ s with a := a, f := (s.f &&& FC) ||| szxyp a }).tick 18
      | _ => s.tick 8
  else if g == 2 && z ≤ 3 && y ≥ 4 then s.execBlock inp y z
  else s.tick 8

/-- The `ED` page. -/
def execED (s : Cpu) (inp : UInt16 → UInt8) : Cpu :=
  let (op, s) := s.fetch
  edOp s.bumpR inp op

/-- An instruction of the main page, `x` naming the register pair that
plays `HL` (the prefix has been counted already). -/
def execMain (s : Cpu) (inp : UInt16 → UInt8) (op : UInt8) (x : Idx) : Cpu :=
  let g := op >>> 6
  let y := (op >>> 3) &&& 7
  let z := op &&& 7
  let p := y >>> 1
  let q := y &&& 1
  match g with
  | 0 =>
    match z with
    | 0 =>
      match y with
      | 0 => s.tick 4
      | 1 => ({ s with a := s.a', f := s.f', a' := s.a, f' := s.f }).tick 4
      | 2 =>
        let b := s.b - 1
        let s := { s with b := b }
        let (d, s) := s.fetch
        if b != 0 then ({ s with pc := s.pc + sext d }).tick 13 else s.tick 8
      | 3 => s.jr true
      | _ => s.jr (s.cond (y - 4))
    | 1 =>
      if q == 0 then
        let (nn, s) := s.fetch16
        (s.setRp x p nn).tick 10
      else
        let (r, s) := s.add16 (s.idxGet x) (s.rp x p)
        (s.idxSet x r).tick 11
    | 2 =>
      match y with
      | 0 => (s.wr s.bc s.a).tick 7
      | 1 => ({ s with a := s.rd s.bc }).tick 7
      | 2 => (s.wr s.de s.a).tick 7
      | 3 => ({ s with a := s.rd s.de }).tick 7
      | 4 => let (nn, s) := s.fetch16; (s.wr16 nn (s.idxGet x)).tick 16
      | 5 => let (nn, s) := s.fetch16; (s.idxSet x (s.rd16 nn)).tick 16
      | 6 => let (nn, s) := s.fetch16; (s.wr nn s.a).tick 13
      | _ => let (nn, s) := s.fetch16; ({ s with a := s.rd nn }).tick 13
    | 3 => (s.setRp x p (if q == 0 then s.rp x p + 1 else s.rp x p - 1)).tick 6
    | 4 =>
      if y == 6 then
        let (a, s) := s.memAddr x
        let (r, s) := s.inc8 (s.rd a)
        (s.wr a r).tick 11
      else
        let (r, s) := s.inc8 (s.reg x y)
        (s.setReg x y r).tick 4
    | 5 =>
      if y == 6 then
        let (a, s) := s.memAddr x
        let (r, s) := s.dec8 (s.rd a)
        (s.wr a r).tick 11
      else
        let (r, s) := s.dec8 (s.reg x y)
        (s.setReg x y r).tick 4
    | 6 =>
      if y == 6 then
        -- LD (IX+d),n is 19 T-states with its prefix: the displacement
        -- costs 5 here, not 8
        let (a, s) := s.memAddr x
        let (n, s) := s.fetch
        let s := s.wr a n
        if x == .hl then s.tick 10 else { s with cycles := s.cycles + 7 }
      else
        let (n, s) := s.fetch
        (s.setReg x y n).tick 7
    | _ =>
      match y with
      | 0 =>
        let a : UInt8 := (s.a <<< 1) ||| (s.a >>> 7)
        ({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 0x80 != 0) FC }).tick 4
      | 1 =>
        let a : UInt8 := (s.a >>> 1) ||| (s.a <<< 7)
        ({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 1 != 0) FC }).tick 4
      | 2 =>
        let a : UInt8 := (s.a <<< 1) ||| (if s.flag FC then 1 else 0)
        ({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 0x80 != 0) FC }).tick 4
      | 3 =>
        let a : UInt8 := (s.a >>> 1) ||| (if s.flag FC then 0x80 else 0)
        ({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 1 != 0) FC }).tick 4
      | 4 => s.daa.tick 4
      | 5 =>
        let a := ~~~s.a
        ({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV ||| FC)) ||| FH ||| FN ||| (a &&& FXY) }).tick 4
      | 6 => ({ s with f := (s.f &&& (FS ||| FZ ||| FPV)) ||| FC ||| (s.a &&& FXY) }).tick 4
      | _ =>
        ({ s with f := (s.f &&& (FS ||| FZ ||| FPV)) ||| bit (s.flag FC) FH ||| bit (!s.flag FC) FC |||
                       (s.a &&& FXY) }).tick 4
  | 1 =>
    if y == 6 && z == 6 then ({ s with halted := true }).tick 4
    else if z == 6 then
      -- with a memory operand, H and L are the real registers
      let (a, s) := s.memAddr x
      (s.setReg .hl y (s.rd a)).tick 7
    else if y == 6 then
      let (a, s) := s.memAddr x
      (s.wr a (s.reg .hl z)).tick 7
    else (s.setReg x y (s.reg x z)).tick 4
  | 2 =>
    if z == 6 then
      let (a, s) := s.memAddr x
      (s.alu y (s.rd a)).tick 7
    else (s.alu y (s.reg x z)).tick 4
  | _ =>
    match z with
    | 0 =>
      if s.cond y then let (a, s) := s.pop; ({ s with pc := a }).tick 11 else s.tick 5
    | 1 =>
      if q == 0 then
        let (v, s) := s.pop
        (if p == 3 then { s with a := hi v, f := lo v } else s.setRp x p v).tick 10
      else
        match p with
        | 0 => let (a, s) := s.pop; ({ s with pc := a }).tick 10
        | 1 =>
          ({ s with b := s.b', c := s.c', d := s.d', e := s.e', h := s.h', l := s.l',
                    b' := s.b, c' := s.c, d' := s.d, e' := s.e, h' := s.h, l' := s.l }).tick 4
        | 2 => ({ s with pc := s.idxGet x }).tick 4
        | _ => ({ s with sp := s.idxGet x }).tick 6
    | 2 =>
      let (nn, s) := s.fetch16
      (if s.cond y then { s with pc := nn } else s).tick 10
    | 3 =>
      match y with
      | 0 => let (nn, s) := s.fetch16; ({ s with pc := nn }).tick 10
      | 1 => s.execCB x
      | 2 => let (n, s) := s.fetch; ({ s with io := .write (mk16 s.a n) s.a }).tick 11
      | 3 =>
        let (n, s) := s.fetch
        let port := mk16 s.a n
        ({ s with a := inp port, io := .read port }).tick 11
      | 4 =>
        let v := s.rd16 s.sp
        let s := s.wr16 s.sp (s.idxGet x)
        (s.idxSet x v).tick 19
      | 5 => ({ s with d := s.h, e := s.l, h := s.d, l := s.e }).tick 4
      | 6 => ({ s with iff1 := false, iff2 := false }).tick 4
      | _ => ({ s with iff1 := true, iff2 := true, eiDelay := true }).tick 4
    | 4 =>
      let (nn, s) := s.fetch16
      if s.cond y then ({ (s.push s.pc) with pc := nn }).tick 17 else s.tick 10
    | 5 =>
      if q == 0 then
        (s.push (if p == 3 then s.af else s.rp x p)).tick 11
      else
        -- p = 0: CALL; the prefixes are handled by `step`
        let (nn, s) := s.fetch16
        ({ (s.push s.pc) with pc := nn }).tick 17
    | 6 => let (n, s) := s.fetch; (s.alu y n).tick 7
    | _ => ({ (s.push s.pc) with pc := (y <<< 3).toUInt16 }).tick 11

/-- Execute one instruction (a halted CPU executes `NOP`s).  `inp` is what
the I/O bus answers; `io` afterwards tells what was read or written. -/
def step (s : Cpu) (inp : UInt16 → UInt8 := fun _ => 0xFF) : Cpu :=
  let s := { s with io := .none, eiDelay := false }
  if s.halted then s.bumpR.tick 4
  else
    let (op, s) := s.fetch
    let s := s.bumpR
    if op == 0xDD || op == 0xFD then
      let x : Idx := if op == 0xDD then .ix else .iy
      let (op2, s) := s.fetch
      let s := (s.bumpR).tick 4
      if op2 == 0xDD || op2 == 0xFD || op2 == 0xED then
        -- a prefix before a prefix does nothing: it is a 4 T-state NOP
        -- and the second one is decoded next
        { s with pc := s.pc - 1, r := (s.r &&& 0x80) ||| ((s.r - 1) &&& 0x7F) }
      else if op2 == 0xCB then s.execCB x
      else s.execMain inp op2 x
    else if op == 0xED then s.execED inp
    else if op == 0xCB then s.execCB .hl
    else s.execMain inp op .hl

/-- Accept a maskable interrupt if the CPU allows it now (`bus` is the
byte the device puts on the data bus: the vector in mode 2). -/
def interrupt (s : Cpu) (bus : UInt8 := 0xFF) : Cpu :=
  if !s.iff1 || s.eiDelay then s
  else
    let s := { s with halted := false, iff1 := false, iff2 := false }
    let s := (s.bumpR).push s.pc
    if s.im == 2 then ({ s with pc := s.rd16 (mk16 s.i bus) }).tick 19
    else ({ s with pc := 0x0038 }).tick 13

/-- A placeholder without memory, to take the real CPU out of a record
that holds it (so that it stays uniquely referenced and is updated in
place). -/
def hole : Cpu := { mem := ByteArray.empty }

/-- Would an interrupt be accepted now? -/
def interruptible (s : Cpu) : Bool := s.iff1 && !s.eiDelay

def load (s : Cpu) (addr : Nat) (bytes : ByteArray) : Cpu :=
  let mem := (List.range bytes.size).foldl (fun m k => if addr + k < 65536 then m.set! (addr + k) bytes[k]! else m) s.mem
  { s with mem := mem }

end Cpu
end Ember.Z80
