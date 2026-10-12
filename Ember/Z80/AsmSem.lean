import Ember.Z80.Asm
import Ember.Z80.Cpu

/-!
# Ember.Z80.AsmSem — what an assembler instruction does (plan M7.4)

`Ember.Z80.Cpu` executes bytes; `Ember.Z80.Asm` writes instructions as
data and encodes them.  This file says what an instruction of
`Asm.Instr` does to the CPU, by its mnemonic and operands, without
going through its bytes: `exec`.  `Ember/Proof/Z80Encode.lean` proves
that the CPU, stepping on the bytes `Asm.encode` gives, does exactly
that — so the proofs about generated code can speak of instructions.

Covered: every form the assembler accepts that does not use `IX` or
`IY` (the back end and its runtime use neither).  For the others `exec`
is `none`.

The result is the whole CPU state, T-states and `R` included, written
with the CPU model's own helpers (`alu`, `setReg`, `push`, …).  An
immediate operand, already a number, is a parameter of `execI`; `exec`
takes it from the environment the assembler resolves labels in.
-/

namespace Ember.Z80.Asm
open Ember.Z80 Ember.Z80.Cpu

/-- Two bytes as a word, low byte first. -/
def w16 (lo hi : UInt8) : UInt16 := lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- The value of an operand (0 when it has none: an undefined label). -/
def Env.val (env : Env) (v : Val) : Int :=
  match (value v).run env with
  | .ok n => n
  | .error _ => 0

/-- The code of an 8-bit register in an opcode. -/
def r8? : Arg → Option UInt8
  | .b => some 0 | .c => some 1 | .d => some 2 | .e => some 3 | .h => some 4 | .l => some 5 | .a => some 7
  | _ => none

/-- `bc de hl sp`. -/
def rr? : Arg → Option UInt8
  | .bc => some 0 | .de => some 1 | .hl => some 2 | .sp => some 3
  | _ => none

def cc? : Arg → Option UInt8
  | .nz => some 0 | .z => some 1 | .nc => some 2 | .c => some 3
  | .po => some 4 | .pe => some 5 | .p => some 6 | .m => some 7
  | _ => none

/-- A bit number, 0 to 7. -/
def bitNo? (b : Int) : Option UInt8 := if 0 ≤ b ∧ b ≤ 7 then some (UInt8.ofNat b.toNat) else none

/-- `n` bytes of operand fetched. -/
def skip (s : Cpu) (n : UInt16) : Cpu := { s with pc := s.pc + n }

/-- The state once the opcode is fetched. -/
def op1 (s : Cpu) : Cpu := ({ s with io := .none, eiDelay := false, pc := s.pc + 1 }).bumpR

/-- The state once a prefix (`ED`, `CB`) and the opcode are fetched. -/
def op2 (s : Cpu) : Cpu := (skip (op1 s) 1).bumpR

/-- `ret`: the address popped. -/
def retTo (s : Cpu) : Cpu := { ({ s with sp := s.sp + 2 } : Cpu) with pc := s.rd16 s.sp }

/-- `call nn`, the operand fetched. -/
def callTo (s : Cpu) (nn : UInt16) : Cpu := { (s.push s.pc) with pc := nn }

/-- The instructions without operands; `s` after the opcode, `e` after a prefix and the opcode. -/
def simpleI (op : Op) (s e : Cpu) (inp : UInt16 → UInt8) : Option Cpu :=
  match op with
  | .nop => some (s.tick 4)
  | .halt => some (({ s with halted := true }).tick 4)
  | .di => some (({ s with iff1 := false, iff2 := false }).tick 4)
  | .ei => some (({ s with iff1 := true, iff2 := true, eiDelay := true }).tick 4)
  | .exx =>
    some (({ s with b := s.b', c := s.c', d := s.d', e := s.e', h := s.h', l := s.l',
                    b' := s.b, c' := s.c, d' := s.d, e' := s.e, h' := s.h, l' := s.l }).tick 4)
  | .daa => some (s.daa.tick 4)
  | .cpl =>
    some (({ s with a := ~~~s.a, f := (s.f &&& (FS ||| FZ ||| FPV ||| FC)) ||| FH ||| FN ||| (~~~s.a &&& FXY) }).tick 4)
  | .scf => some (({ s with f := (s.f &&& (FS ||| FZ ||| FPV)) ||| FC ||| (s.a &&& FXY) }).tick 4)
  | .ccf =>
    some (({ s with f := (s.f &&& (FS ||| FZ ||| FPV)) ||| bit (s.flag FC) FH ||| bit (!s.flag FC) FC |||
                         (s.a &&& FXY) }).tick 4)
  | .rlca =>
    let a : UInt8 := (s.a <<< 1) ||| (s.a >>> 7)
    some (({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 0x80 != 0) FC }).tick 4)
  | .rrca =>
    let a : UInt8 := (s.a >>> 1) ||| (s.a <<< 7)
    some (({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 1 != 0) FC }).tick 4)
  | .rla =>
    let a : UInt8 := (s.a <<< 1) ||| (if s.flag FC then 1 else 0)
    some (({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 0x80 != 0) FC }).tick 4)
  | .rra =>
    let a : UInt8 := (s.a >>> 1) ||| (if s.flag FC then 0x80 else 0)
    some (({ s with a := a, f := (s.f &&& (FS ||| FZ ||| FPV)) ||| (a &&& FXY) ||| bit (s.a &&& 1 != 0) FC }).tick 4)
  | .neg => some (({ e with a := (sub8 0 e.a false).1, f := (sub8 0 e.a false).2 }).tick 8)
  | .retn | .reti => some (({ (retTo e) with iff1 := e.iff2 }).tick 14)
  | .rrd =>
    let v : UInt8 := e.rd e.hl
    let a : UInt8 := (e.a &&& 0xF0) ||| (v &&& 0x0F)
    let w := e.wr e.hl ((e.a <<< 4) ||| (v >>> 4))
    some (({ w with a := a, f := (w.f &&& FC) ||| szxyp a }).tick 18)
  | .rld =>
    let v : UInt8 := e.rd e.hl
    let a : UInt8 := (e.a &&& (0xF0 : UInt8)) ||| (v >>> (4 : UInt8))
    let w := e.wr e.hl ((v <<< 4) ||| (e.a &&& 0x0F))
    some (({ w with a := a, f := (w.f &&& FC) ||| szxyp a }).tick 18)
  -- the block instructions are the CPU model's `execBlock`
  | .ldi => some (e.execBlock inp 4 0) | .cpi => some (e.execBlock inp 4 1)
  | .ini => some (e.execBlock inp 4 2) | .outi => some (e.execBlock inp 4 3)
  | .ldd => some (e.execBlock inp 5 0) | .cpd => some (e.execBlock inp 5 1)
  | .ind => some (e.execBlock inp 5 2) | .outd => some (e.execBlock inp 5 3)
  | .ldir => some (e.execBlock inp 6 0) | .cpir => some (e.execBlock inp 6 1)
  | .inir => some (e.execBlock inp 6 2) | .otir => some (e.execBlock inp 6 3)
  | .lddr => some (e.execBlock inp 7 0) | .cpdr => some (e.execBlock inp 7 1)
  | .indr => some (e.execBlock inp 7 2) | .otdr => some (e.execBlock inp 7 3)
  | _ => none

/-- `ld dst,src`; `n`, `nn`: the immediate operand or address. -/
def ldI (dst src : Arg) (n : UInt8) (nn : UInt16) (s e : Cpu) : Option Cpu :=
  match dst, src with
  | .a, .mbc => some (({ s with a := s.rd s.bc }).tick 7)
  | .a, .mde => some (({ s with a := s.rd s.de }).tick 7)
  | .mbc, .a => some ((s.wr s.bc s.a).tick 7)
  | .mde, .a => some ((s.wr s.de s.a).tick 7)
  | .a, .mem _ => some (({ (skip s 2) with a := s.rd nn }).tick 13)
  | .mem _, .a => some (((skip s 2).wr nn s.a).tick 13)
  | .a, .i => some (({ e with a := e.i, f := (e.f &&& FC) ||| szxy e.i ||| bit e.iff2 FPV }).tick 9)
  | .a, .r => some (({ e with a := e.r, f := (e.f &&& FC) ||| szxy e.r ||| bit e.iff2 FPV }).tick 9)
  | .i, .a => some (({ e with i := e.a }).tick 9)
  | .r, .a => some (({ e with r := e.a }).tick 9)
  | .sp, .hl => some (({ s with sp := s.hl }).tick 6)
  | _, _ =>
    match rr? dst, src with
    | some p, .imm _ => some (((skip s 2).setRp .hl p nn).tick 10)
    | some p, .mem _ =>
      if p == 2 then some (((skip s 2).setHL (s.rd16 nn)).tick 16)
      else some (((skip e 2).setRp .hl p (e.rd16 nn)).tick 20)
    | _, _ =>
      match dst, rr? src with
      | .mem _, some p =>
        if p == 2 then some (((skip s 2).wr16 nn s.hl).tick 16)
        else some (((skip e 2).wr16 nn (e.rp .hl p)).tick 20)
      | _, _ =>
        match dst, src with
        | .mhl, .imm _ => some (((skip s 1).wr s.hl n).tick 10)
        | .mhl, _ => (r8? src).map fun z => (s.wr s.hl (s.reg .hl z)).tick 7
        | _, .imm _ => (r8? dst).map fun y => ((skip s 1).setReg .hl y n).tick 7
        | _, .mhl => (r8? dst).map fun y => (s.setReg .hl y (s.rd s.hl)).tick 7
        | _, _ =>
          match r8? dst, r8? src with
          | some y, some z => some ((s.setReg .hl y (s.reg .hl z)).tick 4)
          | _, _ => none

/-- The accumulator operation `k` (`add adc sub sbc and xor or cp`) with the operand `x`. -/
def aluI (k : UInt8) (x : Arg) (n : UInt8) (s : Cpu) : Option Cpu :=
  match x with
  | .imm _ => some (((skip s 1).alu k n).tick 7)
  | .mhl => some ((s.alu k (s.rd s.hl)).tick 7)
  | _ => (r8? x).map fun z => (s.alu k (s.reg .hl z)).tick 4

def incI (x : Arg) (s : Cpu) : Option Cpu :=
  match rr? x with
  | some p => some ((s.setRp .hl p (s.rp .hl p + 1)).tick 6)
  | none =>
    match x with
    | .mhl => some (((s.inc8 (s.rd s.hl)).2.wr s.hl (s.inc8 (s.rd s.hl)).1).tick 11)
    | _ => (r8? x).map fun y => ((s.inc8 (s.reg .hl y)).2.setReg .hl y (s.inc8 (s.reg .hl y)).1).tick 4

def decI (x : Arg) (s : Cpu) : Option Cpu :=
  match rr? x with
  | some p => some ((s.setRp .hl p (s.rp .hl p - 1)).tick 6)
  | none =>
    match x with
    | .mhl => some (((s.dec8 (s.rd s.hl)).2.wr s.hl (s.dec8 (s.rd s.hl)).1).tick 11)
    | _ => (r8? x).map fun y => ((s.dec8 (s.reg .hl y)).2.setReg .hl y (s.dec8 (s.reg .hl y)).1).tick 4

/-- The rotate or shift `k` (`rlc rrc rl rr sla sra sll srl`). -/
def rotI (k : UInt8) (x : Arg) (e : Cpu) : Option Cpu :=
  match x with
  | .mhl => some (((e.rot k (e.rd e.hl)).2.wr e.hl (e.rot k (e.rd e.hl)).1).tick 15)
  | _ => (r8? x).map fun z => ((e.rot k (e.reg .hl z)).2.setReg .hl z (e.rot k (e.reg .hl z)).1).tick 8

def bitI (y : UInt8) (x : Arg) (e : Cpu) : Option Cpu :=
  match x with
  | .mhl => some ((e.bitTest y (e.rd e.hl) e.h).tick 12)
  | _ => (r8? x).map fun z => (e.bitTest y (e.reg .hl z) (e.reg .hl z)).tick 8

/-- `res` (`f` clears the bit) and `set` (`f` sets it). -/
def bitSetI (f : UInt8 → UInt8) (x : Arg) (e : Cpu) : Option Cpu :=
  match x with
  | .mhl => some ((e.wr e.hl (f (e.rd e.hl))).tick 15)
  | _ => (r8? x).map fun z => (e.setReg .hl z (f (e.reg .hl z))).tick 8

/-- The instructions with one operand. -/
def exec1 (op : Op) (x : Arg) (n : UInt8) (nn : UInt16) (s e : Cpu) : Option Cpu :=
  match op, x with
  | .push, .af => some ((s.push s.af).tick 11)
  | .push, .bc => some ((s.push s.bc).tick 11)
  | .push, .de => some ((s.push s.de).tick 11)
  | .push, .hl => some ((s.push s.hl).tick 11)
  | .pop, .af =>
    some (({ ({ s with sp := s.sp + 2 } : Cpu) with a := hi (s.rd16 s.sp), f := lo (s.rd16 s.sp) }).tick 10)
  | .pop, .bc => some ((({ s with sp := s.sp + 2 } : Cpu).setBC (s.rd16 s.sp)).tick 10)
  | .pop, .de => some ((({ s with sp := s.sp + 2 } : Cpu).setDE (s.rd16 s.sp)).tick 10)
  | .pop, .hl => some ((({ s with sp := s.sp + 2 } : Cpu).setHL (s.rd16 s.sp)).tick 10)
  | .sub, x => aluI 2 x n s
  | .and, x => aluI 4 x n s
  | .xor, x => aluI 5 x n s
  | .or, x => aluI 6 x n s
  | .cp, x => aluI 7 x n s
  | .inc, x => incI x s
  | .dec, x => decI x s
  | .rlc, x => rotI 0 x e
  | .rrc, x => rotI 1 x e
  | .rl, x => rotI 2 x e
  | .rr, x => rotI 3 x e
  | .sla, x => rotI 4 x e
  | .sra, x => rotI 5 x e
  | .sll, x => rotI 6 x e
  | .srl, x => rotI 7 x e
  | .jp, .mhl => some (({ s with pc := s.hl }).tick 4)
  | .jp, .imm _ => some (({ (skip s 2) with pc := nn }).tick 10)
  | .jr, .imm _ => some (({ (skip s 1) with pc := (skip s 1).pc + sext n }).tick 12)
  | .djnz, .imm _ =>
    some (if s.b - 1 != 0 then
        ({ (skip { s with b := s.b - 1 } 1) with pc := (skip { s with b := s.b - 1 } 1).pc + sext n }).tick 13
      else (skip { s with b := s.b - 1 } 1).tick 8)
  | .call, .imm _ => some ((callTo (skip s 2) nn).tick 17)
  | .ret, cc => (cc? cc).map fun k => if s.cond k then (retTo s).tick 11 else s.tick 5
  | .rst, .imm (.num a) =>
    if 0 ≤ a ∧ a ≤ 56 ∧ a % 8 = 0 then
      some (({ (s.push s.pc) with pc := ((UInt8.ofNat (a.toNat / 8)) <<< 3).toUInt16 }).tick 11)
    else none
  | .im, .imm (.num 0) => some (({ e with im := 0 }).tick 8)
  | .im, .imm (.num 1) => some (({ e with im := 1 }).tick 8)
  | .im, .imm (.num 2) => some (({ e with im := 2 }).tick 8)
  | _, _ => none

/-- The instructions with two operands. -/
def exec2 (op : Op) (x y : Arg) (n : UInt8) (nn : UInt16) (s e : Cpu) (inp : UInt16 → UInt8) : Option Cpu :=
  match op, x, y with
  | .ld, dst, src => ldI dst src n nn s e
  | .ex, .de, .hl => some (({ s with d := s.h, e := s.l, h := s.d, l := s.e }).tick 4)
  | .ex, .af, .af' => some (({ s with a := s.a', f := s.f', a' := s.a, f' := s.f }).tick 4)
  | .ex, .msp, .hl => some (((s.wr16 s.sp s.hl).setHL (s.rd16 s.sp)).tick 19)
  | .add, .hl, y => (rr? y).map fun p => ((s.add16 s.hl (s.rp .hl p)).2.setHL (s.add16 s.hl (s.rp .hl p)).1).tick 11
  | .adc, .hl, y => (rr? y).map fun p => (e.adc16 (e.rp .hl p)).tick 15
  | .sbc, .hl, y => (rr? y).map fun p => (e.sbc16 (e.rp .hl p)).tick 15
  | .add, .a, y => aluI 0 y n s
  | .adc, .a, y => aluI 1 y n s
  | .sbc, .a, y => aluI 3 y n s
  | .bit, .imm (.num b), y => (bitNo? b).bind fun k => bitI k y e
  | .res, .imm (.num b), y => (bitNo? b).bind fun k => bitSetI (· &&& ~~~((1 : UInt8) <<< k)) y e
  | .set, .imm (.num b), y => (bitNo? b).bind fun k => bitSetI (· ||| ((1 : UInt8) <<< k)) y e
  | .jp, cc, .imm _ => (cc? cc).map fun k => (if s.cond k then { (skip s 2) with pc := nn } else skip s 2).tick 10
  | .jr, cc, .imm _ =>
    (cc? cc).bind fun k =>
      if k > 3 then none
      else some (if s.cond k then ({ (skip s 1) with pc := (skip s 1).pc + sext n }).tick 12 else (skip s 1).tick 7)
  | .call, cc, .imm _ =>
    (cc? cc).map fun k => if s.cond k then (callTo (skip s 2) nn).tick 17 else (skip s 2).tick 10
  | .in, .a, .mem _ => some (({ (skip s 1) with a := inp (mk16 s.a n), io := .read (mk16 s.a n) }).tick 11)
  | .in, x, .mc =>
    (r8? x).map fun k =>
      (({ e with f := (e.f &&& FC) ||| szxyp (inp e.bc), io := .read e.bc } : Cpu).setReg .hl k (inp e.bc)).tick 12
  | .out, .mem _, .a => some (({ (skip s 1) with io := .write (mk16 s.a n) s.a }).tick 11)
  | .out, .mc, y => (r8? y).map fun k => ({ e with io := .write e.bc (e.reg .hl k) }).tick 12
  | _, _, _ => none

/-- **What an instruction does**, from the state `s0` before its opcode
is fetched; `n` and `nn` are its immediate operand (a byte, a relative
displacement; a word, an address).  `none`: not an instruction this
file covers. -/
def execI (i : Instr) (n : UInt8) (nn : UInt16) (s0 : Cpu) (inp : UInt16 → UInt8) : Option Cpu :=
  match i.args with
  | [] => if i.op == .ret then some ((retTo (op1 s0)).tick 10) else simpleI i.op (op1 s0) (op2 s0) inp
  | [x] => exec1 i.op x n nn (op1 s0) (op2 s0)
  | [x, y] => exec2 i.op x y n nn (op1 s0) (op2 s0) inp
  | _ => none

/-- The operand that is a number or an address, if there is one. -/
def Instr.immVal? (i : Instr) : Option Val :=
  i.args.findSome? fun
    | .imm v => some v
    | .mem v => some v
    | _ => none

def Instr.immInt (env : Env) (i : Instr) : Int :=
  match i.immVal? with
  | some v => env.val v
  | none => 0

/-- The immediate byte: a number, or for `jr` and `djnz` the displacement to the target. -/
def Instr.immB (env : Env) (i : Instr) : UInt8 :=
  byteOf (if i.op == .jr || i.op == .djnz then i.immInt env - (env.pc + 2) else i.immInt env)

def Instr.immW (env : Env) (i : Instr) : UInt16 := w16 (byteOf (i.immInt env)) (byteOf (i.immInt env / 256))

/-- **What an instruction at `env.pc` does**, its labels resolved by `env`. -/
def exec (env : Env) (i : Instr) (s : Cpu) (inp : UInt16 → UInt8 := fun _ => 0xFF) : Option Cpu :=
  execI i (i.immB env) (i.immW env) s inp

end Ember.Z80.Asm
