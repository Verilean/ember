import Ember.Proof.Z80LoopIR
import Ember.Lang.Examples

/-!
# Ember.Proof.Z80Crc32IR — the IR of `crc32`, written out (plan M7.3)

`Crc32.ir` is what `IR.lower` returns for `Ember.Lang.Examples.Crc32.prog`
(`update`: the table-less CRC-32 of one byte, a loop of eight shifts of
four bytes by one; `main`: one byte of input into the global `crc`, or,
on `0x0100`, the four bytes of its complement out and `crc` reset), as
a term the kernel can run the generator and the checks on.  That it is
the lowering is a `#guard` — evaluated when this file is built, not
proved.  Nothing here is a theorem about the program's image.

Generated: `repr` of the functions and globals of the lowered program
(`Ember.Tools.ProofGen.fnText`, `globalText`).
-/

namespace Ember.Proof.Z80Gen.Crc32
open Ember.Z80

def update : IR.Fn :=
  { name := "update", regParam := some (1, { area := IR.Area.frame "update", off := 4 }), frame := 10, body := #[
      IR.Instr.ext 4 (IR.Dst.tmp 0) 1 (IR.Opd.slot { area := IR.Area.frame "update", off := 4 }),
      IR.Instr.bin (IR.Bin.xor) 4 (IR.Dst.slot { area := IR.Area.frame "update", off := 5 }) (IR.Opd.tmp 0) (IR.Opd.slot { area := IR.Area.frame "update", off := 0 }),
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.frame "update", off := 9 }) (IR.Opd.const 0),
      IR.Instr.label 0,
      IR.Instr.br (IR.Cmp.ge) 1 (IR.Opd.slot { area := IR.Area.frame "update", off := 9 }) (IR.Opd.const 8) 1,
      IR.Instr.bin (IR.Bin.and) 4 (IR.Dst.tmp 1) (IR.Opd.slot { area := IR.Area.frame "update", off := 5 }) (IR.Opd.const 1),
      IR.Instr.br (IR.Cmp.ne) 4 (IR.Opd.tmp 1) (IR.Opd.const 1) 2,
      IR.Instr.shift false 4 (IR.Dst.tmp 2) (IR.Opd.slot { area := IR.Area.frame "update", off := 5 }) 1 (IR.Opd.const 1),
      IR.Instr.bin (IR.Bin.xor) 4 (IR.Dst.slot { area := IR.Area.frame "update", off := 5 }) (IR.Opd.tmp 2) (IR.Opd.const 3988292384),
      IR.Instr.jmp 3,
      IR.Instr.label 2,
      IR.Instr.shift false 4 (IR.Dst.slot { area := IR.Area.frame "update", off := 5 }) (IR.Opd.slot { area := IR.Area.frame "update", off := 5 }) 1 (IR.Opd.const 1),
      IR.Instr.label 3,
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.slot { area := IR.Area.frame "update", off := 9 }) (IR.Opd.slot { area := IR.Area.frame "update", off := 9 }) (IR.Opd.const 1),
      IR.Instr.jmp 0,
      IR.Instr.label 1,
      IR.Instr.ret (some (4, IR.Opd.slot { area := IR.Area.frame "update", off := 5 }))], tmps := #[4, 4, 4], inlined := [], dead := false }

def main : IR.Fn :=
  { name := "main", regParam := none, frame := 6, body := #[
      IR.Instr.eff (Ember.Lang.Effect.inputNext) [] (some (2, IR.Dst.slot { area := IR.Area.frame "main", off := 0 })),
      IR.Instr.br (IR.Cmp.ne) 2 (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }) (IR.Opd.const 65535) 0,
      IR.Instr.ret none,
      IR.Instr.label 0,
      IR.Instr.br (IR.Cmp.ne) 2 (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }) (IR.Opd.const 256) 1,
      IR.Instr.not 4 (IR.Dst.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.slot { area := IR.Area.global "crc", off := 0 }),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.slot { area := IR.Area.frame "main", off := 2 })] none,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.slot { area := IR.Area.frame "main", off := 3 })] none,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.slot { area := IR.Area.frame "main", off := 4 })] none,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.slot { area := IR.Area.frame "main", off := 5 })] none,
      IR.Instr.eff (Ember.Lang.Effect.outEnd) [] none,
      IR.Instr.mov 4 (IR.Dst.slot { area := IR.Area.global "crc", off := 0 }) (IR.Opd.const 4294967295),
      IR.Instr.ret none,
      IR.Instr.label 1,
      IR.Instr.mov 4 (IR.Dst.slot { area := IR.Area.frame "update", off := 0 }) (IR.Opd.slot { area := IR.Area.global "crc", off := 0 }),
      IR.Instr.call "update" (some (4, IR.Dst.slot { area := IR.Area.global "crc", off := 0 })) (some (1, IR.Opd.slot { area := IR.Area.frame "main", off := 0 })),
      IR.Instr.ret none], tmps := #[], inlined := [], dead := false }

def ir : IR.Prog :=
  { globals :=
      [{ name := "crc", size := 4, init := some (ByteArray.mk #[255, 255, 255, 255]) }],
    fns := [update, main],
    entry := "main" }

/-- The lowering of the program is `ir`. -/
def irIsLowering : Bool :=
  match Ember.Lang.Examples.Crc32.prog.check with
  | .ok q =>
    match IR.lower q with
    | .ok r => Loop.sameProg r ir
    | .error _ => false
  | .error _ => false

#guard irIsLowering

end Ember.Proof.Z80Gen.Crc32
