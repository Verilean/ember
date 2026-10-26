import Ember.Proof.Z80LoopIR
import Ember.Z80.Wide

/-!
# Ember.Proof.Z80WideIR — the IR of `Ember.Z80.Wide`, written out (plan M7.3)

`Wide.ir` is what `IR.lower` returns for `Ember.Z80.Wide.prog`, as a
term the kernel can run the generator and the checks on.  That it is the
lowering is a `#guard` — evaluated when this file is built, not proved.

Generated: `repr` of the functions of the lowered program
(`Ember.Tools.ProofGen.fnText`).
-/

namespace Ember.Proof.Z80Gen.Wide
open Ember.Z80

def main : IR.Fn :=
  { name := "main", regParam := none, frame := 3, body := #[
      IR.Instr.eff (Ember.Lang.Effect.inputNext) [] (some (2, IR.Dst.slot { area := IR.Area.frame "main", off := 0 })),
      IR.Instr.br (IR.Cmp.ne) 2 (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }) (IR.Opd.const 65535) 0,
      IR.Instr.ret none,
      IR.Instr.label 0,
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "main", off := 2 }, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.const 305419896),
      IR.Instr.ext 4 (IR.Dst.tmp 1) 2 (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }),
      IR.Instr.bin (IR.Bin.add) 4 (IR.Dst.tmp 0) (IR.Opd.tmp 1) (IR.Opd.const 305419896),
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 3) (IR.Opd.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.const 1),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 2) (IR.Opd.tmp 3) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 2, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.tmp 0),
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 5) (IR.Opd.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.const 2),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 4) (IR.Opd.tmp 5) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 4, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.const 70000),
      IR.Instr.load 4 (IR.Dst.tmp 6) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "main", off := 2 }, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 2 (IR.Dst.tmp 7) 4 (IR.Opd.tmp 6),
      IR.Instr.ext 1 (IR.Dst.tmp 8) 2 (IR.Opd.tmp 7),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 8)] none,
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 10) (IR.Opd.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.const 1),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 9) (IR.Opd.tmp 10) (IR.Opd.const 3),
      IR.Instr.load 4 (IR.Dst.tmp 11) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 9, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 2 (IR.Dst.tmp 12) 4 (IR.Opd.tmp 11),
      IR.Instr.ext 1 (IR.Dst.tmp 13) 2 (IR.Opd.tmp 12),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 13)] none,
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 15) (IR.Opd.slot { area := IR.Area.frame "main", off := 2 }) (IR.Opd.const 2),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 14) (IR.Opd.tmp 15) (IR.Opd.const 3),
      IR.Instr.load 4 (IR.Dst.tmp 16) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 14, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 2 (IR.Dst.tmp 17) 4 (IR.Opd.tmp 16),
      IR.Instr.ext 1 (IR.Dst.tmp 18) 2 (IR.Opd.tmp 17),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 18)] none,
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "main", off := 0 }, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.const 305419896),
      IR.Instr.eff (Ember.Lang.Effect.outEnd) [] none,
      IR.Instr.ret none], tmps := #[4, 4, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1], inlined := [], dead := false }

def ir : IR.Prog :=
  { globals :=
      [{ name := "wa", size := 16 },
       { name := "WV", size := 4, init := some (ByteArray.mk #[120, 86, 52, 18]), const := true }],
    fns := [main],
    entry := "main" }

/-- The lowering of the program is `ir`. -/
def irIsLowering : Bool :=
  match Ember.Z80.Wide.prog.check with
  | .ok q =>
    match IR.lower q with
    | .ok r => Loop.sameProg r ir
    | .error _ => false
  | .error _ => false

#guard irIsLowering

end Ember.Proof.Z80Gen.Wide
