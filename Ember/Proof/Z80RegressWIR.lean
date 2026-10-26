import Ember.Proof.Z80LoopIR

/-!
# Ember.Proof.Z80RegressWIR — the IR of `regress_wide_store`, written out (plan M7.3)

`RegressW.ir` is what `IR.lower` returns for `regress_wide_store`
(`Ember.Tests.LangPrograms.Regress.p5`: four-byte stores through
addresses of a global `wv` with an initial value, of a sum, of a
constant; four-byte loads to one byte; an index check that can trap),
as a term the kernel can run the generator and the checks on.  The
program is a fixture of `Tests`, which `Ember` does not import: that
`ir` is its lowering is a `#guard` in `Tests/Ember/Z80RegressW.lean` —
evaluated when that file is built, not proved.  Nothing here is a
theorem about the program's image.

Generated: `repr` of the functions and globals of the lowered program
(`Ember.Tools.ProofGen.fnText`, `globalText`).
-/

namespace Ember.Proof.Z80Gen.RegressW
open Ember.Z80

def wide_store : IR.Fn :=
  { name := "wide_store", regParam := none, frame := 3, body := #[
      IR.Instr.eff (Ember.Lang.Effect.inputNext) [] (some (2, IR.Dst.slot { area := IR.Area.frame "wide_store", off := 0 })),
      IR.Instr.br (IR.Cmp.ne) 2 (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 0 }) (IR.Opd.const 65535) 0,
      IR.Instr.ret none,
      IR.Instr.label 0,
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.slot { area := IR.Area.frame "wide_store", off := 2 }) (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 0 }) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.slot { area := IR.Area.global "wv", off := 0 }),
      IR.Instr.ext 4 (IR.Dst.tmp 1) 2 (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 0 }),
      IR.Instr.bin (IR.Bin.add) 4 (IR.Dst.tmp 0) (IR.Opd.tmp 1) (IR.Opd.slot { area := IR.Area.global "wv", off := 0 }),
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 3) (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }) (IR.Opd.const 1),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 2) (IR.Opd.tmp 3) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 2, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.tmp 0),
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 5) (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }) (IR.Opd.const 2),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 4) (IR.Opd.tmp 5) (IR.Opd.const 3),
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 4, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.const 70000),
      IR.Instr.load 4 (IR.Dst.tmp 6) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 1 (IR.Dst.tmp 7) 4 (IR.Opd.tmp 6),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 7)] none,
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 9) (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }) (IR.Opd.const 1),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 8) (IR.Opd.tmp 9) (IR.Opd.const 3),
      IR.Instr.load 4 (IR.Dst.tmp 10) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 8, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 1 (IR.Dst.tmp 11) 4 (IR.Opd.tmp 10),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 11)] none,
      IR.Instr.bin (IR.Bin.add) 1 (IR.Dst.tmp 13) (IR.Opd.slot { area := IR.Area.frame "wide_store", off := 2 }) (IR.Opd.const 2),
      IR.Instr.bin (IR.Bin.and) 1 (IR.Dst.tmp 12) (IR.Opd.tmp 13) (IR.Opd.const 3),
      IR.Instr.load 4 (IR.Dst.tmp 14) { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.tmp 12, size := 1, scale := 4, len := some 4, bound := some 4 } },
      IR.Instr.ext 1 (IR.Dst.tmp 15) 4 (IR.Opd.tmp 14),
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.tmp 15)] none,
      IR.Instr.store 4 { root := IR.Root.static { area := IR.Area.global "wa", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "wide_store", off := 0 }, size := 1, scale := 4, len := some 4, bound := some 4 } } (IR.Opd.slot { area := IR.Area.global "wv", off := 0 }),
      IR.Instr.eff (Ember.Lang.Effect.outEnd) [] none,
      IR.Instr.ret none], tmps := #[4, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1], inlined := [], dead := false }

def ir : IR.Prog :=
  { globals :=
      [{ name := "wa", size := 16 },
       { name := "wv", size := 4, init := some (ByteArray.mk #[120, 86, 52, 18]) }],
    fns := [wide_store],
    entry := "wide_store" }

end Ember.Proof.Z80Gen.RegressW
