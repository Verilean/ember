import Ember.Proof.Z80StackHGen.F_parse_mss_0

/-! The generator on `parse_mss` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_parse_mss : GEnv := fnEnv Stack.fn_parse_mss g_parse_mss.missed g_parse_mss.live

def s2_parse_mss_pre : GS :=
  { out := ⟨(items.drop 2186).take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 0 }], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_parse_mss : runG (genPre Stack.fn_parse_mss false) e2_parse_mss (fnStart Stack.fn_parse_mss #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)]) = .ok ((), s2_parse_mss_pre) := by
  decide +kernel
def s2_parse_mss_20 : GS :=
  { out := ⟨(items.drop 2186).take 47⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(1, { a := [], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := true, reads := #[true, false, true, false, false, false, false, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_parse_mss_0 : runG (genBody Stack.fn_parse_mss false 0 ((Stack.fn_parse_mss.body.toList.drop 0).take 20)) e2_parse_mss s2_parse_mss_pre =
    .ok ((), s2_parse_mss_20) := by
  decide +kernel

def s2_parse_mss_40 : GS :=
  { out := ⟨(items.drop 2186).take 99⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(9, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := false, reads := #[true, false, true, false, false, true, true, false], addrTaken := false,
    jumps := [(9, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }, IR.Opd.tmp 8], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(9, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_parse_mss_20 : runG (genBody Stack.fn_parse_mss false 20 ((Stack.fn_parse_mss.body.toList.drop 20).take 20)) e2_parse_mss s2_parse_mss_20 =
    .ok ((), s2_parse_mss_40) := by
  decide +kernel

def s2_parse_mss_45 : GS :=
  { out := ⟨(items.drop 2186).take 107⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := true, reads := #[true, false, true, false, true, true, true, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }, IR.Opd.tmp 8], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(1, { a := [], hl := [], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_parse_mss_40 : runG (genBody Stack.fn_parse_mss false 40 ((Stack.fn_parse_mss.body.toList.drop 40).take 5)) e2_parse_mss s2_parse_mss_40 =
    .ok ((), s2_parse_mss_45) := by
  decide +kernel

theorem body2_parse_mss : runG (genBody Stack.fn_parse_mss false 0 (Stack.fn_parse_mss.body.toList.drop 0)) e2_parse_mss s2_parse_mss_pre = .ok ((), s2_parse_mss_45) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c2_parse_mss_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c2_parse_mss_20
    (body_step _ _ _ _ 40 5 _ _ _ (by decide +kernel) c2_parse_mss_40
    (body_end _ _ _ _ 45 _ (by decide +kernel))))
theorem jumps2_parse_mss : jumpsOk s2_parse_mss_45 = true := by decide +kernel
theorem gen2_parse_mss : genFn Stack.fn_parse_mss g_parse_mss.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] false g_parse_mss.live false =
    .ok (s2_parse_mss_45.out, s2_parse_mss_45.missed, s2_parse_mss_45.lits, (tmpLayout Stack.fn_parse_mss g_parse_mss.missed).2,
      if s2_parse_mss_45.addrTaken then none else some s2_parse_mss_45.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre2_parse_mss body2_parse_mss jumps2_parse_mss

theorem p1_parse_mss : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_parse_mss = true :=
  pass1B_of gen1_parse_mss (by rw [shared_eq]; decide +kernel)
theorem entry_parse_mss : (Stack.fn_parse_mss.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_parse_mss : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_parse_mss = true :=
  pass2B_of (g := g_parse_mss) rfl
    ((congrArg (fun b => genFn Stack.fn_parse_mss g_parse_mss.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] b g_parse_mss.live false)
      entry_parse_mss).trans gen2_parse_mss) (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
