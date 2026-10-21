import Ember.Proof.Z80StackHGen.F_listen_input_0

/-! The generator on `listen_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_listen_input : GEnv := fnEnv Stack.fn_listen_input g_listen_input.missed g_listen_input.live

def s2_listen_input_pre : GS :=
  { out := ⟨(items.drop 1558).take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_listen_input : runG (genPre Stack.fn_listen_input false) e2_listen_input (fnStart Stack.fn_listen_input #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)]) = .ok ((), s2_listen_input_pre) := by
  decide +kernel
def s2_listen_input_20 : GS :=
  { out := ⟨(items.drop 1558).take 33⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false, false, false, false], addrTaken := false,
    jumps := [(4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c2_listen_input_0 : runG (genBody Stack.fn_listen_input false 0 ((Stack.fn_listen_input.body.toList.drop 0).take 20)) e2_listen_input s2_listen_input_pre =
    .ok ((), s2_listen_input_20) := by
  decide +kernel

def s2_listen_input_40 : GS :=
  { out := ⟨(items.drop 1558).take 88⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false], addrTaken := false,
    jumps := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c2_listen_input_20 : runG (genBody Stack.fn_listen_input false 20 ((Stack.fn_listen_input.body.toList.drop 20).take 20)) e2_listen_input s2_listen_input_20 =
    .ok ((), s2_listen_input_40) := by
  decide +kernel

def s2_listen_input_47 : GS :=
  { out := ⟨(items.drop 1558).take 96⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false], addrTaken := false,
    jumps := [(6, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(6, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c2_listen_input_40 : runG (genBody Stack.fn_listen_input false 40 ((Stack.fn_listen_input.body.toList.drop 40).take 7)) e2_listen_input s2_listen_input_40 =
    .ok ((), s2_listen_input_47) := by
  decide +kernel

theorem body2_listen_input : runG (genBody Stack.fn_listen_input false 0 (Stack.fn_listen_input.body.toList.drop 0)) e2_listen_input s2_listen_input_pre = .ok ((), s2_listen_input_47) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c2_listen_input_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c2_listen_input_20
    (body_step _ _ _ _ 40 7 _ _ _ (by decide +kernel) c2_listen_input_40
    (body_end _ _ _ _ 47 _ (by decide +kernel))))
theorem jumps2_listen_input : jumpsOk s2_listen_input_47 = true := by decide +kernel
theorem gen2_listen_input : genFn Stack.fn_listen_input g_listen_input.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] false g_listen_input.live false =
    .ok (s2_listen_input_47.out, s2_listen_input_47.missed, s2_listen_input_47.lits, (tmpLayout Stack.fn_listen_input g_listen_input.missed).2,
      if s2_listen_input_47.addrTaken then none else some s2_listen_input_47.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre2_listen_input body2_listen_input jumps2_listen_input

theorem p1_listen_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_listen_input = true :=
  pass1B_of gen1_listen_input (by rw [shared_eq]; decide +kernel)
theorem entry_listen_input : (Stack.fn_listen_input.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_listen_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_listen_input = true :=
  pass2B_of (g := g_listen_input) rfl
    ((congrArg (fun b => genFn Stack.fn_listen_input g_listen_input.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] b g_listen_input.live false)
      entry_listen_input).trans gen2_listen_input) (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
