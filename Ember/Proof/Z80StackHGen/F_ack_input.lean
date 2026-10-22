import Ember.Proof.Z80StackHGen.F_ack_input_0

/-! The generator on `ack_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_ack_input : GEnv := fnEnv Stack.fn_ack_input g_ack_input.missed g_ack_input.live

def s2_ack_input_pre : GS :=
  { out := ⟨(items.drop 1654).take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_ack_input : runG (genPre Stack.fn_ack_input false) e2_ack_input (fnStart Stack.fn_ack_input #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)]) = .ok ((), s2_ack_input_pre) := by
  decide +kernel
def s2_ack_input_20 : GS :=
  { out := ⟨(items.drop 1655).take 54⟩,
    regs := { a := [], hl := [], acc := some (4, IR.Opd.tmp 1) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, true, false, false, false, false, false, false], addrTaken := false,
    jumps := [(2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c2_ack_input_0 : runG (genBody Stack.fn_ack_input false 0 ((Stack.fn_ack_input.body.toList.drop 0).take 20)) e2_ack_input (noItems s2_ack_input_pre) =
    .ok ((), s2_ack_input_20) := by
  decide +kernel

def s2_ack_input_40 : GS :=
  { out := ⟨(items.drop 1709).take 64⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 0], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, true, false, false, true, false, true, false], addrTaken := false,
    jumps := [(6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 13 }], acc := some (4, IR.Opd.tmp 1) }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c2_ack_input_20 : runG (genBody Stack.fn_ack_input false 20 ((Stack.fn_ack_input.body.toList.drop 20).take 20)) e2_ack_input (noItems s2_ack_input_20) =
    .ok ((), s2_ack_input_40) := by
  decide +kernel

def s2_ack_input_59 : GS :=
  { out := ⟨(items.drop 1773).take 30⟩,
    regs := { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }, IR.Opd.const 20], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 6], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := true, reads := #[true, false, false, false, false, false, false, false, true, false, true, true, false, true, false], addrTaken := false,
    jumps := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }, IR.Opd.const 20], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 6], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 0], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 13 }], acc := some (4, IR.Opd.tmp 1) }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c2_ack_input_40 : runG (genBody Stack.fn_ack_input false 40 ((Stack.fn_ack_input.body.toList.drop 40).take 19)) e2_ack_input (noItems s2_ack_input_40) =
    .ok ((), s2_ack_input_59) := by
  decide +kernel

theorem body2_ack_input : RunsTo Stack.fn_ack_input false e2_ack_input Stack.fn_ack_input.body.toList 0 s2_ack_input_pre s2_ack_input_59
    (s2_ack_input_20.out ++ (s2_ack_input_40.out ++ (s2_ack_input_59.out ++ (#[])))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c2_ack_input_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c2_ack_input_20
    (body_step_out _ _ _ _ 40 19 _ _ _ _ (by decide +kernel) c2_ack_input_40
    (body_end_out _ _ _ _ 59 _ (by decide +kernel))))
theorem jumps2_ack_input : jumpsOk s2_ack_input_59 = true := by decide +kernel
theorem gen2_ack_input : genFn Stack.fn_ack_input g_ack_input.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] false g_ack_input.live false =
    .ok (s2_ack_input_pre.out ++ (s2_ack_input_20.out ++ (s2_ack_input_40.out ++ (s2_ack_input_59.out ++ (#[])))), s2_ack_input_59.missed, s2_ack_input_59.lits, (tmpLayout Stack.fn_ack_input g_ack_input.missed).2,
      if s2_ack_input_59.addrTaken then none else some s2_ack_input_59.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre2_ack_input body2_ack_input jumps2_ack_input

theorem code2_ack_input : (s2_ack_input_pre.out ++ (s2_ack_input_20.out ++ (s2_ack_input_40.out ++ (s2_ack_input_59.out ++ (#[]))))).toList = (items.drop 1654).take 149 :=
  slices_toList items 1654 [1, 54, 64, 30]

theorem p1_ack_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_ack_input = true :=
  pass1B_of gen1_ack_input (by rw [shared_eq]; decide +kernel)
theorem entry_ack_input : (Stack.fn_ack_input.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_ack_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_ack_input = true :=
  pass2B_of' (g := g_ack_input) rfl
    ((congrArg (fun b => genFn Stack.fn_ack_input g_ack_input.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] b g_ack_input.live false)
      entry_ack_input).trans gen2_ack_input) code2_ack_input (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
