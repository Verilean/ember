import Ember.Proof.Z80StackHGen.F_udp_input_0

/-! The generator on `udp_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_udp_input : GEnv := fnEnv Stack.fn_udp_input g_udp_input.missed g_udp_input.live

def s2_udp_input_pre : GS :=
  { out := ⟨(items.drop 488).take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 8 }], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_udp_input : runG (genPre Stack.fn_udp_input false) e2_udp_input (fnStart Stack.fn_udp_input #[(4, 167772161)]) = .ok ((), s2_udp_input_pre) := by
  decide +kernel
def s2_udp_input_20 : GS :=
  { out := ⟨(items.drop 488).take 54⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_udp_input_0 : runG (genBody Stack.fn_udp_input false 0 ((Stack.fn_udp_input.body.toList.drop 0).take 20)) e2_udp_input s2_udp_input_pre =
    .ok ((), s2_udp_input_20) := by
  decide +kernel

def s2_udp_input_40 : GS :=
  { out := ⟨(items.drop 488).take 97⟩,
    regs := { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "pseudo", off := 4 }) },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, true, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_udp_input_20 : runG (genBody Stack.fn_udp_input false 20 ((Stack.fn_udp_input.body.toList.drop 20).take 20)) e2_udp_input s2_udp_input_20 =
    .ok ((), s2_udp_input_40) := by
  decide +kernel

def s2_udp_input_58 : GS :=
  { out := ⟨(items.drop 488).take 134⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, false, false, true, false], addrTaken := false,
    jumps := [(7, { a := [], hl := [], acc := none }), (7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c2_udp_input_40 : runG (genBody Stack.fn_udp_input false 40 ((Stack.fn_udp_input.body.toList.drop 40).take 18)) e2_udp_input s2_udp_input_40 =
    .ok ((), s2_udp_input_58) := by
  decide +kernel

theorem body2_udp_input : runG (genBody Stack.fn_udp_input false 0 (Stack.fn_udp_input.body.toList.drop 0)) e2_udp_input s2_udp_input_pre = .ok ((), s2_udp_input_58) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c2_udp_input_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c2_udp_input_20
    (body_step _ _ _ _ 40 18 _ _ _ (by decide +kernel) c2_udp_input_40
    (body_end _ _ _ _ 58 _ (by decide +kernel))))
theorem jumps2_udp_input : jumpsOk s2_udp_input_58 = true := by decide +kernel
theorem gen2_udp_input : genFn Stack.fn_udp_input g_udp_input.missed #[(4, 167772161)] false g_udp_input.live false =
    .ok (s2_udp_input_58.out, s2_udp_input_58.missed, s2_udp_input_58.lits, (tmpLayout Stack.fn_udp_input g_udp_input.missed).2,
      if s2_udp_input_58.addrTaken then none else some s2_udp_input_58.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre2_udp_input body2_udp_input jumps2_udp_input

theorem p1_udp_input : pass1B Stack.ir #[(4, 167772161)] g_udp_input = true :=
  pass1B_of gen1_udp_input (by rw [shared_eq]; decide +kernel)
theorem entry_udp_input : (Stack.fn_udp_input.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_udp_input : pass2B Stack.ir #[(4, 167772161)] g_udp_input = true :=
  pass2B_of (g := g_udp_input) rfl
    ((congrArg (fun b => genFn Stack.fn_udp_input g_udp_input.missed #[(4, 167772161)] b g_udp_input.live false)
      entry_udp_input).trans gen2_udp_input) (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
