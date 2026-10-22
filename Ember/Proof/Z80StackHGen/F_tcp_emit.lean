import Ember.Proof.Z80StackHGen.F_tcp_emit_0

/-! The generator on `tcp_emit` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_tcp_emit : GEnv := fnEnv Stack.fn_tcp_emit g_tcp_emit.missed g_tcp_emit.live

def s2_tcp_emit_pre : GS :=
  { out := ⟨(items.drop 1038).take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_tcp_emit : runG (genPre Stack.fn_tcp_emit false) e2_tcp_emit (fnStart Stack.fn_tcp_emit #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)]) = .ok ((), s2_tcp_emit_pre) := by
  decide +kernel
def s2_tcp_emit_20 : GS :=
  { out := ⟨(items.drop 1040).take 52⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := false, reads := #[false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, true, false, true, false, false, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c2_tcp_emit_0 : runG (genBody Stack.fn_tcp_emit false 0 ((Stack.fn_tcp_emit.body.toList.drop 0).take 20)) e2_tcp_emit (noItems s2_tcp_emit_pre) =
    .ok ((), s2_tcp_emit_20) := by
  decide +kernel

def s2_tcp_emit_40 : GS :=
  { out := ⟨(items.drop 1092).take 49⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := false, reads := #[false, false, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c2_tcp_emit_20 : runG (genBody Stack.fn_tcp_emit false 20 ((Stack.fn_tcp_emit.body.toList.drop 20).take 20)) e2_tcp_emit (noItems s2_tcp_emit_20) =
    .ok ((), s2_tcp_emit_40) := by
  decide +kernel

def s2_tcp_emit_55 : GS :=
  { out := ⟨(items.drop 1141).take 38⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := true, reads := #[true, false, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c2_tcp_emit_40 : runG (genBody Stack.fn_tcp_emit false 40 ((Stack.fn_tcp_emit.body.toList.drop 40).take 15)) e2_tcp_emit (noItems s2_tcp_emit_40) =
    .ok ((), s2_tcp_emit_55) := by
  decide +kernel

theorem body2_tcp_emit : RunsTo Stack.fn_tcp_emit false e2_tcp_emit Stack.fn_tcp_emit.body.toList 0 s2_tcp_emit_pre s2_tcp_emit_55
    (s2_tcp_emit_20.out ++ (s2_tcp_emit_40.out ++ (s2_tcp_emit_55.out ++ (#[])))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c2_tcp_emit_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c2_tcp_emit_20
    (body_step_out _ _ _ _ 40 15 _ _ _ _ (by decide +kernel) c2_tcp_emit_40
    (body_end_out _ _ _ _ 55 _ (by decide +kernel))))
theorem jumps2_tcp_emit : jumpsOk s2_tcp_emit_55 = true := by decide +kernel
theorem gen2_tcp_emit : genFn Stack.fn_tcp_emit g_tcp_emit.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] false g_tcp_emit.live false =
    .ok (s2_tcp_emit_pre.out ++ (s2_tcp_emit_20.out ++ (s2_tcp_emit_40.out ++ (s2_tcp_emit_55.out ++ (#[])))), s2_tcp_emit_55.missed, s2_tcp_emit_55.lits, (tmpLayout Stack.fn_tcp_emit g_tcp_emit.missed).2,
      if s2_tcp_emit_55.addrTaken then none else some s2_tcp_emit_55.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre2_tcp_emit body2_tcp_emit jumps2_tcp_emit

theorem code2_tcp_emit : (s2_tcp_emit_pre.out ++ (s2_tcp_emit_20.out ++ (s2_tcp_emit_40.out ++ (s2_tcp_emit_55.out ++ (#[]))))).toList = (items.drop 1038).take 141 :=
  slices_toList items 1038 [2, 52, 49, 38]

theorem p1_tcp_emit : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_tcp_emit = true :=
  pass1B_of gen1_tcp_emit (by rw [shared_eq]; decide +kernel)
theorem entry_tcp_emit : (Stack.fn_tcp_emit.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_tcp_emit : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_tcp_emit = true :=
  pass2B_of' (g := g_tcp_emit) rfl
    ((congrArg (fun b => genFn Stack.fn_tcp_emit g_tcp_emit.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] b g_tcp_emit.live false)
      entry_tcp_emit).trans gen2_tcp_emit) code2_tcp_emit (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
