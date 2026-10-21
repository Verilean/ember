import Ember.Proof.Z80StackHGen.F_tcp_tick_0

/-! The generator on `tcp_tick` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def e2_tcp_tick : GEnv := fnEnv Stack.fn_tcp_tick g_tcp_tick.missed g_tcp_tick.live

def s2_tcp_tick_pre : GS :=
  { out := ⟨(items.drop 2388).take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre2_tcp_tick : runG (genPre Stack.fn_tcp_tick false) e2_tcp_tick (fnStart Stack.fn_tcp_tick #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)]) = .ok ((), s2_tcp_tick_pre) := by
  decide +kernel
def s2_tcp_tick_20 : GS :=
  { out := ⟨(items.drop 2388).take 36⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false], addrTaken := false,
    jumps := [(6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c2_tcp_tick_0 : runG (genBody Stack.fn_tcp_tick false 0 ((Stack.fn_tcp_tick.body.toList.drop 0).take 20)) e2_tcp_tick s2_tcp_tick_pre =
    .ok ((), s2_tcp_tick_20) := by
  decide +kernel

def s2_tcp_tick_40 : GS :=
  { out := ⟨(items.drop 2388).take 85⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[false], addrTaken := false,
    jumps := [(10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c2_tcp_tick_20 : runG (genBody Stack.fn_tcp_tick false 20 ((Stack.fn_tcp_tick.body.toList.drop 20).take 20)) e2_tcp_tick s2_tcp_tick_20 =
    .ok ((), s2_tcp_tick_40) := by
  decide +kernel

def s2_tcp_tick_60 : GS :=
  { out := ⟨(items.drop 2388).take 118⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true], addrTaken := false,
    jumps := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c2_tcp_tick_40 : runG (genBody Stack.fn_tcp_tick false 40 ((Stack.fn_tcp_tick.body.toList.drop 40).take 20)) e2_tcp_tick s2_tcp_tick_40 =
    .ok ((), s2_tcp_tick_60) := by
  decide +kernel

def s2_tcp_tick_65 : GS :=
  { out := ⟨(items.drop 2388).take 125⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true], addrTaken := false,
    jumps := [(12, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(12, { a := [], hl := [], acc := none }), (14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c2_tcp_tick_60 : runG (genBody Stack.fn_tcp_tick false 60 ((Stack.fn_tcp_tick.body.toList.drop 60).take 5)) e2_tcp_tick s2_tcp_tick_60 =
    .ok ((), s2_tcp_tick_65) := by
  decide +kernel

theorem body2_tcp_tick : runG (genBody Stack.fn_tcp_tick false 0 (Stack.fn_tcp_tick.body.toList.drop 0)) e2_tcp_tick s2_tcp_tick_pre = .ok ((), s2_tcp_tick_65) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c2_tcp_tick_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c2_tcp_tick_20
    (body_step _ _ _ _ 40 20 _ _ _ (by decide +kernel) c2_tcp_tick_40
    (body_step _ _ _ _ 60 5 _ _ _ (by decide +kernel) c2_tcp_tick_60
    (body_end _ _ _ _ 65 _ (by decide +kernel)))))
theorem jumps2_tcp_tick : jumpsOk s2_tcp_tick_65 = true := by decide +kernel
theorem gen2_tcp_tick : genFn Stack.fn_tcp_tick g_tcp_tick.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] false g_tcp_tick.live false =
    .ok (s2_tcp_tick_65.out, s2_tcp_tick_65.missed, s2_tcp_tick_65.lits, (tmpLayout Stack.fn_tcp_tick g_tcp_tick.missed).2,
      if s2_tcp_tick_65.addrTaken then none else some s2_tcp_tick_65.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre2_tcp_tick body2_tcp_tick jumps2_tcp_tick

theorem p1_tcp_tick : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_tick = true :=
  pass1B_of gen1_tcp_tick (by rw [shared_eq]; decide +kernel)
theorem entry_tcp_tick : (Stack.fn_tcp_tick.name == Stack.ir.entry) = false := by decide +kernel
theorem p2_tcp_tick : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_tick = true :=
  pass2B_of (g := g_tcp_tick) rfl
    ((congrArg (fun b => genFn Stack.fn_tcp_tick g_tcp_tick.missed #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] b g_tcp_tick.live false)
      entry_tcp_tick).trans gen2_tcp_tick) (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
