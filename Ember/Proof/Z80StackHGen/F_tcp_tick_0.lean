import Ember.Proof.Z80StackHGen.F_tcp_input

/-! The generator on `tcp_tick` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_tcp_tick : FnPart :=
  { f := Stack.fn_tcp_tick, missed := #[false, false, false], live := some #[true],
    code := (items.drop 2388).take 125, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }

def p1code_tcp_tick : List Item := [
  .label "f_tcp_tick",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_tcp_tick_0" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_tcp_tick_0",
  .ins { op := .cp, args := [.imm (.num 8)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_tcp_tick_1" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 32)] },
  .ins { op := .cp, args := [.mhl] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_tcp_tick_2" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_tcb_reset" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_tcp_tick_3" 0)] },
  .label "l_tcp_tick_2",
  .ins { op := .ld, args := [.c, .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 32)] },
  .ins { op := .sub, args := [.c] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 32), .a] },
  .label "l_tcp_tick_3",
  .ins { op := .ret, args := [] },
  .label "l_tcp_tick_1",
  .ins { op := .cp, args := [.imm (.num 6)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_tcp_tick_4" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 33)] },
  .ins { op := .inc, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_tick_46_t" 0), .a] },
  .ins { op := .cp, args := [.imm (.num 60)] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_tcp_tick_5" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_tcb_reset" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 36)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_tcp_tick_6" 0)] },
  .label "l_tcp_tick_5",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 33)] },
  .ins { op := .inc, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 33), .a] },
  .label "l_tcp_tick_6",
  .ins { op := .ret, args := [] },
  .label "l_tcp_tick_4",
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_tcp_tick_7" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 30)] },
  .ins { op := .cp, args := [.mhl] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_tcp_tick_8" 0)] },
  .ins { op := .ld, args := [.c, .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 31)] },
  .ins { op := .add, args := [.a, .c] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_tick" 0), .a] },
  .ins { op := .ld, args := [.c, .a] },
  .ins { op := .ld, args := [.a, .imm (.num 8)] },
  .ins { op := .cp, args := [.c] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_tcp_tick_9" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 7)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 4), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 5)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 6), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 8)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 15)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 12)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 4)] },
  .ins { op := .or, args := [.imm (.num 16)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 16), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 17), .hl] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 19), .a] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 20), .hl] },
  .ins { op := .call, args := [.imm (.sym "f_tcp_emit" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_tcb_reset" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 35)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_tcp_tick_10" 0)] },
  .label "l_tcp_tick_9",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_tcp_tick" 0)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 31), .a] },
  .ins { op := .call, args := [.imm (.sym "f_rto" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_tick_46_t" 1), .a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .ins { op := .call, args := [.imm (.sym "f_rexmit" 0)] },
  .label "l_tcp_tick_10",
  .ins { op := .jp, args := [.imm (.sym "l_tcp_tick_11" 0)] },
  .label "l_tcp_tick_8",
  .ins { op := .ld, args := [.c, .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 30)] },
  .ins { op := .sub, args := [.c] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .label "l_tcp_tick_11",
  .ins { op := .ret, args := [] },
  .label "l_tcp_tick_7",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .cp, args := [.imm (.num 2)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_tcp_tick_12" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 19)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_tcp_tick_12" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 33)] },
  .ins { op := .inc, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_tick_46_t" 2), .a] },
  .ins { op := .cp, args := [.imm (.num 60)] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_tcp_tick_13" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 34), .a] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 33), .a] },
  .ins { op := .call, args := [.imm (.sym "f_output" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_tcp_tick_14" 0)] },
  .label "l_tcp_tick_13",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 33)] },
  .ins { op := .inc, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 33), .a] },
  .label "l_tcp_tick_14",
  .label "l_tcp_tick_12",
  .ins { op := .ret, args := [] }]

def e1_tcp_tick : GEnv := fnEnv Stack.fn_tcp_tick (Array.replicate Stack.fn_tcp_tick.tmps.size true) none

def s1_tcp_tick_pre : GS :=
  { out := ⟨p1code_tcp_tick.take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_tcp_tick : runG (genPre Stack.fn_tcp_tick false) e1_tcp_tick (fnStart Stack.fn_tcp_tick #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)]) = .ok ((), s1_tcp_tick_pre) := by
  decide +kernel
def s1_tcp_tick_20 : GS :=
  { out := ⟨p1code_tcp_tick.take 37⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false], addrTaken := false,
    jumps := [(6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_tcp_tick_0 : runG (genBody Stack.fn_tcp_tick false 0 ((Stack.fn_tcp_tick.body.toList.drop 0).take 20)) e1_tcp_tick s1_tcp_tick_pre =
    .ok ((), s1_tcp_tick_20) := by
  decide +kernel

def s1_tcp_tick_40 : GS :=
  { out := ⟨p1code_tcp_tick.take 86⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[false], addrTaken := false,
    jumps := [(10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_tcp_tick_20 : runG (genBody Stack.fn_tcp_tick false 20 ((Stack.fn_tcp_tick.body.toList.drop 20).take 20)) e1_tcp_tick s1_tcp_tick_20 =
    .ok ((), s1_tcp_tick_40) := by
  decide +kernel

def s1_tcp_tick_60 : GS :=
  { out := ⟨p1code_tcp_tick.take 121⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true], addrTaken := false,
    jumps := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_tcp_tick_40 : runG (genBody Stack.fn_tcp_tick false 40 ((Stack.fn_tcp_tick.body.toList.drop 40).take 20)) e1_tcp_tick s1_tcp_tick_40 =
    .ok ((), s1_tcp_tick_60) := by
  decide +kernel

def s1_tcp_tick_65 : GS :=
  { out := ⟨p1code_tcp_tick.take 128⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true], addrTaken := false,
    jumps := [(12, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 33 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(12, { a := [], hl := [], acc := none }), (14, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.tmp 2], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 19 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := none }), (8, { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [], hl := [], acc := none }), (9, { a := [IR.Opd.const 8], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.const 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_tcp_tick_60 : runG (genBody Stack.fn_tcp_tick false 60 ((Stack.fn_tcp_tick.body.toList.drop 60).take 5)) e1_tcp_tick s1_tcp_tick_60 =
    .ok ((), s1_tcp_tick_65) := by
  decide +kernel

theorem body1_tcp_tick : runG (genBody Stack.fn_tcp_tick false 0 (Stack.fn_tcp_tick.body.toList.drop 0)) e1_tcp_tick s1_tcp_tick_pre = .ok ((), s1_tcp_tick_65) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c1_tcp_tick_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c1_tcp_tick_20
    (body_step _ _ _ _ 40 20 _ _ _ (by decide +kernel) c1_tcp_tick_40
    (body_step _ _ _ _ 60 5 _ _ _ (by decide +kernel) c1_tcp_tick_60
    (body_end _ _ _ _ 65 _ (by decide +kernel)))))
theorem jumps1_tcp_tick : jumpsOk s1_tcp_tick_65 = true := by decide +kernel
theorem gen1_tcp_tick : genFn Stack.fn_tcp_tick (Array.replicate Stack.fn_tcp_tick.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] false none false =
    .ok (s1_tcp_tick_65.out, s1_tcp_tick_65.missed, s1_tcp_tick_65.lits, (tmpLayout Stack.fn_tcp_tick (Array.replicate Stack.fn_tcp_tick.tmps.size true)).2,
      if s1_tcp_tick_65.addrTaken then none else some s1_tcp_tick_65.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre1_tcp_tick body1_tcp_tick jumps1_tcp_tick


end Ember.Proof.Z80Gen.StackH
