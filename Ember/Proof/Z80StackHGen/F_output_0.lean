import Ember.Proof.Z80StackHGen.F_send_reset

/-! The generator on `output` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_output : FnPart :=
  { f := Stack.fn_output, missed := #[true, false, false, true, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1289).take 155, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 5 }

def p1code_output : List Item := [
  .label "f_output",
  .ins { op := .ld, args := [.mem (.sym "fr_output" 0), .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .cp, args := [.imm (.num 2)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_1" 0)] },
  .ins { op := .cp, args := [.imm (.num 3)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_0" 0)] },
  .label "l_output_1",
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 19)] },
  .ins { op := .ld, args := [.de, .mem (.sym "g_t" 21)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 1), .hl] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 23)] },
  .ins { op := .xor, args := [.imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output_46_t" 0), .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .cp, args := [.imm (.num 3)] },
  .ins { op := .ld, args := [.a, .imm (.num 0)] },
  .ins { op := .jr, args := [.nz, .imm (.sym "x_output_0" 0)] },
  .ins { op := .inc, args := [.a] },
  .label "x_output_0",
  .ins { op := .ld, args := [.mem (.sym "fr_output_46_t" 2), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 34)] },
  .ins { op := .or, args := [.mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_output_46_t" 1), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output_46_t" 0)] },
  .ins { op := .and, args := [.mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 3), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 1)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_3" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 3)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_2" 0)] },
  .label "l_output_3",
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 0)] },
  .ins { op := .jr, args := [.z, .imm (.sym "x_output_1" 0)] },
  .ins { op := .inc, args := [.a] },
  .label "x_output_1",
  .ins { op := .ld, args := [.mem (.sym "fr_output" 4), .a] },
  .ins { op := .ld, args := [.a, .imm (.num 16)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 5), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 1)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_4" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 5)] },
  .ins { op := .or, args := [.imm (.num 8)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 5), .a] },
  .label "l_output_4",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 3)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_5" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 5)] },
  .ins { op := .or, args := [.imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 5), .a] },
  .label "l_output_5",
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output" 6)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 21)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 10), .hl] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 3)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_6" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .cp, args := [.imm (.num 3)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_7" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 4)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 0), .a] },
  .ins { op := .jp, args := [.imm (.sym "l_output_8" 0)] },
  .label "l_output_7",
  .ins { op := .ld, args := [.a, .imm (.num 5)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 0), .a] },
  .label "l_output_8",
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 23), .a] },
  .label "l_output_6",
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 19)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 21), .hl] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 3)] },
  .ins { op := .call, args := [.imm (.sym "rt_acc_a" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output_46_t" 3)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_acc_hl" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output_46_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_add32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output_46_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output_46_t" 3)] },
  .ins { op := .call, args := [.imm (.sym "rt_add32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 5)] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 0), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_output" 6)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_send_seg" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 10)] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 5), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 1)] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 7), .hl] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .call, args := [.imm (.sym "f_send_seg" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 4)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_9" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 3)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 31), .a] },
  .label "l_output_9",
  .ins { op := .ret, args := [] },
  .label "l_output_2",
  .label "l_output_0",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_11" 0)] },
  .ins { op := .cp, args := [.imm (.num 1)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_10" 0)] },
  .label "l_output_11",
  .ins { op := .ret, args := [] },
  .label "l_output_10",
  .ins { op := .call, args := [.imm (.sym "f_wnd" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_output" 1), .hl] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_output" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_13" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 28)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_output_12" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_output" 1)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_output_12" 0)] },
  .label "l_output_13",
  .ins { op := .ld, args := [.a, .imm (.num 16)] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 0), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_send_seg" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 5), .hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_send_seg" 7), .hl] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .call, args := [.imm (.sym "f_send_seg" 0)] },
  .label "l_output_12",
  .ins { op := .ret, args := [] }]

def e1_output : GEnv := fnEnv Stack.fn_output (Array.replicate Stack.fn_output.tmps.size true) none

def s1_output_pre : GS :=
  { out := ⟨p1code_output.take 2⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 0 }], hl := [], acc := none },
    missed := #[false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_output : runG (genPre Stack.fn_output false) e1_output (fnStart Stack.fn_output #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)]) = .ok ((), s1_output_pre) := by
  decide +kernel
def s1_output_20 : GS :=
  { out := ⟨p1code_output.take 67⟩,
    regs := { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) },
    missed := #[true, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 2,
    atLabel := [(5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false, true, false, true, false, true, false, false, false, false, false, false], addrTaken := false,
    jumps := [(5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_output_0 : runG (genBody Stack.fn_output false 0 ((Stack.fn_output.body.toList.drop 0).take 20)) e1_output s1_output_pre =
    .ok ((), s1_output_20) := by
  decide +kernel

def s1_output_40 : GS :=
  { out := ⟨p1code_output.take 115⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[true, false, false, true, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 2,
    atLabel := [(8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false, true, false, true, false, true, true, false, false, false, true, false], addrTaken := false,
    jumps := [(6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 23 }, IR.Opd.const 1], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 5], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_output_20 : runG (genBody Stack.fn_output false 20 ((Stack.fn_output.body.toList.drop 20).take 20)) e1_output s1_output_20 =
    .ok ((), s1_output_40) := by
  decide +kernel

def s1_output_60 : GS :=
  { out := ⟨p1code_output.take 156⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "send_seg", off := 5 }, IR.Opd.const 0], acc := some (4, IR.Opd.slot { area := IR.Area.frame "send_seg", off := 1 }) },
    missed := #[true, false, false, true, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 2,
    atLabel := [(12, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 4 }], hl := [], acc := none }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[true, true, false, true, true, true, true, false, false, false, true, false], addrTaken := false,
    jumps := [(13, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 28 }], acc := none }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 31 }, IR.Opd.const 0], hl := [], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 4 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 23 }, IR.Opd.const 1], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 5], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(13, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (9, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_output_40 : runG (genBody Stack.fn_output false 40 ((Stack.fn_output.body.toList.drop 40).take 20)) e1_output s1_output_40 =
    .ok ((), s1_output_60) := by
  decide +kernel

def s1_output_64 : GS :=
  { out := ⟨p1code_output.take 161⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[true, false, false, true, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 2,
    atLabel := [(12, { a := [], hl := [], acc := none }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 4 }], hl := [], acc := none }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true, true, false, true, true, true, true, false, false, false, true, false], addrTaken := false,
    jumps := [(12, { a := [], hl := [], acc := none }), (13, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 28 }], acc := none }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 31 }, IR.Opd.const 0], hl := [], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 4 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 23 }, IR.Opd.const 1], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 5], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 4], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(12, { a := [], hl := [], acc := none }), (13, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (0, { a := [], hl := [], acc := none }), (2, { a := [IR.Opd.slot { area := IR.Area.frame "output", off := 3 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (9, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 10 }, IR.Opd.slot { area := IR.Area.global "t", off := 21 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "output", off := 6 }) }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "output", off := 1 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })] }

theorem c1_output_60 : runG (genBody Stack.fn_output false 60 ((Stack.fn_output.body.toList.drop 60).take 4)) e1_output s1_output_60 =
    .ok ((), s1_output_64) := by
  decide +kernel

theorem body1_output : runG (genBody Stack.fn_output false 0 (Stack.fn_output.body.toList.drop 0)) e1_output s1_output_pre = .ok ((), s1_output_64) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c1_output_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c1_output_20
    (body_step _ _ _ _ 40 20 _ _ _ (by decide +kernel) c1_output_40
    (body_step _ _ _ _ 60 4 _ _ _ (by decide +kernel) c1_output_60
    (body_end _ _ _ _ 64 _ (by decide +kernel)))))
theorem jumps1_output : jumpsOk s1_output_64 = true := by decide +kernel
theorem gen1_output : genFn Stack.fn_output (Array.replicate Stack.fn_output.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] false none false =
    .ok (s1_output_64.out, s1_output_64.missed, s1_output_64.lits, (tmpLayout Stack.fn_output (Array.replicate Stack.fn_output.tmps.size true)).2,
      if s1_output_64.addrTaken then none else some s1_output_64.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre1_output body1_output jumps1_output


end Ember.Proof.Z80Gen.StackH
