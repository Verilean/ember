import Ember.Proof.Z80StackHGen.F_listen_input

/-! The generator on `ack_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_ack_input : FnPart :=
  { f := Stack.fn_ack_input, missed := #[true, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1654).take 149, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], size := 4 }

def p1code_ack_input : List Item := [
  .label "f_ack_input",
  .ins { op := .ld, args := [.hl, .imm (.sym "g_sg" 12)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_sub32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_sub32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ack_input_0" 0)] },
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
  .ins { op := .ld, args := [.a, .imm (.num 33)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ret, args := [] },
  .label "l_ack_input_0",
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_0" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ack_input_1" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ret, args := [] },
  .label "l_ack_input_1",
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 21)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 8), .hl] },
  .ins { op := .call, args := [.imm (.sym "rt_acc_hl" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input_46_t" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input_46_t" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ack_input_2" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ack_input" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 8), .hl] },
  .label "l_ack_input_2",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ack_input" 8)] },
  .ins { op := .call, args := [.imm (.sym "rt_acc_hl" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input_46_t" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ack_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 0)] },
  .ins { op := .rla, args := [] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 10), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 11), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 19)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ack_input" 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 13), .hl] },
  .label "l_ack_input_3",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ack_input" 11)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ack_input" 13)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ack_input_4" 0)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ack_input" 8)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input_46_t" 8), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65280)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_pend" 256)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.a, .mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input_46_t" 10), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ack_input" 11)] },
  .ins { op := .ld, args := [.bc, .imm (.num 65280)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_pend" 256)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.mhl, .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ack_input" 11)] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_ack_input" 11), .hl] },
  .ins { op := .jp, args := [.imm (.sym "l_ack_input_3" 0)] },
  .label "l_ack_input_4",
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 19)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ack_input" 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 19), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 21)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ack_input" 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 21), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_sg" 12)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 31), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ack_input_5" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 3)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .ins { op := .jp, args := [.imm (.sym "l_ack_input_6" 0)] },
  .label "l_ack_input_5",
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .label "l_ack_input_6",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_ack_input" 10)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ack_input_7" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .cp, args := [.imm (.num 5)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ack_input_8" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 6)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 0), .a] },
  .ins { op := .jp, args := [.imm (.sym "l_ack_input_9" 0)] },
  .label "l_ack_input_8",
  .ins { op := .cp, args := [.imm (.num 7)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ack_input_10" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 8)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 0), .a] },
  .ins { op := .ld, args := [.a, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 32), .a] },
  .ins { op := .jp, args := [.imm (.sym "l_ack_input_11" 0)] },
  .label "l_ack_input_10",
  .ins { op := .cp, args := [.imm (.num 4)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ack_input_12" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_tcb_reset" 0)] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ret, args := [] },
  .label "l_ack_input_12",
  .label "l_ack_input_11",
  .label "l_ack_input_9",
  .label "l_ack_input_7",
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ret, args := [] }]

def e1_ack_input : GEnv := fnEnv Stack.fn_ack_input (Array.replicate Stack.fn_ack_input.tmps.size true) none

def s1_ack_input_pre : GS :=
  { out := ⟨(p1code_ack_input.drop 0).take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_ack_input : runG (genPre Stack.fn_ack_input false) e1_ack_input (fnStart Stack.fn_ack_input #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)]) = .ok ((), s1_ack_input_pre) := by
  decide +kernel
def s1_ack_input_20 : GS :=
  { out := ⟨(p1code_ack_input.drop 1).take 56⟩,
    regs := { a := [], hl := [], acc := some (4, IR.Opd.tmp 1) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, true, false, false, false, false, false, false], addrTaken := false,
    jumps := [(2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c1_ack_input_0 : runG (genBody Stack.fn_ack_input false 0 ((Stack.fn_ack_input.body.toList.drop 0).take 20)) e1_ack_input (noItems s1_ack_input_pre) =
    .ok ((), s1_ack_input_20) := by
  decide +kernel

def s1_ack_input_40 : GS :=
  { out := ⟨(p1code_ack_input.drop 57).take 66⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 0], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, true, false, false, true, false, true, false], addrTaken := false,
    jumps := [(6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 13 }], acc := some (4, IR.Opd.tmp 1) }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c1_ack_input_20 : runG (genBody Stack.fn_ack_input false 20 ((Stack.fn_ack_input.body.toList.drop 20).take 20)) e1_ack_input (noItems s1_ack_input_20) =
    .ok ((), s1_ack_input_40) := by
  decide +kernel

def s1_ack_input_59 : GS :=
  { out := ⟨(p1code_ack_input.drop 123).take 30⟩,
    regs := { a := [IR.Opd.const 1], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) },
    missed := #[true, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }, IR.Opd.const 20], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 6], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    dead := true, reads := #[true, false, false, false, false, false, false, false, true, false, true, true, false, true, false], addrTaken := false,
    jumps := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 32 }, IR.Opd.const 20], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }, IR.Opd.const 6], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (7, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 0], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }, IR.Opd.const 3], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (3, { a := [IR.Opd.tmp 3], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 10 }], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 13 }], acc := some (4, IR.Opd.tmp 1) }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 8 }, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })],
    labelRegs := [(7, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (11, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (12, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 30 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (5, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 7 }) }), (4, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ack_input", off := 11 }], acc := none }), (3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (1, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 0 }) }), (0, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ack_input", off := 4 }) })] }

theorem c1_ack_input_40 : runG (genBody Stack.fn_ack_input false 40 ((Stack.fn_ack_input.body.toList.drop 40).take 19)) e1_ack_input (noItems s1_ack_input_40) =
    .ok ((), s1_ack_input_59) := by
  decide +kernel

theorem body1_ack_input : RunsTo Stack.fn_ack_input false e1_ack_input Stack.fn_ack_input.body.toList 0 s1_ack_input_pre s1_ack_input_59
    (s1_ack_input_20.out ++ (s1_ack_input_40.out ++ (s1_ack_input_59.out ++ (#[])))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c1_ack_input_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c1_ack_input_20
    (body_step_out _ _ _ _ 40 19 _ _ _ _ (by decide +kernel) c1_ack_input_40
    (body_end_out _ _ _ _ 59 _ (by decide +kernel))))
theorem jumps1_ack_input : jumpsOk s1_ack_input_59 = true := by decide +kernel
theorem gen1_ack_input : genFn Stack.fn_ack_input (Array.replicate Stack.fn_ack_input.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] false none false =
    .ok (s1_ack_input_pre.out ++ (s1_ack_input_20.out ++ (s1_ack_input_40.out ++ (s1_ack_input_59.out ++ (#[])))), s1_ack_input_59.missed, s1_ack_input_59.lits, (tmpLayout Stack.fn_ack_input (Array.replicate Stack.fn_ack_input.tmps.size true)).2,
      if s1_ack_input_59.addrTaken then none else some s1_ack_input_59.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre1_ack_input body1_ack_input jumps1_ack_input


end Ember.Proof.Z80Gen.StackH
