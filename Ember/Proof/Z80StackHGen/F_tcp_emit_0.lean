import Ember.Proof.Z80StackHGen.F_seg_len

/-! The generator on `tcp_emit` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_tcp_emit : FnPart :=
  { f := Stack.fn_tcp_emit, missed := #[false, false, false, false, false, false, false], live := some #[true, true, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false],
    code := (items.drop 1038).take 141, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }

def p1code_tcp_emit : List Item := [
  .label "f_tcp_emit",
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 22), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 24), .hl] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_tcp_emit" 19)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_tcp_emit_0" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 24)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 24), .hl] },
  .label "l_tcp_emit_0",
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 26), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 22)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 28), .hl] },
  .label "l_tcp_emit_1",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_tcp_emit" 28)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_tcp_emit_2" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 20)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 0), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65280)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_pend" 256)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.a, .mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 2), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_tcp_emit" 24)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 5), .hl] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 3), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65240)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_buf" 296)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.mhl, .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 26), .hl] },
  .ins { op := .jp, args := [.imm (.sym "l_tcp_emit_1" 0)] },
  .label "l_tcp_emit_2",
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 4)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 22)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 6)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 8)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_set32" 2)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 24)] },
  .ins { op := .call, args := [.imm (.sym "f_set32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 12)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_set32" 2)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 28)] },
  .ins { op := .call, args := [.imm (.sym "f_set32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 24)] },
  .ins { op := .srl, args := [.h] },
  .ins { op := .rr, args := [.l] },
  .ins { op := .srl, args := [.h] },
  .ins { op := .rr, args := [.l] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 9), .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 7), .hl] },
  .ins { op := .ld, args := [.a, .l] },
  .ins { op := .ld, args := [.mem (.sym "g_buf" 32), .a] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_tcp_emit" 16)] },
  .ins { op := .ld, args := [.mem (.sym "g_buf" 33), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 34)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 17)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 36)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 38)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_tcp_emit" 19)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_tcp_emit_3" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 2)] },
  .ins { op := .ld, args := [.mem (.sym "g_buf" 40), .a] },
  .ins { op := .ld, args := [.a, .imm (.num 4)] },
  .ins { op := .ld, args := [.mem (.sym "g_buf" 41), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 42)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_t" 26)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .label "l_tcp_emit_3",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 24)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_tcp_emit" 22)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 26), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_167772161" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 6)] },
  .ins { op := .ld, args := [.mem (.sym "fr_pseudo" 8), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .call, args := [.imm (.sym "f_pseudo" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 28), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 2), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 28)] },
  .ins { op := .call, args := [.imm (.sym "f_csum" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit" 30), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 36)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 30)] },
  .ins { op := .call, args := [.imm (.sym "rt_not16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_tcp_emit_46_t" 11), .hl] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 6)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_send" 0), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_emit" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_send" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_tcp_emit" 26)] },
  .ins { op := .call, args := [.imm (.sym "f_ip_send" 0)] },
  .ins { op := .ret, args := [] }]

def e1_tcp_emit : GEnv := fnEnv Stack.fn_tcp_emit (Array.replicate Stack.fn_tcp_emit.tmps.size true) none

def s1_tcp_emit_pre : GS :=
  { out := ⟨p1code_tcp_emit.take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_tcp_emit : runG (genPre Stack.fn_tcp_emit false) e1_tcp_emit (fnStart Stack.fn_tcp_emit #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)]) = .ok ((), s1_tcp_emit_pre) := by
  decide +kernel
def s1_tcp_emit_20 : GS :=
  { out := ⟨p1code_tcp_emit.take 58⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := false, reads := #[false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, true, false, true, false, false, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c1_tcp_emit_0 : runG (genBody Stack.fn_tcp_emit false 0 ((Stack.fn_tcp_emit.body.toList.drop 0).take 20)) e1_tcp_emit s1_tcp_emit_pre =
    .ok ((), s1_tcp_emit_20) := by
  decide +kernel

def s1_tcp_emit_40 : GS :=
  { out := ⟨p1code_tcp_emit.take 109⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := false, reads := #[false, false, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c1_tcp_emit_20 : runG (genBody Stack.fn_tcp_emit false 20 ((Stack.fn_tcp_emit.body.toList.drop 20).take 20)) e1_tcp_emit s1_tcp_emit_20 =
    .ok ((), s1_tcp_emit_40) := by
  decide +kernel

def s1_tcp_emit_55 : GS :=
  { out := ⟨p1code_tcp_emit.take 148⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    dead := true, reads := #[true, false, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 28 }, IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 22 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 24], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(3, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 26 }], acc := none }), (1, { a := [], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 19 }], hl := [IR.Opd.slot { area := IR.Area.frame "tcp_emit", off := 24 }], acc := none })] }

theorem c1_tcp_emit_40 : runG (genBody Stack.fn_tcp_emit false 40 ((Stack.fn_tcp_emit.body.toList.drop 40).take 15)) e1_tcp_emit s1_tcp_emit_40 =
    .ok ((), s1_tcp_emit_55) := by
  decide +kernel

theorem body1_tcp_emit : runG (genBody Stack.fn_tcp_emit false 0 (Stack.fn_tcp_emit.body.toList.drop 0)) e1_tcp_emit s1_tcp_emit_pre = .ok ((), s1_tcp_emit_55) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c1_tcp_emit_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c1_tcp_emit_20
    (body_step _ _ _ _ 40 15 _ _ _ (by decide +kernel) c1_tcp_emit_40
    (body_end _ _ _ _ 55 _ (by decide +kernel))))
theorem jumps1_tcp_emit : jumpsOk s1_tcp_emit_55 = true := by decide +kernel
theorem gen1_tcp_emit : genFn Stack.fn_tcp_emit (Array.replicate Stack.fn_tcp_emit.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] false none false =
    .ok (s1_tcp_emit_55.out, s1_tcp_emit_55.missed, s1_tcp_emit_55.lits, (tmpLayout Stack.fn_tcp_emit (Array.replicate Stack.fn_tcp_emit.tmps.size true)).2,
      if s1_tcp_emit_55.addrTaken then none else some s1_tcp_emit_55.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre1_tcp_emit body1_tcp_emit jumps1_tcp_emit


end Ember.Proof.Z80Gen.StackH
