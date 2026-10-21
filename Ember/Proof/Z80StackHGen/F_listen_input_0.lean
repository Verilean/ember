import Ember.Proof.Z80StackHGen.F_acceptable

/-! The generator on `listen_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_listen_input : FnPart :=
  { f := Stack.fn_listen_input, missed := #[false, false, false, false], live := some #[true, true, true, true],
    code := (items.drop 1558).take 96, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], size := 0 }

def p1code_listen_input : List Item := [
  .label "f_listen_input",
  .ins { op := .ld, args := [.a, .mem (.sym "g_t" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_listen_input_0" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_sg" 16)] },
  .ins { op := .and, args := [.imm (.num 4)] },
  .ins { op := .ld, args := [.mem (.sym "fr_listen_input_46_t" 0), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_listen_input_1" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 22)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_listen_input_2" 0)] },
  .label "l_listen_input_1",
  .ins { op := .call, args := [.imm (.sym "f_send_reset" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 23)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .label "l_listen_input_2",
  .ins { op := .ret, args := [] },
  .label "l_listen_input_0",
  .ins { op := .ld, args := [.a, .mem (.sym "g_sg" 16)] },
  .ins { op := .and, args := [.imm (.num 4)] },
  .ins { op := .ld, args := [.mem (.sym "fr_listen_input_46_t" 1), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_listen_input_3" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 24)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_listen_input_3",
  .ins { op := .ld, args := [.a, .mem (.sym "g_sg" 16)] },
  .ins { op := .and, args := [.imm (.num 16)] },
  .ins { op := .ld, args := [.mem (.sym "fr_listen_input_46_t" 2), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_listen_input_4" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_send_reset" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 25)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_listen_input_4",
  .ins { op := .ld, args := [.a, .mem (.sym "g_sg" 16)] },
  .ins { op := .and, args := [.imm (.num 2)] },
  .ins { op := .ld, args := [.mem (.sym "fr_listen_input_46_t" 3), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_listen_input_5" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 26)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_listen_input_5",
  .ins { op := .ld, args := [.hl, .imm (.sym "g_iss" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_listen_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_iss" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_65536" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_add32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_iss" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .call, args := [.imm (.sym "f_tcb_reset" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 0), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_sg" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_sg" 4)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 5), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_sg" 8)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_1" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_add32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 15)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_listen_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_listen_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_1" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_add32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "g_t" 11)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_sg" 17)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_listen_input_6" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_sg" 18)] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_listen_input_7" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 24), .hl] },
  .ins { op := .jp, args := [.imm (.sym "l_listen_input_8" 0)] },
  .label "l_listen_input_7",
  .ins { op := .ld, args := [.mem (.sym "g_t" 24), .hl] },
  .label "l_listen_input_8",
  .label "l_listen_input_6",
  .ins { op := .ld, args := [.a, .imm (.num 3)] },
  .ins { op := .ld, args := [.mem (.sym "g_t" 30), .a] },
  .ins { op := .call, args := [.imm (.sym "f_send_syn_ack" 0)] },
  .ins { op := .ret, args := [] }]

def e1_listen_input : GEnv := fnEnv Stack.fn_listen_input (Array.replicate Stack.fn_listen_input.tmps.size true) none

def s1_listen_input_pre : GS :=
  { out := ⟨p1code_listen_input.take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_listen_input : runG (genPre Stack.fn_listen_input false) e1_listen_input (fnStart Stack.fn_listen_input #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)]) = .ok ((), s1_listen_input_pre) := by
  decide +kernel
def s1_listen_input_20 : GS :=
  { out := ⟨p1code_listen_input.take 36⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], labels := 0,
    atLabel := [(4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := false, reads := #[false, false, false, false], addrTaken := false,
    jumps := [(4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c1_listen_input_0 : runG (genBody Stack.fn_listen_input false 0 ((Stack.fn_listen_input.body.toList.drop 0).take 20)) e1_listen_input s1_listen_input_pre =
    .ok ((), s1_listen_input_20) := by
  decide +kernel

def s1_listen_input_40 : GS :=
  { out := ⟨p1code_listen_input.take 92⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false], addrTaken := false,
    jumps := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c1_listen_input_20 : runG (genBody Stack.fn_listen_input false 20 ((Stack.fn_listen_input.body.toList.drop 20).take 20)) e1_listen_input s1_listen_input_20 =
    .ok ((), s1_listen_input_40) := by
  decide +kernel

def s1_listen_input_47 : GS :=
  { out := ⟨p1code_listen_input.take 100⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], labels := 0,
    atLabel := [(8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false], addrTaken := false,
    jumps := [(6, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }, IR.Opd.const 1], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (6, { a := [IR.Opd.slot { area := IR.Area.global "sg", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none })],
    labelRegs := [(6, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (8, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "t", off := 24 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (7, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }], acc := some (4, IR.Opd.slot { area := IR.Area.global "t", off := 11 }) }), (5, { a := [IR.Opd.tmp 3], hl := [], acc := none }), (4, { a := [IR.Opd.tmp 2], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.global "t", off := 0 }], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none })] }

theorem c1_listen_input_40 : runG (genBody Stack.fn_listen_input false 40 ((Stack.fn_listen_input.body.toList.drop 40).take 7)) e1_listen_input s1_listen_input_40 =
    .ok ((), s1_listen_input_47) := by
  decide +kernel

theorem body1_listen_input : runG (genBody Stack.fn_listen_input false 0 (Stack.fn_listen_input.body.toList.drop 0)) e1_listen_input s1_listen_input_pre = .ok ((), s1_listen_input_47) :=
  body_step _ _ _ _ 0 20 _ _ _ (by decide +kernel) c1_listen_input_0
    (body_step _ _ _ _ 20 20 _ _ _ (by decide +kernel) c1_listen_input_20
    (body_step _ _ _ _ 40 7 _ _ _ (by decide +kernel) c1_listen_input_40
    (body_end _ _ _ _ 47 _ (by decide +kernel))))
theorem jumps1_listen_input : jumpsOk s1_listen_input_47 = true := by decide +kernel
theorem gen1_listen_input : genFn Stack.fn_listen_input (Array.replicate Stack.fn_listen_input.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] false none false =
    .ok (s1_listen_input_47.out, s1_listen_input_47.missed, s1_listen_input_47.lits, (tmpLayout Stack.fn_listen_input (Array.replicate Stack.fn_listen_input.tmps.size true)).2,
      if s1_listen_input_47.addrTaken then none else some s1_listen_input_47.reads) :=
  genFn_of _ _ _ _ _ _ _ _ pre1_listen_input body1_listen_input jumps1_listen_input


end Ember.Proof.Z80Gen.StackH
