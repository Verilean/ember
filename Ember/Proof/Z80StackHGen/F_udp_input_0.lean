import Ember.Proof.Z80StackHGen.F_icmp_input

/-! The generator on `udp_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_udp_input : FnPart :=
  { f := Stack.fn_udp_input, missed := #[], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 488).take 134, lits := #[(4, 167772161)], size := 0 }

def p1code_udp_input : List Item := [
  .label "f_udp_input",
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 8), .hl] },
  .ins { op := .ld, args := [.de, .imm (.num 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_udp_input_0" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 14)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_udp_input_0",
  .ins { op := .ld, args := [.hl, .imm (.num 24)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 10), .hl] },
  .ins { op := .ld, args := [.de, .imm (.num 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_udp_input_2" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_udp_input_1" 0)] },
  .label "l_udp_input_2",
  .ins { op := .ld, args := [.a, .imm (.num 15)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_udp_input_1",
  .ins { op := .ld, args := [.hl, .imm (.num 26)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 12), .hl] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_udp_input_3" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 17)] },
  .ins { op := .ld, args := [.mem (.sym "fr_pseudo" 8), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 10)] },
  .ins { op := .call, args := [.imm (.sym "f_pseudo" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 14), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 10)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 2), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 14)] },
  .ins { op := .call, args := [.imm (.sym "f_csum" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 16), .hl] },
  .ins { op := .call, args := [.imm (.sym "f_verifies" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 18), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_udp_input_4" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 16)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_udp_input_4",
  .label "l_udp_input_3",
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 14), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 22)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 16), .hl] },
  .ins { op := .ld, args := [.a, .l] },
  .ins { op := .xor, args := [.imm (.num 7)] },
  .ins { op := .or, args := [.h] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_udp_input_5" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 17)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_udp_input_5",
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 16)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 22)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 14)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 26)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_167772161" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_pseudo" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 17)] },
  .ins { op := .ld, args := [.mem (.sym "fr_pseudo" 8), .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 10)] },
  .ins { op := .call, args := [.imm (.sym "f_pseudo" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 18), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 10)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 2), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 18)] },
  .ins { op := .call, args := [.imm (.sym "f_csum" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 20), .hl] },
  .ins { op := .call, args := [.imm (.sym "rt_not16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_udp_input" 22), .hl] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_udp_input_6" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 26)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 65535)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_udp_input_7" 0)] },
  .label "l_udp_input_6",
  .ins { op := .ld, args := [.hl, .imm (.num 26)] },
  .ins { op := .ld, args := [.mem (.sym "fr_set16" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 22)] },
  .ins { op := .call, args := [.imm (.sym "f_set16" 0)] },
  .label "l_udp_input_7",
  .ins { op := .ld, args := [.a, .imm (.num 17)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_send" 0), .a] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_send" 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_udp_input" 10)] },
  .ins { op := .call, args := [.imm (.sym "f_ip_send" 0)] },
  .ins { op := .ret, args := [] }]

def e1_udp_input : GEnv := fnEnv Stack.fn_udp_input (Array.replicate Stack.fn_udp_input.tmps.size true) none

def s1_udp_input_pre : GS :=
  { out := ⟨(p1code_udp_input.drop 0).take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 8 }], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_udp_input : runG (genPre Stack.fn_udp_input false) e1_udp_input (fnStart Stack.fn_udp_input #[(4, 167772161)]) = .ok ((), s1_udp_input_pre) := by
  decide +kernel
def s1_udp_input_20 : GS :=
  { out := ⟨(p1code_udp_input.drop 2).take 52⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_udp_input_0 : runG (genBody Stack.fn_udp_input false 0 ((Stack.fn_udp_input.body.toList.drop 0).take 20)) e1_udp_input (noItems s1_udp_input_pre) =
    .ok ((), s1_udp_input_20) := by
  decide +kernel

def s1_udp_input_40 : GS :=
  { out := ⟨(p1code_udp_input.drop 54).take 43⟩,
    regs := { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "pseudo", off := 4 }) },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, true, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_udp_input_20 : runG (genBody Stack.fn_udp_input false 20 ((Stack.fn_udp_input.body.toList.drop 20).take 20)) e1_udp_input (noItems s1_udp_input_20) =
    .ok ((), s1_udp_input_40) := by
  decide +kernel

def s1_udp_input_58 : GS :=
  { out := ⟨(p1code_udp_input.drop 97).take 37⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, false, false, true, false], addrTaken := false,
    jumps := [(7, { a := [], hl := [], acc := none }), (7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (3, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 12 }], acc := none }), (2, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 10 }], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(7, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 22 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 16 }], acc := none }), (3, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "udp_input", off := 18 }], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (2, { a := [], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_udp_input_40 : runG (genBody Stack.fn_udp_input false 40 ((Stack.fn_udp_input.body.toList.drop 40).take 18)) e1_udp_input (noItems s1_udp_input_40) =
    .ok ((), s1_udp_input_58) := by
  decide +kernel

theorem body1_udp_input : RunsTo Stack.fn_udp_input false e1_udp_input Stack.fn_udp_input.body.toList 0 s1_udp_input_pre s1_udp_input_58
    (s1_udp_input_20.out ++ (s1_udp_input_40.out ++ (s1_udp_input_58.out ++ (#[])))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c1_udp_input_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c1_udp_input_20
    (body_step_out _ _ _ _ 40 18 _ _ _ _ (by decide +kernel) c1_udp_input_40
    (body_end_out _ _ _ _ 58 _ (by decide +kernel))))
theorem jumps1_udp_input : jumpsOk s1_udp_input_58 = true := by decide +kernel
theorem gen1_udp_input : genFn Stack.fn_udp_input (Array.replicate Stack.fn_udp_input.tmps.size true) #[(4, 167772161)] false none false =
    .ok (s1_udp_input_pre.out ++ (s1_udp_input_20.out ++ (s1_udp_input_40.out ++ (s1_udp_input_58.out ++ (#[])))), s1_udp_input_58.missed, s1_udp_input_58.lits, (tmpLayout Stack.fn_udp_input (Array.replicate Stack.fn_udp_input.tmps.size true)).2,
      if s1_udp_input_58.addrTaken then none else some s1_udp_input_58.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre1_udp_input body1_udp_input jumps1_udp_input


end Ember.Proof.Z80Gen.StackH
