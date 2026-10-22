import Ember.Proof.Z80StackHGen.F_udp_input

/-! The generator on `ip_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_ip_input : FnPart :=
  { f := Stack.fn_ip_input, missed := #[false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false],
    code := (items.drop 622).take 218, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }

def p1code_ip_input : List Item := [
  .label "f_ip_input",
  .ins { op := .ld, args := [.hl, .mem (.sym "g_len" 0)] },
  .ins { op := .ld, args := [.de, .imm (.num 20)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ip_input_0" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_0",
  .ins { op := .ld, args := [.a, .mem (.sym "g_buf" 0)] },
  .ins { op := .ld, args := [.b, .imm (.num 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_shr8" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 0), .a] },
  .ins { op := .cp, args := [.imm (.num 4)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ip_input_1" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 2)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_1",
  .ins { op := .ld, args := [.a, .mem (.sym "g_buf" 0)] },
  .ins { op := .and, args := [.imm (.num 15)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 1), .a] },
  .ins { op := .ld, args := [.l, .a] },
  .ins { op := .ld, args := [.h, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 2), .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .add, args := [.hl, .hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 0), .hl] },
  .ins { op := .ld, args := [.de, .imm (.num 20)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_ip_input_3" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_len" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ip_input_2" 0)] },
  .label "l_ip_input_3",
  .ins { op := .ld, args := [.a, .imm (.num 3)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_2",
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 0), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_csum" 2), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .call, args := [.imm (.sym "f_csum" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 2), .hl] },
  .ins { op := .call, args := [.imm (.sym "f_verifies" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 4), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_4" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_4",
  .ins { op := .ld, args := [.hl, .imm (.num 2)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 5), .hl] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_ip_input_6" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "g_len" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ip_input_5" 0)] },
  .label "l_ip_input_6",
  .ins { op := .ld, args := [.a, .imm (.num 5)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_5",
  .ins { op := .ld, args := [.hl, .imm (.num 6)] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 7), .hl] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .and, args := [.imm (.num 63)] },
  .ins { op := .ld, args := [.h, .a] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 4), .hl] },
  .ins { op := .ld, args := [.a, .h] },
  .ins { op := .or, args := [.l] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ip_input_7" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 6)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_7",
  .ins { op := .ld, args := [.a, .mem (.sym "g_buf" 8)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_8" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 7)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_8",
  .ins { op := .ld, args := [.hl, .imm (.num 16)] },
  .ins { op := .call, args := [.imm (.sym "f_get32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 9)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_167772161" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ip_input_9" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_4294967295" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ip_input_9" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 8)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_9",
  .ins { op := .ld, args := [.hl, .imm (.num 12)] },
  .ins { op := .call, args := [.imm (.sym "f_get32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 13)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "g_buf" 9)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 17), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ip_input_10" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 18), .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 5)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 20), .hl] },
  .label "l_ip_input_11",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 20)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_ip_input_12" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 6), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65240)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_buf" 296)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.a, .mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 8), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input_46_t" 9), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65240)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_buf" 296)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.mhl, .a] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 18), .hl] },
  .ins { op := .jp, args := [.imm (.sym "l_ip_input_11" 0)] },
  .label "l_ip_input_12",
  .label "l_ip_input_10",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 5)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_ip_input" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_ip_input" 18), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 9)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "lit32_4294967295" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_cmp32" 0)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_13" 0)] },
  .ins { op := .ld, args := [.a, .mem (.sym "fr_ip_input" 17)] },
  .ins { op := .cp, args := [.imm (.num 17)] },
  .ins { op := .jp, args := [.z, .imm (.sym "l_ip_input_13" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 9)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .ins { op := .ret, args := [] },
  .label "l_ip_input_13",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_ip_input" 17)] },
  .ins { op := .cp, args := [.imm (.num 1)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_14" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 13)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_icmp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .call, args := [.imm (.sym "f_icmp_input" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_ip_input_15" 0)] },
  .label "l_ip_input_14",
  .ins { op := .cp, args := [.imm (.num 17)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_16" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 13)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 9)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_udp_input" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .call, args := [.imm (.sym "f_udp_input" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_ip_input_17" 0)] },
  .label "l_ip_input_16",
  .ins { op := .cp, args := [.imm (.num 6)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_ip_input_18" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 13)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_input" 0)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_ip_input" 9)] },
  .ins { op := .call, args := [.imm (.sym "rt_ld32" 0)] },
  .ins { op := .ld, args := [.hl, .imm (.sym "fr_tcp_input" 4)] },
  .ins { op := .call, args := [.imm (.sym "rt_st32" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_ip_input" 18)] },
  .ins { op := .call, args := [.imm (.sym "f_tcp_input" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_ip_input_19" 0)] },
  .label "l_ip_input_18",
  .ins { op := .ld, args := [.a, .imm (.num 10)] },
  .ins { op := .call, args := [.imm (.sym "rt_drop" 0)] },
  .label "l_ip_input_19",
  .label "l_ip_input_17",
  .label "l_ip_input_15",
  .ins { op := .ret, args := [] }]

def e1_ip_input : GEnv := fnEnv Stack.fn_ip_input (Array.replicate Stack.fn_ip_input.tmps.size true) none

def s1_ip_input_pre : GS :=
  { out := ⟨(p1code_ip_input.drop 0).take 1⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_ip_input : runG (genPre Stack.fn_ip_input false) e1_ip_input (fnStart Stack.fn_ip_input #[(4, 167772161)]) = .ok ((), s1_ip_input_pre) := by
  decide +kernel
def s1_ip_input_20 : GS :=
  { out := ⟨(p1code_ip_input.drop 1).take 47⟩,
    regs := { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "csum", off := 2 }, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_ip_input_0 : runG (genBody Stack.fn_ip_input false 0 ((Stack.fn_ip_input.body.toList.drop 0).take 20)) e1_ip_input (noItems s1_ip_input_pre) =
    .ok ((), s1_ip_input_20) := by
  decide +kernel

def s1_ip_input_40 : GS :=
  { out := ⟨(p1code_ip_input.drop 48).take 46⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161)], labels := 0,
    atLabel := [(8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [(8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_ip_input_20 : runG (genBody Stack.fn_ip_input false 20 ((Stack.fn_ip_input.body.toList.drop 20).take 20)) e1_ip_input (noItems s1_ip_input_20) =
    .ok ((), s1_ip_input_40) := by
  decide +kernel

def s1_ip_input_60 : GS :=
  { out := ⟨(p1code_ip_input.drop 94).take 64⟩,
    regs := { a := [IR.Opd.tmp 5], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295)], labels := 0,
    atLabel := [(12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := false, reads := #[true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false], addrTaken := false,
    jumps := [(12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 20 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(11, { a := [], hl := [], acc := none }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_ip_input_40 : runG (genBody Stack.fn_ip_input false 40 ((Stack.fn_ip_input.body.toList.drop 40).take 20)) e1_ip_input (noItems s1_ip_input_40) =
    .ok ((), s1_ip_input_60) := by
  decide +kernel

def s1_ip_input_80 : GS :=
  { out := ⟨(p1code_ip_input.drop 158).take 47⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295)], labels := 0,
    atLabel := [(17, { a := [], hl := [], acc := none }), (16, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (15, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (11, { a := [IR.Opd.tmp 5], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false], addrTaken := false,
    jumps := [(17, { a := [], hl := [], acc := none }), (16, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (15, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (10, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [IR.Opd.tmp 5], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 20 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (10, { a := [], hl := [], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [], hl := [], acc := none }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_ip_input_60 : runG (genBody Stack.fn_ip_input false 60 ((Stack.fn_ip_input.body.toList.drop 60).take 20)) e1_ip_input (noItems s1_ip_input_60) =
    .ok ((), s1_ip_input_80) := by
  decide +kernel

def s1_ip_input_92 : GS :=
  { out := ⟨(p1code_ip_input.drop 205).take 21⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295)], labels := 0,
    atLabel := [(19, { a := [], hl := [], acc := none }), (18, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (17, { a := [], hl := [], acc := none }), (16, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (15, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (11, { a := [IR.Opd.tmp 5], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    dead := true, reads := #[true, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false], addrTaken := false,
    jumps := [(15, { a := [], hl := [], acc := none }), (17, { a := [], hl := [], acc := none }), (19, { a := [], hl := [], acc := none }), (19, { a := [], hl := [], acc := none }), (18, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (17, { a := [], hl := [], acc := none }), (16, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (15, { a := [], hl := [], acc := none }), (14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (10, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [IR.Opd.tmp 5], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 20 }], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (10, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }, IR.Opd.slot { area := IR.Area.global "buf", off := 9 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 13 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (6, { a := [], hl := [], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 5 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 0 }], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })],
    labelRegs := [(15, { a := [], hl := [], acc := none }), (17, { a := [], hl := [], acc := none }), (19, { a := [], hl := [], acc := none }), (18, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (16, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (14, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 17 }], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (13, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (10, { a := [], hl := [], acc := none }), (12, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 18 }], acc := none }), (11, { a := [], hl := [], acc := none }), (9, { a := [], hl := [], acc := some (4, IR.Opd.slot { area := IR.Area.frame "ip_input", off := 9 }) }), (8, { a := [IR.Opd.slot { area := IR.Area.global "buf", off := 8 }], hl := [IR.Opd.tmp 3], acc := none }), (7, { a := [], hl := [IR.Opd.tmp 3], acc := none }), (5, { a := [], hl := [], acc := none }), (6, { a := [], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "ip_input", off := 4 }], hl := [], acc := none }), (2, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (3, { a := [IR.Opd.tmp 1], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 0], hl := [], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_ip_input_80 : runG (genBody Stack.fn_ip_input false 80 ((Stack.fn_ip_input.body.toList.drop 80).take 12)) e1_ip_input (noItems s1_ip_input_80) =
    .ok ((), s1_ip_input_92) := by
  decide +kernel

theorem body1_ip_input : RunsTo Stack.fn_ip_input false e1_ip_input Stack.fn_ip_input.body.toList 0 s1_ip_input_pre s1_ip_input_92
    (s1_ip_input_20.out ++ (s1_ip_input_40.out ++ (s1_ip_input_60.out ++ (s1_ip_input_80.out ++ (s1_ip_input_92.out ++ (#[])))))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c1_ip_input_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c1_ip_input_20
    (body_step_out _ _ _ _ 40 20 _ _ _ _ (by decide +kernel) c1_ip_input_40
    (body_step_out _ _ _ _ 60 20 _ _ _ _ (by decide +kernel) c1_ip_input_60
    (body_step_out _ _ _ _ 80 12 _ _ _ _ (by decide +kernel) c1_ip_input_80
    (body_end_out _ _ _ _ 92 _ (by decide +kernel))))))
theorem jumps1_ip_input : jumpsOk s1_ip_input_92 = true := by decide +kernel
theorem gen1_ip_input : genFn Stack.fn_ip_input (Array.replicate Stack.fn_ip_input.tmps.size true) #[(4, 167772161)] false none false =
    .ok (s1_ip_input_pre.out ++ (s1_ip_input_20.out ++ (s1_ip_input_40.out ++ (s1_ip_input_60.out ++ (s1_ip_input_80.out ++ (s1_ip_input_92.out ++ (#[])))))), s1_ip_input_92.missed, s1_ip_input_92.lits, (tmpLayout Stack.fn_ip_input (Array.replicate Stack.fn_ip_input.tmps.size true)).2,
      if s1_ip_input_92.addrTaken then none else some s1_ip_input_92.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre1_ip_input body1_ip_input jumps1_ip_input


end Ember.Proof.Z80Gen.StackH
