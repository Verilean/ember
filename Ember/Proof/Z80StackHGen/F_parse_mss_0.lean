import Ember.Proof.Z80StackHGen.F_tcp_segment

/-! The generator on `parse_mss` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_parse_mss : FnPart :=
  { f := Stack.fn_parse_mss, missed := #[false, false, false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true],
    code := (items.drop 2186).take 107, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }

def p1code_parse_mss : List Item := [
  .label "f_parse_mss",
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 0), .hl] },
  .ins { op := .xor, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "g_sg" 17), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "g_sg" 18), .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 2), .hl] },
  .ins { op := .ld, args := [.a, .imm (.num 40)] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 4), .a] },
  .label "l_parse_mss_0",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_parse_mss" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_parse_mss_2" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_parse_mss_1" 0)] },
  .label "l_parse_mss_2",
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 0), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65240)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_buf" 296)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.a, .mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 5), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_parse_mss_3" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_parse_mss_1" 0)] },
  .label "l_parse_mss_3",
  .ins { op := .cp, args := [.imm (.num 1)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_parse_mss_4" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 2), .hl] },
  .ins { op := .jp, args := [.imm (.sym "l_parse_mss_5" 0)] },
  .label "l_parse_mss_4",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 2), .hl] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_parse_mss" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_parse_mss_6" 0)] },
  .ins { op := .jp, args := [.imm (.sym "l_parse_mss_1" 0)] },
  .label "l_parse_mss_6",
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 6), .hl] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 4), .hl] },
  .ins { op := .ld, args := [.bc, .imm (.num 65240)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .jp, args := [.c, .imm (.sym "rt_trap" 0)] },
  .ins { op := .ld, args := [.bc, .imm (.sym "g_buf" 296)] },
  .ins { op := .add, args := [.hl, .bc] },
  .ins { op := .ld, args := [.a, .mhl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 8), .a] },
  .ins { op := .ld, args := [.l, .a] },
  .ins { op := .ld, args := [.h, .imm (.num 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 6), .hl] },
  .ins { op := .ld, args := [.de, .imm (.num 2)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .jp, args := [.c, .imm (.sym "l_parse_mss_8" 0)] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 9), .hl] },
  .ins { op := .ex, args := [.de, .hl] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 0)] },
  .ins { op := .or, args := [.a] },
  .ins { op := .sbc, args := [.hl, .de] },
  .ins { op := .jp, args := [.nc, .imm (.sym "l_parse_mss_7" 0)] },
  .label "l_parse_mss_8",
  .ins { op := .jp, args := [.imm (.sym "l_parse_mss_1" 0)] },
  .label "l_parse_mss_7",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_parse_mss" 5)] },
  .ins { op := .cp, args := [.imm (.num 2)] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_parse_mss_9" 0)] },
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 6)] },
  .ins { op := .ld, args := [.a, .l] },
  .ins { op := .xor, args := [.imm (.num 4)] },
  .ins { op := .or, args := [.h] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_parse_mss_9" 0)] },
  .ins { op := .ld, args := [.a, .imm (.num 1)] },
  .ins { op := .ld, args := [.mem (.sym "g_sg" 17), .a] },
  .ins { op := .ld, args := [.hl, .imm (.num 20)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 13), .hl] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .inc, args := [.hl] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 11), .hl] },
  .ins { op := .call, args := [.imm (.sym "f_get16" 0)] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss_46_t" 15), .hl] },
  .ins { op := .ld, args := [.mem (.sym "g_sg" 18), .hl] },
  .label "l_parse_mss_9",
  .ins { op := .ld, args := [.hl, .mem (.sym "fr_parse_mss" 2)] },
  .ins { op := .ld, args := [.de, .mem (.sym "fr_parse_mss" 6)] },
  .ins { op := .add, args := [.hl, .de] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 2), .hl] },
  .label "l_parse_mss_5",
  .ins { op := .ld, args := [.a, .mem (.sym "fr_parse_mss" 4)] },
  .ins { op := .dec, args := [.a] },
  .ins { op := .ld, args := [.mem (.sym "fr_parse_mss" 4), .a] },
  .ins { op := .or, args := [.a] },
  .ins { op := .jp, args := [.nz, .imm (.sym "l_parse_mss_0" 0)] },
  .label "l_parse_mss_1",
  .ins { op := .ret, args := [] }]

def e1_parse_mss : GEnv := fnEnv Stack.fn_parse_mss (Array.replicate Stack.fn_parse_mss.tmps.size true) none

def s1_parse_mss_pre : GS :=
  { out := ⟨(p1code_parse_mss.drop 0).take 2⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 0 }], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [],
    dead := false, reads := #[false, false, false, false, false, false, false, false], addrTaken := false,
    jumps := [],
    labelRegs := [] }

theorem pre1_parse_mss : runG (genPre Stack.fn_parse_mss false) e1_parse_mss (fnStart Stack.fn_parse_mss #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)]) = .ok ((), s1_parse_mss_pre) := by
  decide +kernel
def s1_parse_mss_20 : GS :=
  { out := ⟨(p1code_parse_mss.drop 2).take 47⟩,
    regs := { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(1, { a := [], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := true, reads := #[true, false, true, false, false, false, false, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_parse_mss_0 : runG (genBody Stack.fn_parse_mss false 0 ((Stack.fn_parse_mss.body.toList.drop 0).take 20)) e1_parse_mss (noItems s1_parse_mss_pre) =
    .ok ((), s1_parse_mss_20) := by
  decide +kernel

def s1_parse_mss_40 : GS :=
  { out := ⟨(p1code_parse_mss.drop 49).take 59⟩,
    regs := { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(9, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := false, reads := #[true, false, true, false, false, true, true, false], addrTaken := false,
    jumps := [(9, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }, IR.Opd.tmp 8], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(9, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_parse_mss_20 : runG (genBody Stack.fn_parse_mss false 20 ((Stack.fn_parse_mss.body.toList.drop 20).take 20)) e1_parse_mss (noItems s1_parse_mss_20) =
    .ok ((), s1_parse_mss_40) := by
  decide +kernel

def s1_parse_mss_45 : GS :=
  { out := ⟨(p1code_parse_mss.drop 108).take 8⟩,
    regs := { a := [], hl := [], acc := none },
    missed := #[false, false, false, false, false, false, false, false, false], lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], labels := 0,
    atLabel := [(0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [], acc := none }), (1, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none })],
    dead := true, reads := #[true, false, true, false, true, true, true, false], addrTaken := false,
    jumps := [(1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.global "sg", off := 18 }, IR.Opd.tmp 8], acc := none }), (9, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (9, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 6 }], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (5, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (1, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 4 }, IR.Opd.const 40], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }, IR.Opd.const 20], acc := none })],
    labelRegs := [(1, { a := [], hl := [], acc := none }), (5, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (9, { a := [], hl := [], acc := none }), (7, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (8, { a := [IR.Opd.tmp 4], hl := [], acc := none }), (6, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (4, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (3, { a := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 5 }], hl := [], acc := none }), (2, { a := [], hl := [IR.Opd.slot { area := IR.Area.frame "parse_mss", off := 2 }], acc := none }), (0, { a := [], hl := [], acc := none })] }

theorem c1_parse_mss_40 : runG (genBody Stack.fn_parse_mss false 40 ((Stack.fn_parse_mss.body.toList.drop 40).take 5)) e1_parse_mss (noItems s1_parse_mss_40) =
    .ok ((), s1_parse_mss_45) := by
  decide +kernel

theorem body1_parse_mss : RunsTo Stack.fn_parse_mss false e1_parse_mss Stack.fn_parse_mss.body.toList 0 s1_parse_mss_pre s1_parse_mss_45
    (s1_parse_mss_20.out ++ (s1_parse_mss_40.out ++ (s1_parse_mss_45.out ++ (#[])))) :=
  body_step_out _ _ _ _ 0 20 _ _ _ _ (by decide +kernel) c1_parse_mss_0
    (body_step_out _ _ _ _ 20 20 _ _ _ _ (by decide +kernel) c1_parse_mss_20
    (body_step_out _ _ _ _ 40 5 _ _ _ _ (by decide +kernel) c1_parse_mss_40
    (body_end_out _ _ _ _ 45 _ (by decide +kernel))))
theorem jumps1_parse_mss : jumpsOk s1_parse_mss_45 = true := by decide +kernel
theorem gen1_parse_mss : genFn Stack.fn_parse_mss (Array.replicate Stack.fn_parse_mss.tmps.size true) #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] false none false =
    .ok (s1_parse_mss_pre.out ++ (s1_parse_mss_20.out ++ (s1_parse_mss_40.out ++ (s1_parse_mss_45.out ++ (#[])))), s1_parse_mss_45.missed, s1_parse_mss_45.lits, (tmpLayout Stack.fn_parse_mss (Array.replicate Stack.fn_parse_mss.tmps.size true)).2,
      if s1_parse_mss_45.addrTaken then none else some s1_parse_mss_45.reads) :=
  genFn_of_out _ _ _ _ _ _ _ _ _ pre1_parse_mss body1_parse_mss jumps1_parse_mss


end Ember.Proof.Z80Gen.StackH
