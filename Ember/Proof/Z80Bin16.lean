import Ember.Proof.Z80Rep

/-!
# Ember.Proof.Z80Bin16 — two-byte arithmetic (plan M7.3)

In `HL`, the second operand a constant or in `DE`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin)

/-- `inc hl`, `dec hl`, `add hl,de`, `ld de,nn` as the model runs them. -/
def incHL (s : Cpu) : Cpu := ((op1 s).setRp .hl 2 ((op1 s).rp .hl 2 + 1)).tick 6
def decHL (s : Cpu) : Cpu := ((op1 s).setRp .hl 2 ((op1 s).rp .hl 2 - 1)).tick 6
def addHLDE (s : Cpu) : Cpu :=
  (((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 1)).2.setHL ((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 1)).1).tick 11
def ldDE (v : Nat) (s : Cpu) : Cpu :=
  ((skip (op1 s) 2).setRp .hl 1 (w16 (byteOf (Int.ofNat (v % 65536))) (byteOf (Int.ofNat (v % 65536) / 256)))).tick 10

/-- `A`, `DE` and everything but `HL` are as they were. -/
def KeepADE (s s' : Cpu) : Prop := Sys s s' ∧ s'.a = s.a ∧ s'.de = s.de

theorem KeepADE.refl (s : Cpu) : KeepADE s s := ⟨Sys.refl s, rfl, rfl⟩

theorem KeepADE.trans {s s' s'' : Cpu} (h1 : KeepADE s s') (h2 : KeepADE s' s'') : KeepADE s s'' :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem incHL_keep (s : Cpu) : KeepADE s (incHL s) := by simp only [KeepADE, Sys, incHL, zsim, and_self]
theorem decHL_keep (s : Cpu) : KeepADE s (decHL s) := by simp only [KeepADE, Sys, decHL, zsim, and_self]

theorem incHL_hl (s : Cpu) : (incHL s).hl.toNat = (s.hl.toNat + 1) % 65536 := by
  simp only [incHL, zsim]
  rw [UInt16.toNat_add]
  rfl

theorem decHL_hl (s : Cpu) : (decHL s).hl.toNat = (s.hl.toNat + 65535) % 65536 := by
  simp only [decHL, zsim]
  rw [UInt16.toNat_sub]
  show (2 ^ 16 - 1 + s.hl.toNat) % 2 ^ 16 = _
  omega

theorem iter_incHL : ∀ (k : Nat) (s : Cpu), (iter k incHL s).hl.toNat = (s.hl.toNat + k) % 65536
  | 0, s => by have := s.hl.toNat_lt; simp only [iter]; omega
  | k + 1, s => by
    rw [iter, iter_incHL k, incHL_hl]
    omega

theorem iter_decHL : ∀ (k : Nat) (s : Cpu), (iter k decHL s).hl.toNat = (s.hl.toNat + k * 65535) % 65536
  | 0, s => by have := s.hl.toNat_lt; simp only [iter]; omega
  | k + 1, s => by
    rw [iter, iter_decHL k, decHL_hl]
    omega

theorem ldDE_de (v : Nat) (s : Cpu) : (ldDE v s).de.toNat = v % 65536 := by
  simp only [ldDE, zsim]
  exact w16_val _ (Nat.mod_lt _ (by decide))

theorem addHLDE_hl (s : Cpu) : (addHLDE s).hl.toNat = (s.hl.toNat + s.de.toNat) % 65536 := by
  simp only [addHLDE, zsim]
  exact add16_val _ _ _

theorem binOp_add16 (x v : Nat) : IR.binOp .add 2 x v = (x + v) % 65536 := rfl
theorem binOp_sub16 (x v : Nat) : IR.binOp .sub 2 x v = (x + 65536 - v) % 65536 := rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- What a fragment that works on `HL` promises: from `HL = x` to `HL = res x`, the tracker forgetting `HL`. -/
def HlPost (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (H : Prop) (res : Nat → Nat) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt { s1.regs with hl := [] } ist tmps s' ∧ s'.hl.toNat = res s.hl.toNat)

/-- `HL` plus or minus a constant. -/
theorem addConst_ok (ok : Z.OK) (F : GFinal Z base sF) (v : Nat) (hv : v < 65536) (s0 : GS) :
    wpg (bin16Const .add v) E (HlPost Z E base sF dt True (fun x => IR.binOp .add 2 x v) s0) s0 := by
  simp only [bin16Const]
  by_cases h3 : v ≤ 3
  · rw [if_pos h3, wpg_rep_ins]
    refine ⟨pushK_ext _ _ _, fun hx _ fr ist tmps s R hat => ?_⟩
    obtain ⟨st, at', _⟩ := run_rep ok F incHL (fun _ _ _ => rfl) rfl (fun s => (incHL_keep s).1) (fun _ => rfl) v s0 s hx R.mach hat
    have hk := iter_inv incHL KeepADE KeepADE.refl (fun _ _ _ => KeepADE.trans) incHL_keep v s
    refine ⟨_, st, at', R.hl_gone hk.1 rfl (Or.inr ⟨by rw [pushK_regs], hk.2.1⟩)
      (fun n o h => by rw [pushK_regs] at h; exact h), ?_⟩
    show _ = IR.binOp .add 2 s.hl.toNat v
    rw [iter_incHL, binOp_add16]
  · rw [if_neg h3]
    by_cases h5 : v ≥ 65533
    · rw [if_pos h5, wpg_rep_ins]
      refine ⟨pushK_ext _ _ _, fun hx _ fr ist tmps s R hat => ?_⟩
      obtain ⟨st, at', _⟩ := run_rep ok F decHL (fun _ _ _ => rfl) rfl (fun s => (decHL_keep s).1) (fun _ => rfl) (65536 - v) s0 s hx
        R.mach hat
      have hk := iter_inv decHL KeepADE KeepADE.refl (fun _ _ _ => KeepADE.trans) decHL_keep (65536 - v) s
      refine ⟨_, st, at', R.hl_gone hk.1 rfl (Or.inr ⟨by rw [pushK_regs], hk.2.1⟩)
        (fun n o h => by rw [pushK_regs] at h; exact h), ?_⟩
      show _ = IR.binOp .add 2 s.hl.toNat v
      rw [iter_decHL, binOp_add16]
      have := s.hl.toNat_lt
      omega
    · rw [if_neg h5]
      simp only [wpg_bind, wpg_ins]
      refine ⟨(GExt.push _ _).trans (GExt.push _ _), fun hx _ fr ist tmps s R hat => ?_⟩
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.de, n16 v]⟩) })
        ((GExt.push _ _).trans hx) rfl R.mach hat (ldDE v s) (fun ad _ => rfl) rfl
        (by simp only [Sys, ldDE, zsim, and_self])
      obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := { s0 with out := s0.out.push (.ins ⟨.ld, [.de, n16 v]⟩) })
        hx rfl M1 at1 (addHLDE (ldDE v s)) (fun ad _ => rfl) rfl (by simp only [Sys, addHLDE, zsim, and_self])
      refine ⟨_, st1.trans st2, at2, R.hl_gone (by simp only [Sys, addHLDE, ldDE, zsim, and_self]) rfl
        (Or.inr ⟨rfl, by simp only [addHLDE, ldDE, zsim]⟩) (fun n o h => h), ?_⟩
      show _ = IR.binOp .add 2 s.hl.toNat v
      rw [addHLDE_hl, ldDE_de, binOp_add16, Nat.mod_eq_of_lt hv]
      congr 2

theorem subConst_ok (ok : Z.OK) (F : GFinal Z base sF) (v : Nat) (hv : v < 65536) (s0 : GS) :
    wpg (bin16Const .sub v) E (HlPost Z E base sF dt True (fun x => IR.binOp .sub 2 x v) s0) s0 := by
  simp only [bin16Const]
  by_cases h3 : v ≤ 3
  · rw [if_pos h3, wpg_rep_ins]
    refine ⟨pushK_ext _ _ _, fun hx _ fr ist tmps s R hat => ?_⟩
    obtain ⟨st, at', _⟩ := run_rep ok F decHL (fun _ _ _ => rfl) rfl (fun s => (decHL_keep s).1) (fun _ => rfl) v s0 s hx R.mach hat
    have hk := iter_inv decHL KeepADE KeepADE.refl (fun _ _ _ => KeepADE.trans) decHL_keep v s
    refine ⟨_, st, at', R.hl_gone hk.1 rfl (Or.inr ⟨by rw [pushK_regs], hk.2.1⟩)
      (fun n o h => by rw [pushK_regs] at h; exact h), ?_⟩
    show _ = IR.binOp .sub 2 s.hl.toNat v
    rw [iter_decHL, binOp_sub16]
    have := s.hl.toNat_lt
    omega
  · rw [if_neg h3]
    simp only [wpg_bind, wpg_ins]
    refine ⟨(GExt.push _ _).trans (GExt.push _ _), fun hx _ fr ist tmps s R hat => ?_⟩
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.de, n16 (65536 - v)]⟩) })
      ((GExt.push _ _).trans hx) rfl R.mach hat (ldDE (65536 - v) s) (fun ad _ => rfl) rfl
      (by simp only [Sys, ldDE, zsim, and_self])
    obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := { s0 with out := s0.out.push (.ins ⟨.ld, [.de, n16 (65536 - v)]⟩) })
      hx rfl M1 at1 (addHLDE (ldDE (65536 - v) s)) (fun ad _ => rfl) rfl (by simp only [Sys, addHLDE, zsim, and_self])
    refine ⟨_, st1.trans st2, at2, R.hl_gone (by simp only [Sys, addHLDE, ldDE, zsim, and_self]) rfl
      (Or.inr ⟨rfl, by simp only [addHLDE, ldDE, zsim]⟩) (fun n o h => h), ?_⟩
    show _ = IR.binOp .sub 2 s.hl.toNat v
    rw [addHLDE_hl, ldDE_de, binOp_sub16]
    have e : (ldDE (65536 - v) s).hl = s.hl := by simp only [ldDE, zsim]
    rw [e]
    have := s.hl.toNat_lt
    omega

/-- The same with the second operand in `DE`. -/
def HlDePost (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (H : Prop) (res : Nat → Nat → Nat)
    (s0 : GS) (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt { s1.regs with hl := [] } ist tmps s' ∧ s'.hl.toNat = res s.hl.toNat s.de.toNat)

theorem addReg_ok (ok : Z.OK) (F : GFinal Z base sF) (s0 : GS) :
    wpg (bin16Reg .add) E (HlDePost Z E base sF dt True (IR.binOp .add 2) s0) s0 := by
  simp only [bin16Reg, wpg_ins]
  refine ⟨GExt.of_out (by simp) rfl rfl, fun hx _ fr ist tmps s R hat => ?_⟩
  obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (addHLDE s) (fun ad _ => rfl) rfl
    (by simp only [Sys, addHLDE, zsim, and_self])
  exact ⟨_, st, at', R.hl_gone (by simp only [Sys, addHLDE, zsim, and_self]) rfl
    (Or.inr ⟨rfl, by simp only [addHLDE, zsim]⟩) (fun n o h => h), addHLDE_hl s⟩

theorem subReg_ok (ok : Z.OK) (F : GFinal Z base sF) (s0 : GS) :
    wpg (bin16Reg .sub) E (HlDePost Z E base sF dt True (IR.binOp .sub 2) s0) s0 := by
  simp only [bin16Reg, wpg_bind, wpg_ins]
  refine ⟨(GExt.push _ _).trans (GExt.push _ _), fun hx _ fr ist tmps s R hat => ?_⟩
  obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.or, [.a]⟩) })
    ((GExt.push _ _).trans hx) rfl R.mach hat (((op1 s).alu 6 ((op1 s).reg .hl 7)).tick 4) (fun ad _ => rfl) rfl
    (by simp only [Sys, zsim, and_self])
  obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := { s0 with out := s0.out.push (.ins ⟨.or, [.a]⟩) })
    hx rfl M1 at1
    (((op2 (((op1 s).alu 6 ((op1 s).reg .hl 7)).tick 4)).sbc16
      ((op2 (((op1 s).alu 6 ((op1 s).reg .hl 7)).tick 4)).rp .hl 1)).tick 15)
    (fun ad _ => rfl) rfl (by simp only [Sys, zsim, and_self])
  refine ⟨_, st1.trans st2, at2, R.hl_gone (by simp only [Sys, zsim, and_self]) rfl
    (Or.inr ⟨rfl, by simp only [zsim]; exact UInt8.or_self⟩) (fun n o h => h), ?_⟩
  simp only [zsim]
  rw [sbc16_val _ _ (by simp only [zsim]; exact alu6_flag _ _)]
  simp only [zsim]
  rfl

/-! ## The logic operations, byte by byte -/

def ldAR (z : UInt8) (s : Cpu) : Cpu := ((op1 s).setReg .hl 7 ((op1 s).reg .hl z)).tick 4
def ldRA (z : UInt8) (s : Cpu) : Cpu := ((op1 s).setReg .hl z ((op1 s).reg .hl 7)).tick 4
def aluR (k y : UInt8) (s : Cpu) : Cpu := ((op1 s).alu k ((op1 s).reg .hl y)).tick 4
def aluN (k : UInt8) (v : Nat) (s : Cpu) : Cpu := ((skip (op1 s) 1).alu k (byteOf (Int.ofNat (v % 256)))).tick 7

theorem does_ld_a_l : Does ⟨.ld, [.a, .l]⟩ (ldAR 5) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldAR, zsim, and_self], fun s => by simp only [ldAR, zsim]⟩
theorem does_ld_a_h : Does ⟨.ld, [.a, .h]⟩ (ldAR 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldAR, zsim, and_self], fun s => by simp only [ldAR, zsim]⟩
theorem does_ld_l_a : Does ⟨.ld, [.l, .a]⟩ (ldRA 5) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRA, zsim, and_self], fun s => by simp only [ldRA, zsim]⟩
theorem does_ld_h_a : Does ⟨.ld, [.h, .a]⟩ (ldRA 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRA, zsim, and_self], fun s => by simp only [ldRA, zsim]⟩

theorem does_alu_reg {op : Bin} {k : UInt8} (hk : aluK op = some k) {x : Arg} {z : UInt8} (hz : r8? x = some z) :
    Does (aluIns op x) (aluR k z) :=
  ⟨fun _ _ _ => exec_alu_reg _ _ _ hk hz, aluIns_falls _ _, fun s => by simp only [Sys, aluR, zsim, and_self], fun s => by simp only [aluR, zsim]⟩

theorem does_alu_imm {op : Bin} {k : UInt8} (hk : aluK op = some k) (v : Nat) :
    Does (aluIns op (n8 v)) (aluN k v) :=
  ⟨fun _ _ _ => exec_alu_imm _ _ _ hk v, aluIns_falls _ _, fun s => by simp only [Sys, aluN, zsim, and_self], fun s => by simp only [aluN, zsim]⟩

/-- `and`, `or`, `xor`. -/
def isLogic (op : Bin) : Prop := op = .and ∨ op = .or ∨ op = .xor

/-- A logic operation on two bytes each is the operation on the words. -/
theorem logic16 {op : Bin} (hl : isLogic op) (h l d e : Nat) (hh : h < 256) (hl' : l < 256) (hd : d < 256)
    (he : e < 256) :
    IR.binOp op 2 (h * 256 + l) (d * 256 + e) = IR.binOp op 1 h d * 256 + IR.binOp op 1 l e := by
  rcases hl with rfl | rfl | rfl
  · show ((h * 256 + l) &&& (d * 256 + e)) % 2 ^ (8 * 2) = (h &&& d) % 2 ^ (8 * 1) * 256 + (l &&& e) % 2 ^ (8 * 1)
    rw [and_split _ _ _ _ hl' he]
    have h1 : h &&& d < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hh
    have h2 : l &&& e < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hl'
    omega
  · show ((h * 256 + l) ||| (d * 256 + e)) % 2 ^ (8 * 2) = (h ||| d) % 2 ^ (8 * 1) * 256 + (l ||| e) % 2 ^ (8 * 1)
    rw [or_split _ _ _ _ hl' he]
    have h1 : h ||| d < 256 := Nat.or_lt_two_pow (n := 8) hh hd
    have h2 : l ||| e < 256 := Nat.or_lt_two_pow (n := 8) hl' he
    omega
  · show ((h * 256 + l) ^^^ (d * 256 + e)) % 2 ^ (8 * 2) = (h ^^^ d) % 2 ^ (8 * 1) * 256 + (l ^^^ e) % 2 ^ (8 * 1)
    rw [xor_split _ _ _ _ hl' he]
    have h1 : h ^^^ d < 256 := Nat.xor_lt_two_pow (n := 8) hh hd
    have h2 : l ^^^ e < 256 := Nat.xor_lt_two_pow (n := 8) hl' he
    omega

theorem de_toNat (s : Cpu) : s.de.toNat = s.d.toNat * 256 + s.e.toNat := mk16_toNat _ _

theorem bin16Reg_logic {op : Bin} (hl : isLogic op) :
    bin16Reg op = (do
      ins .ld [.a, .l]
      alu8 op .e
      ins .ld [.l, .a]
      ins .ld [.a, .h]
      alu8 op .d
      ins .ld [.h, .a]
      setRegs fun r => { r with a := [] }) := by
  rcases hl with rfl | rfl | rfl <;> rfl

theorem logicReg_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (hl : isLogic op) (s0 : GS) :
    wpg (bin16Reg op) E (HlDePost Z E base sF dt True (IR.binOp op 2) s0) s0 := by
  rw [bin16Reg_logic hl]
  simp only [wpg_bind, wpg_ins, wpg_alu8 hk, wpg_setRegs]
  refine ⟨(pushL_ext [⟨.ld, [.a, .l]⟩, aluIns op .e, ⟨.ld, [.l, .a]⟩, ⟨.ld, [.a, .h]⟩, aluIns op .d, ⟨.ld, [.h, .a]⟩] s0).trans
    (GExt.regs _ _), fun hx _ fr ist tmps s R hat => ?_⟩
  obtain ⟨st, at', _, hS⟩ := run_list ok F
    [(⟨.ld, [.a, .l]⟩, ldAR 5), (aluIns op .e, aluR k 3), (⟨.ld, [.l, .a]⟩, ldRA 5),
     (⟨.ld, [.a, .h]⟩, ldAR 4), (aluIns op .d, aluR k 2), (⟨.ld, [.h, .a]⟩, ldRA 4)]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact does_ld_a_l
      · exact does_alu_reg hk rfl
      · exact does_ld_l_a
      · exact does_ld_a_h
      · exact does_alu_reg hk rfl
      · exact does_ld_h_a) s0 s ((GExt.regs _ _).trans hx) R.mach hat
  refine ⟨_, st, at', R.hl_gone hS rfl (Or.inl rfl) (fun n o h => h), ?_⟩
  simp only [List.map, runL, ldAR, ldRA, aluR, zsim]
  rw [mk16_toNat, alu_val hk, alu_val hk]
  simp only [zsim]
  rw [hl_toNat, de_toNat, logic16 hl _ _ _ _ s.h.toNat_lt s.l.toNat_lt s.d.toNat_lt s.e.toNat_lt]

/-- `logicConst` on `l`: the byte with the constant, the other byte as it was. -/
theorem logicConstL_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (hl : isLogic op) (m : Nat) (hm : m < 256) (s0 : GS) :
    wpg (logicConst op .l m) E (fun _ s1 => GExt s0 s1 ∧ s1.regs.hl = s0.regs.hl ∧ s1.regs.acc = s0.regs.acc ∧
      (GExt s1 sF → ∀ s, Mach Z s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Mach Z s' ∧ Sys s s' ∧
          s'.l.toNat = IR.binOp op 1 s.l.toNat m ∧ s'.h = s.h ∧ (s1.regs.a = [] ∨ (s1.regs.a = s0.regs.a ∧ s'.a = s.a)))) s0 := by
  unfold logicConst
  by_cases h1 : (if (op == Bin.and) = true then m == 255 else m == 0) = true
  · rw [if_pos h1, wpg_pure]
    refine ⟨GExt.of_out (List.prefix_refl _) rfl rfl, rfl, rfl, fun _ s M hat => ⟨s, Steps.refl _, hat, M, Sys.refl s, ?_, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    have hx := s.l.toNat_lt
    rcases hl with rfl | rfl | rfl
    · have : m = 255 := by
        have hb : (Bin.and == Bin.and) = true := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.l.toNat &&& 255) % 2 ^ (8 * 1)
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    · have : m = 0 := by
        have hb : (Bin.or == Bin.and) = false := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.l.toNat ||| 0) % 2 ^ (8 * 1)
      rw [Nat.or_zero]
      omega
    · have : m = 0 := by
        have hb : (Bin.xor == Bin.and) = false := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.l.toNat ^^^ 0) % 2 ^ (8 * 1)
      rw [Nat.xor_zero]
      omega
  · rw [if_neg h1]
    by_cases h2 : (op == Bin.and && m == 0) = true
    · rw [if_pos h2, wpg_ins]
      have hop : op = .and := bin_beq (by simp only [Bool.and_eq_true] at h2; exact h2.1)
      have hm0 : m = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at h2; exact h2.2
      subst hop hm0
      refine ⟨GExt.of_out (by simp) rfl rfl, rfl, rfl, fun hx s M hat => ?_⟩
      obtain ⟨st, at', M'⟩ := run_reg ok F (s0 := s0) hx rfl M hat
        (((skip (op1 s) 1).setReg .hl 5 (byteOf (Int.ofNat (0 % 256)))).tick 7) (fun ad _ => rfl) rfl
        (by simp only [Sys, zsim, and_self])
      refine ⟨_, st, at', M', by simp only [Sys, zsim, and_self], ?_, by simp only [zsim], Or.inr ⟨rfl, by simp only [zsim]⟩⟩
      simp only [zsim]
      show (0 : Nat) = (s.l.toNat &&& 0) % 2 ^ (8 * 1)
      simp
    · rw [if_neg h2]
      by_cases h3 : (op == Bin.or && m == 255) = true
      · rw [if_pos h3, wpg_ins]
        have hop : op = .or := bin_beq (by simp only [Bool.and_eq_true] at h3; exact h3.1)
        have hm0 : m = 255 := by simp only [Bool.and_eq_true, beq_iff_eq] at h3; exact h3.2
        subst hop hm0
        refine ⟨GExt.of_out (by simp) rfl rfl, rfl, rfl, fun hx s M hat => ?_⟩
        obtain ⟨st, at', M'⟩ := run_reg ok F (s0 := s0) hx rfl M hat
          (((skip (op1 s) 1).setReg .hl 5 (byteOf (Int.ofNat (255 % 256)))).tick 7) (fun ad _ => rfl) rfl
          (by simp only [Sys, zsim, and_self])
        refine ⟨_, st, at', M', by simp only [Sys, zsim, and_self], ?_, by simp only [zsim], Or.inr ⟨rfl, by simp only [zsim]⟩⟩
        simp only [zsim]
        show (255 : Nat) = (s.l.toNat ||| 255) % 2 ^ (8 * 1)
        have hx := s.l.toNat_lt
        have h1' : s.l.toNat ||| 255 < 256 := Nat.or_lt_two_pow (n := 8) hx (by decide)
        have h2' : 255 ≤ s.l.toNat ||| 255 := Nat.right_le_or
        omega
      · rw [if_neg h3]
        simp only [wpg_bind, wpg_ins, wpg_alu8 hk, wpg_setRegs]
        refine ⟨(pushL_ext [⟨.ld, [.a, .l]⟩, aluIns op (n8 m), ⟨.ld, [.l, .a]⟩] s0).trans (GExt.regs _ _),
          (by first | rfl | trivial), (by first | rfl | trivial), fun hx s M hat => ?_⟩
        obtain ⟨st, at', M', hS⟩ := run_list ok F
          [(⟨.ld, [.a, .l]⟩, ldAR 5), (aluIns op (n8 m), aluN k m), (⟨.ld, [.l, .a]⟩, ldRA 5)]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl
            · exact does_ld_a_l
            · exact does_alu_imm hk m
            · exact does_ld_l_a) s0 s ((GExt.regs _ _).trans hx) M hat
        refine ⟨_, st, at', M', hS, ?_, by simp only [List.map, runL, ldAR, ldRA, aluN, zsim], Or.inl trivial⟩
        · simp only [List.map, runL, ldAR, ldRA, aluN, zsim]
          rw [alu_val hk]
          simp only [zsim]
          rw [byteOf_toNat]
          have : (Int.ofNat (m % 256) % 256).toNat = m := by
            show (((m % 256 : Nat) : Int) % 256).toNat = m
            omega
          rw [this]

/-- `logicConst` on `h`: the byte with the constant, the other byte as it was. -/
theorem logicConstH_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (hl : isLogic op) (m : Nat) (hm : m < 256) (s0 : GS) :
    wpg (logicConst op .h m) E (fun _ s1 => GExt s0 s1 ∧ s1.regs.hl = s0.regs.hl ∧ s1.regs.acc = s0.regs.acc ∧
      (GExt s1 sF → ∀ s, Mach Z s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Mach Z s' ∧ Sys s s' ∧
          s'.h.toNat = IR.binOp op 1 s.h.toNat m ∧ s'.l = s.l ∧ (s1.regs.a = [] ∨ (s1.regs.a = s0.regs.a ∧ s'.a = s.a)))) s0 := by
  unfold logicConst
  by_cases h1 : (if (op == Bin.and) = true then m == 255 else m == 0) = true
  · rw [if_pos h1, wpg_pure]
    refine ⟨GExt.of_out (List.prefix_refl _) rfl rfl, rfl, rfl, fun _ s M hat => ⟨s, Steps.refl _, hat, M, Sys.refl s, ?_, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    have hx := s.h.toNat_lt
    rcases hl with rfl | rfl | rfl
    · have : m = 255 := by
        have hb : (Bin.and == Bin.and) = true := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.h.toNat &&& 255) % 2 ^ (8 * 1)
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    · have : m = 0 := by
        have hb : (Bin.or == Bin.and) = false := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.h.toNat ||| 0) % 2 ^ (8 * 1)
      rw [Nat.or_zero]
      omega
    · have : m = 0 := by
        have hb : (Bin.xor == Bin.and) = false := by decide
        simpa [hb] using h1
      subst this
      show _ = (s.h.toNat ^^^ 0) % 2 ^ (8 * 1)
      rw [Nat.xor_zero]
      omega
  · rw [if_neg h1]
    by_cases h2 : (op == Bin.and && m == 0) = true
    · rw [if_pos h2, wpg_ins]
      have hop : op = .and := bin_beq (by simp only [Bool.and_eq_true] at h2; exact h2.1)
      have hm0 : m = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at h2; exact h2.2
      subst hop hm0
      refine ⟨GExt.of_out (by simp) rfl rfl, rfl, rfl, fun hx s M hat => ?_⟩
      obtain ⟨st, at', M'⟩ := run_reg ok F (s0 := s0) hx rfl M hat
        (((skip (op1 s) 1).setReg .hl 4 (byteOf (Int.ofNat (0 % 256)))).tick 7) (fun ad _ => rfl) rfl
        (by simp only [Sys, zsim, and_self])
      refine ⟨_, st, at', M', by simp only [Sys, zsim, and_self], ?_, by simp only [zsim], Or.inr ⟨rfl, by simp only [zsim]⟩⟩
      simp only [zsim]
      show (0 : Nat) = (s.h.toNat &&& 0) % 2 ^ (8 * 1)
      simp
    · rw [if_neg h2]
      by_cases h3 : (op == Bin.or && m == 255) = true
      · rw [if_pos h3, wpg_ins]
        have hop : op = .or := bin_beq (by simp only [Bool.and_eq_true] at h3; exact h3.1)
        have hm0 : m = 255 := by simp only [Bool.and_eq_true, beq_iff_eq] at h3; exact h3.2
        subst hop hm0
        refine ⟨GExt.of_out (by simp) rfl rfl, rfl, rfl, fun hx s M hat => ?_⟩
        obtain ⟨st, at', M'⟩ := run_reg ok F (s0 := s0) hx rfl M hat
          (((skip (op1 s) 1).setReg .hl 4 (byteOf (Int.ofNat (255 % 256)))).tick 7) (fun ad _ => rfl) rfl
          (by simp only [Sys, zsim, and_self])
        refine ⟨_, st, at', M', by simp only [Sys, zsim, and_self], ?_, by simp only [zsim], Or.inr ⟨rfl, by simp only [zsim]⟩⟩
        simp only [zsim]
        show (255 : Nat) = (s.h.toNat ||| 255) % 2 ^ (8 * 1)
        have hx := s.h.toNat_lt
        have h1' : s.h.toNat ||| 255 < 256 := Nat.or_lt_two_pow (n := 8) hx (by decide)
        have h2' : 255 ≤ s.h.toNat ||| 255 := Nat.right_le_or
        omega
      · rw [if_neg h3]
        simp only [wpg_bind, wpg_ins, wpg_alu8 hk, wpg_setRegs]
        refine ⟨(pushL_ext [⟨.ld, [.a, .h]⟩, aluIns op (n8 m), ⟨.ld, [.h, .a]⟩] s0).trans (GExt.regs _ _),
          (by first | rfl | trivial), (by first | rfl | trivial), fun hx s M hat => ?_⟩
        obtain ⟨st, at', M', hS⟩ := run_list ok F
          [(⟨.ld, [.a, .h]⟩, ldAR 4), (aluIns op (n8 m), aluN k m), (⟨.ld, [.h, .a]⟩, ldRA 4)]
          (by
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl
            · exact does_ld_a_h
            · exact does_alu_imm hk m
            · exact does_ld_h_a) s0 s ((GExt.regs _ _).trans hx) M hat
        refine ⟨_, st, at', M', hS, ?_, by simp only [List.map, runL, ldAR, ldRA, aluN, zsim], Or.inl trivial⟩
        · simp only [List.map, runL, ldAR, ldRA, aluN, zsim]
          rw [alu_val hk]
          simp only [zsim]
          rw [byteOf_toNat]
          have : (Int.ofNat (m % 256) % 256).toNat = m := by
            show (((m % 256 : Nat) : Int) % 256).toNat = m
            omega
          rw [this]

theorem bin16Const_logic {op : Bin} (hl : isLogic op) (v : Nat) :
    bin16Const op v = (do logicConst op .l (v % 256); logicConst op .h (v / 256)) := by
  rcases hl with rfl | rfl | rfl <;> rfl

theorem logicConst_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (hl : isLogic op) (v : Nat) (hv : v < 65536) (s0 : GS) :
    wpg (bin16Const op v) E (HlPost Z E base sF dt True (fun x => IR.binOp op 2 x v) s0) s0 := by
  rw [bin16Const_logic hl, wpg_bind]
  refine wpg_mono (logicConstL_ok ok F hk hl (v % 256) (Nat.mod_lt _ (by decide)) s0) ?_
  intro _ s1 ⟨hx1, hhl1, hacc1, h1⟩
  refine wpg_mono (logicConstH_ok ok F hk hl (v / 256) (by omega) s1) ?_
  intro _ s2 ⟨hx2, hhl2, hacc2, h2⟩
  refine ⟨hx1.trans hx2, fun hx _ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, M1, S1, hL, hH, ha1⟩ := h1 (hx2.trans hx) s R.mach hat
  obtain ⟨s'', st2, at2, _, S2, hH2, hL2, ha2⟩ := h2 hx s' M1 at1
  refine ⟨s'', st1.trans st2, at2, R.hl_gone (S1.trans S2) rfl ?_ (fun n o h => by
    have h' : s2.regs.acc = some (n, o) := h
    rw [hacc2, hacc1] at h'
    exact h'), ?_⟩
  · show s2.regs.a = [] ∨ (s2.regs.a = s0.regs.a ∧ s''.a = s.a)
    rcases ha2 with e2 | ⟨e2, a2⟩
    · exact Or.inl e2
    · rcases ha1 with e1 | ⟨e1, a1⟩
      · exact Or.inl (e2.trans e1)
      · exact Or.inr ⟨e2.trans e1, a2.trans a1⟩
  · show _ = IR.binOp op 2 s.hl.toNat v
    rw [hl_toNat, hH2, hL2, hL, hH, hl_toNat]
    have := logic16 hl s.h.toNat s.l.toNat (v / 256) (v % 256) s.h.toNat_lt s.l.toNat_lt (by omega)
      (Nat.mod_lt _ (by decide))
    rw [show v / 256 * 256 + v % 256 = v by omega] at this
    exact this.symm

theorem aluK_cases {op : Bin} {k : UInt8} (hk : aluK op = some k) : op = .add ∨ op = .sub ∨ isLogic op := by
  cases op <;> first | (cases hk; done) | simp [isLogic]

/-- **A two-byte operation with a constant.** -/
theorem const16_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (v : Nat) (hv : v < 65536) (s0 : GS) :
    wpg (bin16Const op v) E (HlPost Z E base sF dt True (fun x => IR.binOp op 2 x v) s0) s0 := by
  rcases aluK_cases hk with rfl | rfl | hl
  · exact addConst_ok ok F v hv s0
  · exact subConst_ok ok F v hv s0
  · exact logicConst_ok ok F hk hl v hv s0

/-- The routine of a two-byte `mul`, `div` or `mod`. -/
theorem rt16 (hrt : RtOK Z) {op : Bin} (hop : aluK op = none) :
    RtPure Z (routine16 op) (fun s s' => s'.hl.toNat = IR.binOp op 2 s.hl.toNat s.de.toNat) := by
  cases op <;> first | (cases hop; done) | skip
  · refine hrt.mul16.mono (fun s s' h1 => ?_)
    rw [h1]
    rfl
  · refine hrt.div16.mono (fun s s' h1 => ?_)
    rw [h1]
    have ha := s.hl.toNat_lt
    show _ = (if (s.de.toNat == 0) = true then 0 else s.hl.toNat / s.de.toNat) % 2 ^ (8 * 2)
    by_cases he : s.de.toNat = 0
    · simp [he]
    · have : s.hl.toNat / s.de.toNat ≤ s.hl.toNat := Nat.div_le_self _ _
      simp only [he, if_false, beq_iff_eq]
      exact (Nat.mod_eq_of_lt (by omega : s.hl.toNat / s.de.toNat < 2 ^ (8 * 2))).symm
  · refine hrt.mod16.mono (fun s s' h1 => ?_)
    rw [h1]
    have ha := s.hl.toNat_lt
    show _ = (if (s.de.toNat == 0) = true then 0 else s.hl.toNat % s.de.toNat) % 2 ^ (8 * 2)
    by_cases he : s.de.toNat = 0
    · simp [he]
    · have : s.hl.toNat % s.de.toNat ≤ s.hl.toNat := Nat.mod_le _ _
      simp only [he, if_false, beq_iff_eq]
      exact (Nat.mod_eq_of_lt (by omega : s.hl.toNat % s.de.toNat < 2 ^ (8 * 2))).symm

theorem bin16Reg_rt {op : Bin} (hop : aluK op = none) :
    bin16Reg op = (do call (routine16 op); setRegs fun r => { r with a := [] }) := by
  cases op <;> first | (cases hop; done) | rfl

theorem de_congr {s s' : Cpu} (hd : s'.d = s.d) (he : s'.e = s.e) : s'.de = s.de := by
  simp only [Cpu.de, hd, he]

/-- **A two-byte operation, the operands in `HL` and `DE`.** -/
theorem reg16_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Bin) (s0 : GS) :
    wpg (bin16Reg op) E
      (HlDePost Z E base sF dt (RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) (IR.binOp op 2) s0) s0 := by
  cases hk : aluK op with
  | some k =>
    have weaken : ∀ {m : GM Unit}, wpg m E (HlDePost Z E base sF dt True (IR.binOp op 2) s0) s0 →
        wpg m E (HlDePost Z E base sF dt (RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) (IR.binOp op 2) s0) s0 :=
      fun h => wpg_mono h (fun _ s1 ⟨hx, h⟩ => ⟨hx, fun hxF _ => h hxF trivial⟩)
    rcases aluK_cases hk with rfl | rfl | hl
    · exact weaken (addReg_ok ok F s0)
    · exact weaken (subReg_ok ok F s0)
    · exact weaken (logicReg_ok ok F hk hl s0)
  | none =>
    rw [bin16Reg_rt hk]
    simp only [wpg_bind, wpg_call, wpg_setRegs]
    refine ⟨(GExt.push _ _).trans (GExt.regs _ _), fun hx ⟨hrt, hdep⟩ fr ist tmps s R hat => ?_⟩
    obtain ⟨c1, s', cs, st, at', hval, hRel⟩ := rt_call ok hT F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.call, [.imm (.sym (routine16 op))]⟩) })
      ((GExt.regs _ _).trans hx) rfl (rt16 hrt hk) hdep R hat
    refine ⟨s', st, at', hRel _ (fun o ho => by cases ho) (fun o ho => by cases ho) (fun sl hsl => by cases hsl)
      (fun sl hsl => by cases hsl) (fun n o h => h), ?_⟩
    rw [hval, hl_congr cs.h cs.l, de_congr cs.d cs.e]

/-! ## The second operand into `DE` -/

/-- What `loadDE o` promises: `o` in `DE`, `A` and `HL` as they were. -/
def LoadDE (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (o : Opd) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs = s0.regs ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 2 o → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.hl = s.hl ∧ s'.a = s.a ∧ s'.de.toNat = IR.Sem.opd Z.c ist tmps 2 o)

theorem loadDE_ok (ok : Z.OK) (F : GFinal Z base sF) (o : Opd) (s0 : GS) :
    wpg (loadDE o) E (LoadDE Z E base sF dt o s0) s0 := by
  unfold loadDE
  simp only [wpg_bind, wpg_get]
  by_cases h1 : s0.regs.hl.contains o = true
  · simp only [h1, if_true, wpg_bind, wpg_ins]
    have hmem : o ∈ s0.regs.hl := by simpa using h1
    refine ⟨pushL_ext [⟨.ld, [.d, .h]⟩, ⟨.ld, [.e, .l]⟩] s0, rfl, fun hx fr ist tmps s hrd R hat => ?_⟩
    obtain ⟨st, at', _, hS⟩ := run_list ok F
      [(⟨.ld, [.d, .h]⟩, fun s => ((op1 s).setReg .hl 2 ((op1 s).reg .hl 4)).tick 4),
       (⟨.ld, [.e, .l]⟩, fun s => ((op1 s).setReg .hl 3 ((op1 s).reg .hl 5)).tick 4)]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, zsim, and_self], fun s => by simp only [zsim]⟩
        · exact ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, zsim, and_self], fun s => by simp only [zsim]⟩) s0 s hx R.mach hat
    refine ⟨_, st, at', R.keep hS (by simp only [List.map, runL, zsim]) (by simp only [List.map, runL, zsim]),
      by simp only [List.map, runL, zsim], by simp only [List.map, runL, zsim], ?_⟩
    rw [← R.rhl o hmem hrd.own, de_toNat, hl_toNat]
    simp only [List.map, runL, zsim]
  · simp only [h1, Bool.false_eq_true, if_false]
    have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
        wpg (do
          let p ← addrOf o
          ins .ld [.de, .mem p]) E (LoadDE Z E base sF dt o s0) s0 := by
      intro o hc
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok o s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1⟩
      subst hp
      simp only [wpg_ins]
      refine ⟨GExt.of_out (by simp [ho1]) hj1 hl1, hr1, fun hx fr ist tmps s hrd R hat => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.de, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o :=
        immW_toNat _ _ _ _ rfl hv (by omega)
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s1) (i := ⟨.ld, [.de, .mem (opdVal E o)]⟩) hx rfl R.mach
        (by rw [ho1]; exact ⟨ad, had, hpc⟩)
        (((skip (op2 s) 2).setRp .hl 1
          ((op2 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.de, .mem (opdVal E o)]⟩))).tick 20)
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          intro _
          rfl) rfl (by simp only [Sys, zsim, and_self])
      refine ⟨_, st, at', ?_, by simp only [zsim], by simp only [zsim], ?_⟩
      · rw [hr1]
        exact R.keep (by simp only [Sys, zsim, and_self]) (by simp only [zsim]) (by simp only [zsim])
      · simp only [zsim]
        rw [cpu_rd16 _ _ (by rw [hnn]; omega), hnn]
        exact opd_mem hrd hsp hc R
    cases o with
    | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
    | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
    | const v =>
      simp only [wpg_ins]
      refine ⟨GExt.of_out (by simp) rfl rfl, rfl, fun hx fr ist tmps s hrd R hat => ?_⟩
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (ldDE v s) (fun ad _ => rfl) rfl
        (by simp only [Sys, ldDE, zsim, and_self])
      refine ⟨_, st, at', R.keep (by simp only [Sys, ldDE, zsim, and_self]) (by simp only [ldDE, zsim])
        (by simp only [ldDE, zsim]), by simp only [ldDE, zsim], by simp only [ldDE, zsim], ?_⟩
      rw [ldDE_de]
      rfl

/-! ## The operation -/

/-- What a two-byte operation promises: the result in `HL`. -/
def Bin16 (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (op : Bin) (a b : Opd) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name → ∀ fr ist tmps s, Rd Z E dt 2 a → Rd Z E dt 2 b →
      Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.hl.toNat = IR.binOp op 2 (IR.Sem.opd Z.c ist tmps 2 a) (IR.Sem.opd Z.c ist tmps 2 b))

theorem small16_iff (op : Bin) : small16 op = (aluK op).isSome := by cases op <;> rfl

/-- `ex de,hl` as the model runs it. -/
def exDEHL (s : Cpu) : Cpu :=
  ({ (op1 s) with d := (op1 s).h, e := (op1 s).l, h := (op1 s).d, l := (op1 s).e } : Cpu).tick 4

theorem bin16_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Bin) (a b : Opd) (s0 : GS) :
    wpg (bin16 op a b) E (Bin16 Z E base sF dt op a b s0) s0 := by
  -- the operation on `HL` and `DE`, then the tracker forgets `HL`
  have regfin : ∀ (s1 : GS), GExt s0 s1 →
      (∀ s2, GExt s1 s2 → GExt s2 sF → ∀ fr ist tmps s, Rd Z E dt 2 a → Rd Z E dt 2 b →
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 a ∧ s'.de.toNat = IR.Sem.opd Z.c ist tmps 2 b) →
      wpg (do bin16Reg op; setRegs fun r => { r with hl := [] }) E (Bin16 Z E base sF dt op a b s0) s1 := by
    intro s1 hx1 hpre
    rw [wpg_bind]
    refine wpg_mono (reg16_ok (dt := dt) ok hT F op s1) ?_
    intro _ s2 ⟨hx2, h⟩
    rw [wpg_setRegs]
    refine ⟨hx1.trans (hx2.trans (GExt.regs _ _)), fun hx hH fr ist tmps s hra hrb R hat => ?_⟩
    obtain ⟨s', st1, at1, R1, hHL, hDE⟩ := hpre s2 hx2 ((GExt.regs _ _).trans hx) fr ist tmps s hra hrb R hat
    obtain ⟨s'', st2, at2, R2, hv⟩ := h ((GExt.regs _ _).trans hx) hH fr ist tmps s' R1 at1
    exact ⟨s'', st1.trans st2, at2, R2, by rw [hv, hHL, hDE]⟩
  unfold bin16
  simp only [wpg_bind, wpg_get]
  by_cases hat : (s0.regs.hl.contains b && a != b) = true
  · -- the second operand is in `HL`: it goes to `DE`
    simp only [hat, if_true, wpg_bind, wpg_ins, wpg_setRegs]
    have hbmem : b ∈ s0.regs.hl := by
      simp only [Bool.and_eq_true] at hat
      simpa using hat.1
    refine wpg_mono (loadHL_ok (dt := dt) ok F a _) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    have tail : wpg (do bin16Reg op; setRegs fun r => { r with hl := [] }) E (Bin16 Z E base sF dt op a b s0) s1 := by
      refine regfin s1 (((GExt.push _ _).trans (GExt.regs _ _)).trans hx1) (fun s2 hx2 hxF fr ist tmps s hra hrb R hat0 => ?_)
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.ex, [.de, .hl]⟩) })
        (((GExt.regs _ _).trans hx1).trans (hx2.trans hxF)) rfl R.mach hat0 (exDEHL s) (fun ad _ => rfl) rfl
        (by simp only [Sys, exDEHL, zsim, and_self])
      have R1 : Rel Z E fr dt { s0.regs with hl := [] } ist tmps (exDEHL s) :=
        R.hl_gone (by simp only [Sys, exDEHL, zsim, and_self]) rfl (Or.inr ⟨rfl, by simp only [exDEHL, zsim]⟩)
          (fun n o h => h)
      obtain ⟨s2', st2, at2, R2, hk2, hHL⟩ := hl (hx2.trans hxF) fr ist tmps _ hra R1 at1
      refine ⟨s2', st1.trans st2, at2, R2, hHL, ?_⟩
      rw [de_congr hk2.2.2.2.2.1 hk2.2.2.2.2.2.1, ← R.rhl b hbmem hrb.own, de_toNat, hl_toNat]
      simp only [exDEHL, zsim]
    cases b <;> simpa using tail
  · simp only [hat, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    -- the second operand into `DE`, then the operation
    have viaDE : wpg (do loadDE b; bin16Reg op; setRegs fun r => { r with hl := [] }) E
        (Bin16 Z E base sF dt op a b s0) s1 := by
      rw [wpg_bind]
      refine wpg_mono (loadDE_ok (dt := dt) ok F b s1) ?_
      intro _ s2 ⟨hx2, hr2, hd⟩
      refine regfin s2 (hx1.trans hx2) (fun s3 hx3 hxF fr ist tmps s hra hrb R hat0 => ?_)
      obtain ⟨s1', st1, at1, R1, _, hHL⟩ := hl (hx2.trans (hx3.trans hxF)) fr ist tmps s hra R hat0
      obtain ⟨s2', st2, at2, R2, hhl, _, hDE⟩ := hd (hx3.trans hxF) fr ist tmps s1' hrb R1 at1
      exact ⟨s2', st1.trans st2, at2, R2, by rw [hhl, hHL], hDE⟩
    cases b with
    | slot sl => simpa using viaDE
    | tmp t => simpa using viaDE
    | const v =>
      by_cases hsm : small16 op = true
      · simp only [hsm, Bool.not_false, Bool.and_self, if_true, wpg_bind]
        have hk : ∃ k, aluK op = some k := by
          rw [small16_iff] at hsm
          exact Option.isSome_iff_exists.mp hsm
        obtain ⟨k, hk⟩ := hk
        refine wpg_mono (const16_ok (dt := dt) ok F hk (v % 65536) (Nat.mod_lt _ (by decide)) s1) ?_
        intro _ s2 ⟨hx2, h⟩
        rw [wpg_setRegs]
        refine ⟨hx1.trans (hx2.trans (GExt.regs _ _)), fun hx _ fr ist tmps s hra hrb R hat0 => ?_⟩
        obtain ⟨s1', st1, at1, R1, _, hHL⟩ := hl (hx2.trans ((GExt.regs _ _).trans hx)) fr ist tmps s hra R hat0
        obtain ⟨s2', st2, at2, R2, hv⟩ := h ((GExt.regs _ _).trans hx) trivial fr ist tmps s1' R1 at1
        exact ⟨s2', st1.trans st2, at2, R2, by rw [hv, hHL]; rfl⟩
      · simpa [hsm] using viaDE

/-- **The code of a two-byte `bin` does what the IR's instruction does.** -/
theorem bin2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Bin) (d : Dst) (a b : Opd) (s0 : GS) :
    wpg (genInstr (.bin op 2 d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.bin op 2 d a b)
        (Rd Z E dt 2 a ∧ Rd Z E dt 2 b ∧ Wr Z E 2 d ∧ RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s0 := by
  simp only [genInstr, genBin, store, wpg_bind, beq_self_eq_true, if_true,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (bin16_ok (dt := dt) ok hT F op a b s0) ?_
  intro _ s1 ⟨hx1, h⟩
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hra, hrb, hwr, hrt, hdep⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, hHL⟩ := h (hx2.trans hxF) ⟨hrt, hdep⟩ fr ist tmps s hra hrb R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' _ hwr R1 at1 (by
    rw [hHL, Nat.mod_eq_of_lt (binOp_lt _ 2 _ _)])
  exact ⟨s'', st1.trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
