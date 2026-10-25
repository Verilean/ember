import Ember.Proof.Z80Ext
import Ember.Proof.Z80Addr

/-!
# Ember.Proof.Z80Shift — shifts by a constant, one and two bytes (plan M7.3)
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- `add a,a`, `srl r`/`rr r`, `ld b,n` as the model runs them. -/
def rotR (k z : UInt8) (s : Cpu) : Cpu :=
  ((op2 s).rot k ((op2 s).reg .hl z)).2.setReg .hl z ((op2 s).rot k ((op2 s).reg .hl z)).1 |>.tick 8
def ldB (k : Nat) (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 0 (byteOf (Int.ofNat (k % 256)))).tick 7

theorem does_add_a_a : Does ⟨.add, [.a, .a]⟩ (aluR 0 7) := does_alu_reg (op := .add) rfl rfl
section
variable (s : Cpu) (v : UInt8)

@[zsim] theorem rot7_fst : (s.rot 7 v).1 = v >>> 1 := rfl
@[zsim] theorem rot3_fst : (s.rot 3 v).1 = (v >>> 1) ||| ((if s.flag FC then (1 : UInt8) else 0) <<< 7) := rfl
@[zsim] theorem rot7_f : (s.rot 7 v).2.f = szxyp (v >>> 1) ||| Cpu.bit (v &&& 1 != 0) FC := rfl
@[zsim] theorem rot7_a : (s.rot 7 v).2.a = s.a := rfl
@[zsim] theorem rot7_h : (s.rot 7 v).2.h = s.h := rfl
@[zsim] theorem rot7_l : (s.rot 7 v).2.l = s.l := rfl
@[zsim] theorem rot7_sp : (s.rot 7 v).2.sp = s.sp := rfl
@[zsim] theorem rot7_mem : (s.rot 7 v).2.mem = s.mem := rfl
@[zsim] theorem rot7_halted : (s.rot 7 v).2.halted = s.halted := rfl
@[zsim] theorem rot7_ramStart : (s.rot 7 v).2.ramStart = s.ramStart := rfl
@[zsim] theorem rot7_io : (s.rot 7 v).2.io = s.io := rfl
@[zsim] theorem rot3_a : (s.rot 3 v).2.a = s.a := rfl
@[zsim] theorem rot3_h : (s.rot 3 v).2.h = s.h := rfl
@[zsim] theorem rot3_l : (s.rot 3 v).2.l = s.l := rfl
@[zsim] theorem rot3_sp : (s.rot 3 v).2.sp = s.sp := rfl
@[zsim] theorem rot3_mem : (s.rot 3 v).2.mem = s.mem := rfl
@[zsim] theorem rot3_halted : (s.rot 3 v).2.halted = s.halted := rfl
@[zsim] theorem rot3_ramStart : (s.rot 3 v).2.ramStart = s.ramStart := rfl
@[zsim] theorem rot3_io : (s.rot 3 v).2.io = s.io := rfl
@[zsim] theorem op2_flag (m : UInt8) : (op2 s).flag m = s.flag m := rfl

end

theorem does_srl_a : Does ⟨.srl, [.a]⟩ (rotR 7 7) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, rotR, zsim, and_self], fun s => by simp only [rotR, zsim]⟩
theorem does_ld_b (k : Nat) : Does ⟨.ld, [.b, n8 k]⟩ (ldB k) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldB, zsim, and_self], fun s => by simp only [ldB, zsim]⟩

theorem aluR_add_a (s : Cpu) : (aluR 0 7 s).a.toNat = s.a.toNat * 2 % 256 := by
  rw [show (aluR 0 7 s).a = ((op1 s).alu 0 s.a).a from rfl, alu_val (op := .add) rfl]
  show (s.a.toNat + s.a.toNat) % 2 ^ (8 * 1) = _
  omega

theorem aluR_add_hl (s : Cpu) : (aluR 0 7 s).hl = s.hl := by simp only [aluR, zsim]

theorem iter_add_a : ∀ (k : Nat) (s : Cpu), (iter k (aluR 0 7) s).a.toNat = s.a.toNat * 2 ^ k % 256 ∧
    (iter k (aluR 0 7) s).hl = s.hl
  | 0, s => ⟨by have := s.a.toNat_lt; simp only [iter]; omega, rfl⟩
  | k + 1, s => by
    obtain ⟨h1, h2⟩ := iter_add_a k (aluR 0 7 s)
    refine ⟨?_, by rw [iter, h2, aluR_add_hl]⟩
    rw [iter, h1, aluR_add_a, Nat.pow_succ, Nat.mod_mul_mod]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_comm 2]

theorem rotR_srl_a (s : Cpu) : (rotR 7 7 s).a.toNat = s.a.toNat / 2 := by
  simp only [rotR, zsim]
  rw [UInt8.toNat_shiftRight]
  rfl

theorem ldB_b (k : Nat) (hk : k < 256) (s : Cpu) : (ldB k s).b.toNat = k := by
  simp only [ldB, zsim]
  rw [byteOf_toNat]
  have e : (Int.ofNat (k % 256) : Int) = ((k % 256 : Nat) : Int) := rfl
  rw [e]
  omega

theorem does_srl_h : Does ⟨.srl, [.h]⟩ (rotR 7 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, rotR, zsim, and_self], fun s => by simp only [rotR, zsim]⟩
theorem does_rr_l : Does ⟨.rr, [.l]⟩ (rotR 3 5) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, rotR, zsim, and_self], fun s => by simp only [rotR, zsim]⟩

def ldRR (y z : UInt8) (s : Cpu) : Cpu := ((op1 s).setReg .hl y ((op1 s).reg .hl z)).tick 4
def ldL0 (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 5 (byteOf (Int.ofNat (0 % 256)))).tick 7

theorem does_ld_h_l : Does ⟨.ld, [.h, .l]⟩ (ldRR 4 5) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩
theorem does_ld_l_h : Does ⟨.ld, [.l, .h]⟩ (ldRR 5 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩
theorem does_ld_l_0 : Does ⟨.ld, [.l, n8 0]⟩ ldL0 :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldL0, zsim, and_self], fun s => by simp only [ldL0, zsim]⟩

set_option maxRecDepth 100000 in
theorem srl_byte (v : UInt8) : (v >>> 1).toNat = v.toNat / 2 ∧ (v &&& 1 != 0) = decide (v.toNat % 2 = 1) := by
  have h : ∀ n : Fin 256, ((UInt8.ofNat n.val) >>> 1).toNat = (UInt8.ofNat n.val).toNat / 2 ∧
      ((UInt8.ofNat n.val) &&& 1 != 0) = decide ((UInt8.ofNat n.val).toNat % 2 = 1) := by decide
  have := h ⟨v.toNat, v.toNat_lt⟩
  simpa using this

set_option maxRecDepth 100000 in
theorem rr_byte (v : UInt8) : ((v >>> 1) ||| ((1 : UInt8) <<< 7)).toNat = v.toNat / 2 + 128 ∧
    ((v >>> 1) ||| ((0 : UInt8) <<< 7)).toNat = v.toNat / 2 := by
  have h : ∀ n : Fin 256, (((UInt8.ofNat n.val) >>> 1) ||| ((1 : UInt8) <<< 7)).toNat =
      (UInt8.ofNat n.val).toNat / 2 + 128 ∧
      (((UInt8.ofNat n.val) >>> 1) ||| ((0 : UInt8) <<< 7)).toNat = (UInt8.ofNat n.val).toNat / 2 := by decide
  have := h ⟨v.toNat, v.toNat_lt⟩
  simpa using this

theorem rot_fc (r : UInt8) (c : Bool) : ((szxyp r ||| Cpu.bit c FC) &&& FC != 0) = c := by
  rw [flagC_bit]
  simp only [szxyp, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  simp [FZ, FPV, FS, FXY, FC, Nat.testBit]

/-- `srl h; rr l`: `HL` halved, `A` as it was. -/
theorem shr1_hl (s : Cpu) : (rotR 3 5 (rotR 7 4 s)).hl.toNat = s.hl.toNat / 2 ∧ (rotR 3 5 (rotR 7 4 s)).a = s.a := by
  have ha1 : ∀ c : Cpu, (rotR 3 5 c).a = c.a := fun c => by simp only [rotR, zsim]
  have ha2 : ∀ c : Cpu, (rotR 7 4 c).a = c.a := fun c => by simp only [rotR, zsim]
  refine ⟨?_, by rw [ha1, ha2]⟩
  have h1 : (rotR 7 4 s).h = s.h >>> 1 := by simp only [rotR, zsim]
  have h2 : (rotR 7 4 s).l = s.l := by simp only [rotR, zsim]
  have h3 : (rotR 7 4 s).flag FC = (s.h &&& 1 != 0) := by
    show ((rotR 7 4 s).f &&& FC != 0) = _
    simp only [rotR, zsim]
    exact rot_fc _ _
  have h4 : ∀ c : Cpu, (rotR 3 5 c).h = c.h := fun c => by simp only [rotR, zsim]
  have h5 : ∀ c : Cpu, (rotR 3 5 c).l = (c.l >>> 1) ||| ((if c.flag FC then (1 : UInt8) else 0) <<< 7) :=
    fun c => by simp only [rotR, zsim]; rfl
  rw [hl_toNat, h4, h1, h5, h2, h3, hl_toNat, (srl_byte s.h).1, (srl_byte s.h).2]
  have hh := s.h.toNat_lt
  have hl := s.l.toNat_lt
  by_cases hodd : s.h.toNat % 2 = 1
  · simp only [hodd, decide_true, if_true]
    rw [(rr_byte s.l).1]
    omega
  · simp only [hodd, decide_false, Bool.false_eq_true, if_false]
    rw [(rr_byte s.l).2]
    omega

theorem iter_add_hl : ∀ (k : Nat) (s : Cpu), (iter k addHLHL s).hl.toNat = s.hl.toNat * 2 ^ k % 65536 ∧
    (iter k addHLHL s).a = s.a
  | 0, s => ⟨by have := s.hl.toNat_lt; simp only [iter]; omega, rfl⟩
  | k + 1, s => by
    obtain ⟨h1, h2⟩ := iter_add_hl k (addHLHL s)
    refine ⟨?_, by rw [iter, h2, (addHLHL_keep s).2.1]⟩
    rw [iter, h1, addHLHL_hl, Nat.pow_succ, Nat.mod_mul_mod]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_comm 2]

/-- The value the IR's shift gives. -/
def shiftVal (left : Bool) (n x k : Nat) : Nat :=
  if k ≥ 8 * n then 0 else if left then IR.modN n (x <<< k) else x >>> k

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

theorem rt_shift8 (hrt : RtOK Z) (left : Bool) :
    RtPure Z (toString "rt_" ++ toString (if left = true then "shl" else "shr") ++ toString (8 * 1))
      (fun s s' => s'.a.toNat = (if left then s.a.toNat * 2 ^ s.b.toNat % 256 else s.a.toNat / 2 ^ s.b.toNat) ∧
        s'.hl = s.hl) := by
  cases left
  · exact hrt.shr8
  · exact hrt.shl8

/-- **A one-byte shift by a constant.** -/
theorem shift1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (left : Bool) (d : Dst) (a : Opd) (m k : Nat) (s0 : GS) :
    wpg (genInstr (.shift left 1 d a m (.const k))) E
      (InsPost Z E base sF dt (dtAfter dt d) (.shift left 1 d a m (.const k))
        ((Rd Z E dt 1 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, genShift, store, Codegen.load, beq_self_eq_true, if_true, bits]
  -- the value in `A`, then stored
  have fin : ∀ (s1 : GS), GExt s0 s1 →
      (GExt s1 sF → Rd Z E dt 1 a ∧ k < 2 ^ (8 * m) → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.a.toNat = shiftVal left 1 (IR.Sem.opd Z.c ist tmps 1 a) k) →
      wpg (storeA d) E (InsPost Z E base sF dt (dtAfter dt d) (.shift left 1 d a m (.const k))
        ((Rd Z E dt 1 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 1 d) s0) s1 := by
    intro s1 hx1 run
    refine wpg_mono (thenStoreA (dt := dt) ok hT F d s0 s1 (Rd Z E dt 1 a ∧ k < 2 ^ (8 * m))
      (fun ist tmps => shiftVal left 1 (IR.Sem.opd Z.c ist tmps 1 a) k) hx1
      (fun hx hH fr ist tmps s R hat => ?_)) ?_
    · obtain ⟨s', st, at', R', hA⟩ := run hx hH fr ist tmps s R hat
      refine ⟨s', st, at', R', ?_⟩
      rw [hA]
      have := s'.a.toNat_lt
      omega
    · intro _ s2 ⟨hx, h⟩
      refine ⟨hx, fun hxF hH fr ist tmps s R hat => ?_⟩
      have hkk : IR.Sem.opd Z.c ist tmps m (.const k) = k := Nat.mod_eq_of_lt hH.1.2
      have := h hxF hH fr ist tmps s R hat
      simp only [IR.Sem.step, hkk]
      exact this
  by_cases h8 : k ≥ 8 * 1
  · simp only [h8, if_true, wpg_bind]
    refine wpg_mono (loadA_ok (dt := dt) ok F (.const 0) s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine fin s1 hx1 (fun hx hH fr ist tmps s R hat => ?_)
    obtain ⟨s', st, at', R', _, hA⟩ := hl hx fr ist tmps s trivial R hat
    refine ⟨s', st, at', R', ?_⟩
    rw [hA, shiftVal, if_pos h8]
    rfl
  · simp only [h8, if_false]
    by_cases h0 : (k == 0) = true
    · simp only [h0, if_true, wpg_bind]
      have hk0 : k = 0 := by simpa using h0
      refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine fin s1 hx1 (fun hx hH fr ist tmps s R hat => ?_)
      obtain ⟨s', st, at', R', _, hA⟩ := hl hx fr ist tmps s hH.1 R hat
      refine ⟨s', st, at', R', ?_⟩
      have hlt := opd_lt Z.c ist tmps 1 a
      rw [hA, shiftVal, if_neg h8, hk0]
      cases left
      · rfl
      · show _ = (IR.Sem.opd Z.c ist tmps 1 a <<< 0) % 2 ^ (8 * 1)
        rw [Nat.shiftLeft_zero, Nat.mod_eq_of_lt hlt]
    · simp only [h0, Bool.false_eq_true, if_false, wpg_bind]
      refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      by_cases hc1 : (left && decide (k ≤ 3)) = true
      · simp only [hc1, if_true, wpg_bind]
        rw [wpg_rep_ins, wpg_setRegs]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
        obtain ⟨hleft, hk3⟩ := hc1
        refine fin _ (hx1.trans ((pushK_ext _ _ _).trans (GExt.regs _ _))) (fun hx hH fr ist tmps s R hat => ?_)
        have hxk : GExt (pushK (.ins ⟨.add, [.a, .a]⟩) k s1) sF := (GExt.regs _ _).trans hx
        obtain ⟨s', st, at', R', _, hA⟩ := hl ((pushK_ext _ _ _).trans hxk) fr ist tmps s hH.1 R hat
        obtain ⟨st2, at2, _⟩ := run_rep ok F (aluR 0 7) does_add_a_a.exec does_add_a_a.falls does_add_a_a.sys
          does_add_a_a.io k s1 s' hxk R'.mach at'
        have hS := iter_inv (aluR 0 7) Sys Sys.refl (fun _ _ _ => Sys.trans) does_add_a_a.sys k s'
        obtain ⟨hv, hhl⟩ := iter_add_a k s'
        refine ⟨_, st.trans st2, at2, R'.of_sys hS rfl (fun o h => by rw [pushK_regs] at h; exact h)
          (fun o ho hown => by rw [hhl]; exact R'.rhl o (by rw [pushK_regs] at ho; exact ho) hown)
          (fun n o h => by rw [pushK_regs] at h; exact h), ?_⟩
        rw [hv, hA, shiftVal, if_neg h8, hleft]
        show _ = (IR.Sem.opd Z.c ist tmps 1 a <<< k) % 2 ^ (8 * 1)
        rw [Nat.shiftLeft_eq]
      · simp only [hc1, Bool.false_eq_true, if_false]
        by_cases hc2 : (!left && k == 1) = true
        · simp only [hc2, if_true, wpg_bind, wpg_ins, wpg_setRegs]
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc2
          obtain ⟨hleft, hk1⟩ := hc2
          refine fin _ (hx1.trans ((GExt.push _ _).trans (GExt.regs _ _))) (fun hx hH fr ist tmps s R hat => ?_)
          have hxk : GExt { s1 with out := s1.out.push (.ins ⟨.srl, [.a]⟩) } sF := (GExt.regs _ _).trans hx
          obtain ⟨s', st, at', R', _, hA⟩ := hl ((GExt.push _ _).trans hxk) fr ist tmps s hH.1 R hat
          obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1) hxk rfl R'.mach at' (rotR 7 7 s')
            (fun _ _ => does_srl_a.exec _ _ _) rfl (does_srl_a.sys s') (does_srl_a.io s')
          refine ⟨_, st.trans st2, at2, R'.of_sys (does_srl_a.sys s') rfl (fun o h => h)
            (fun o ho hown => R'.rhl o ho hown) (fun n o h => h), ?_⟩
          rw [rotR_srl_a, hA, shiftVal, if_neg h8, hleft, hk1]
          show _ = IR.Sem.opd Z.c ist tmps 1 a >>> 1
          rw [Nat.shiftRight_eq_div_pow]
        · simp only [hc2, Bool.false_eq_true, if_false, wpg_bind, wpg_ins, wpg_call, wpg_setRegs]
          refine fin _ (hx1.trans (((GExt.push _ _).trans (GExt.push _ _)).trans (GExt.regs _ _)))
            (fun hx hH fr ist tmps s R hat => ?_)
          have hxk : GExt (pushL [⟨.ld, [.b, n8 k]⟩, ⟨.call, [.imm (.sym (toString "rt_" ++
              toString (if left = true then "shl" else "shr") ++ toString (8 * 1)))]⟩] s1) sF :=
            (GExt.regs _ _).trans hx
          obtain ⟨s', st, at', R', _, hA⟩ :=
            hl (((GExt.push _ _).trans (GExt.push _ _)).trans hxk) fr ist tmps s hH.1 R hat
          obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1)
            (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) ((GExt.push _ _).trans hxk) rfl
            R'.mach at' (ldB k s') (fun _ _ => rfl) rfl ((does_ld_b k).sys s') ((does_ld_b k).io s')
          have R2 : Rel Z E fr dt s1.regs ist tmps (ldB k s') :=
            R'.keep ((does_ld_b k).sys s') (by simp only [ldB, zsim]) (by simp only [ldB, zsim])
          obtain ⟨c1, s'', cs, st3, at3, ⟨hval, hhl⟩, hRel⟩ := rt_call ok hT F
            (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) hxk rfl (rt_shift8 hrt left) hdep R2 at2
          refine ⟨s'', (st.trans st2).trans st3, at3, hRel _ (fun o ho => by cases ho) (fun o ho hown => ?_)
            (fun sl hsl => by cases hsl) (fun sl hsl => R2.inhl sl hsl) (fun n o h => h), ?_⟩
          · rw [hhl, hl_congr cs.h cs.l]
            exact R2.rhl o ho hown
          · rw [hval, cs.a, cs.b, ldB_b k (by omega)]
            have ha2 : (ldB k s').a = s'.a := by simp only [ldB, zsim]
            rw [ha2, hA, shiftVal, if_neg h8]
            cases left
            · show _ = IR.Sem.opd Z.c ist tmps 1 a >>> k
              rw [Nat.shiftRight_eq_div_pow]
              rfl
            · show _ = (IR.Sem.opd Z.c ist tmps 1 a <<< k) % 2 ^ (8 * 1)
              rw [Nat.shiftLeft_eq]
              rfl

theorem rt_shift16 (hrt : RtOK Z) (left : Bool) :
    RtPure Z (toString "rt_" ++ toString (if left = true then "shl" else "shr") ++ toString (8 * 2))
      (fun s s' => s'.hl.toNat = (if left then s.hl.toNat * 2 ^ s.b.toNat % 65536 else s.hl.toNat / 2 ^ s.b.toNat) ∧
        s'.a = s.a) := by
  cases left
  · exact hrt.shr16
  · exact hrt.shl16

/-- **A two-byte shift by a constant.** -/
theorem shift2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (left : Bool) (d : Dst) (a : Opd) (m k : Nat) (s0 : GS) :
    wpg (genInstr (.shift left 2 d a m (.const k))) E
      (InsPost Z E base sF dt (dtAfter dt d) (.shift left 2 d a m (.const k))
        ((Rd Z E dt 2 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 2 d) s0) s0 := by
  simp only [genInstr, genShift, store, Codegen.load, beq_self_eq_true, if_true, bits,
    show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false]
  have fin : ∀ (s1 : GS), GExt s0 s1 →
      (GExt s1 sF → Rd Z E dt 2 a ∧ k < 2 ^ (8 * m) → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.hl.toNat = shiftVal left 2 (IR.Sem.opd Z.c ist tmps 2 a) k) →
      wpg (storeHL d) E (InsPost Z E base sF dt (dtAfter dt d) (.shift left 2 d a m (.const k))
        ((Rd Z E dt 2 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 2 d) s0) s1 := by
    intro s1 hx1 run
    refine wpg_mono (thenStoreHL (dt := dt) ok hT F d s0 s1 (Rd Z E dt 2 a ∧ k < 2 ^ (8 * m))
      (fun ist tmps => shiftVal left 2 (IR.Sem.opd Z.c ist tmps 2 a) k) hx1
      (fun hx hH fr ist tmps s R hat => ?_)) ?_
    · obtain ⟨s', st, at', R', hHL⟩ := run hx hH fr ist tmps s R hat
      refine ⟨s', st, at', R', ?_⟩
      rw [hHL]
      have := s'.hl.toNat_lt
      omega
    · intro _ s2 ⟨hx, h⟩
      refine ⟨hx, fun hxF hH fr ist tmps s R hat => ?_⟩
      have hkk : IR.Sem.opd Z.c ist tmps m (.const k) = k := Nat.mod_eq_of_lt hH.1.2
      have := h hxF hH fr ist tmps s R hat
      simp only [IR.Sem.step, hkk]
      exact this
  -- the operand in `HL`, then code on registers alone: `f`, leaving `A` as it was
  have reg : ∀ (l : List (Instr × (Cpu → Cpu))), (∀ q, q ∈ l → Does q.1 q.2) → ∀ (s1 : GS), GExt s0 s1 →
      (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 2 a → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧ KeepHL s s' ∧
          s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 a) →
      (∀ s' : Cpu, (runL (l.map (·.2)) s').a = s'.a ∧
        ∀ x, s'.hl.toNat = x → x < 65536 → (runL (l.map (·.2)) s').hl.toNat = shiftVal left 2 x k) →
      wpg (storeHL d) E (InsPost Z E base sF dt (dtAfter dt d) (.shift left 2 d a m (.const k))
        ((Rd Z E dt 2 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 2 d) s0)
        { (pushL (l.map (·.1)) s1) with regs := { s1.regs with hl := [] } } := by
    intro l hd s1 hx1 hl hf
    refine fin _ (hx1.trans ((pushL_ext _ _).trans (GExt.regs _ _))) (fun hx hH fr ist tmps s R hat => ?_)
    have hxk : GExt (pushL (l.map (·.1)) s1) sF := (GExt.regs _ _).trans hx
    obtain ⟨s', st, at', R', _, hHL⟩ := hl ((pushL_ext _ _).trans hxk) fr ist tmps s hH.1 R hat
    obtain ⟨st2, at2, _, hS⟩ := run_list ok F l hd s1 s' hxk R'.mach at'
    obtain ⟨hfa, hfv⟩ := hf s'
    exact ⟨_, st.trans st2, at2, R'.hl_gone hS rfl (Or.inr ⟨rfl, hfa⟩) (fun n o h => h),
      hfv _ hHL (opd_lt Z.c ist tmps 2 a)⟩
  by_cases h8 : k ≥ 8 * 2
  · simp only [h8, if_true, wpg_bind]
    refine wpg_mono (loadHL_ok (dt := dt) ok F (.const 0) s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine fin s1 hx1 (fun hx hH fr ist tmps s R hat => ?_)
    obtain ⟨s', st, at', R', _, hHL⟩ := hl hx fr ist tmps s trivial R hat
    refine ⟨s', st, at', R', ?_⟩
    rw [hHL, shiftVal, if_pos h8]
    rfl
  · simp only [h8, if_false]
    by_cases h0 : (k == 0) = true
    · simp only [h0, if_true, wpg_bind]
      have hk0 : k = 0 := by simpa using h0
      refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine fin s1 hx1 (fun hx hH fr ist tmps s R hat => ?_)
      obtain ⟨s', st, at', R', _, hHL⟩ := hl hx fr ist tmps s hH.1 R hat
      refine ⟨s', st, at', R', ?_⟩
      have hlt := opd_lt Z.c ist tmps 2 a
      rw [hHL, shiftVal, if_neg h8, hk0]
      cases left
      · rfl
      · show _ = (IR.Sem.opd Z.c ist tmps 2 a <<< 0) % 2 ^ (8 * 2)
        rw [Nat.shiftLeft_zero, Nat.mod_eq_of_lt hlt]
    · simp only [h0, Bool.false_eq_true, if_false, wpg_bind]
      have hk0 : k ≠ 0 := by simpa using h0
      refine wpg_mono (loadHL_ok (dt := dt) ok F a s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      by_cases hc1 : (left && decide (k ≤ 4)) = true
      · simp only [hc1, if_true, wpg_bind]
        rw [wpg_rep_ins, wpg_setRegs]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
        obtain ⟨hleft, hk4⟩ := hc1
        refine fin _ (hx1.trans ((pushK_ext _ _ _).trans (GExt.regs _ _))) (fun hx hH fr ist tmps s R hat => ?_)
        have hxk : GExt (pushK (.ins ⟨.add, [.hl, .hl]⟩) k s1) sF := (GExt.regs _ _).trans hx
        obtain ⟨s', st, at', R', _, hHL⟩ := hl ((pushK_ext _ _ _).trans hxk) fr ist tmps s hH.1 R hat
        obtain ⟨st2, at2, _⟩ := run_rep ok F addHLHL does_add_hl_hl.exec does_add_hl_hl.falls does_add_hl_hl.sys
          does_add_hl_hl.io k s1 s' hxk R'.mach at'
        have hS := iter_inv addHLHL Sys Sys.refl (fun _ _ _ => Sys.trans) does_add_hl_hl.sys k s'
        obtain ⟨hv, ha⟩ := iter_add_hl k s'
        refine ⟨_, st.trans st2, at2, R'.hl_gone hS rfl (Or.inr ⟨by rw [pushK_regs], ha⟩)
          (fun n o h => by rw [pushK_regs] at h; exact h), ?_⟩
        rw [hv, hHL, shiftVal, if_neg h8, hleft]
        show _ = (IR.Sem.opd Z.c ist tmps 2 a <<< k) % 2 ^ (8 * 2)
        rw [Nat.shiftLeft_eq]
      · simp only [hc1, Bool.false_eq_true, if_false]
        by_cases hc2 : (left && k == 8) = true
        · simp only [hc2, if_true, wpg_bind, wpg_ins, wpg_setRegs]
          simp only [Bool.and_eq_true, beq_iff_eq] at hc2
          obtain ⟨hleft, hk8⟩ := hc2
          refine reg [(⟨.ld, [.h, .l]⟩, ldRR 4 5), (⟨.ld, [.l, n8 0]⟩, ldL0)] (by
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact does_ld_h_l
            · exact does_ld_l_0) s1 hx1 hl (fun s' => ⟨by simp only [List.map, runL, ldRR, ldL0, zsim], fun x hx hlt => ?_⟩)
          rw [shiftVal, if_neg h8, hleft, hk8, hl_toNat]
          simp only [List.map, runL, ldRR, ldL0, zsim]
          rw [byte0, ← hx, hl_toNat]
          show s'.l.toNat * 256 + 0 = ((s'.h.toNat * 256 + s'.l.toNat) <<< 8) % 2 ^ (8 * 2)
          rw [Nat.shiftLeft_eq]
          have := s'.l.toNat_lt
          omega
        · simp only [hc2, Bool.false_eq_true, if_false]
          by_cases hc3 : (!left && k == 8) = true
          · simp only [hc3, if_true, wpg_bind, wpg_ins, wpg_setRegs]
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc3
            obtain ⟨hleft, hk8⟩ := hc3
            refine reg [(⟨.ld, [.l, .h]⟩, ldRR 5 4), (⟨.ld, [.h, n8 0]⟩, ldH0)] (by
              intro q hq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl
              · exact does_ld_l_h
              · exact does_ld_h_0) s1 hx1 hl (fun s' => ⟨by simp only [List.map, runL, ldRR, ldH0, zsim], fun x hx hlt => ?_⟩)
            rw [shiftVal, if_neg h8, hleft, hk8, hl_toNat]
            simp only [List.map, runL, ldRR, ldH0, zsim]
            rw [byte0, ← hx, hl_toNat]
            show 0 * 256 + s'.h.toNat = (s'.h.toNat * 256 + s'.l.toNat) >>> 8
            rw [Nat.shiftRight_eq_div_pow]
            have := s'.l.toNat_lt
            omega
          · simp only [hc3, Bool.false_eq_true, if_false]
            by_cases hc4 : (!left && decide (k ≤ 2)) = true
            · simp only [hc4, if_true, wpg_bind]
              simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc4
              obtain ⟨hleft, hk2⟩ := hc4
              have hk12 : k = 1 ∨ k = 2 := by omega
              rcases hk12 with rfl | rfl
              · simp only [rep, wpg_bind, wpg_ins, wpg_pure, wpg_setRegs]
                refine reg [(⟨.srl, [.h]⟩, rotR 7 4), (⟨.rr, [.l]⟩, rotR 3 5)] (by
                  intro q hq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                  rcases hq with rfl | rfl
                  · exact does_srl_h
                  · exact does_rr_l) s1 hx1 hl (fun s' => ⟨(shr1_hl s').2, fun x hx hlt => ?_⟩)
                rw [shiftVal, if_neg h8, hleft]
                show (rotR 3 5 (rotR 7 4 s')).hl.toNat = x >>> 1
                rw [(shr1_hl s').1, hx, Nat.shiftRight_eq_div_pow]
              · simp only [rep, wpg_bind, wpg_ins, wpg_pure, wpg_setRegs]
                refine reg [(⟨.srl, [.h]⟩, rotR 7 4), (⟨.rr, [.l]⟩, rotR 3 5), (⟨.srl, [.h]⟩, rotR 7 4),
                  (⟨.rr, [.l]⟩, rotR 3 5)] (by
                  intro q hq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                  rcases hq with rfl | rfl | rfl | rfl
                  · exact does_srl_h
                  · exact does_rr_l
                  · exact does_srl_h
                  · exact does_rr_l) s1 hx1 hl (fun s' => ⟨by
                    show (rotR 3 5 (rotR 7 4 (rotR 3 5 (rotR 7 4 s')))).a = s'.a
                    rw [(shr1_hl _).2, (shr1_hl _).2], fun x hx hlt => ?_⟩)
                rw [shiftVal, if_neg h8, hleft]
                show (rotR 3 5 (rotR 7 4 (rotR 3 5 (rotR 7 4 s')))).hl.toNat = x >>> 2
                rw [(shr1_hl _).1, (shr1_hl s').1, hx, Nat.shiftRight_eq_div_pow]
                omega
            · simp only [hc4, Bool.false_eq_true, if_false, wpg_bind, wpg_ins, wpg_call, wpg_setRegs]
              refine fin _ (hx1.trans (((GExt.push _ _).trans (GExt.push _ _)).trans (GExt.regs _ _)))
                (fun hx hH fr ist tmps s R hat => ?_)
              have hxk : GExt (pushL [⟨.ld, [.b, n8 k]⟩, ⟨.call, [.imm (.sym (toString "rt_" ++
                  toString (if left = true then "shl" else "shr") ++ toString (8 * 2)))]⟩] s1) sF :=
                (GExt.regs _ _).trans hx
              obtain ⟨s', st, at', R', _, hHL⟩ :=
                hl (((GExt.push _ _).trans (GExt.push _ _)).trans hxk) fr ist tmps s hH.1 R hat
              obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1)
                (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) ((GExt.push _ _).trans hxk) rfl
                R'.mach at' (ldB k s') (fun _ _ => rfl) rfl ((does_ld_b k).sys s') ((does_ld_b k).io s')
              have R2 : Rel Z E fr dt s1.regs ist tmps (ldB k s') :=
                R'.keep ((does_ld_b k).sys s') (by simp only [ldB, zsim]) (by simp only [ldB, zsim])
              obtain ⟨c1, s'', cs, st3, at3, ⟨hval, ha⟩, hRel⟩ := rt_call ok hT F
                (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) hxk rfl (rt_shift16 hrt left) hdep
                R2 at2
              refine ⟨s'', (st.trans st2).trans st3, at3, hRel _ (fun o ho hown => ?_) (fun o ho => by cases ho)
                (fun sl hsl => R2.ina sl hsl) (fun sl hsl => by cases hsl) (fun n o h => h), ?_⟩
              · rw [ha, cs.a]
                exact R2.ra o ho hown
              · rw [hval, hl_congr cs.h cs.l, cs.b, ldB_b k (by omega)]
                have hhl2 : (ldB k s').hl = s'.hl := by simp only [ldB, zsim]
                rw [hhl2, hHL, shiftVal, if_neg h8]
                cases left
                · show _ = IR.Sem.opd Z.c ist tmps 2 a >>> k
                  rw [Nat.shiftRight_eq_div_pow]
                  rfl
                · show _ = (IR.Sem.opd Z.c ist tmps 2 a <<< k) % 2 ^ (8 * 2)
                  rw [Nat.shiftLeft_eq]
                  rfl

theorem sym_off (pc : Nat) {name : String} {entry : Nat} (h : Z.sym name entry) (off : Nat) :
    (Z.a.env pc).val (.sym name (Int.ofNat off)) = Int.ofNat (entry + off) := by
  unfold ZCtx.sym at h
  rw [val_sym _ _ _ (Int.ofNat entry) (by simp [Assembled.env, h])]
  show ((entry : Int) + (off : Int)) = ((entry + off : Nat) : Int)
  omega

/-- A word written at `A` (in RAM) from `HL`. -/
theorem wr16_mem (s : Cpu) (x : UInt16) {A v : Nat} (hx : x.toNat = A) (hb : A + 2 ≤ 65536)
    (hram : s.ramStart.toNat ≤ A) (hHL : s.hl.toNat = v % 65536) :
    (((skip (op1 s) 2).wr16 x (op1 s).hl).tick 16).mem = IR.Sem.wr s.mem A 2 v := by
  have hx1 : (x + 1).toNat = A + 1 := by
    rw [UInt16.toNat_add, hx]
    show (A + 1) % 65536 = _
    omega
  simp only [zsim, Cpu.wr16]
  rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hx1]; omega),
    cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hx]; exact hram)]
  simp only [zsim]
  rw [hx, hx1]
  refine wr_two _ _ _ (by omega) _ _ ?_ ?_
  · rw [UInt16.toNat_toUInt8, hHL]
    omega
  · rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, hHL]
    rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]
    omega

/-- `ld hl,(p); ld (q),hl; ld hl,0; ld (p),hl`: the word at `P` moved to `Q`, `P` cleared. -/
theorem moveWord (ok : Z.OK) (F : GFinal Z base sF) {s1 : GS} (vp vq : Val) (P Q : Nat)
    (hvp : ∀ pc, (Z.a.env pc).val vp = Int.ofNat P) (hvq : ∀ pc, (Z.a.env pc).val vq = Int.ofNat Q)
    (hP : Z.ramStart ≤ P ∧ P + 2 ≤ 65536) (hQ : Z.ramStart ≤ Q ∧ Q + 2 ≤ 65536)
    (hx : GExt (pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩, ⟨.ld, [.mem vp, .hl]⟩] s1) sF)
    {s : Cpu} (M : Mach Z s) (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536)
    (hat : At Z.addrs (base + s1.out.size) s) :
    ∃ s', Steps s s' ∧
      At Z.addrs (base + (pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩,
        ⟨.ld, [.mem vp, .hl]⟩] s1).out.size) s' ∧
      s'.mem = IR.Sem.wr (IR.Sem.wr s.mem Q 2 (IR.Sem.rd s.mem P 2)) P 2 0 ∧ s'.sp = s.sp ∧
      s'.halted = s.halted ∧ s'.ramStart = s.ramStart := by
  obtain ⟨ad, had, hpc⟩ := hat
  -- ld hl,(p)
  have hnn1 : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem vp]⟩).toNat = P := immW_toNat _ _ _ _ rfl (hvp ad) (by omega)
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((skip (op1 s) 2).setHL
      ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem vp]⟩))).tick 16 := ⟨_, rfl⟩
  have hS1 : Sys s c1 := by rw [hc1]; simp only [Sys, zsim, and_self]
  obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1) (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem vp]⟩) })
    ((pushL_ext [⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩, ⟨.ld, [.mem vp, .hl]⟩] _).trans hx) rfl M
    ⟨ad, had, hpc⟩ c1 (fun ad' had' => by
      rw [had] at had'
      cases had'
      intro _
      rw [hc1]
      rfl) rfl hS1 (by rw [hc1]; simp only [zsim])
  have hhl1 : c1.hl.toNat = IR.Sem.rd s.mem P 2 := by
    rw [hc1]
    simp only [zsim]
    rw [cpu_rd16 _ _ (by rw [hnn1]; omega), hnn1]
  -- ld (q),hl
  obtain ⟨ad2, had2, hpc2⟩ := at1
  have hnn2 : (Instr.immW (Z.a.env ad2) ⟨.ld, [.mem vq, .hl]⟩).toNat = Q := immW_toNat _ _ _ _ rfl (hvq ad2) (by omega)
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ((skip (op1 c1) 2).wr16 (Instr.immW (Z.a.env ad2) ⟨.ld, [.mem vq, .hl]⟩)
      (op1 c1).hl).tick 16 := ⟨_, rfl⟩
  obtain ⟨st2, at2⟩ := run_ins ok F (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem vp]⟩) })
    (s1 := pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩] s1) (i := ⟨.ld, [.mem vq, .hl]⟩)
    ((pushL_ext [⟨.ld, [.hl, n16 0]⟩, ⟨.ld, [.mem vp, .hl]⟩] _).trans hx) rfl M1.1 M1.2 ⟨ad2, had2, hpc2⟩
    (s' := c2) (fun ad' had' => by
      rw [had2] at had'
      cases had'
      intro _
      rw [hc2]
      rfl) rfl (by rw [hc2]; simp only [zsim])
  have hm2 : c2.mem = IR.Sem.wr s.mem Q 2 (IR.Sem.rd s.mem P 2) := by
    rw [hc2, wr16_mem c1 _ hnn2 hQ.2 (by rw [hS1.2.1, hrs]; exact hQ.1)
      (v := IR.Sem.rd s.mem P 2) (by rw [hhl1]; exact (Nat.mod_eq_of_lt (rd_lt _ _ 2)).symm), hS1.1]
  have hrs2 : c2.ramStart = s.ramStart := by rw [hc2]; simp only [zsim]; exact hS1.2.1
  have hh2 : c2.halted = s.halted := by rw [hc2]; simp only [zsim]; exact hS1.2.2.1
  have hsp2 : c2.sp = s.sp := by rw [hc2]; simp only [zsim]; exact hS1.2.2.2
  have M2 : Mach Z c2 :=
    ⟨Img.of_wr M.1 hrs2 hm2 (by rw [hrs]; exact hQ.1) hQ.2, by rw [hh2]; exact M.2⟩
  -- ld hl,0
  obtain ⟨c3, hc3⟩ : ∃ c3 : Cpu, c3 = ((skip (op1 c2) 2).setHL
      (w16 (byteOf (Int.ofNat (0 % 65536))) (byteOf (Int.ofNat (0 % 65536) / 256)))).tick 10 := ⟨_, rfl⟩
  have hS3 : Sys c2 c3 := by rw [hc3]; simp only [Sys, zsim, and_self]
  obtain ⟨st3, at3, M3⟩ := run_reg ok F (s0 := pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩] s1)
    (s1 := pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩] s1)
    ((pushL_ext [⟨.ld, [.mem vp, .hl]⟩] _).trans hx) rfl M2 at2 c3 (fun _ _ => by intro _; rw [hc3]; rfl) rfl hS3
    (by rw [hc3]; simp only [zsim])
  have hhl3 : c3.hl.toNat = 0 := by
    rw [hc3]
    simp only [zsim]
    exact w16_val 0 (by decide)
  -- ld (p),hl
  obtain ⟨ad4, had4, hpc4⟩ := at3
  have hnn4 : (Instr.immW (Z.a.env ad4) ⟨.ld, [.mem vp, .hl]⟩).toNat = P := immW_toNat _ _ _ _ rfl (hvp ad4) (by omega)
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = ((skip (op1 c3) 2).wr16 (Instr.immW (Z.a.env ad4) ⟨.ld, [.mem vp, .hl]⟩)
      (op1 c3).hl).tick 16 := ⟨_, rfl⟩
  obtain ⟨st4, at4⟩ := run_ins ok F (s0 := pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩] s1)
    (s1 := pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩, ⟨.ld, [.mem vp, .hl]⟩] s1)
    (i := ⟨.ld, [.mem vp, .hl]⟩) hx rfl M3.1 M3.2 ⟨ad4, had4, hpc4⟩
    (s' := c4) (fun ad' had' => by
      rw [had4] at had'
      cases had'
      intro _
      rw [hc4]
      rfl) rfl (by rw [hc4]; simp only [zsim])
  have hm4 : c4.mem = IR.Sem.wr c2.mem P 2 0 := by
    rw [hc4, wr16_mem c3 _ hnn4 hP.2 (by rw [hS3.2.1, hrs2, hrs]; exact hP.1) (v := 0) (by rw [hhl3]), hS3.1]
  refine ⟨c4, ((st1.trans st2).trans st3).trans st4, at4, by rw [hm4, hm2], ?_, ?_, ?_⟩
  · rw [hc4]
    simp only [zsim]
    rw [hS3.2.2.2, hsp2]
  · rw [hc4]
    simp only [zsim]
    rw [hS3.2.2.1, hh2]
  · rw [hc4]
    simp only [zsim]
    rw [hS3.2.1, hrs2]

theorem shift4_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (left : Bool) (d : Dst) (a : Opd) (m : Nat) (s0 : GS) :
    wpg (genInstr (.shift left 4 d a m (.const 16))) E
      (InsPost Z E base sF dt (dtAfter dt d) (.shift left 4 d a m (.const 16))
        ((RdW Z E dt 4 a ∧ 16 < 2 ^ (8 * m)) ∧ Wr Z E 4 d) s0) s0 := by
  simp only [genInstr, genShift, store, Codegen.load, bits, show ¬ ((16 : Nat) ≥ 8 * 4) from by decide, if_false,
    show ((16 : Nat) == 0) = false from rfl, show ((4 : Nat) == 1) = false from rfl,
    show ((4 : Nat) == 2) = false from rfl, Bool.false_eq_true, beq_self_eq_true, Bool.and_self, if_true]
  have hacr := ok.accRam
  -- the word moved within the accumulator (`P` to `Q`), then the accumulator stored
  have core : ∀ (vp vq : Val) (P Q : Nat), (∃ off, vp = .sym "rt_acc" off) →
      (AccRef Z → ∀ pc, (Z.a.env pc).val vp = Int.ofNat P) →
      (AccRef Z → ∀ pc, (Z.a.env pc).val vq = Int.ofNat Q) → Z.acc ≤ P → P + 2 ≤ Z.acc + 8 → Z.acc ≤ Q → Q + 2 ≤ Z.acc + 8 →
      (∀ m : ByteArray, m.size = 65536 →
        IR.Sem.rd (IR.Sem.wr (IR.Sem.wr m Q 2 (IR.Sem.rd m P 2)) P 2 0) Z.acc 4 =
          shiftVal left 4 (IR.Sem.rd m Z.acc 4) 16) →
      wpg (do
        (do
          loadAcc 4 a
          ins .ld [.hl, .mem vp]
          ins .ld [.mem vq, .hl]
          ins .ld [.hl, n16 0]
          ins .ld [.mem vp, .hl]
          killAll)
        storeAcc 4 d) E
        (InsPost Z E base sF dt (dtAfter dt d) (.shift left 4 d a m (.const 16))
          ((RdW Z E dt 4 a ∧ 16 < 2 ^ (8 * m)) ∧ Wr Z E 4 d) s0) s0 := by
    intro vp vq P Q hsym hvp hvq hP1 hP2 hQ1 hQ2 hval
    simp only [wpg_bind]
    refine wpg_mono (loadAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep a s0) ?_
    intro _ s1 ⟨hx1, hacc1, hl⟩
    simp only [wpg_ins, killAll, wpg_setRegs]
    refine wpg_mono (storeAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep d _) ?_
    intro _ s2 ⟨hx2, hs⟩
    have hxp : GExt s1 (pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩,
        ⟨.ld, [.mem vp, .hl]⟩] s1) := pushL_ext _ _
    refine ⟨hx1.trans ((hxp.trans (GExt.regs _ _)).trans hx2), fun hxF ⟨⟨hrd, hk⟩, hwr⟩ fr ist tmps s R hat => ?_⟩
    have hxm : GExt (pushL [⟨.ld, [.hl, .mem vp]⟩, ⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩,
        ⟨.ld, [.mem vp, .hl]⟩] s1) sF := (GExt.regs _ _).trans (hx2.trans hxF)
    obtain ⟨s', st1, at1, R1⟩ := hl (hxp.trans hxm) fr ist tmps s hrd R hat
    have href : AccRef Z := by
      obtain ⟨off, rfl⟩ := hsym
      exact ⟨_, ⟨.ld, [.hl, .mem (.sym "rt_acc" off)]⟩, off,
        F.emitted (s := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .mem (.sym "rt_acc" off)]⟩) })
          ((pushL_ext [⟨.ld, [.mem vq, .hl]⟩, ⟨.ld, [.hl, n16 0]⟩, ⟨.ld, [.mem (.sym "rt_acc" off), .hl]⟩] _).trans hxm)
          rfl, rfl⟩
    obtain ⟨s'', st2, at2, hmem, hsp', hh', hrs'⟩ := moveWord ok F vp vq P Q (hvp href) (hvq href) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ hxm R1.mach R1.rs R1.msz at1
    have hfree : AccFree Z s' s'' := by
      intro x _ _ hx
      rw [hmem, wr_get_far _ _ _ _ _ (by omega) (by omega), wr_get_far _ _ _ _ _ (by omega) (by omega)]
    have R2 : Rel Z E fr dt {} ist tmps s'' :=
      R1.acc_free ok hT hfree (by rw [hmem, wr_size, wr_size]; exact R1.msz) hrs' hh' hsp' (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h)
        (fun k sl h => by cases h) (fun k o h => by cases h)
    obtain ⟨s3, st3, at3, R3⟩ := hs hxF fr ist tmps s'' (shiftVal left 4 (IR.Sem.opd Z.c ist tmps 4 a) 16) hwr R2 at2
      (by rw [hmem, hval _ R1.msz, R1.racc 4 a hacc1 (Rd.own_w hrd)])
    have hkk : IR.Sem.opd Z.c ist tmps m (.const 16) = 16 := Nat.mod_eq_of_lt hk
    simp only [IR.Sem.step, hkk]
    exact ⟨s3, (st1.trans st2).trans st3, at3, R3⟩
  have h16 : (2 : Nat) ^ (8 * 2) = 65536 := by decide
  have h32 : (2 : Nat) ^ (8 * 4) = 4294967296 := by decide
  cases left with
  | true =>
    simp only [if_true]
    refine core (.sym "rt_acc") (.sym "rt_acc" 2) Z.acc (Z.acc + 2) ⟨0, rfl⟩ (fun hr pc => sym_val pc (ok.accSym hr))
      (fun hr pc => sym_off pc (ok.accSym hr) 2) (by omega) (by omega) (by omega) (by omega) (fun mm hm => ?_)
    rw [rd_add _ _ 2 2, rd_wr _ _ _ _ (by rw [wr_size, hm]; omega) (by rw [wr_size, hm]; exact Nat.le_refl _),
      rd_wr_other _ _ _ _ _ 2 (by omega) (by omega) (Or.inl (Nat.le_refl _)),
      rd_wr _ _ _ _ (by rw [hm]; omega) (by rw [hm]; exact Nat.le_refl _), rd_low mm Z.acc 2 2]
    rw [show IR.Sem.rd mm Z.acc (2 + 2) = IR.Sem.rd mm Z.acc 4 from rfl]
    show _ = (if 16 ≥ 8 * 4 then 0 else if true = true then (IR.Sem.rd mm Z.acc 4 <<< 16) % 2 ^ (8 * 4) else _)
    rw [if_neg (by decide), if_pos rfl, Nat.shiftLeft_eq, h16, h32]
    have := rd_lt mm Z.acc 4
    rw [h32] at this
    omega
  | false =>
    simp only [Bool.false_eq_true, if_false]
    refine core (.sym "rt_acc" 2) (.sym "rt_acc") (Z.acc + 2) Z.acc ⟨2, rfl⟩ (fun hr pc => sym_off pc (ok.accSym hr) 2)
      (fun hr pc => sym_val pc (ok.accSym hr)) (by omega) (by omega) (by omega) (by omega) (fun mm hm => ?_)
    rw [rd_add _ _ 2 2, rd_wr_other _ _ _ _ _ 2 (by omega) (by omega) (Or.inr (Nat.le_refl _)),
      rd_wr _ _ _ _ (by rw [hm]; omega) (by rw [hm]; exact Nat.le_refl _),
      rd_wr _ _ _ _ (by rw [wr_size, hm]; omega) (by rw [wr_size, hm]; exact Nat.le_refl _), rd_high mm Z.acc 2 2]
    rw [show IR.Sem.rd mm Z.acc (2 + 2) = IR.Sem.rd mm Z.acc 4 from rfl]
    show _ = (if 16 ≥ 8 * 4 then 0 else if false = true then _ else IR.Sem.rd mm Z.acc 4 >>> 16)
    rw [if_neg (by decide), if_neg (by decide), Nat.shiftRight_eq_div_pow, h16]
    have := rd_lt mm Z.acc 4
    rw [h32] at this
    omega


/-- **A four-byte right shift by a constant** other than 16: `ld b,k` and `call rt_shr32`
(`RtOK.shr32`). -/
theorem shiftR4_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (a : Opd) (m k : Nat) (hk0 : 0 < k) (hk : k < 32)
    (hk16 : k ≠ 16) (s0 : GS) :
    wpg (genInstr (.shift false 4 d a m (.const k))) E
      (InsPost Z E base sF dt (dtAfter dt d) (.shift false 4 d a m (.const k))
        ((RdW Z E dt 4 a ∧ k < 2 ^ (8 * m)) ∧ Wr Z E 4 d) s0) s0 := by
  have hge : ¬ (k ≥ 8 * 4) := by omega
  have h0 : (k == 0) = false := by simp; omega
  have h16 : (k == 16) = false := by simp; omega
  simp only [genInstr, genShift, store, Codegen.load, bits, hge, if_false, h0, h16,
    show ((4 : Nat) == 1) = false from rfl, show ((4 : Nat) == 2) = false from rfl, beq_self_eq_true,
    Bool.and_false, Bool.false_eq_true, wpg_bind]
  have hname : toString "rt_" ++ toString "shr" ++ toString (8 * 4) = "rt_shr32" := rfl
  simp only [hname]
  refine wpg_mono (loadAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep a s0) ?_
  intro _ s1 ⟨hx1, hacc1, hl⟩
  simp only [wpg_ins, wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F (by omega) hrt.wide hdep d _) ?_
  intro _ s2 ⟨hx2, hs⟩
  refine ⟨hx1.trans (((GExt.push _ _).trans (GExt.push _ _)).trans ((GExt.regs _ _).trans hx2)),
    fun hxF ⟨⟨hrd, hkm⟩, hwr⟩ fr ist tmps s R hat => ?_⟩
  have hxc : GExt
      { s1 with out := (s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩)).push (.ins ⟨.call, [.imm (.sym "rt_shr32")]⟩) } sF :=
    (GExt.regs _ {}).trans (hx2.trans hxF)
  obtain ⟨s', st1, at1, R1⟩ := hl (((GExt.push _ _).trans (GExt.push _ _)).trans hxc) fr ist tmps s hrd R hat
  have hv := R1.racc 4 a hacc1 (Rd.own_w hrd)
  -- ld b,k
  obtain ⟨st2, at2, _⟩ := run_reg ok F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) ((GExt.push _ _).trans hxc) rfl
    R1.mach at1 (ldB k s') (fun _ _ => rfl) rfl ((does_ld_b k).sys s') ((does_ld_b k).io s')
  have R2 := R1.keep ((does_ld_b k).sys s') (by simp only [ldB, zsim]) (by simp only [ldB, zsim])
  -- call rt_shr32
  obtain ⟨c1, s'', cs, st3, at3, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F
    (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.b, n8 k]⟩) }) hxc rfl hrt.shr32 hdep R2 at2
    (fun _ _ => trivial)
  have hroom := R2.room
  have hstk := ok.stack
  have hacr := ok.accRam
  have hacs := ok.accStack
  have hspv : (ldB k s').sp.toNat = fr.sp.toNat := by rw [R2.sp]
  have hc1 : IR.Sem.rd c1.mem Z.acc 4 = IR.Sem.rd s'.mem Z.acc 4 := by
    rw [rd_congr _ _ _ _ (by omega) (fun x h1 h2 => cs.mem x (by omega)), ((does_ld_b k).sys s').1]
  have R3 : Rel Z E fr dt {} ist tmps s'' :=
    R2.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho) (fun o ho => by cases ho)
      (fun sl h => by cases h) (fun sl h => by cases h) (fun k o h => by cases h) (fun k sl h => by cases h)
      (fun k o h => by cases h)
  obtain ⟨s3, st4, at4, R4⟩ := hs hxF fr ist tmps s'' (shiftVal false 4 (IR.Sem.opd Z.c ist tmps 4 a) k) hwr R3 at3
    (by
      rw [hrel, hc1, hv, cs.b, ldB_b k (by omega), shiftVal, if_neg hge]
      show _ = IR.Sem.opd Z.c ist tmps 4 a >>> k
      rw [Nat.shiftRight_eq_div_pow])
  have hkk : IR.Sem.opd Z.c ist tmps m (.const k) = k := Nat.mod_eq_of_lt hkm
  simp only [IR.Sem.step, hkk]
  exact ⟨s3, ((st1.trans st2).trans st3).trans st4, at4, R4⟩
end

end Ember.Proof.Z80Gen
