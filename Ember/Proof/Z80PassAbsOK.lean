import Ember.Proof.Z80PassAbs
import Ember.Proof.Z80PassChkOK
import Ember.Proof.Z80PassTaint
import Ember.Proof.Z80Flags
import Ember.Proof.Z80Bits

/-!
# Ember.Proof.Z80PassAbsOK — what is known of the registers, kept by the instructions (plan M7.3)
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Gen

theorem szxyp_fc1 (r : UInt8) : ((szxyp r ||| FH) &&& FC != 0) = false := by
  cases r with
  | ofBitVec bv => cases bv with
    | ofFin k => revert k; decide +kernel

theorem szxyp_fc2 (r : UInt8) : (szxyp r &&& FC != 0) = false := by
  cases r with
  | ofBitVec bv => cases bv with
    | ofFin k => revert k; decide +kernel

set_option linter.unusedSimpArgs false in
/-- **What an ordinary instruction leaves of the registers**, by the classes of `Z80PassAbs`. -/
theorem form_frame (f : Form) (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (s s' : Cpu)
    (hs : execI f.instr n nn s inp = some s') :
    (f.writesH = false → s'.h = s.h) ∧ (f.writesL = false → s'.l = s.l) ∧
      (f.keepsDE = true → s'.d = s.d ∧ s'.e = s.e) ∧ (f.keepsBC = true → s'.b = s.b ∧ s'.c = s.c) ∧
      (f.keepsCF = true → s'.f = s.f) ∧ (f.clearsCF = true → s'.flag FC = false) := by
  cases s with
  | mk a f0 b c0 d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r0 iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  cases f
  all_goals
    simp +decide only [Form.instr, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?,
      Option.some.injEq, Option.map_some, if_true, if_false] at hs
    subst hs
    simp only [Form.writesH, Form.writesL, Form.keepsDE, Form.keepsBC, Form.keepsCF, Form.clearsCF,
      op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp, Cpu.rp,
      Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.add16, Cpu.sbc16, Cpu.rd, Cpu.wr, Cpu.wr16, Cpu.rd16, Cpu.de, Cpu.flag,
      Cpu.inc8, Cpu.dec8, Cpu.rot, Cpu.setBC, Cpu.setDE, Cpu.bc, Ember.Proof.Z80Gen.lo_mk16,
      Ember.Proof.Z80Gen.hi_mk16, Bool.false_eq_true, Bool.true_eq_false, implies_true, false_implies, true_implies, true_and, and_true,
      forall_const]
  all_goals (try (repeat' split))
  all_goals first
    | with_reducible rfl
    | (simp only [szxyp_fc1, szxyp_fc2]; done)
    | (exfalso; simp_all +decide; done)
    | (simp; done)
    | skip

/-! ## The instructions that change what is known -/

section
variable {n : UInt8} {nn : UInt16} {inp : UInt16 → UInt8} {s s' : Cpu}

set_option linter.unusedSimpArgs false

/-- The simp set of the forms' instructions. -/
macro "form_simp" hs:ident : tactic => `(tactic| (
  simp +decide only [Form.instr, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?,
    Option.some.injEq, Option.map_some, if_true, if_false] at $hs:ident
  subst $hs:ident
  simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp, Cpu.rp,
    Cpu.idxGet, Cpu.idxSet, Cpu.setBC, Cpu.setDE, Cpu.bc, Cpu.de, Cpu.flag]))

theorem sp_ldHLI (v : Val) (hs : execI (Form.ldHLI v).instr n nn s inp = some s') : s'.hl = nn := by
  cases s; form_simp hs; exact mk16_hi_lo nn

theorem sp_ldBCI (v : Val) (hs : execI (Form.ldBCI v).instr n nn s inp = some s') : s'.bc = nn := by
  cases s; form_simp hs; exact mk16_hi_lo nn

theorem sp_ldDEI (v : Val) (hs : execI (Form.ldDEI v).instr n nn s inp = some s') : s'.de = nn := by
  cases s; form_simp hs; exact mk16_hi_lo nn

theorem sp_addHLBC (hs : execI Form.addHLBC.instr n nn s inp = some s') :
    s'.hl = (s.add16 s.hl s.bc).1 ∧ s'.f = (s.add16 s.hl s.bc).2.f := by
  cases s; form_simp hs; exact ⟨mk16_hi_lo _, rfl⟩

theorem sp_addHLDE (hs : execI Form.addHLDE.instr n nn s inp = some s') :
    s'.hl = (s.add16 s.hl s.de).1 ∧ s'.f = (s.add16 s.hl s.de).2.f := by
  cases s; form_simp hs; exact ⟨mk16_hi_lo _, rfl⟩

theorem sp_sbcHLDE (hs : execI Form.sbcHLDE.instr n nn s inp = some s') :
    s'.hl = (s.sbc16 s.de).hl ∧ s'.f = (s.sbc16 s.de).f := by
  cases s; form_simp hs; first | exact ⟨rfl, rfl⟩ | simp

theorem sp_incHL (hs : execI Form.incHL.instr n nn s inp = some s') : s'.hl = s.hl + 1 := by
  cases s; form_simp hs; exact mk16_hi_lo _

theorem sp_decHL (hs : execI Form.decHL.instr n nn s inp = some s') : s'.hl = s.hl - 1 := by
  cases s; form_simp hs; exact mk16_hi_lo _

theorem sp_decBC (hs : execI Form.decBC.instr n nn s inp = some s') : s'.bc = s.bc - 1 := by
  cases s; form_simp hs; exact mk16_hi_lo _

theorem sp_incDE (hs : execI Form.incDE.instr n nn s inp = some s') : s'.de = s.de + 1 := by
  cases s; form_simp hs; exact mk16_hi_lo _

theorem sp_exDEHL (hs : execI Form.exDEHL.instr n nn s inp = some s') : s'.hl = s.de ∧ s'.de = s.hl := by
  cases s; form_simp hs; first | exact ⟨rfl, rfl⟩ | simp

theorem sp_ldDH (hs : execI Form.ldDH.instr n nn s inp = some s') : s'.d = s.h ∧ s'.e = s.e := by
  cases s; form_simp hs; first | exact ⟨rfl, rfl⟩ | simp

theorem sp_ldEL (hs : execI Form.ldEL.instr n nn s inp = some s') : s'.e = s.l ∧ s'.d = s.d := by
  cases s; form_simp hs; first | exact ⟨rfl, rfl⟩ | simp

end

/-! ## Intervals -/

namespace Itv

theorem In_top {v : Nat} (h : v < 65536) : Itv.In v Itv.top := ⟨Nat.zero_le _, by simp [Itv.top]; omega⟩

theorem not_In_emp (v : Nat) : ¬ Itv.In v Itv.emp := by simp [Itv.In, Itv.emp]; omega

theorem isEmp_false {v : Nat} {i : Itv} (h : Itv.In v i) : i.isEmp = false := by
  simp only [Itv.isEmp, decide_eq_false_iff_not, Nat.not_lt]; exact Nat.le_trans h.1 h.2

theorem In_hull_l {v : Nat} {a : Itv} (b : Itv) (h : Itv.In v a) : Itv.In v (a.hull b) := by
  unfold Itv.hull
  rw [isEmp_false h]
  simp only [Bool.false_eq_true, if_false]
  split
  · exact h
  · exact ⟨by simp only; have := h.1; omega, by simp only; have := h.2; omega⟩

theorem In_hull_r {v : Nat} (a : Itv) {b : Itv} (h : Itv.In v b) : Itv.In v (a.hull b) := by
  unfold Itv.hull
  split
  · exact h
  · rw [isEmp_false h]
    simp only [Bool.false_eq_true, if_false]
    exact ⟨by simp only; have := h.1; omega, by simp only; have := h.2; omega⟩

theorem In_cst {x : Nat} (v : Option Int) (hv : ∀ n, v = some n → 0 ≤ n → n < 65536 → x = n.toNat)
    (hx : x < 65536) : Itv.In x (Itv.cst v) := by
  unfold Itv.cst
  split
  · rename_i n
    split
    · rename_i h
      rw [hv n rfl h.1 h.2]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · exact In_top hx
  · exact In_top hx

theorem In_add {x y : Nat} {X Y : Itv} (hx : Itv.In x X) (hy : Itv.In y Y) :
    (x + y < 65536 → Itv.In (x + y) (Itv.add X Y).1) ∧ (65536 ≤ x + y → Itv.In (x + y - 65536) (Itv.add X Y).2) := by
  unfold Itv.add
  rw [isEmp_false hx, isEmp_false hy]
  simp only [Bool.or_false, Bool.false_eq_true, if_false]
  obtain ⟨a1, a2⟩ := hx
  obtain ⟨b1, b2⟩ := hy
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos (by omega)]; exact ⟨by simp only; omega, by simp only; omega⟩
  · rw [if_pos (by omega)]; exact ⟨by simp only; omega, by simp only; omega⟩

theorem In_sub {x y c : Nat} {X Y : Itv} (hx : Itv.In x X) (hy : Itv.In y Y) :
    (y + c ≤ x → Itv.In (x - y - c) (Itv.sub X Y c).1) ∧ (x < y + c → Itv.In (x + 65536 - y - c) (Itv.sub X Y c).2) := by
  unfold Itv.sub
  rw [isEmp_false hx, isEmp_false hy]
  simp only [Bool.or_false, Bool.false_eq_true, if_false]
  obtain ⟨a1, a2⟩ := hx
  obtain ⟨b1, b2⟩ := hy
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos (by omega)]; exact ⟨by simp only; omega, by simp only; omega⟩
  · rw [if_pos (by omega)]; exact ⟨by simp only; omega, by simp only; omega⟩

theorem In_inc {x : Nat} {X : Itv} (hx : Itv.In x X) (h : x < 65536) : Itv.In ((x + 1) % 65536) X.inc := by
  unfold Itv.inc
  rw [isEmp_false hx]
  simp only [Bool.false_eq_true, if_false]
  obtain ⟨a1, a2⟩ := hx
  split
  · exact ⟨by simp only; omega, by simp only; omega⟩
  · exact In_top (Nat.mod_lt _ (by decide))

theorem In_dec {x : Nat} {X : Itv} (hx : Itv.In x X) (h : x < 65536) : Itv.In ((x + 65535) % 65536) X.dec := by
  unfold Itv.dec
  rw [isEmp_false hx]
  simp only [Bool.false_eq_true, if_false]
  obtain ⟨a1, a2⟩ := hx
  split
  · exact ⟨by simp only; omega, by simp only; omega⟩
  · exact In_top (Nat.mod_lt _ (by decide))

theorem In_le {x : Nat} {X Y : Itv} (h : X.le Y = true) (hx : Itv.In x X) : Itv.In x Y := by
  unfold Itv.le at h
  rw [isEmp_false hx] at h
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨Nat.le_trans h.1 hx.1, Nat.le_trans hx.2 h.2⟩

theorem In_within {x : Nat} {X : Itv} {lo hi n : Nat} (h : X.within lo hi n = true) (hx : Itv.In x X) :
    lo ≤ x ∧ x + n ≤ hi := by
  unfold Itv.within at h
  rw [isEmp_false hx] at h
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨Nat.le_trans h.1 hx.1, by have := hx.2; omega⟩

end Itv

/-! ## What is known, of a CPU -/

theorem AF.top_sat (s : Cpu) : AF.top.Sat s := by
  refine ⟨fun _ => Itv.In_top s.hl.toNat_lt, fun _ => Itv.In_top s.hl.toNat_lt, Itv.In_top s.de.toNat_lt,
    Itv.In_top s.bc.toNat_lt, fun v h => ?_, fun v h => ?_⟩ <;> cases h

theorem AF.sat_getD {a : AS} {s : Cpu} (h : ASat a s) : (a.getD AF.top).Sat s := by
  cases a with
  | none => exact AF.top_sat s
  | some a => exact h

theorem AF.norm_sat {a : AF} {s : Cpu} (h : a.Sat s) : ASat a.norm s := by
  unfold AF.norm; split
  · trivial
  · exact h

theorem AF.hl_sat {a : AF} {s : Cpu} (h : a.Sat s) : Itv.In s.hl.toNat a.hl := by
  cases hc : s.flag FC
  · exact Itv.In_hull_l _ (h.1 hc)
  · exact Itv.In_hull_r _ (h.2.1 hc)

theorem AF.hlR_sat {a : AF} {s : Cpu} (h : a.Sat s) : Itv.In s.hl.toNat a.hlR := by
  unfold AF.hlR
  split
  · rename_i v hv
    split
    · rename_i hb
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
      have e := h.2.2.2.2.1 v hv
      have hbc := h.2.2.2.1
      unfold Itv.In at hbc ⊢
      exact ⟨by simp only; omega, by simp only; omega⟩
    · exact AF.hl_sat h
  · exact AF.hl_sat h

theorem AF.deR_sat {a : AF} {s : Cpu} (h : a.Sat s) : Itv.In s.de.toNat a.deR := by
  unfold AF.deR
  split
  · rename_i v hv
    split
    · rename_i hb
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
      have e := h.2.2.2.2.2 v hv
      have hbc := h.2.2.2.1
      unfold Itv.In at hbc ⊢
      exact ⟨by simp only; omega, by simp only; omega⟩
    · exact h.2.2.1
  · exact h.2.2.1

theorem AS.hlR_sat {a : AS} {s : Cpu} (h : ASat a s) : Itv.In s.hl.toNat a.hlR := AF.hlR_sat (AF.sat_getD h)
theorem AS.deR_sat {a : AS} {s : Cpu} (h : ASat a s) : Itv.In s.de.toNat a.deR := AF.deR_sat (AF.sat_getD h)

theorem one?_eq {i : Itv} {p : Nat} (h : i.one? = some p) {x : Nat} (hx : Itv.In x i) : x = p := by
  unfold Itv.one? at h
  split at h
  · cases h; have := hx.1; have := hx.2; omega
  · cases h

theorem AF.hbD_sat {a : AF} {s : Cpu} (h : a.Sat s) : ∀ v, a.hbD = some v → s.hl.toNat + s.bc.toNat = v := by
  intro v hv
  unfold AF.hbD at hv
  split at hv
  · cases hv; exact h.2.2.2.2.1 _ (by assumption)
  · split at hv
    · rename_i p q hp hq
      cases hv
      rw [one?_eq hp (AF.hl_sat h), one?_eq hq h.2.2.2.1]
    · cases hv

theorem AF.dbD_sat {a : AF} {s : Cpu} (h : a.Sat s) : ∀ v, a.dbD = some v → s.de.toNat + s.bc.toNat = v := by
  intro v hv
  unfold AF.dbD at hv
  split at hv
  · cases hv; exact h.2.2.2.2.2 _ (by assumption)
  · split at hv
    · rename_i p q hp hq
      cases hv
      rw [one?_eq hp h.2.2.1, one?_eq hq h.2.2.2.1]
    · cases hv

theorem AF.le_sat {x y : AF} {s : Cpu} (hle : x.le y = true) (h : x.Sat s) : y.Sat s := by
  unfold AF.le at hle
  simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hle
  obtain ⟨⟨⟨⟨⟨l0, l1⟩, l2⟩, l3⟩, l4⟩, l5⟩ := hle
  refine ⟨fun hc => Itv.In_le l0 (h.1 hc), fun hc => Itv.In_le l1 (h.2.1 hc), Itv.In_le l2 h.2.2.1,
    Itv.In_le l3 h.2.2.2.1, fun v hv => ?_, fun v hv => ?_⟩
  · rcases l4 with e | e
    · rw [e] at hv; cases hv
    · rw [e] at hv; exact AF.hbD_sat h v hv
  · rcases l5 with e | e
    · rw [e] at hv; cases hv
    · rw [e] at hv; exact AF.dbD_sat h v hv

theorem AS.le_sat {x y : AS} {s : Cpu} (hle : AS.le x y = true) (h : ASat x s) : ASat y s := by
  cases y with
  | none => trivial
  | some y =>
    cases x with
    | none => exact AF.le_sat hle (AF.top_sat s)
    | some x => exact AF.le_sat hle h

/-- What is known of a CPU is of its registers `H`, `L`, `D`, `E`, `B`, `C` and its flags. -/
theorem AF.congr {a : AF} {s s' : Cpu} (h : a.Sat s) (e1 : s'.h = s.h) (e2 : s'.l = s.l) (e3 : s'.d = s.d)
    (e4 : s'.e = s.e) (e5 : s'.b = s.b) (e6 : s'.c = s.c) (e7 : s'.f = s.f) : a.Sat s' := by
  have hl : s'.hl = s.hl := by simp only [Cpu.hl, e1, e2]
  have de : s'.de = s.de := by simp only [Cpu.de, e3, e4]
  have bc : s'.bc = s.bc := by simp only [Cpu.bc, e5, e6]
  have fc : s'.flag FC = s.flag FC := by simp only [Cpu.flag, e7]
  unfold AF.Sat at h ⊢
  rw [hl, de, bc, fc]; exact h

theorem ASat.congr {a : AS} {s s' : Cpu} (h : ASat a s) (e1 : s'.h = s.h) (e2 : s'.l = s.l) (e3 : s'.d = s.d)
    (e4 : s'.e = s.e) (e5 : s'.b = s.b) (e6 : s'.c = s.c) (e7 : s'.f = s.f) : ASat a s' := by
  cases a with
  | none => trivial
  | some a => exact AF.congr h e1 e2 e3 e4 e5 e6 e7

/-! ## An ordinary instruction keeps what is known -/

theorem absF_gen (la : List (String × Nat)) (f : Form) (a : AF) (hf : f.special = false) : absF la f a = absG f a := by
  cases f <;> first | rfl | simp [Form.special] at hf

theorem hl_eq {s s' : Cpu} (e1 : s'.h = s.h) (e2 : s'.l = s.l) : s'.hl = s.hl := by simp only [Cpu.hl, e1, e2]
theorem de_eq {s s' : Cpu} (e1 : s'.d = s.d) (e2 : s'.e = s.e) : s'.de = s.de := by simp only [Cpu.de, e1, e2]
theorem bc_eq {s s' : Cpu} (e1 : s'.b = s.b) (e2 : s'.c = s.c) : s'.bc = s.bc := by simp only [Cpu.bc, e1, e2]
theorem fc_eq {s s' : Cpu} (e : s'.f = s.f) : s'.flag FC = s.flag FC := by simp only [Cpu.flag, e]

/-- **The instructions with no effect of their own** on what is known. -/
theorem absG_sound (f : Form) {n : UInt8} {nn : UInt16} {inp : UInt16 → UInt8} {s s' : Cpu}
    (hs : execI f.instr n nn s inp = some s') {a : AF} (h : a.Sat s) : (absG f a).Sat s' := by
  obtain ⟨fH, fL, fDE, fBC, fCF, fClr⟩ := form_frame f n nn inp s s' hs
  have hlT := Itv.In_top s'.hl.toNat_lt
  have hlS := AF.hl_sat h
  unfold absG AF.Sat
  simp only
  refine ⟨fun hc => ?_, fun hc => ?_, ?_, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · split
    · exact hlT
    · rename_i hw
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hw
      rw [hl_eq (fH hw.1) (fL hw.2)]
      split
      · rename_i hk; rw [fc_eq (fCF hk)] at hc; exact h.1 hc
      · split <;> exact hlS
  · split
    · exact hlT
    · rename_i hw
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hw
      rw [hl_eq (fH hw.1) (fL hw.2)]
      split
      · rename_i hk; rw [fc_eq (fCF hk)] at hc; exact h.2.1 hc
      · split
        · rename_i _ hk; rw [fClr hk] at hc; cases hc
        · exact hlS
  · split
    · rename_i hk; obtain ⟨e1, e2⟩ := fDE hk; rw [de_eq e1 e2]; exact h.2.2.1
    · exact Itv.In_top s'.de.toNat_lt
  · split
    · rename_i hk; obtain ⟨e1, e2⟩ := fBC hk; rw [bc_eq e1 e2]; exact h.2.2.2.1
    · exact Itv.In_top s'.bc.toNat_lt
  · split at hv
    · cases hv
    · rename_i hw
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hw
      obtain ⟨⟨w1, w2⟩, w3⟩ := hw
      obtain ⟨e1, e2⟩ := fBC (by simpa using w3)
      rw [hl_eq (fH w1) (fL w2), bc_eq e1 e2]; exact h.2.2.2.2.1 v hv
  · split at hv
    · cases hv
    · rename_i hw
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hw
      obtain ⟨d1, d2⟩ := fDE (by simpa using hw.1)
      obtain ⟨e1, e2⟩ := fBC (by simpa using hw.2)
      rw [de_eq d1 d2, bc_eq e1 e2]; exact h.2.2.2.2.2 v hv

/-! ## `sbc hl,rr` with either carry -/

set_option linter.unusedSimpArgs false in
theorem sbc16_hl (s : Cpu) (b : UInt16) :
    (s.sbc16 b).hl.toNat = (s.hl.toNat + 2 * 65536 - b.toNat - (if s.flag FC then 1 else 0)) % 65536 := by
  have ha := s.hl.toNat_lt
  have hb := b.toNat_lt
  unfold Cpu.sbc16
  show (Cpu.setHL s _).hl.toNat = _
  rw [setHL_hl]
  cases hc : s.flag FC <;>
    simp only [hc, Bool.false_eq_true, if_false, if_true, UInt32.toNat_toUInt16, UInt32.toNat_sub,
      UInt16.toNat_toUInt32, UInt32.toNat_zero, UInt32.toNat_one] <;> omega

set_option linter.unusedSimpArgs false in
theorem sbc16_c (s : Cpu) (b : UInt16) :
    (s.sbc16 b).flag FC = decide (s.hl.toNat < b.toNat + (if s.flag FC then 1 else 0)) := by
  have ha := s.hl.toNat_lt
  have hb := b.toNat_lt
  unfold Cpu.sbc16
  show ((_ : UInt8) &&& FC != 0) = _
  rw [flagC_bit]
  cases hc : s.flag FC
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or,
      Nat.testBit_and, bit_testBit]
    simp [FZ, FPV, FH, FC, FN, FS, FXY, Nat.testBit]
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_sub, UInt16.toNat_toUInt32, UInt32.toNat_zero, UInt32.toNat_one]
    have h65 : (65535 : UInt32).toNat = 65535 := rfl
    simp only [h65]
    omega

/-! ## The instructions with an effect of their own -/

theorem AF.sat_of {a : AF} {s : Cpu} (h0 : s.flag FC = false → Itv.In s.hl.toNat a.h0)
    (h1 : s.flag FC = true → Itv.In s.hl.toNat a.h1) (hde : Itv.In s.de.toNat a.de) (hbc : Itv.In s.bc.toNat a.bc)
    (hhb : ∀ v, a.hb = some v → s.hl.toNat + s.bc.toNat = v) (hdb : ∀ v, a.db = some v → s.de.toNat + s.bc.toNat = v) :
    a.Sat s := ⟨h0, h1, hde, hbc, hhb, hdb⟩

/-- **An ordinary instruction keeps what is known**, as `absF` says (`hv`: its operand's value, from
`A`'s labels, is the immediate it runs with). -/
theorem absF_sound (la : List (String × Nat)) (f : Form) {n : UInt8} {nn : UInt16} {inp : UInt16 → UInt8}
    {s s' : Cpu} (hs : execI f.instr n nn s inp = some s')
    (hv : ∀ m, valOf la (argVal f.instr) = some m → 0 ≤ m → m < 65536 → nn.toNat = m.toNat)
    {a : AF} (h : a.Sat s) : (absF la f a).Sat s' := by
  cases hsp : f.special
  · rw [absF_gen la f a hsp]; exact absG_sound f hs h
  obtain ⟨fH, fL, fDE, fBC, fCF, fClr⟩ := form_frame f n nn inp s s' hs
  have hlS := AF.hl_sat h
  have hlT := Itv.In_top s'.hl.toNat_lt
  obtain ⟨h0, h1, hde, hbc, hhb, hdb⟩ := h
  cases f <;> simp only [Form.special, Bool.false_eq_true] at hsp
  case ldHLI v =>
    have e := sp_ldHLI v hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hv' : ∀ m, valOf la v = some m → 0 ≤ m → m < 65536 → nn.toNat = m.toNat := hv
    have hi := Itv.In_cst (valOf la v) hv' (by rw [← e]; exact s'.hl.toNat_lt)
    refine AF.sat_of (fun _ => by rw [e]; exact hi) (fun _ => by rw [e]; exact hi) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case ldBCI v =>
    have e := sp_ldBCI v hs
    obtain ⟨d1, d2⟩ := fDE rfl
    have hv' : ∀ m, valOf la v = some m → 0 ≤ m → m < 65536 → nn.toNat = m.toNat := hv
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [e]; exact Itv.In_cst _ hv' (by rw [← e]; exact s'.bc.toNat_lt)) (fun v hv => by cases hv) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
  case ldDEI v =>
    have e := sp_ldDEI v hs
    obtain ⟨b1, b2⟩ := fBC rfl
    have hv' : ∀ m, valOf la v = some m → 0 ≤ m → m < 65536 → nn.toNat = m.toNat := hv
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [e]; exact Itv.In_cst _ hv' (by rw [← e]; exact s'.de.toNat_lt)) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => ?_) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
    · rw [hl, bc_eq b1 b2]; exact hhb v hv
  case addHLBC =>
    obtain ⟨e, ef⟩ := sp_addHLBC hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hval : s'.hl.toNat = (s.hl.toNat + s.bc.toNat) % 65536 := by rw [e]; exact add16_val _ _ _
    have hc : s'.flag FC = decide (65536 ≤ s.hl.toNat + s.bc.toNat) := by
      rw [← add16_fc s s.hl s.bc]; simp only [Cpu.flag, ef]
    have A := Itv.In_add hlS hbc
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [hc] at c; simp only [decide_eq_false_iff_not, Nat.not_le] at c
      rw [hval, Nat.mod_eq_of_lt c]; exact A.1 c
    · rw [hc] at c; simp only [decide_eq_true_eq] at c
      have := s.hl.toNat_lt; have := s.bc.toNat_lt
      rw [hval, show (s.hl.toNat + s.bc.toNat) % 65536 = s.hl.toNat + s.bc.toNat - 65536 by omega]; exact A.2 c
    · rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case addHLDE =>
    obtain ⟨e, ef⟩ := sp_addHLDE hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hval : s'.hl.toNat = (s.hl.toNat + s.de.toNat) % 65536 := by rw [e]; exact add16_val _ _ _
    have hc : s'.flag FC = decide (65536 ≤ s.hl.toNat + s.de.toNat) := by
      rw [← add16_fc s s.hl s.de]; simp only [Cpu.flag, ef]
    have A := Itv.In_add hlS hde
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [hc] at c; simp only [decide_eq_false_iff_not, Nat.not_le] at c
      rw [hval, Nat.mod_eq_of_lt c]; exact A.1 c
    · rw [hc] at c; simp only [decide_eq_true_eq] at c
      have := s.hl.toNat_lt; have := s.de.toNat_lt
      rw [hval, show (s.hl.toNat + s.de.toNat) % 65536 = s.hl.toNat + s.de.toNat - 65536 by omega]; exact A.2 c
    · rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case sbcHLDE =>
    obtain ⟨e, ef⟩ := sp_sbcHLDE hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hval := sbc16_hl s s.de
    have hc := sbc16_c s s.de
    rw [← e] at hval
    have hc' : s'.flag FC = (s.sbc16 s.de).flag FC := by simp only [Cpu.flag, ef]
    rw [← hc'] at hc
    have hx := s.hl.toNat_lt
    have hy := s.de.toNat_lt
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [hc] at c; simp only [decide_eq_false_iff_not, Nat.not_lt] at c
      cases c0 : s.flag FC
      · rw [c0] at hval c; simp only [Bool.false_eq_true, if_false] at hval c
        have := (Itv.In_sub (c := 0) (h0 c0) hde).1 (by omega)
        rw [hval, show (s.hl.toNat + 2 * 65536 - s.de.toNat - 0) % 65536 = s.hl.toNat - s.de.toNat - 0 by omega]
        exact Itv.In_hull_l _ this
      · rw [c0] at hval c; simp only [if_true] at hval c
        have := (Itv.In_sub (c := 1) (h1 c0) hde).1 (by omega)
        rw [hval, show (s.hl.toNat + 2 * 65536 - s.de.toNat - 1) % 65536 = s.hl.toNat - s.de.toNat - 1 by omega]
        exact Itv.In_hull_r _ this
    · rw [hc] at c; simp only [decide_eq_true_eq] at c
      cases c0 : s.flag FC
      · rw [c0] at hval c; simp only [Bool.false_eq_true, if_false] at hval c
        have := (Itv.In_sub (c := 0) (h0 c0) hde).2 (by omega)
        rw [hval, show (s.hl.toNat + 2 * 65536 - s.de.toNat - 0) % 65536 = s.hl.toNat + 65536 - s.de.toNat - 0 by omega]
        exact Itv.In_hull_l _ this
      · rw [c0] at hval c; simp only [if_true] at hval c
        have := (Itv.In_sub (c := 1) (h1 c0) hde).2 (by omega)
        rw [hval, show (s.hl.toNat + 2 * 65536 - s.de.toNat - 1) % 65536 = s.hl.toNat + 65536 - s.de.toNat - 1 by omega]
        exact Itv.In_hull_r _ this
    · rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case incHL =>
    have e := sp_incHL hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hc := fc_eq (fCF rfl)
    have hval : s'.hl.toNat = (s.hl.toNat + 1) % 65536 := by rw [e, UInt16.toNat_add]; rfl
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [hc] at c; rw [hval]; exact Itv.In_inc (h0 c) s.hl.toNat_lt
    · rw [hc] at c; rw [hval]; exact Itv.In_inc (h1 c) s.hl.toNat_lt
    · rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case decHL =>
    have e := sp_decHL hs
    obtain ⟨d1, d2⟩ := fDE rfl
    obtain ⟨b1, b2⟩ := fBC rfl
    have hc := fc_eq (fCF rfl)
    have hval : s'.hl.toNat = (s.hl.toNat + 65535) % 65536 := by
      rw [e, UInt16.toNat_sub]; simp only [UInt16.toNat_one]; omega
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => by cases hv) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [hc] at c; rw [hval]; exact Itv.In_dec (h0 c) s.hl.toNat_lt
    · rw [hc] at c; rw [hval]; exact Itv.In_dec (h1 c) s.hl.toNat_lt
    · rw [de_eq d1 d2, bc_eq b1 b2]; exact hdb v hv
  case decBC =>
    have e := sp_decBC hs
    obtain ⟨d1, d2⟩ := fDE rfl
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    have hval : s'.bc.toNat = (s.bc.toNat + 65535) % 65536 := by
      rw [e, UInt16.toNat_sub]; simp only [UInt16.toNat_one]; omega
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [de_eq d1 d2]; exact hde) (by rw [hval]; exact Itv.In_dec hbc s.bc.toNat_lt) (fun v hv => by cases hv) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
  case incDE =>
    have e := sp_incDE hs
    obtain ⟨b1, b2⟩ := fBC rfl
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    have hval : s'.de.toNat = (s.de.toNat + 1) % 65536 := by rw [e, UInt16.toNat_add]; rfl
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (by rw [hval]; exact Itv.In_inc hde s.de.toNat_lt) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => ?_) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
    · rw [hl, bc_eq b1 b2]; exact hhb v hv
  case exDEHL =>
    obtain ⟨e1, e2⟩ := sp_exDEHL hs
    obtain ⟨b1, b2⟩ := fBC rfl
    refine AF.sat_of (fun _ => by rw [e1]; exact hde) (fun _ => by rw [e1]; exact hde) (by rw [e2]; exact hlS) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => ?_) (fun v hv => ?_)
    all_goals dsimp only [absF] at *
    · rw [e1, bc_eq b1 b2]; exact hdb v hv
    · rw [e2, bc_eq b1 b2]; exact hhb v hv
  case ldDH =>
    obtain ⟨e1, e2⟩ := sp_ldDH hs
    obtain ⟨b1, b2⟩ := fBC rfl
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (?_) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => ?_) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
    · show Itv.In s'.de.toNat (match a.hl.one? with | some p => (p / 256 * 256, p / 256 * 256 + 255) | none => Itv.top)
      split
      · rename_i p hp
        have hp' := one?_eq hp hlS
        rw [hl_toNat] at hp'
        rw [de_toNat, e1, e2]
        have := s.l.toNat_lt; have := s.e.toNat_lt
        have hq : p / 256 = s.h.toNat := by omega
        exact ⟨by simp only; rw [hq]; omega, by simp only; rw [hq]; omega⟩
      · exact Itv.In_top s'.de.toNat_lt
    · rw [hl, bc_eq b1 b2]; exact hhb v hv
  case ldEL =>
    obtain ⟨e1, e2⟩ := sp_ldEL hs
    obtain ⟨b1, b2⟩ := fBC rfl
    have hl := hl_eq (fH rfl) (fL rfl)
    have hc := fc_eq (fCF rfl)
    refine AF.sat_of (fun c => ?_) (fun c => ?_) (?_) (by rw [bc_eq b1 b2]; exact hbc) (fun v hv => ?_) (fun v hv => by cases hv)
    all_goals dsimp only [absF] at *
    · rw [hl]; rw [hc] at c; exact h0 c
    · rw [hl]; rw [hc] at c; exact h1 c
    · show Itv.In s'.de.toNat (match a.hl.one? with
        | some p => if a.de.1 / 256 = a.de.2 / 256 ∧ a.de.2 < 65536 then (a.de.1 / 256 * 256 + p % 256, a.de.1 / 256 * 256 + p % 256)
            else Itv.top
        | none => Itv.top)
      split
      · rename_i p hp
        split
        · rename_i hb
          have hp' := one?_eq hp hlS
          rw [hl_toNat] at hp'
          obtain ⟨q1, q2⟩ := hde
          rw [de_toNat] at q1 q2
          have := s.l.toNat_lt; have := s.e.toNat_lt; have := s.d.toNat_lt
          have hd : a.de.1 / 256 = s.d.toNat := by omega
          rw [de_toNat, e1, e2, hd]
          exact ⟨by simp only; omega, by simp only; omega⟩
        · exact Itv.In_top s'.de.toNat_lt
      · exact Itv.In_top s'.de.toNat_lt
    · rw [hl, bc_eq b1 b2]; exact hhb v hv

theorem absT_sound (la : List (String × Nat)) (f : Form) {n : UInt8} {nn : UInt16} {inp : UInt16 → UInt8}
    {s s' : Cpu} (hs : execI f.instr n nn s inp = some s')
    (hv : ∀ m, valOf la (argVal f.instr) = some m → 0 ≤ m → m < 65536 → nn.toNat = m.toNat)
    {a : AS} (h : ASat a s) : ASat (absT la f a) s' :=
  AF.norm_sat (absF_sound la f hs hv (AF.sat_getD h))

/-! ## Jumps and returns not taken, rounds of `ldir` -/

theorem taken_c (s : Cpu) : taken (some .c) s = s.flag FC := rfl
theorem taken_nc (s : Cpu) : taken (some .nc) s = !s.flag FC := rfl

/-- **A conditional jump or return not taken**, to a state with the same registers. -/
theorem absJ_sound {cc : Arg} {s s' : Cpu} (hnt : taken (some cc) s = false) {a : AS} (h : ASat a s)
    (e1 : s'.h = s.h) (e2 : s'.l = s.l) (e3 : s'.d = s.d) (e4 : s'.e = s.e) (e5 : s'.b = s.b) (e6 : s'.c = s.c)
    (e7 : s'.f = s.f) : ASat (absJ cc a) s' := by
  cases a with
  | none => trivial
  | some a =>
    have h' := AF.congr h e1 e2 e3 e4 e5 e6 e7
    have hf : s'.flag FC = s.flag FC := fc_eq e7
    obtain ⟨h0, h1, hde, hbc, hhb, hdb⟩ := h'
    cases cc with
    | c =>
      rw [taken_c] at hnt
      exact AF.sat_of h0 (fun c => by rw [hf, hnt] at c; cases c) hde hbc hhb hdb
    | nc =>
      rw [taken_nc] at hnt
      exact AF.sat_of (fun c => by rw [hf] at c; rw [c] at hnt; cases hnt) h1 hde hbc hhb hdb
    | _ => exact AF.sat_of h0 h1 hde hbc hhb hdb

theorem fc_ldir (x n : UInt8) (m y : Bool) :
    (((x &&& (FS ||| FZ ||| FC)) ||| bit m FPV ||| (n &&& FX) ||| bit y FY) &&& FC != 0) = (x &&& FC != 0) := by
  rw [flagC_bit, flagC_bit]
  simp only [UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
  have e1 : (FS.toNat.testBit 0 || FZ.toNat.testBit 0 || FC.toNat.testBit 0) = true := by decide
  have e2 : FPV.toNat.testBit 0 = false := by decide
  have e3 : FX.toNat.testBit 0 = false := by decide
  have e4 : FY.toNat.testBit 0 = false := by decide
  simp only [e1, e2, e3, e4, Bool.and_true, Bool.and_false, Bool.or_false]

theorem ldirS_abs (s : Cpu) :
    (ldirS s).hl = s.hl + 1 ∧ (ldirS s).de = s.de + 1 ∧ (ldirS s).bc = s.bc - 1 ∧
      (ldirS s).flag FC = s.flag FC := by
  obtain ⟨r1, r2, r3⟩ := ldirS_regs s
  refine ⟨r1, r2, r3, ?_⟩
  simp only [ldirS, ldirG]
  split <;> exact fc_ldir _ _ _ _

/-- **A round of `ldir` that goes on** keeps `ldirIter` of what is known. -/
theorem ldirIter_sound {s : Cpu} (hb : (s.bc - 1 != 0) = true) {a : AS} (h : ASat a s) :
    ASat (ldirIter a) (ldirS s) := by
  cases a with
  | none => trivial
  | some a =>
    obtain ⟨r1, r2, r3, r4⟩ := ldirS_abs s
    obtain ⟨h0, h1, hde, hbc, hhb, hdb⟩ := h
    have hx := s.hl.toNat_lt
    have hy := s.de.toNat_lt
    have hz := s.bc.toNat_lt
    have hb1 : s.bc.toNat ≠ 1 := by
      intro e
      have e' : s.bc = 1 := UInt16.toNat_inj.mp (by rw [e]; rfl)
      rw [e'] at hb; exact absurd hb (by decide)
    have vl : (ldirS s).hl.toNat = (s.hl.toNat + 1) % 65536 := by rw [r1, UInt16.toNat_add]; rfl
    have vd : (ldirS s).de.toNat = (s.de.toNat + 1) % 65536 := by rw [r2, UInt16.toNat_add]; rfl
    have vb : (ldirS s).bc.toNat = (s.bc.toNat + 65535) % 65536 := by
      rw [r3, UInt16.toNat_sub]; simp only [UInt16.toNat_one]; omega
    refine AF.sat_of (fun c => ?_) (fun c => ?_) ?_ ?_ (fun v hv => ?_) (fun v hv => ?_)
    · rw [r4] at c; rw [vl]; exact Itv.In_inc (h0 c) hx
    · rw [r4] at c; rw [vl]; exact Itv.In_inc (h1 c) hx
    · rw [vd]; exact Itv.In_inc hde hy
    · show Itv.In _ (if a.bc.isEmp then Itv.emp else if 1 ≤ a.bc.1 then (max 1 (a.bc.1 - 1), a.bc.2 - 1) else Itv.top)
      rw [Itv.isEmp_false hbc]
      simp only [Bool.false_eq_true, if_false]
      split
      · rename_i h1'
        have := hbc.1; have := hbc.2
        rw [vb]; exact ⟨by simp only; omega, by simp only; omega⟩
      · exact Itv.In_top (by rw [vb]; exact Nat.mod_lt _ (by decide))
    · simp only at hv
      rw [Itv.isEmp_false hbc] at hv
      simp only [Bool.not_false, Bool.true_and] at hv
      split at hv
      · rename_i hok
        simp only [decide_eq_true_eq] at hok
        cases e : a.hb with
        | none => rw [e] at hv; cases hv
        | some u =>
          rw [e] at hv
          simp only [Option.bind_some] at hv
          split at hv
          · cases hv
            have := hhb v e; have := hbc.1
            rw [vl, vb]; omega
          · cases hv
      · cases hv
    · simp only at hv
      rw [Itv.isEmp_false hbc] at hv
      simp only [Bool.not_false, Bool.true_and] at hv
      split at hv
      · rename_i hok
        simp only [decide_eq_true_eq] at hok
        cases e : a.db with
        | none => rw [e] at hv; cases hv
        | some u =>
          rw [e] at hv
          simp only [Option.bind_some] at hv
          split at hv
          · cases hv
            have := hdb v e; have := hbc.1
            rw [vd, vb]; omega
          · cases hv
      · cases hv

/-! ## What the segments take, from what is known -/

/-- A symbol of the table of labels is a label. -/
theorem notLabel_spec' {xs : List Item} {l : String} (h : notLabel (labTbl xs 0) l = false)
    (hn : ∀ j : Nat, xs[j]? ≠ some (Item.label l)) : False := by
  simp only [notLabel, Option.isNone_eq_false_iff, Option.isSome_iff_exists] at h
  obtain ⟨⟨i, suf⟩, hl⟩ := h
  obtain ⟨_, h2, _⟩ := labTbl_lookup xs 0 l i suf hl
  exact hn _ h2

theorem viaHL_mhl (f : Form) (h : f.viaHL = true) : f.instr.args.contains .mhl = true := by
  cases f <;> first | rfl | (simp [Form.viaHL] at h)

theorem viaDE_mde (f : Form) (h : f.viaDE = true) : f.instr.args.contains .mde = true := by
  cases f <;> first | rfl | (simp [Form.viaDE] at h)

/-- **`needOK`, as facts of the registers**: from what is known at a meeting point of `A` (`xs`: its
items), the bytes read and written at `HL`, `DE` in `[lo, hi)`, and the four at `HL` that a routine
of the runtime is called with, unless after `ld hl,l` of a label. -/
theorem needOK_spec {xs : List Item} {lo hi k : Nat} {a : AS} {s : Cpu} {i : Instr}
    (hk : xs[k]? = some (.ins i)) (h : needOK (labTbl xs 0) lo hi (prevOf xs k) (.ins i) a = true)
    (hs : ASat a s) :
    (∀ f : Form, f.instr = i →
      (f.viaHL = true → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi) ∧ (f.viaDE = true → lo ≤ s.de.toNat ∧ s.de.toNat < hi)) ∧
    (i = ⟨.ldir, []⟩ → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi ∧ lo ≤ s.de.toNat ∧ s.de.toNat < hi) ∧
    (∀ f, i = ⟨.call, [.imm (.sym f 0)]⟩ → (ptrRoutine f).isSome = true →
      (∀ l, 0 < k → xs[k - 1]? = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) → ∀ j : Nat, xs[j]? ≠ some (Item.label l)) →
      lo ≤ s.hl.toNat ∧ s.hl.toNat + 4 ≤ hi) := by
  have HL := AS.hlR_sat hs
  have DE := AS.deR_sat hs
  simp only [needOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hm, hd⟩, hl⟩, hc⟩ := h
  refine ⟨fun f hf => ⟨fun hv => ?_, fun hv => ?_⟩, fun e => ?_, fun g e hp hpre => ?_⟩
  · have := viaHL_mhl f hv; rw [hf] at this
    rcases hm with e | e
    · rw [e] at this; cases this
    · have := Itv.In_within e HL; omega
  · have := viaDE_mde f hv; rw [hf] at this
    rcases hd with e | e
    · rw [e] at this; cases this
    · have := Itv.In_within e DE; omega
  · subst e
    rcases hl with e | ⟨e1, e2⟩
    · simp at e
    · have := Itv.In_within e1 HL; have := Itv.In_within e2 DE; omega
  · subst e
    simp only [Bool.or_eq_true] at hc
    rcases hc with (e | e) | e
    · simp only [Option.isNone_iff_eq_none] at e; rw [e] at hp; cases hp
    · exfalso
      unfold litPrev at e
      split at e
      · rename_i l hpv
        simp only [prevOf] at hpv
        split at hpv
        · cases hpv
        · rename_i hk0
          simp only [Bool.not_eq_true'] at e
          exact notLabel_spec' e (hpre l (by omega) hpv)
      · cases e
    · exact Itv.In_within e HL

end Ember.Proof.PassSim
