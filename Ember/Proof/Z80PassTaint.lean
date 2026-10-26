import Ember.Proof.Z80PassStep

/-!
# Ember.Proof.Z80PassTaint — an ordinary instruction where `H` or `L` may differ (plan M7.3)

After a routine of the runtime has read a literal of the ROM through
`HL`, the two machines' `HL` differ (each points past the literal in its
own image).  Until it is written again, the relation leaves `H` and `L`
free (`EqvT`); an instruction that reads neither keeps the relation,
and one that writes them makes them equal again.  `Form.readsH`, … say
which forms read and write which; `h_comm`, `l_comm`: an instruction
that does not read `H` does with any `H` what it does, `H` aside.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc

/-- Does the form read `H` (alone, in `HL`, or as an address)? -/
def Form.readsH : Form → Bool
  | .adcAM | .sbcAM | .andM | .cpM | .orM | .incM | .stHLA | .stHLN _ | .ldAHL | .stHL _ | .addHLBC | .addHLDE | .addHLHL | .decHL | .exDEHL | .incHL | .ldAH | .ldDH | .orH | .sbcHLDE | .srlH => true
  | _ => false

/-- Does the form read `L`? -/
def Form.readsL : Form → Bool
  | .adcAM | .sbcAM | .andM | .cpM | .orM | .incM | .stHLA | .stHLN _ | .ldAHL | .stHL _ | .addHLBC | .addHLDE | .addHLHL | .decHL | .exDEHL | .incHL | .andL | .ldAL | .ldEL | .ldHL2 | .orL | .rrL | .sbcHLDE => true
  | _ => false

/-- Does the form write `H`? -/
def Form.writesH : Form → Bool
  | .ldHLNN _ | .addHLBC | .addHLDE | .addHLHL | .decHL | .exDEHL | .incHL | .ldHA | .ldHL2 | .ldHI _ | .ldHLI _ | .sbcHLDE | .srlH => true
  | _ => false

/-- Does the form write `L`? -/
def Form.writesL : Form → Bool
  | .ldHLNN _ | .addHLBC | .addHLDE | .addHLHL | .decHL | .exDEHL | .incHL | .ldHLI _ | .ldLA | .ldLI _ | .rrL | .sbcHLDE => true
  | _ => false

-- one simp set for all the forms: some forms need lemmas others do not
set_option linter.unusedSimpArgs false in
theorem h_comm (f : Form) (hr : f.readsH = false) (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (t : Cpu)
    (x : UInt8) :
    execI f.instr n nn { t with h := x } inp =
      (execI f.instr n nn t inp).map (fun r => if f.writesH then r else { r with h := x }) := by
  cases t with
  | mk a f0 b c0 d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r0 iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  cases f <;> simp only [Form.readsH, Bool.true_eq_false, reduceCtorEq] at hr
  all_goals
    simp +decide only [Form.instr, Form.writesH, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?,
      Option.map_some, if_true, if_false]
    simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp,
      Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.add16, Cpu.sbc16, Cpu.rd, Cpu.wr, Cpu.wr16, Cpu.rd16, Cpu.de, Cpu.flag,
      Cpu.inc8, Cpu.dec8, Cpu.rot, Cpu.setBC, Cpu.setDE, Cpu.rp, Cpu.bc, Ember.Proof.Z80Gen.lo_mk16,
      Ember.Proof.Z80Gen.hi_mk16]
  all_goals ((repeat' split) <;> first | rfl | (exfalso; simp_all +decide))

set_option linter.unusedSimpArgs false in
theorem l_comm (f : Form) (hr : f.readsL = false) (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (t : Cpu)
    (x : UInt8) :
    execI f.instr n nn { t with l := x } inp =
      (execI f.instr n nn t inp).map (fun r => if f.writesL then r else { r with l := x }) := by
  cases t with
  | mk a f0 b c0 d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r0 iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  cases f <;> simp only [Form.readsL, Bool.true_eq_false, reduceCtorEq] at hr
  all_goals
    simp +decide only [Form.instr, Form.writesL, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?,
      Option.map_some, if_true, if_false]
    simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp,
      Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.add16, Cpu.sbc16, Cpu.rd, Cpu.wr, Cpu.wr16, Cpu.rd16, Cpu.de, Cpu.flag,
      Cpu.inc8, Cpu.dec8, Cpu.rot, Cpu.setBC, Cpu.setDE, Cpu.rp, Cpu.bc, Ember.Proof.Z80Gen.lo_mk16,
      Ember.Proof.Z80Gen.hi_mk16]
  all_goals ((repeat' split) <;> first | rfl | (exfalso; simp_all +decide))

/-- info: 'Ember.Proof.PassSim.h_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms h_comm

/-- `t` with `H` and `L` taken from `s` where they are free. -/
def mask (th tl : Bool) (s t : Cpu) : Cpu :=
  { t with h := if th then s.h else t.h, l := if tl then s.l else t.l }

/-- **The relation with `H` and `L` free**: `Eqv`, but `H` (when `th`) and `L` (when `tl`) may differ. -/
def EqvT (lo hi : Nat) (th tl : Bool) (s t : Cpu) : Prop := Eqv lo hi s (mask th tl s t)

theorem mask_ff (s t : Cpu) : mask false false s t = t := by cases t; rfl

theorem EqvT.of_eqv {lo hi : Nat} {s t : Cpu} (E : Eqv lo hi s t) : EqvT lo hi false false s t := by
  unfold EqvT; rw [mask_ff]; exact E

theorem Eqv.h {lo hi : Nat} {s t : Cpu} (E : Eqv lo hi s t) : s.h = t.h := by
  obtain ⟨_, _, _, _, _, e⟩ := regs_ex E.regs; rw [e]
theorem Eqv.l {lo hi : Nat} {s t : Cpu} (E : Eqv lo hi s t) : s.l = t.l := by
  obtain ⟨_, _, _, _, _, e⟩ := regs_ex E.regs; rw [e]

set_option linter.unusedSimpArgs false in
/-- **An ordinary instruction, `H` or `L` free**: when the instruction reads neither of those
that are free, from CPUs related so it gives CPUs related so, free what it did not write. -/
theorem ord_eqvT (lo hi : Nat) (hhi : hi ≤ 65536) (f : Form) (th tl : Bool)
    (hrh : th = true → f.readsH = false) (hrl : tl = true → f.readsL = false)
    (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (s t : Cpu) (E : EqvT lo hi th tl s t)
    (hhl : f.viaHL = true → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi) (hde : f.viaDE = true → lo ≤ s.de.toNat ∧ s.de.toNat < hi)
    (hnn : f.viaNN = true → lo ≤ nn.toNat ∧ nn.toNat + 1 < hi)
    (s' : Cpu) (hs : execI f.instr n nn s inp = some s') :
    ∃ t', execI f.instr n nn t inp = some t' ∧
      EqvT lo hi (th && !f.writesH) (tl && !f.writesL) s' t' := by
  obtain ⟨t1, ht1, E1⟩ := ord_eqv lo hi hhi f n nn inp s _ E hhl hde hnn s' hs
  -- `execI` from `mask` is `execI` from `t`, the free halves aside
  have key : ∀ (b1 b2 : Bool) (x y : UInt8), (b1 = true → f.readsH = false) → (b2 = true → f.readsL = false) →
      execI f.instr n nn { t with h := if b1 then x else t.h, l := if b2 then y else t.l } inp =
        (execI f.instr n nn t inp).map (fun r => { r with
          h := if b1 && !f.writesH then x else r.h, l := if b2 && !f.writesL then y else r.l }) := by
    intro b1 b2 x y h1 h2
    cases b1 <;> cases b2
    · simp only [Bool.false_and, Bool.false_eq_true, if_false]
      have e : ({ t with h := t.h, l := t.l } : Cpu) = t := by cases t; rfl
      rw [e]; cases execI f.instr n nn t inp <;> rfl
    · have e : { t with h := if false = true then x else t.h, l := if true = true then y else t.l } =
          { t with l := y } := by cases t; rfl
      rw [e, l_comm f (h2 rfl)]
      cases execI f.instr n nn t inp <;> simp only [Option.map_none, Option.map_some]
      rename_i r; cases hw : f.writesL <;> simp [hw] <;> cases r <;> rfl
    · have e : { t with h := if true = true then x else t.h, l := if false = true then y else t.l } =
          { t with h := x } := by cases t; rfl
      rw [e, h_comm f (h1 rfl)]
      cases execI f.instr n nn t inp <;> simp only [Option.map_none, Option.map_some]
      rename_i r; cases hw : f.writesH <;> simp [hw] <;> cases r <;> rfl
    · have e : { t with h := if true = true then x else t.h, l := if true = true then y else t.l } =
          { { t with h := x } with l := y } := by cases t; rfl
      rw [e, l_comm f (h2 rfl), h_comm f (h1 rfl)]
      cases execI f.instr n nn t inp <;> simp only [Option.map_none, Option.map_some]
      rename_i r; cases hw : f.writesH <;> cases hw' : f.writesL <;> simp [hw, hw'] <;> cases r <;> rfl
  have k := key th tl s.h s.l hrh hrl
  unfold mask at ht1
  rw [k] at ht1
  cases ht : execI f.instr n nn t inp with
  | none => rw [ht] at ht1; cases ht1
  | some t' =>
    rw [ht] at ht1
    simp only [Option.map_some, Option.some.injEq] at ht1
    refine ⟨t', rfl, ?_⟩
    unfold EqvT mask
    -- the halves that stay free are those of `s`, which the instruction did not write
    have eh : (th && !f.writesH) = true → s'.h = s.h := by
      intro hb
      have := E1.h; rw [← ht1] at this; simp only [hb, if_true] at this; exact this
    have el : (tl && !f.writesL) = true → s'.l = s.l := by
      intro hb
      have := E1.l; rw [← ht1] at this; simp only [hb, if_true] at this; exact this
    have e2 : ({ t' with h := if (th && !f.writesH) = true then s'.h else t'.h, l := if (tl && !f.writesL) = true then s'.l else t'.l } : Cpu) = t1 := by
      rw [← ht1]
      by_cases b1 : (th && !f.writesH) = true <;> by_cases b2 : (tl && !f.writesL) = true <;>
        simp only [b1, b2, if_true, if_false, Bool.false_eq_true, eh, el]
    rw [e2]; exact E1

/-- info: 'Ember.Proof.PassSim.ord_eqvT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ord_eqvT

theorem Form.viaHL_readsH (f : Form) (h : f.viaHL = true) : f.readsH = true := by
  cases f <;> simp_all [Form.viaHL, Form.readsH]

theorem Form.viaHL_readsL (f : Form) (h : f.viaHL = true) : f.readsL = true := by
  cases f <;> simp_all [Form.viaHL, Form.readsL]

end Ember.Proof.PassSim
