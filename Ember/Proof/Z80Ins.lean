import Ember.Proof.Z80CallFn
import Ember.Proof.Z80Bin16
import Ember.Proof.Z80Una

/-!
# Ember.Proof.Z80Ins — every instruction, one statement (plan M7.3)

`Ins`: what the code of an IR instruction does, for whatever
`IR.Sem.step` says the instruction does — go on, jump, call, return or
trap.  `ins_ok` gathers the theorems about the single instructions.

`Covered` are the instructions proved so far; `Need` is what each needs
of the program (its operands can be read, its destination written, …),
to be established by checks on the program.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The temporaries assigned after an instruction.  After a label none
is taken to be: a temporary is not read across a label. -/
def dtNext (dt : Nat → Prop) : IR.Instr → Nat → Prop
  | .label _ => fun _ => False
  | .mov _ d _ | .bin _ _ d _ _ | .shift _ _ d _ _ _ | .not _ d _ | .neg _ d _ | .ext _ d _ _
  | .cmp _ _ d _ _ | .load _ d _ | .lea d _ => dtAfter dt d
  | .call _ ret _ | .eff _ _ ret => dtRet dt ret
  | _ => dt

def size12 (n : Nat) : Bool := n == 1 || n == 2

theorem size12_spec {n : Nat} (h : size12 n = true) : n = 1 ∨ n = 2 := by
  simpa [size12] using h

/-- The instructions the proofs cover so far. -/
def Covered : IR.Instr → Bool
  | .mov n _ _ | .bin _ n _ _ _ | .not n _ _ | .neg n _ _ | .cmp _ n _ _ _ | .br _ n _ _ _ => size12 n
  | .jmp _ | .label _ | .trap => true
  | .ret v => (v.map fun p => size12 p.1).getD true
  | .call _ ret reg => (ret.map fun p => size12 p.1).getD true && (reg.map fun p => size12 p.1).getD true
  | _ => false

/-- What an instruction needs of the program. -/
def Need (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) : IR.Instr → Prop
  | .mov n d src => Rd Z E dt n src ∧ Wr Z E n d
  | .bin _ n d a b => Rd Z E dt n a ∧ Rd Z E dt n b ∧ Wr Z E n d
  | .not n d a | .neg n d a => Rd Z E dt n a ∧ Wr Z E n d
  | .cmp _ n d a b => Rd Z E dt n a ∧ Rd Z E dt n b ∧ Wr Z E 1 d
  | .br _ n a b l => Rd Z E dt n a ∧ Rd Z E dt n b ∧ ∃ j : Nat, Z.items[j]? = some (Item.label (lname E l))
  | .jmp _ | .label _ => True
  | .ret v => ∀ n o, v = some (n, o) → Rd Z E dt n o
  | .trap => ∃ j : Nat, Z.items[j]? = some (Item.label "rt_trap")
  | .call g ret reg => CallNeed Z E dt g ret reg
  | _ => False

/-- What the code does from `s`, for what the IR's instruction does. -/
def After (Z : ZCtx) (E : GEnv) (base : Nat) (fr : Fr) (dt : Nat → Prop) (i : IR.Instr) (s1 : GS)
    (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) : IR.Sem.Step → Prop
  | .next ist' tmps' => ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr (dtNext dt i) s1.regs ist' tmps' s'
  | .goto l => ∀ j : Nat, Z.items[j]? = some (Item.label (lname E l)) →
      ∃ s' r, Steps Z.inp s s' ∧ At Z.addrs j s' ∧ (l, r) ∈ s1.jumps ∧ Rel Z E fr dt r ist tmps s'
  | .call g st1 ret => ∀ res, Callee Z g st1 res →
      AfterCall Z E fr (dtNext dt i) s1.regs (base + s1.out.size) tmps ret s res
  | .stop (.ok r st') => ∃ s' v, Steps Z.inp s s' ∧ i = .ret v ∧ RetSt Z E.fn fr st' (v.map (·.1)) r s'
  | .stop (.trap st') => ∃ s', Steps Z.inp s s' ∧ Trapped Z st' s'
  | .stop _ => True

/-- **What the generator promises for the instruction `i`.**  A label
is told apart: the states agree after it for what `jumpsOk` checks. -/
def Ins (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (i : IR.Instr) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    match i with
    | .label l => s1.out = s0.out.push (.label (lname E l)) ∧ (l, s1.regs) ∈ s1.labelRegs ∧
        (prevFalls E.fn.body l = true → (l, s0.regs) ∈ s1.jumps)
    | _ => GExt s1 sF → Need Z E dt i → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s → After Z E base fr dt i s1 ist tmps s (IR.Sem.step Z.c ist tmps i)

theorem step_call (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (g : String) (ret : Option (Nat × Dst))
    (reg : Option (Nat × Opd)) :
    IR.Sem.step c ist tmps (.call g ret reg) = .call g (callSt c ist tmps g reg) ret := by
  cases reg <;> rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- **Every covered instruction.** -/
theorem ins_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (i : IR.Instr) (hc : Covered i = true) (s0 : GS) :
    wpg (genInstr i) E (Ins Z E base sF dt i s0) s0 := by
  cases i with
  | mov n d src =>
    rcases size12_spec hc with rfl | rfl
    · refine wpg_mono (mov1_ok (dt := dt) ok hT F d src s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF hN⟩
    · refine wpg_mono (mov2_ok (dt := dt) ok hT F d src s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF hN⟩
  | bin op n d a b =>
    rcases size12_spec hc with rfl | rfl
    · refine wpg_mono (bin1_ok (dt := dt) ok hT F op d a b s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF ⟨hN.1, hN.2.1, hN.2.2, hrt, hdep⟩⟩
    · refine wpg_mono (bin2_ok (dt := dt) ok hT F op d a b s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF ⟨hN.1, hN.2.1, hN.2.2, hrt, hdep⟩⟩
  | not n d a =>
    rcases size12_spec hc with rfl | rfl
    · refine wpg_mono (not1_ok (dt := dt) ok hT F d a s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF hN⟩
    · refine wpg_mono (not2_ok (dt := dt) ok hT F d a s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF ⟨hN.1, hN.2, hrt, hdep⟩⟩
  | neg n d a =>
    rcases size12_spec hc with rfl | rfl
    · refine wpg_mono (neg1_ok (dt := dt) ok hT F d a s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF hN⟩
    · refine wpg_mono (neg2_ok (dt := dt) ok hT F d a s0) ?_
      intro _ s1 ⟨hx, h⟩
      exact ⟨hx, fun hxF hN => h hxF ⟨hN.1, hN.2, hrt, hdep⟩⟩
  | cmp op n d a b =>
    refine wpg_mono (cmp_ok (dt := dt) ok hT F op n (size12_spec hc) d a b s0) ?_
    intro _ s1 ⟨hx, h⟩
    exact ⟨hx, fun hxF hN => h hxF hN⟩
  | br op n a b l =>
    refine wpg_mono (br_ok (dt := dt) ok F op n (size12_spec hc) a b l s0) ?_
    intro _ s1 ⟨hx, hj, h⟩
    refine ⟨hx, fun hxF hN fr ist tmps s R hat => ?_⟩
    obtain ⟨hra, hrb, j0, hj0⟩ := hN
    show After Z E base fr dt _ s1 ist tmps s
      (if IR.cmpOp op (IR.Sem.opd Z.c ist tmps n a) (IR.Sem.opd Z.c ist tmps n b) then .goto l else .next ist tmps)
    by_cases hcnd : IR.cmpOp op (IR.Sem.opd Z.c ist tmps n a) (IR.Sem.opd Z.c ist tmps n b) = true
    · rw [if_pos hcnd]
      intro j hlab
      obtain ⟨s', st, R', hat'⟩ := h hxF fr ist tmps s j hlab hra hrb R hat
      rw [if_pos hcnd] at hat'
      exact ⟨s', s1.regs, st, hat', hj, R'⟩
    · rw [if_neg hcnd]
      obtain ⟨s', st, R', hat'⟩ := h hxF fr ist tmps s j0 hj0 hra hrb R hat
      rw [if_neg hcnd] at hat'
      exact ⟨s', st, hat', R'⟩
  | jmp l =>
    refine wpg_mono (jmp_ok (dt := dt) ok F l s0) ?_
    intro _ s1 ⟨hx, hj, h⟩
    refine ⟨hx, fun hxF _ fr ist tmps s R hat j hlab => ?_⟩
    obtain ⟨s', st, hat', R'⟩ := h hxF fr ist tmps s j hlab R hat
    exact ⟨s', s0.regs, st, hat', hj, R'⟩
  | label l =>
    refine wpg_mono (label_ok l s0) ?_
    intro _ s1 ⟨hx, h⟩
    exact ⟨hx, h⟩
  | ret v =>
    refine wpg_mono (ret_ok (dt := dt) ok F v (fun n o h => by
      subst h
      exact size12_spec hc) s0) ?_
    intro _ s1 ⟨hx, h⟩
    refine ⟨hx, fun hxF hN fr ist tmps s R hat => ?_⟩
    obtain ⟨s', st, hret⟩ := h hxF hN fr ist tmps s R hat
    exact ⟨s', v, st, rfl, hret⟩
  | trap =>
    refine wpg_mono (trap_ok (dt := dt) ok F s0) ?_
    intro _ s1 ⟨hx, h⟩
    refine ⟨hx, fun hxF hN fr ist tmps s R hat => ?_⟩
    obtain ⟨j, hj⟩ := hN
    exact h hxF j hj fr ist tmps s R hat
  | call g ret reg =>
    have hc' : ((ret.map fun p => size12 p.1).getD true && (reg.map fun p => size12 p.1).getD true) = true := hc
    rw [Bool.and_eq_true] at hc'
    refine wpg_mono (call_ok (dt := dt) ok hT F g ret reg (fun n o h => by
      subst h
      exact size12_spec hc'.2) (fun n d h => by
      subst h
      exact size12_spec hc'.1) s0) ?_
    intro _ s1 ⟨hx, h⟩
    refine ⟨hx, fun hxF hN fr ist tmps s R hat => ?_⟩
    rw [step_call]
    exact fun res hcal => h hxF hN fr ist tmps s R hat res hcal
  | shift _ _ _ _ _ _ => cases hc
  | ext _ _ _ _ => cases hc
  | load _ _ _ => cases hc
  | store _ _ _ => cases hc
  | lea _ _ => cases hc
  | zero _ _ => cases hc
  | eff _ _ _ => cases hc

end

end Ember.Proof.Z80Gen
