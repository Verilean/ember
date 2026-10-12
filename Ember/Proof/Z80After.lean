import Ember.Proof.Z80CallFn

/-!
# Ember.Proof.Z80After — what follows an instruction (plan M7.3)

`After`: what the code of an instruction does from a state, for each
thing `IR.Sem.step` can say the instruction does.
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

/-- What the code of an instruction without effects does from `s`, for
what the IR's instruction does: it does no I/O (but for what the
functions it calls do). -/
def After (Z : ZCtx) (E : GEnv) (base : Nat) (fr : Fr) (dt : Nat → Prop) (i : IR.Instr) (s1 : GS)
    (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) : IR.Sem.Step → Prop
  | .next ist' tmps' => ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr (dtNext dt i) s1.regs ist' tmps' s'
  | .goto l => ∀ j : Nat, Z.items[j]? = some (Item.label (lname E l)) →
      ∃ s' r, Steps s s' ∧ At Z.addrs j s' ∧ (l, r) ∈ s1.jumps ∧ Rel Z E fr dt r ist tmps s'
  | .call g st1 ret => ∀ w, Z.wrel ist.world w → ∀ res, Callee Z g st1 res →
      AfterCall Z E fr (dtNext dt i) s1.regs (base + s1.out.size) tmps ret s w res
  | .stop (.ok r st') => ∃ s' v, Steps s s' ∧ i = .ret v ∧ RetSt Z E.fn fr st' (v.map (·.1)) r s'
  | .stop (.trap st') => ∃ s', Steps s s' ∧ Trapped Z st' s'
  | .stop _ => True

/-- What the code does from `s` in the machine `w`, for what the IR's
instruction does. -/
def MAfter (Z : ZCtx) (E : GEnv) (base : Nat) (fr : Fr) (dt : Nat → Prop) (i : IR.Instr) (s1 : GS)
    (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) (w : Z.W) : IR.Sem.Step → Prop
  | .next ist' tmps' => ∃ s' w', WSteps Z (s, w) (s', w') ∧ Z.wrel ist'.world w' ∧
      At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr (dtNext dt i) s1.regs ist' tmps' s'
  | .goto l => ∀ j : Nat, Z.items[j]? = some (Item.label (lname E l)) →
      ∃ s' r, WSteps Z (s, w) (s', w) ∧ At Z.addrs j s' ∧ (l, r) ∈ s1.jumps ∧ Rel Z E fr dt r ist tmps s'
  | .call g st1 ret => ∀ res, Callee Z g st1 res →
      AfterCall Z E fr (dtNext dt i) s1.regs (base + s1.out.size) tmps ret s w res
  | .stop (.ok r st') => ∃ s' w' v, WSteps Z (s, w) (s', w') ∧ Z.wrel st'.world w' ∧ i = .ret v ∧
      RetSt Z E.fn fr st' (v.map (·.1)) r s'
  | .stop (.trap st') => ∃ s' w', WSteps Z (s, w) (s', w') ∧ Z.wrel st'.world w' ∧ Trapped Z st' s'
  | .stop _ => True

theorem setDst_world (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (n : Nat) (d : Dst) (v : Nat) :
    (IR.Sem.setDst c st tmps n d v).1.world = st.world := by
  cases d <;> rfl

theorem setRet_world (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (ret : Option (Nat × Dst)) (r : Option Nat) :
    (IR.Sem.setRet c st tmps ret r).1.world = st.world := by
  cases ret with
  | none => rfl
  | some p => exact setDst_world ..

/-- An instruction without effects leaves the world as it is. -/
theorem step_world {c : IR.Ctx} {ist : IR.Sem.St} {tmps : Array Nat} {i : IR.Instr}
    (hne : ∀ e a r, i ≠ .eff e a r) :
    match IR.Sem.step c ist tmps i with
    | .next ist' _ => ist'.world = ist.world
    | .stop (.ok _ st') => st'.world = ist.world
    | .stop (.trap st') => st'.world = ist.world
    | _ => True := by
  cases i with
  | eff e a r => exact absurd rfl (hne e a r)
  | mov n d src => exact setDst_world ..
  | bin op n d a b => exact setDst_world ..
  | shift l n d a m amt => exact setDst_world ..
  | not n d a => exact setDst_world ..
  | neg n d a => exact setDst_world ..
  | ext n d m src => exact setDst_world ..
  | cmp op n d a b => exact setDst_world ..
  | br op n a b l =>
    simp only [IR.Sem.step]
    by_cases hc : IR.cmpOp op (IR.Sem.opd c ist tmps n a) (IR.Sem.opd c ist tmps n b) = true
    · simp only [hc, if_true]
    · simp only [hc, Bool.false_eq_true, if_false]
  | jmp l => trivial
  | label l => rfl
  | load n d p =>
    simp only [IR.Sem.step]
    cases IR.Sem.addr c ist tmps p with
    | none => rfl
    | some a =>
      by_cases hb : IR.Sem.inBound c ist tmps p = true
      · simp only [hb, if_true]
        exact setDst_world ..
      · simp only [hb, Bool.false_eq_true, if_false]
  | store n p src =>
    simp only [IR.Sem.step]
    cases IR.Sem.addr c ist tmps p with
    | none => rfl
    | some a =>
      by_cases hb : IR.Sem.inBound c ist tmps p = true
      · simp only [hb, if_true]
      · simp only [hb, Bool.false_eq_true, if_false]
  | lea d p =>
    simp only [IR.Sem.step]
    cases IR.Sem.addr c ist tmps p with
    | none => rfl
    | some a =>
      by_cases hb : IR.Sem.inBound c ist tmps p = true
      · simp only [hb, if_true]
        exact setDst_world ..
      · simp only [hb, Bool.false_eq_true, if_false]
  | zero sl n => rfl
  | call g ret reg => trivial
  | ret v => rfl
  | trap => rfl

/-- **Without effects, in the machine**: the code does no I/O, and the
machine stands for the world as before. -/
theorem After.lift {Z : ZCtx} {E : GEnv} {base : Nat} {fr : Fr} {dt : Nat → Prop} {i : IR.Instr} {s1 : GS}
    {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu} (ok : Z.OK) (hne : ∀ e a r, i ≠ .eff e a r)
    (h : After Z E base fr dt i s1 ist tmps s (IR.Sem.step Z.c ist tmps i)) (w : Z.W) (hw : Z.wrel ist.world w) :
    MAfter Z E base fr dt i s1 ist tmps s w (IR.Sem.step Z.c ist tmps i) := by
  have hwd := step_world (c := Z.c) (ist := ist) (tmps := tmps) hne
  cases hs : IR.Sem.step Z.c ist tmps i with
  | next ist' tmps' =>
    rw [hs] at h hwd
    obtain ⟨s', st, hat, R⟩ := h
    exact ⟨s', w, Steps.lift ok st w, by rw [show ist'.world = ist.world from hwd]; exact hw, hat, R⟩
  | goto l =>
    rw [hs] at h
    intro j hj
    obtain ⟨s', r, st, hat, hjr, R⟩ := h j hj
    exact ⟨s', r, Steps.lift ok st w, hat, hjr, R⟩
  | call g st1 ret =>
    rw [hs] at h
    exact h w hw
  | stop r =>
    rw [hs] at h hwd
    cases r with
    | fuel => trivial
    | bad => trivial
    | trap st' =>
      obtain ⟨s', st, htr⟩ := h
      exact ⟨s', w, Steps.lift ok st w, by rw [show st'.world = ist.world from hwd]; exact hw, htr⟩
    | ok r st' =>
      obtain ⟨s', v, st, hv, hret⟩ := h
      exact ⟨s', w, v, Steps.lift ok st w, by rw [show st'.world = ist.world from hwd]; exact hw, hv, hret⟩

end Ember.Proof.Z80Gen
