import Ember.Z80.Codegen

/-!
# Ember.Proof.Z80Wp — reasoning about the code generator's monad (plan M7.3)

`Codegen.GM` reads an environment, threads a state and may fail.  `wpg m
E Q s`: if `m` succeeds from `s`, its result and final state satisfy
`Q`.  One rule per primitive (`ins`, `get`, `read`, `modify`, …), as
`Ember/Proof/IRWp.lean` does for the lowering.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Codegen
open Ember.Z80.Asm (Arg Op Item Val)

def wpg {α : Type} (m : GM α) (E : GEnv) (Q : α → GS → Prop) (s : GS) : Prop :=
  match m E s with
  | .ok (a, s') => Q a s'
  | .error _ => True

section
variable {α β : Type} {E : GEnv} {s : GS}

theorem wpg_pure (a : α) (Q : α → GS → Prop) : wpg (pure a : GM α) E Q s ↔ Q a s := Iff.rfl

theorem wpg_bind (m : GM α) (f : α → GM β) (Q : β → GS → Prop) :
    wpg (m >>= f) E Q s ↔ wpg m E (fun a s' => wpg (f a) E Q s') s := by
  show (match (m >>= f) E s with | .ok (a, s') => Q a s' | .error _ => True) ↔
    (match m E s with | .ok (a, s') => wpg (f a) E Q s' | .error _ => True)
  have : (m >>= f) E s = (match m E s with | .ok (a, s') => f a E s' | .error e => .error e) := by
    show (m E >>= fun a => f a E) s = _
    show (do let p ← m E s; (fun a => f a E) p.1 p.2 : Except String (β × GS)) = _
    cases m E s <;> rfl
  rw [this]
  cases m E s with
  | error e => exact Iff.rfl
  | ok p => exact Iff.rfl

theorem wpg_mono {m : GM α} {Q Q' : α → GS → Prop} (h : wpg m E Q s) (hq : ∀ a s', Q a s' → Q' a s') :
    wpg m E Q' s := by
  unfold wpg at h ⊢
  cases hm : m E s with
  | error e => trivial
  | ok p => rw [hm] at h; exact hq _ _ h

theorem wpg_get (Q : GS → GS → Prop) : wpg (get : GM GS) E Q s ↔ Q s s := Iff.rfl

theorem wpg_read (Q : GEnv → GS → Prop) : wpg (read : GM GEnv) E Q s ↔ Q E s := Iff.rfl

theorem wpg_modify (f : GS → GS) (Q : Unit → GS → Prop) : wpg (modify f : GM Unit) E Q s ↔ Q () (f s) := Iff.rfl

theorem wpg_throw (e : String) (Q : α → GS → Prop) : wpg (throw e : GM α) E Q s := trivial

theorem wpg_ins (op : Op) (args : List Arg) (Q : Unit → GS → Prop) :
    wpg (ins op args) E Q s ↔ Q () { s with out := s.out.push (.ins { op, args }) } := Iff.rfl

theorem wpg_setRegs (f : Regs → Regs) (Q : Unit → GS → Prop) :
    wpg (setRegs f) E Q s ↔ Q () { s with regs := f s.regs } := Iff.rfl

theorem wpg_call (r : String) (Q : Unit → GS → Prop) :
    wpg (call r) E Q s ↔ Q () { s with out := s.out.push (.ins { op := .call, args := [.imm (.sym r)] }) } := Iff.rfl

end

-- the rules meet the code as it is written
example (o : IR.Opd) (E : GEnv) (s : GS) (Q : Unit → GS → Prop)
    (h : ¬ s.regs.hl.contains o = true) (v : Nat) (ho : o = .const v)
    (hq : Q () { s with out := s.out.push (.ins { op := .ld, args := [.hl, n16 v] }), regs := { s.regs with hl := [o] } }) :
    wpg (loadHL o) E Q s := by
  subst ho
  unfold loadHL
  simp only [wpg_bind, wpg_get, wpg_pure, h, Bool.false_eq_true, if_false, wpg_ins, wpg_setRegs]
  exact hq

end Ember.Proof.Z80Gen
