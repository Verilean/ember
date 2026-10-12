import Ember.Proof.Z80Prog
import Ember.Proof.IRNet

/-!
# Ember.Proof.Z80Shape — what `FnStatic` asks of a function's body, checked (plan M7.3)

Of `FnStatic` (what the theorems about generated code assume of a
function) four parts speak of the body alone: its instructions are
covered by the instruction theorems, it is not empty and ends with an
instruction that does not go on, and a label is in it once.  `shapeB`
decides them; the `#guard`s say it accepts every function of the builds
of the stack — the SLIP build, the loopback program — as `IR.lower`
returns them.  (The other parts speak of the layout; no checker yet.)
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- A label at `pc` is the first of its name. -/
def labelOnce (body : Array IR.Instr) (pc : Nat) : IR.Instr → Bool
  | .label l => body.findIdx? (· == .label l) == some pc
  | _ => true

/-- The body is covered, ends with an instruction that does not go on, and has every label once. -/
def shapeB (f : IR.Fn) : Bool :=
  f.body.toList.all Covered && decide (0 < f.body.size) &&
    ((List.range f.body.size).all fun pc =>
      match f.body[pc]? with
      | some i => (!canFall i || decide (pc + 1 < f.body.size)) && labelOnce f.body pc i
      | none => true)

structure Shape (f : IR.Fn) : Prop where
  covered : ∀ i, i ∈ f.body.toList → Covered i = true
  falls : ∀ pc i, f.body[pc]? = some i → canFall i = true → pc + 1 < f.body.size
  nonempty : 0 < f.body.size
  labels : ∀ pc l, f.body[pc]? = some (.label l) → f.body.findIdx? (· == .label l) = some pc

theorem shapeB_sound {f : IR.Fn} (h : shapeB f = true) : Shape f := by
  simp only [shapeB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨hcov, hne⟩, hall⟩ := h
  have hlt : ∀ pc i, f.body[pc]? = some i → pc < f.body.size := by
    intro pc i hb
    rcases Nat.lt_or_ge pc f.body.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hb; cases hb
  refine ⟨hcov, fun pc i hb hf => ?_, hne, fun pc l hb => ?_⟩
  · have := hall pc (hlt pc i hb)
    rw [hb] at this
    have h2 : ((!canFall i || decide (pc + 1 < f.body.size)) && labelOnce f.body pc i) = true := this
    rw [Bool.and_eq_true] at h2
    simpa [hf] using h2.1
  · have := hall pc (hlt pc _ hb)
    rw [hb] at this
    have h2 : ((!canFall (.label l) || decide (pc + 1 < f.body.size)) &&
        labelOnce f.body pc (.label l)) = true := this
    rw [Bool.and_eq_true] at h2
    simpa [labelOnce] using h2.2

/-- Every function of the program as lowered has the shape. -/
def progShapeB (p : Ember.Lang.Prog) : Bool :=
  match p.check with
  | .ok q =>
    match IR.lower q with
    | .ok r => r.fns.all shapeB
    | .error _ => false
  | .error _ => false

#guard progShapeB Ember.Net.prog
#guard progShapeB Ember.Net.Loop.prog

/-- info: 'Ember.Proof.Z80Gen.shapeB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shapeB_sound

end Ember.Proof.Z80Gen
