import Ember.Z80.Frame

/-!
# Ember.Proof.Z80Frame — the frame validator is right (plan M7.2)

Frames are static and overlaid along the call graph.  `IR.valid` checks
a layout without looking at how it was made; here: a layout it accepts
keeps every function's frame apart from the globals and from the frame
of every function it can reach through calls (`Reach`: the transitive
closure of "calls or has inlined"), and no function reaches itself.

The reachable set is computed with a bound on the rounds; the validator
does not trust the bound — it checks that the set is closed — and
neither does the proof.
-/

namespace Ember.Z80.IR

/-- `g` can be active while `f` is: `f` calls it, directly or through others. -/
inductive Reach (p : Prog) : String → String → Prop
  | call {f g : String} : g ∈ calleesOf p f → Reach p f g
  | step {f g h : String} : Reach p f g → h ∈ calleesOf p g → Reach p f h

/-- Two ranges of bytes that share none. -/
theorem disjoint_spec {a an b bn : Nat} (h : disjoint a an b bn = true) (x : Nat) (ha : a ≤ x ∧ x < a + an)
    (hb : b ≤ x ∧ x < b + bn) : False := by
  simp only [disjoint, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

/-- What a valid layout guarantees. -/
structure Sound (p : Prog) (l : Layout) (frameSize : String → Nat) (lo hi : Nat) : Prop where
  /-- The globals lie in the memory given … -/
  globals_in : ∀ g, g ∈ placed p l → lo ≤ g.2.1 ∧ g.2.1 + g.2.2 ≤ hi
  /-- … and two of different names share no byte. -/
  globals_apart : ∀ g h, g ∈ placed p l → h ∈ placed p l → g.1 ≠ h.1 → disjoint g.2.1 g.2.2 h.2.1 h.2.2 = true
  /-- Every function has a frame in the memory given, apart from every
  global and from the frame of every function it can reach; and it does
  not reach itself. -/
  frames : ∀ f, f ∈ p.fns → ∃ a, l.frames.lookup f.name = some a ∧ lo ≤ a ∧ a + frameSize f.name ≤ hi ∧
    (∀ g, g ∈ placed p l → disjoint a (frameSize f.name) g.2.1 g.2.2 = true) ∧
    ∀ g, Reach p f.name g → g ≠ f.name ∧
      ∃ b, l.frames.lookup g = some b ∧ disjoint a (frameSize f.name) b (frameSize g) = true

theorem valid_sound {p : Prog} {l : Layout} {frameSize : String → Nat} {lo hi : Nat}
    (h : valid p l frameSize lo hi = true) : Sound p l frameSize lo hi := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hin, hap⟩, hf⟩ := h
  refine ⟨fun g hg => hin g hg, fun g h' hg hh hne => ?_, fun f hfm => ?_⟩
  · rcases hap g hg h' hh with e | d
    · exact absurd e hne
    · exact d
  · have hf' := hf f hfm
    cases ha : l.frames.lookup f.name with
    | none => simp [ha] at hf'
    | some a =>
      simp only [ha, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.contains_iff_mem, bne_iff_ne,
        ne_eq] at hf'
      obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hgl⟩, hcall⟩, hclosed⟩, hr⟩ := hf'
      refine ⟨a, rfl, hlo, hhi, hgl, fun g hreach => ?_⟩
      have hmem : g ∈ reach p f.name := by
        induction hreach with
        | call hc => exact hcall _ hc
        | step _ hc ih => exact hclosed _ ih _ hc
      obtain ⟨hne, hd⟩ := hr g hmem
      refine ⟨hne, ?_⟩
      cases hb : l.frames.lookup g with
      | none => simp [hb] at hd
      | some b => exact ⟨b, rfl, by simpa [hb] using hd⟩

/-- **A layout `validate` accepts is sound.** -/
theorem validate_sound {p : Prog} {l : Layout} {frameSize : String → Nat} {lo hi : Nat}
    (h : validate p l frameSize lo hi = .ok ()) : Sound p l frameSize lo hi := by
  unfold validate at h
  split at h
  · exact valid_sound ‹_›
  · split at h <;> cases h

/-- info: 'Ember.Z80.IR.validate_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validate_sound

end Ember.Z80.IR
