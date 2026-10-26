import Ember.Proof.Z80PassCertD6

/-!
# Ember.Proof.Z80PassCertDOK — the certificate for the stack's images, checked (plan M7.3)

`certD_ok`: the rows of `Z80PassCertD` checked (`RowsOK`), from the parts of the walk by the kernel
(`Z80PassCertD0` …), which cover every item (`rows_of_walks`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem rows_len : rows.length = StackH.items.length := by decide +kernel

theorem starts_walk : ∀ p, p ∈ starts →
    walk ctx part (prevOf StackH.items p.1) (StackH.items.drop p.1) (rows.drop p.1) (StackD.items.drop p.2) p.2 = true := by
  intro p hp
  simp only [starts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact walk0
  · exact walk150
  · exact walk300
  · exact walk450
  · exact walk600
  · exact walk750
  · exact walk900
  · exact walk1050
  · exact walk1200
  · exact walk1350
  · exact walk1500
  · exact walk1650
  · exact walk1800
  · exact walk1950
  · exact walk2100
  · exact walk2250
  · exact walk2400
  · exact walk2550
  · exact walk2700
  · exact walk2850

theorem starts_at : ∀ i (h : i < starts.length), (starts[i]'h).1 = part * i := by
  decide

set_option maxRecDepth 100000 in
theorem starts_reach : StackH.items.length ≤ part * starts.length := by decide +kernel

set_option maxRecDepth 100000 in
theorem first : ∃ r rs, rows = r :: rs ∧ r.tag ≠ .none ∧ r.kb = 0 ∧ r.th = false ∧ r.tl = false ∧ topE ∈ r.act :=
  ⟨_, _, rfl, by decide, rfl, rfl, rfl, by decide⟩

/-- **The certificate's rows checked.** -/
theorem certD_ok : RowsOK StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr :=
  ⟨rows_len, first, rows_of_walks' ctx _ _ rows part starts starts_walk starts_at (by decide) starts_reach rows_len⟩

/-- info: 'Ember.Proof.PassSim.CertD.certD_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms certD_ok

end Ember.Proof.PassSim.CertD
