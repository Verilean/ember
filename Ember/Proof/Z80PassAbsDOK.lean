import Ember.Proof.Z80PassAbsD3
import Ember.Proof.Z80PassCertDOK

/-!
# Ember.Proof.Z80PassAbsDOK — what is known of `StackH`'s registers, checked (plan M7.3)

`absD_ok`: the list and levels of `Z80PassAbsD` checked (`AbsGlob`), from the parts of the walk by the
kernel (`Z80PassAbsD0` …), which cover every item (`absRows_of_walks`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem acl_len : acl.length = StackH.items.length := by decide +kernel

theorem astarts_walk : ∀ p, p ∈ astarts →
    absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart (prevA StackH.items rows acl p) (StackH.items.drop p)
      (rows.drop p) (acl.drop p) = true := by
  intro p hp
  simp only [astarts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact awalk0
  · exact awalk300
  · exact awalk600
  · exact awalk900
  · exact awalk1200
  · exact awalk1500
  · exact awalk1800
  · exact awalk2100
  · exact awalk2400
  · exact awalk2700

theorem astarts_at : ∀ i (h : i < astarts.length), astarts[i]'h = apart * i := by
  decide

set_option maxRecDepth 100000 in
theorem astarts_reach : StackH.items.length ≤ apart * astarts.length := by decide +kernel

theorem acl_first : acAt acl 0 = none := rfl

theorem lv_top : hi + 4 + 2 * lvOf lv topE ≤ 65536 := by decide

/-- **What is known of `StackH`'s registers, and the levels, checked.** -/
theorem absD_ok : AbsGlob StackH.items StackH.asm lo hi rows acl lv :=
  ⟨absRows_of_walks actx lo hi lv _ rows acl rows_len acl_len apart astarts astarts_walk astarts_at (by decide)
    astarts_reach, acl_len, rows_len, acl_first, lv_top⟩

/-- info: 'Ember.Proof.PassSim.CertD.absD_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absD_ok

end Ember.Proof.PassSim.CertD
