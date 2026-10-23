import Ember.Proof.Z80PassAbsD

/-!
# Ember.Proof.Z80PassAbsD0 — parts of the walk over what is known (plan M7.3)

The walk of `Z80PassAbsWalk` over parts of `StackH`'s items, by the kernel (`decide +kernel`), each
from its start (`astarts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem awalk0 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 0) (StackH.items.drop 0) (rows.drop 0) (acl.drop 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk300 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 300) (StackH.items.drop 300) (rows.drop 300) (acl.drop 300) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk600 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 600) (StackH.items.drop 600) (rows.drop 600) (acl.drop 600) = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
