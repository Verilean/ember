import Ember.Proof.Z80PassAbsD0

/-!
# Ember.Proof.Z80PassAbsD1 — parts of the walk over what is known (plan M7.3)

The walk of `Z80PassAbsWalk` over parts of `StackH`'s items, by the kernel (`decide +kernel`), each
from its start (`astarts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem awalk900 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 900) (StackH.items.drop 900) (rows.drop 900) (acl.drop 900) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk1200 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 1200) (StackH.items.drop 1200) (rows.drop 1200) (acl.drop 1200) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk1500 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 1500) (StackH.items.drop 1500) (rows.drop 1500) (acl.drop 1500) = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
