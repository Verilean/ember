import Ember.Proof.Z80PassAbsD1

/-!
# Ember.Proof.Z80PassAbsD2 — parts of the walk over what is known (plan M7.3)

The walk of `Z80PassAbsWalk` over parts of `StackH`'s items, by the kernel (`decide +kernel`), each
from its start (`astarts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem awalk1800 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 1800) (StackH.items.drop 1800) (rows.drop 1800) (acl.drop 1800) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk2100 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 2100) (StackH.items.drop 2100) (rows.drop 2100) (acl.drop 2100) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem awalk2400 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 2400) (StackH.items.drop 2400) (rows.drop 2400) (acl.drop 2400) = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
