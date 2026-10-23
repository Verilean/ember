import Ember.Proof.Z80PassAbsD2

/-!
# Ember.Proof.Z80PassAbsD3 — parts of the walk over what is known (plan M7.3)

The walk of `Z80PassAbsWalk` over parts of `StackH`'s items, by the kernel (`decide +kernel`), each
from its start (`astarts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem awalk2700 : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart
    (prevA StackH.items rows acl 2700) (StackH.items.drop 2700) (rows.drop 2700) (acl.drop 2700) = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
