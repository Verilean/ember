import Ember.Proof.Z80PassCertD2

/-!
# Ember.Proof.Z80PassCertD3 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk1350 : walk ctx part (prevOf StackH.items 1350) (StackH.items.drop 1350) (rows.drop 1350)
    (StackD.items.drop 1298) 1298 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk1500 : walk ctx part (prevOf StackH.items 1500) (StackH.items.drop 1500) (rows.drop 1500)
    (StackD.items.drop 1441) 1441 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk1650 : walk ctx part (prevOf StackH.items 1650) (StackH.items.drop 1650) (rows.drop 1650)
    (StackD.items.drop 1585) 1585 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
