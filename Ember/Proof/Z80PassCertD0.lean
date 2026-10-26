import Ember.Proof.Z80PassCertD

/-!
# Ember.Proof.Z80PassCertD0 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk0 : walk ctx part (prevOf StackH.items 0) (StackH.items.drop 0) (rows.drop 0)
    (StackD.items.drop 0) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk150 : walk ctx part (prevOf StackH.items 150) (StackH.items.drop 150) (rows.drop 150)
    (StackD.items.drop 146) 146 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk300 : walk ctx part (prevOf StackH.items 300) (StackH.items.drop 300) (rows.drop 300)
    (StackD.items.drop 290) 290 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
