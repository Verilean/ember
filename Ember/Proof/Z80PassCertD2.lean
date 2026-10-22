import Ember.Proof.Z80PassCertD1

/-!
# Ember.Proof.Z80PassCertD2 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk900 : walk ctx part (prevOf StackH.items 900) (StackH.items.drop 900) (rows.drop 900)
    (StackD.items.drop 863) 863 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk1050 : walk ctx part (prevOf StackH.items 1050) (StackH.items.drop 1050) (rows.drop 1050)
    (StackD.items.drop 1003) 1003 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk1200 : walk ctx part (prevOf StackH.items 1200) (StackH.items.drop 1200) (rows.drop 1200)
    (StackD.items.drop 1152) 1152 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
