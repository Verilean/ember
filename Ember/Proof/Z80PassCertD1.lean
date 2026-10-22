import Ember.Proof.Z80PassCertD0

/-!
# Ember.Proof.Z80PassCertD1 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk450 : walk ctx part (prevOf StackH.items 450) (StackH.items.drop 450) (rows.drop 450)
    (StackD.items.drop 437) 437 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk600 : walk ctx part (prevOf StackH.items 600) (StackH.items.drop 600) (rows.drop 600)
    (StackD.items.drop 580) 580 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk750 : walk ctx part (prevOf StackH.items 750) (StackH.items.drop 750) (rows.drop 750)
    (StackD.items.drop 721) 721 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
