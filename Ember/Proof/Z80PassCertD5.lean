import Ember.Proof.Z80PassCertD4

/-!
# Ember.Proof.Z80PassCertD5 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk2250 : walk ctx part (prevOf StackH.items 2250) (StackH.items.drop 2250) (rows.drop 2250)
    (StackD.items.drop 2169) 2169 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk2400 : walk ctx part (prevOf StackH.items 2400) (StackH.items.drop 2400) (rows.drop 2400)
    (StackD.items.drop 2313) 2313 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk2550 : walk ctx part (prevOf StackH.items 2550) (StackH.items.drop 2550) (rows.drop 2550)
    (StackD.items.drop 2453) 2453 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
