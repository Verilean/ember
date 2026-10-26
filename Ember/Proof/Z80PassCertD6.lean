import Ember.Proof.Z80PassCertD5

/-!
# Ember.Proof.Z80PassCertD6 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk2700 : walk ctx part (prevOf StackH.items 2700) (StackH.items.drop 2700) (rows.drop 2700)
    (StackD.items.drop 2588) 2588 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk2850 : walk ctx part (prevOf StackH.items 2850) (StackH.items.drop 2850) (rows.drop 2850)
    (StackD.items.drop 2682) 2682 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
