import Ember.Proof.Z80PassCertD3

/-!
# Ember.Proof.Z80PassCertD4 — parts of the check of the certificate (plan M7.3)

The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each
from its start (`starts`).  Written by `ember-passcert`.
-/

namespace Ember.Proof.PassSim.CertD
open Ember.Proof.PassSim Ember.Proof.Z80Gen

set_option maxRecDepth 100000 in
theorem walk1800 : walk ctx part (prevOf StackH.items 1800) (StackH.items.drop 1800) (rows.drop 1800)
    (StackD.items.drop 1734) 1734 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk1950 : walk ctx part (prevOf StackH.items 1950) (StackH.items.drop 1950) (rows.drop 1950)
    (StackD.items.drop 1876) 1876 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem walk2100 : walk ctx part (prevOf StackH.items 2100) (StackH.items.drop 2100) (rows.drop 2100)
    (StackD.items.drop 2023) 2023 = true := by
  decide +kernel

end Ember.Proof.PassSim.CertD
