import Ember.Proof.Z80StackHGen.F_csum_update

/-! The generator on `verifies` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_verifies : FnPart :=
  { f := Stack.fn_verifies, missed := #[false, true, false], live := some #[true, true],
    code := (items.drop 290).take 19, lits := #[], size := 1 }

theorem p1_verifies : pass1B Stack.ir #[] g_verifies = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_verifies : pass2B Stack.ir #[] g_verifies = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
