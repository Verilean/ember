import Ember.Proof.Z80StackHGen.F_add16

/-! The generator on `csum` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_csum : FnPart :=
  { f := Stack.fn_csum, missed := #[false, false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, false, true, false],
    code := (items.drop 183).take 61, lits := #[], size := 0 }

theorem p1_csum : pass1B Stack.ir #[] g_csum = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_csum : pass2B Stack.ir #[] g_csum = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
