import Ember.Proof.Z80StackHGen.F_pseudo

/-! The generator on `csum_update` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_csum_update : FnPart :=
  { f := Stack.fn_csum_update, missed := #[false, false], live := some #[true, true, true, true, true, true, true, true],
    code := (items.drop 275).take 15, lits := #[], size := 0 }

theorem p1_csum_update : pass1B Stack.ir #[] g_csum_update = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_csum_update : pass2B Stack.ir #[] g_csum_update = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
