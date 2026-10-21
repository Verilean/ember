import Ember.Proof.Z80StackHGen.F_csum

/-! The generator on `pseudo` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_pseudo : FnPart :=
  { f := Stack.fn_pseudo, missed := #[false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 244).take 31, lits := #[], size := 0 }
theorem p1_pseudo : pass1B Stack.ir #[] g_pseudo = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_pseudo : pass2B Stack.ir #[] g_pseudo = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
