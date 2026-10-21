import Ember.Proof.Z80StackHGen.F_set32

/-! The generator on `add16` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_add16 : FnPart :=
  { f := Stack.fn_add16, missed := #[false], live := some #[true, true, false, false, false, false],
    code := (items.drop 170).take 13, lits := #[], size := 0 }

theorem p1_add16 : pass1B Stack.ir #[] g_add16 = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_add16 : pass2B Stack.ir #[] g_add16 = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
