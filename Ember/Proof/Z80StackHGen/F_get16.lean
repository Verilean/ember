import Ember.Proof.Z80StackHGen.Shared

/-! The generator on `get16` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_get16 : FnPart :=
  { f := Stack.fn_get16, missed := #[false, false, false, true, false, false, false], live := some #[true, true],
    code := (items.drop 86).take 31, lits := #[], size := 2 }

theorem p1_get16 : pass1B Stack.ir #[] g_get16 = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_get16 : pass2B Stack.ir #[] g_get16 = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
