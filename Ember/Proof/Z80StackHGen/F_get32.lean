import Ember.Proof.Z80StackHGen.F_get16

/-! The generator on `get32` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_get32 : FnPart :=
  { f := Stack.fn_get32, missed := #[false, false, true, false, false], live := some #[true, true, true, true, true, true],
    code := (items.drop 117).take 21, lits := #[], size := 4 }

theorem p1_get32 : pass1B Stack.ir #[] g_get32 = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_get32 : pass2B Stack.ir #[] g_get32 = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
