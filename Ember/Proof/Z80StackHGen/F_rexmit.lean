import Ember.Proof.Z80StackHGen.F_output

/-! The generator on `rexmit` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_rexmit : FnPart :=
  { f := Stack.fn_rexmit, missed := #[], live := some #[true],
    code := (items.drop 1444).take 37, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_rexmit : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_rexmit = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_rexmit : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_rexmit = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
