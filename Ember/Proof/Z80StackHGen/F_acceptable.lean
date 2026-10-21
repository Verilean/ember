import Ember.Proof.Z80StackHGen.F_rexmit

/-! The generator on `acceptable` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_acceptable : FnPart :=
  { f := Stack.fn_acceptable, missed := #[false, false, true, false, false, false, true, true, false, true], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1481).take 77, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 13 }

theorem p1_acceptable : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_acceptable = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_acceptable : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_acceptable = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
