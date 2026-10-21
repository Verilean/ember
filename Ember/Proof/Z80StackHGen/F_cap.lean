import Ember.Proof.Z80StackHGen.F_tcb_reset

/-! The generator on `cap` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_cap : FnPart :=
  { f := Stack.fn_cap, missed := #[], live := some #[],
    code := (items.drop 996).take 11, lits := #[(4, 167772161), (4, 4294967295), (4, 0)], size := 0 }

theorem p1_cap : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_cap = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_cap : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_cap = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
