import Ember.Proof.Z80StackHGen.F_rto

/-! The generator on `tcb_reset` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_tcb_reset : FnPart :=
  { f := Stack.fn_tcb_reset, missed := #[], live := some #[],
    code := (items.drop 958).take 38, lits := #[(4, 167772161), (4, 4294967295), (4, 0)], size := 0 }

theorem p1_tcb_reset : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_tcb_reset = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_tcb_reset : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_tcb_reset = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
