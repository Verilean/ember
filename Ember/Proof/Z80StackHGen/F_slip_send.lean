import Ember.Proof.Z80StackHGen.F_verifies

/-! The generator on `slip_send` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_slip_send : FnPart :=
  { f := Stack.fn_slip_send, missed := #[], live := some #[true, true, true, true, true, true, true],
    code := (items.drop 309).take 50, lits := #[], size := 0 }

theorem p1_slip_send : pass1B Stack.ir #[] g_slip_send = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_slip_send : pass2B Stack.ir #[] g_slip_send = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
