import Ember.Proof.Z80StackHGen.F_slip_send

/-! The generator on `ip_send` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_ip_send : FnPart :=
  { f := Stack.fn_ip_send, missed := #[false, false, false], live := some #[true, true, true, true, true, true, true, true, true],
    code := (items.drop 359).take 68, lits := #[(4, 167772161)], size := 0 }
theorem p1_ip_send : pass1B Stack.ir #[] g_ip_send = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_ip_send : pass2B Stack.ir #[] g_ip_send = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
