import Ember.Proof.Z80StackHGen.F_send_seg

/-! The generator on `send_syn_ack` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_send_syn_ack : FnPart :=
  { f := Stack.fn_send_syn_ack, missed := #[], live := some #[],
    code := (items.drop 1212).take 14, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_send_syn_ack : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_syn_ack = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_send_syn_ack : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_syn_ack = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
