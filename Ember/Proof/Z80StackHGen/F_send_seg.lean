import Ember.Proof.Z80StackHGen.F_tcp_emit

/-! The generator on `send_seg` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_send_seg : FnPart :=
  { f := Stack.fn_send_seg, missed := #[], live := some #[true, true, true, false, false, true, false, true, false, true, true, false],
    code := (items.drop 1179).take 33, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_send_seg : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_seg = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_send_seg : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_seg = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
