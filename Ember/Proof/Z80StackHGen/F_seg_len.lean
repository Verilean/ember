import Ember.Proof.Z80StackHGen.F_wnd

/-! The generator on `seg_len` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_seg_len : FnPart :=
  { f := Stack.fn_seg_len, missed := #[false, false], live := some #[true, true, true, true],
    code := (items.drop 1014).take 24, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }

theorem p1_seg_len : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_seg_len = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_seg_len : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_seg_len = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
