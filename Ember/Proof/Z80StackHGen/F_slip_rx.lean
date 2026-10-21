import Ember.Proof.Z80StackHGen.F_slip_store

/-! The generator on `slip_rx` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_slip_rx : FnPart :=
  { f := Stack.fn_slip_rx, missed := #[], live := some #[true],
    code := (items.drop 872).take 56, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }
theorem p1_slip_rx : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_rx = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_slip_rx : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_rx = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
