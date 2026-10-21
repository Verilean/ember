import Ember.Proof.Z80StackHGen.F_slip_rx

/-! The generator on `rto` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_rto : FnPart :=
  { f := Stack.fn_rto, missed := #[], live := some #[true, true, true, true, true],
    code := (items.drop 928).take 30, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }

theorem p1_rto : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_rto = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_rto : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_rto = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
