import Ember.Proof.Z80StackHGen.F_parse_mss

/-! The generator on `tcp_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_tcp_input : FnPart :=
  { f := Stack.fn_tcp_input, missed := #[false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 2293).take 95, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }
theorem p1_tcp_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_input = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_tcp_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_input = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
