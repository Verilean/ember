import Ember.Proof.Z80StackHGen.F_ip_send

/-! The generator on `icmp_input` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_icmp_input : FnPart :=
  { f := Stack.fn_icmp_input, missed := #[], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 427).take 61, lits := #[(4, 167772161)], size := 0 }

theorem p1_icmp_input : pass1B Stack.ir #[(4, 167772161)] g_icmp_input = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_icmp_input : pass2B Stack.ir #[(4, 167772161)] g_icmp_input = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
