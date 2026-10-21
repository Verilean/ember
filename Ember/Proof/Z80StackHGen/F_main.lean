import Ember.Proof.Z80StackHGen.F_tcp_tick

/-! The generator on `main` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def g_main : FnPart :=
  { f := Stack.fn_main, missed := #[], live := some #[false, false],
    code := (items.drop 2513).take 59, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }

theorem p1_main : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_main = true := by
  unfold pass1B
  rw [shared_eq]
  decide +kernel
theorem p2_main : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_main = true := by decide +kernel

end Ember.Proof.Z80Gen.StackH
