import Ember.Lang.Surface

/-!
# Ember.Z80.Wide — a small program on four-byte values through addresses (plan M7.3)

The program the image theorems of `Ember/Proof/Z80WideH*.lean` are about:
a `store` of four bytes through an address of every kind the generator
has (a constant from the literal pool, a value the accumulator holds
already, the sum `WV + k`), a `load` of four bytes through an address,
an index check that traps when the input byte is 4 or more.  It calls
only routines of the runtime that are proved from their items
(`rt_input`, `rt_ld32`, `rt_st32`, `rt_add32`, `rt_acc_hl`, `rt_bound`,
`rt_out_byte`, `rt_out_end`), and has no initialised variable (start-up
only clears the RAM).
-/

namespace Ember.Z80.Wide
open Ember.Lang

ember global wa : [u32; 4]
ember const WV : u32 := 305419896

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  let i : u8 := (k : u8) &&& 3
  wa[i] := WV
  wa[(i + 1) &&& 3] := WV + (k : u32)
  wa[(i + 2) &&& 3] := 70000
  out.byte(((wa[i] : u16) : u8))
  out.byte(((wa[(i + 1) &&& 3] : u16) : u8))
  out.byte(((wa[(i + 2) &&& 3] : u16) : u8))
  wa[(k : u8)] := WV
  out.end()

def prog : Prog := { globals := [wa, WV], fns := [main], entry := "main" }

end Ember.Z80.Wide
