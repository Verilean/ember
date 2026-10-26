import Ember.Proof.Z80Shape
import Ember.Lang.Examples

/-!
# Ember.Proof.Z80Cover — what the instruction theorems cover of the examples (plan M7.3)

`coverage` lowers a program and lists the instructions `Covered` leaves
out.  This records it for `crc32`: all 34 of its instructions are covered
(the last were `not` of four bytes and the right shift of four bytes by a
constant, `notW_ok` and `shiftR4_ok`).  Coverage is a statement about the
instruction theorems only: it is not a theorem about the program's image.
-/

namespace Ember.Proof.Z80Gen

#guard ((Ember.Lang.Examples.all.filter (·.1 == "crc32")).map fun (_, p) =>
  (coverage p).map fun (a, u) => (List.length a, List.length u)) == [some (34, 0)]

end Ember.Proof.Z80Gen
