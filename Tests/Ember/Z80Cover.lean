import Ember.Proof.Z80Shape
import Tests.Ember.LangPrograms

/-!
# The instruction theorems cover `regress_wide_store` (plan M7.3)

`coverage` (`Ember.Proof.Z80Shape`) lowers a program and lists the
instructions `Covered` leaves out.  `Regress.p5` (`regress_wide_store`)
lowers to 30 instructions, none left out.  The `#guard` evaluates this
when the module is built: it is not a theorem (the type checker,
`Ember.Lang.Check`, is `partial`, so the kernel cannot reduce
`coverage`), and it says nothing of the program's image.
-/

namespace Ember.Tests.Z80Cover

open Ember.Proof.Z80Gen Ember.Tests.LangPrograms

#guard (coverage Regress.p5).map (fun (a, u) => (a.length, u.length)) == some (30, 0)

end Ember.Tests.Z80Cover
