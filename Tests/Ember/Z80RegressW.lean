import Ember.Proof.IRCheck
import Ember.Proof.IRLower
import Ember.Proof.Z80RegressWHItems
import Tests.Ember.LangPrograms

/-!
# `regress_wide_store` and the terms written out for it in `Ember/Proof` (plan M7.3)

`Ember.Proof.Z80Gen.RegressW.ir` and `RegressWH.items`/`layout` are
written out in `Ember` (which does not import `Tests`) for a later
theorem on the image.  Here, where the program is (`Regress.p5`): its
lowering is `RegressW.ir`, and the parts of what such a theorem will
take of the checked program that can be computed hold — `#guard`s,
evaluated when this file is built (by `tools/ember/ci.sh`), not proved;
no theorem here is about the image.
-/

namespace Ember.Tests.Z80RegressW
open Ember Ember.Proof.IRSim Ember.Proof.Z80Gen Ember.Tests.LangPrograms

/-- The lowering of the checked program is `RegressW.ir`. -/
def irIsLowering : Bool :=
  match Regress.p5.check with
  | .ok q =>
    match Ember.Z80.IR.lower q with
    | .ok r => Loop.sameProg r RegressW.ir
    | .error _ => false
  | .error _ => false

#guard irIsLowering

-- what is computable of the checked program: entry, no frame input, typing (`progOkB`), the layout (`irOkB`),
-- no drop reasons, no notes
#guard (Regress.p5.check.toOption.map fun q =>
  q.entry == "wide_store" && q.framed == false && progOkB q && irOkB q RegressWH.layout &&
    q.dropReasons == [] && q.notes == []) == some true

end Ember.Tests.Z80RegressW
