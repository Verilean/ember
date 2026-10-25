import Ember.Proof.IRCheck
import Ember.Proof.IRLower
import Ember.Proof.Z80RegressWHSpec
import Tests.Ember.LangPrograms

/-!
# `regress_wide_store` and the terms written out for it in `Ember/Proof` (plan M7.3)

`Ember.Proof.Z80Gen.RegressW.ir` and `RegressWH.items`/`layout` are
written out in `Ember` (which does not import `Tests`), and the theorems
on the image there (`Z80RegressWHSpec`) take `RegressSrc p` of the Ember
program.  Here, where the program is (`Regress.p5`): its lowering is
`RegressW.ir`, and the other parts of `RegressSrc` hold of the checked
program; and, for two inputs, what the theorems take of the Ember
semantics (calls that end, a call that traps).  All `#guard`s, evaluated
when this file is built (by `tools/ember/ci.sh`), not proved — the
checker is `partial`; that `RegressSrc` holds of the checked `Regress.p5`
is not a kernel theorem.
-/

namespace Ember.Tests.Z80RegressW
open Ember Ember.Proof.IRSim Ember.Proof.Z80Gen Ember.Tests.LangPrograms
open Ember.Proof.Refine (callN)

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

-- the two inputs of `RegressWH`, in the Ember semantics of the checked program: indices in range — two calls
-- end, no input left, the frames `78 79 70`, `78 7a 70` sent (`regressH_harness_halts`); the second byte out of
-- range for the last store — the first call ends, the second, with input remaining, traps (`regressH_harness_trap`)
#guard match Regress.p5.check with
  | .ok q => match callN 1000 q "wide_store" 2 (Lang.Sem.initial q RegressWH.inputsOk) with
    | some st => st.world.next.1 == 0xFFFF && WideH.txs st.world == [[0x78, 0x79, 0x70], [0x78, 0x7a, 0x70]]
    | none => false
  | .error _ => false

#guard match Regress.p5.check with
  | .ok q => match callN 1000 q "wide_store" 1 (Lang.Sem.initial q RegressWH.inputsTrap) with
    | some st => st.world.next.1 != 0xFFFF && WideH.txs st.world == [[0x78, 0x7a, 0x70]] &&
        (match Lang.Sem.call 1000 q st "wide_store" [] with
         | .trap _ => true
         | _ => false)
    | none => false
  | .error _ => false

end Ember.Tests.Z80RegressW
