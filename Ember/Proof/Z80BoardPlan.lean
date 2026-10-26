import Ember.Proof.Z80PlanOf
import Ember.Z80.Runtime

/-!
# Ember.Proof.Z80BoardPlan — the plans of the images for the board pass (plan M7.3)

For a program built for the board (`Codegen.build` with
`Runtime.board`), `boardPlanIn` gives what `mkPlan` makes a plan of: the
program as lowered, the layout and the symbols of the image, the
environments its functions are generated in.  `boardCheck` runs
`planCheck` on it: `okB` of the plan and `fnStaticB` of every function.

The `#guard`s say the check passes for the SLIP build of the stack and
for the loopback program — evaluated when this file is built, not
proved (for the loopback program the kernel computes it: `Z80Loop`).
So what the theorems about generated code assume of the layout holds of
these builds, given that the image has the plan's labels and wide
constants (`Labels`, `Lits`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Codegen

/-- RAM of the board: the runtime's cells from `0x8000` (the accumulator
among them, when the image has one — else eight bytes above everything),
then globals, frames and the slots of temporaries; the stack from there
to the top of memory. -/
def boardPlanIn (prog : Ember.Lang.Prog) : Except String PlanIn := do
  let q ← (prog.check).mapError fun _ => "check"
  let ir ← IR.lower q
  let img ← Codegen.build ir (Runtime.board 0 q.dropReasons q.notes) (Runtime.boardHead 0x8000)
    (reserved := (Runtime.boardCells 0x8000).2)
  let envs ← progEnvs ir false (sharedBytes ir)
  let top := img.layout.top
  let first := ((img.layout.globals.map (·.2)).filter (· ≥ 0x8000) ++ img.layout.frames.map (·.2)).foldl Nat.min top
  let (acc, rt, stackLo) :=
    match img.labels.lookup "rt_acc" with
    | some a => (a, [(0x8000, a), (a + 8, first)], top)
    | none => (top, [(0x8000, first)], top + 8)
  return { c := { prog := ir, layout := img.layout, dropReasons := q.dropReasons, notes := q.notes }, envs,
           ramStart := 0x8000, stackLo, stackHi := 65536, acc, rtK := 32, rt, labels := ["rt_trap"] }

def boardCheck (prog : Ember.Lang.Prog) : Bool :=
  match boardPlanIn prog with
  | .ok I => planCheck I
  | .error _ => false

#guard boardCheck Ember.Net.prog
#guard boardCheck Ember.Net.Loop.prog

end Ember.Proof.Z80Gen
