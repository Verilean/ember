import Tests.Ember.Scenarios
import Ember.Trace.Text

/-!
# `ember-fixtures` — run the hand-written scenarios, write their traces

`lake exe ember-fixtures` checks every scenario's expectations and
(re)writes `Tests/Ember/corpus/<dir>/<name>.trace`; with `--check` it only
checks.  Exit status 1 when any expectation fails.
-/

namespace Ember.Tests.Fixtures
open Ember Ember.Spec.Scenario

def corpusDir : System.FilePath := "Tests/Ember/corpus"

def header (sc : Scenario) : String :=
  s!"# hand-written scenario `{sc.name}` (Tests/Ember/Scenarios.lean): {sc.doc}\n" ++
  "# expected outputs are the Spec's, checked against the scenario's expectations\n"

/-- Run all scenarios; returns the number of failures. -/
def runAll (write : Bool) (verbose := true) : IO Nat := do
  let mut bad := 0
  for sc in Tests.Scenarios.all do
    match sc.run with
    | .error e =>
      bad := bad + 1
      IO.println s!"FAIL {sc.dir}/{sc.name}: {e}"
    | .ok t =>
      if write then
        let d := corpusDir / sc.dir
        IO.FS.createDirAll d
        let p := d / (sc.name ++ ".trace")
        let txt := t.print
        let lines := txt.splitOn "\n"
        IO.FS.writeFile p (lines.head! ++ "\n" ++ header sc ++ "\n".intercalate lines.tail!)
      if verbose then IO.println s!"ok   {sc.dir}/{sc.name}"
  return bad

def main (args : List String) : IO UInt32 := do
  let bad ← runAll (write := !args.contains "--check")
  return if bad == 0 then 0 else 1

end Ember.Tests.Fixtures
