import LSpec
import Tests.Ember.SpecTests
import Tests.Ember.LangTests
import Tests.Ember.NetTests

/-!
# `lake test` — everything

IO suites (corpus replay, scenarios, generators, differential runs) run
first and fail the run with a non-zero exit; then the LSpec unit tests.
-/

open LSpec

def main (args : List String) : IO UInt32 := do
  let mut rc : UInt32 := 0
  IO.println "== Ember.Spec (M1)"
  if (← Ember.Tests.SpecTests.main) != 0 then rc := 1
  IO.println "== Ember.Lang / Ember.C (M2)"
  if (← Ember.Tests.LangTests.main) != 0 then rc := 1
  IO.println "== Ember.Net (M3)"
  if (← Ember.Tests.NetTests.main) != 0 then rc := 1
  let u ← lspecIO (Std.HashMap.ofList [("spec", [Ember.Tests.SpecTests.unitTests]),
                                       ("lang", [Ember.Tests.LangTests.unitTests])]) args
  return if rc != 0 then rc else u
