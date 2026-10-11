import LSpec
import Tests.Ember.SpecTests
import Tests.Ember.LangTests
import Tests.Ember.NetTests
import Tests.Ember.TargetTests
import Tests.Ember.Z80Tests

/-!
# `lake test` — everything

IO suites (corpus replay, scenarios, generators, differential runs) run
first and fail the run with a non-zero exit; then the LSpec unit tests.
-/

open LSpec

def main (args : List String) : IO UInt32 := do
  -- `EMBER_ONLY=spec|lang|net|esp32|z80` runs one suite
  let only ← IO.getEnv "EMBER_ONLY"
  let want (name : String) : Bool := only.isNone || only == some name
  let mut rc : UInt32 := 0
  if want "spec" then
    IO.println "== Ember.Spec (M1)"
    if (← Ember.Tests.SpecTests.main) != 0 then rc := 1
  if want "lang" then
    IO.println "== Ember.Lang / Ember.C (M2)"
    if (← Ember.Tests.LangTests.main) != 0 then rc := 1
  if want "net" then
    IO.println "== Ember.Net (M3)"
    if (← Ember.Tests.NetTests.main) != 0 then rc := 1
  if want "esp32" then
    IO.println "== ESP32-C3 in QEMU (M4)"
    if (← Ember.Tests.TargetTests.main) != 0 then rc := 1
  if want "z80" then
    IO.println "== Z80: the model, SDCC's code on it, and the own back end (M4z, M6)"
    if (← Ember.Tests.Z80Tests.main) != 0 then rc := 1
  if only.isSome then return rc
  let u ← lspecIO (Std.HashMap.ofList [("spec", [Ember.Tests.SpecTests.unitTests]),
                                       ("lang", [Ember.Tests.LangTests.unitTests])]) args
  return if rc != 0 then rc else u
