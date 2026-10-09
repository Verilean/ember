import Ember.Lang.Surface
import Ember.Trace.Event

/-!
# Test programs for `Tests.Ember.LangTests`

`Bad`: one program per type-checker rule, each violating it once.
(The program using every construct is `Ember.Lang.Examples.Constructs`.)
-/

namespace Ember.Tests.LangPrograms
open Ember.Lang


/-! ## One violation per checker rule -/

namespace Bad

ember global g : u8
ember global arr : [u8; 4]
ember const C : u8 := 1

ember def width_mismatch := do
  let a : u8 := 1
  let b : u16 := 2
  let c : u16 := a + b

ember def literal_too_big := do
  let a : u8 := 256

ember def index_oob := do
  arr[4] := 1

ember def no_width := do
  out.byte((1 + 2 : u8) + (3 < 4 : u8))
  let x : bool := 1 < 2

ember def dup := do
  let a : u8 := 1
  let a : u8 := 2

ember def shadow := do
  let g : u8 := 1

ember def assign_const := do
  C := 2

ember def assign_counter := do
  for i in [0, (4 : u8)) do
    i := 3

ember def assign_array := do
  let mut b : [u8; 4]
  b := arr

ember def two_refs (a : ref [u8; 4]) (b : ref [u8; 4]) := do
  a[0] := b[0]

ember def overlap := do
  two_refs(arr, arr)

ember def uses_g (a : ref [u8; 4]) := do
  g := a[0]
  arr[1] := 2

ember def alias_global := do
  uses_g(arr)

ember def rec_a := do
  rec_b()

ember def rec_b := do
  rec_a()

ember def missing_return (x : u8) : u8 := do
  if x > 1 then
    return 1

ember def stray_break := do
  break

ember def bool_arith := do
  let a : bool := true
  let b : bool := a + a

ember def wrong_arity := do
  two_refs(arr)

ember def ref_not_place := do
  two_refs(arr, (g : u8))

ember def unknown_var := do
  out.byte(nope)

ember def nop := do
  return

ember def ok_fn (x : u8) : u8 := do
  if x > 1 then
    return 1
  else
    return 2

/-- The rule, the program that breaks it, and a substring of the error. -/
def cases : List (String × Prog × String) :=
  let base (f : Fn) (fns : List Fn := []) : Prog :=
    { globals := [g, arr, C], fns := fns ++ [f, nop], entry := "nop" }
  [("operand widths", base width_mismatch, "operands of + have different types (u8 and u16)"),
   ("literal range", base literal_too_big, "literal 256 does not fit u8"),
   ("literal index bounds", base index_oob, "index 4 out of bounds [0, 4)"),
   ("literal width inferred", base no_width, "cannot infer the width"),
   ("unique names", base dup, "declared twice"),
   ("no shadowing", base shadow, "shadows a global"),
   ("constants read-only", base assign_const, "'C' is read-only"),
   ("for counter read-only", base assign_counter, "'i' is read-only"),
   ("only scalars assigned", base assign_array, "must be a scalar"),
   ("references disjoint", base overlap [two_refs], "overlap"),
   ("no global by reference to its user", base alias_global [uses_g], "also uses it by name"),
   ("no recursion", base rec_a [rec_b], "recursion"),
   ("every path returns", base missing_return, "not every path returns"),
   ("break inside loops", base stray_break, "break outside a loop"),
   ("bool is not arithmetic", base bool_arith, "must be an integer"),
   ("arity", base wrong_arity [two_refs], "takes 2 argument(s)"),
   ("references are places", base ref_not_place [two_refs], "by reference"),
   ("names resolve", base unknown_var, "unknown variable 'nope'")]

end Bad

/-! ## Regressions found by `ember-fuzz`

Each was a divergence between the interpreter and the emitted C, shrunk
by the fuzzer; both now run in the differential suite. -/

namespace Regress

ember global ga : [u8; 8] := [1, 2, 3]
ember global gw : [u16; 5]
ember global g16 : u16 := 300

/-- Seed 1000003: a trap must not erase the events before it (the
interpreter used to lose its state on an error). -/
ember def trap_after_event := do
  trace.drop(0)
  out.byte((gw[(ga[(gw[g16] % (8 : u16))] % (5 : u8))] : u8))

ember def h0 (p0 : u8) : u16 := do
  trace.drop(0)
  return (p0 : u16)

/-- Seed 42007288: the destination of a call is evaluated after the call,
so the callee's events come before the destination's bounds trap (the C
used to check the index first). -/
ember def call_then_trap := do
  let mut k : u16
  k ← input.next()
  gw[k] ← h0((g16 : u8))

def p1 : Prog :=
  { globals := [ga, gw, g16], fns := [trap_after_event], entry := "trap_after_event", dropReasons := ["d"] }

def p2 : Prog :=
  { globals := [ga, gw, g16], fns := [h0, call_then_trap], entry := "call_then_trap", dropReasons := ["d"] }

def progs : List (String × Prog × Array Ember.Trace.Input) :=
  [("regress_trap_after_event", p1, #[.rx (ByteArray.mk #[0xf1])]),
   ("regress_call_then_trap", p2, #[.rx (ByteArray.mk #[0x5c])])]

end Regress

end Ember.Tests.LangPrograms
