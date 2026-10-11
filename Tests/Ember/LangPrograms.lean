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

ember global big : [u8; 300]
ember global gi : u8

ember def bump : u8 := do
  gi := gi + 1
  return 7

/-- Found by `Ember.C.Sem` (M5.7): the destination's index needs no
check (a `u8` into 300 elements), and the callee changes it.  C does not
order the evaluation of `big[gi]` against the call in `big[gi] =
bump();`, so the call's result goes through a temporary. -/
ember def call_changes_index := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  big[gi] ← bump()
  out.byte(big[0])
  out.byte(big[1])
  out.end()

def p3 : Prog :=
  { globals := [big, gi], fns := [bump, call_changes_index], entry := "call_changes_index" }

ember global g3 : [u8; 3]

/-- Found proving the lowering to the Z80 back end's IR (M7.1): `&&` is
strict, so an operand that traps must trap even when the other one
decides.  The lowering jumped past an operand it took for one that
cannot trap: an index that is constant but not a literal (here `1 + 2`,
out of range). -/
ember def strict_and := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if (k == 0) && (g3[(1 : u8) + 2] == 0) then
    out.byte(1)
  out.byte(2)
  out.end()

def p4 : Prog := { globals := [g3], fns := [strict_and], entry := "strict_and" }

def progs : List (String × Prog × Array Ember.Trace.Input) :=
  [("regress_trap_after_event", p1, #[.rx (ByteArray.mk #[0xf1])]),
   ("regress_call_then_trap", p2, #[.rx (ByteArray.mk #[0x5c])]),
   ("regress_call_changes_index", p3, #[.rx (ByteArray.mk #[0x64])]),
   ("regress_strict_and", p4, #[.rx (ByteArray.mk #[0x64])])]

end Regress

/-! ## Index checks behind a comparison (plan M6.5)

The own Z80 back end drops an index check that a comparison on the way
already made (`Ember.Z80.IR.dropChecks`).  In each program the index is
out of range for some input in a way the comparison does not exclude,
so the check has to be there still: the interpreter traps, and so must
the generated code. -/

namespace Guard

ember global ga : [u8; 8] := [1, 2, 3, 4, 5, 6, 7, 8]
ember global gi : u8
ember global gj : u16

ember def bump := do
  gi := gi + 9

/-- The index changes between the comparison and the use. -/
ember def changed := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gi := (k : u8)
  if gi < 8 then
    out.byte(ga[gi])
    gi := gi + 5
    out.byte(ga[gi])
  out.end()

/-- A call changes the index. -/
ember def through_call := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gi := (k : u8)
  if gi < 8 then
    bump()
    out.byte(ga[gi])
  out.end()

/-- The comparison is against a larger bound than the array has. -/
ember def loose := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gi := (k : u8)
  if gi < 9 then
    out.byte(ga[gi])
  out.end()

/-- The comparison holds on one path only. -/
ember def one_path := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gi := (k : u8)
  if gi < 8 then
    out.byte(1)
  else
    out.byte(2)
  out.byte(ga[gi])
  out.end()

/-- A wider variable is compared, its low byte indexes. -/
ember def widths := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gj := k + 250
  gi := (gj : u8)
  if gj < 8 then
    out.byte(ga[gi])
  if gi < 8 then
    out.byte(ga[gj])
  out.end()

/-- In range by the comparison: no trap, and the loop's own bound. -/
ember def fine := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  gi := (k : u8)
  if gi < 8 then
    out.byte(ga[gi])
  for i in [0, (8 : u8)) do
    out.byte(ga[i])
  for j in [0, (9 : u8)) do
    if gi == 200 then
      out.byte(ga[j])
  out.end()

def progs : List (String × Prog) :=
  [("guard_changed", { globals := [ga, gi, gj], fns := [changed], entry := "changed" }),
   ("guard_through_call", { globals := [ga, gi, gj], fns := [bump, through_call], entry := "through_call" }),
   ("guard_loose", { globals := [ga, gi, gj], fns := [loose], entry := "loose" }),
   ("guard_one_path", { globals := [ga, gi, gj], fns := [one_path], entry := "one_path" }),
   ("guard_widths", { globals := [ga, gi, gj], fns := [widths], entry := "widths" }),
   ("guard_fine", { globals := [ga, gi, gj], fns := [fine], entry := "fine" })]

/-- Indices inside, at and beyond the bound. -/
def inputs : List (Array Ember.Trace.Input) :=
  [0, 2, 3, 6, 7, 8, 9, 13, 200, 255].map fun b => #[.rx (ByteArray.mk #[b])]

end Guard

end Ember.Tests.LangPrograms
