import Ember.Z80.Asm
import Std.Data.HashMap

/-!
# Ember.Z80.StackBound — how deep the stack of an image can get

A static bound, from the items of an image: every path through a
routine is followed with the bytes pushed since its entry (`push`,
`pop`), a `call` adds the return address and the bound of the routine
called (the call graph has no cycle), a jump is followed.  The bound of
the image is that of the start-up code (which calls the program's entry)
plus, when the image has an interrupt routine, the return address an
interrupt pushes and the bound of that routine — it does not let another
interrupt in before it returns.

This is an analysis, not a proof: it is compared with the deepest stack
seen on the model (`ember-z80 stack`) and with the room the build leaves
above the static RAM.  It gives up (`none`) on what it does not follow:
a computed jump, an unbalanced `pop`, `ld sp` anywhere but first.
-/

namespace Ember.Z80.StackBound
open Ember.Z80.Asm

structure Ctx where
  items : Array Item
  labels : Std.HashMap String Nat

def Ctx.of (items : List Item) : Ctx := Id.run do
  let arr := items.toArray
  let mut labels : Std.HashMap String Nat := {}
  for k in [0:arr.size] do
    if let .label n := arr[k]! then labels := labels.insert n k
  return { items := arr, labels }

def target (i : Instr) : Option String :=
  i.args.findSome? fun
    | .imm (.sym s _) => some s
    | _ => none

def isCond (i : Instr) : Bool :=
  i.args.any fun x => match x with
    | .nz | .z | .nc | .c | .po | .pe | .p | .m => true
    | _ => false

abbrev M := StateT (Std.HashMap String (Option Nat)) Id

/-- The deepest the stack gets below the entry of the routine at `name`
(its return address not counted), the routines it calls included. -/
def depth (c : Ctx) : Nat → String → M (Option Nat)
  | 0, _ => pure none
  | fuel + 1, name => do
    if let some r := (← get)[name]? then return r
    let some start := c.labels[name]? | return none
    let mut work : List (Nat × Nat) := [(start, 0)]
    let mut seen : Std.HashMap (Nat × Nat) Unit := {}
    let mut best : Option Nat := some 0
    let mut steps := 0
    while !work.isEmpty && best.isSome && steps < 200000 do
      steps := steps + 1
      let (k, d) := work.head!
      work := work.tail!
      if seen.contains (k, d) then continue
      seen := seen.insert (k, d) ()
      if d > 4096 then best := none; continue
      best := best.map (Nat.max d)
      match c.items[k]? with
      | none => pure ()
      | some (.ins i) =>
        let goto (l : String) (work : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
          (c.labels[l]?).map fun j => (j, d) :: work
        match i.op with
        | .push => work := (k + 1, d + 2) :: work
        | .pop => if d < 2 then best := none else work := (k + 1, d - 2) :: work
        | .call | .rst =>
          match target i with
          | none => best := none
          | some l =>
            match ← depth c fuel l with
            | none => best := none
            | some x =>
              best := best.map (Nat.max (d + 2 + x))
              work := (k + 1, d) :: work
        | .ret | .reti | .retn =>
          if d != 0 then best := none
          else if isCond i then work := (k + 1, d) :: work
        | .jp | .jr | .djnz =>
          match target i with
          | none => best := none
          | some l =>
            match goto l work with
            | none => best := none
            | some w => work := if isCond i || i.op == .djnz then (k + 1, d) :: w else w
        | .ld => if i.args.head? == some .sp then best := none else work := (k + 1, d) :: work
        | .inc | .dec | .ex =>
          if i.args.contains .sp || i.args.contains .msp then best := none else work := (k + 1, d) :: work
        | _ => work := (k + 1, d) :: work
      | some (.db _) | some (.dw _) | some (.ds _) => best := none
      | some _ => work := (k + 1, d) :: work
    let r := if steps ≥ 200000 then none else best
    modify (·.insert name r)
    return r

structure Bound where
  /-- From the start-up code on, the program included. -/
  main : Nat
  /-- An interrupt: its return address and the routine (0 without one). -/
  interrupt : Nat
  deriving Repr

def Bound.total (b : Bound) : Nat := b.main + b.interrupt

/-- The bound of an image.  The start-up code sets the stack pointer
first (`ld sp,0`: the stack grows down from the top of memory); the
interrupt routine is `rt_isr`. -/
def ofItems (items : List Item) : Option Bound :=
  let c := Ctx.of items
  -- start after the `ld sp` of `rt_start`
  let c' : Ctx :=
    match c.labels["rt_start"]? with
    | some k =>
      let j := (List.range 4).find? fun o =>
        match c.items[k + 1 + o]? with
        | some (.ins i) => i.op == .ld && i.args.head? == some .sp
        | _ => false
      match j with
      | some o => { c with labels := c.labels.insert "rt_start'" (k + 2 + o) }
      | none => c
    | none => c
  let run : M (Option Bound) := do
    let some m ← depth c' (items.length + 1) "rt_start'" | return none
    if c'.labels.contains "rt_isr" then
      let some i ← depth c' (items.length + 1) "rt_isr" | return none
      return some { main := m, interrupt := i + 2 }
    else return some { main := m, interrupt := 0 }
  (run.run {}).1

end Ember.Z80.StackBound
