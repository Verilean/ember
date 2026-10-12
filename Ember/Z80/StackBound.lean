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
above the static RAM.  As it is a gate, it answers only for images of
the shape it models and gives up (`none`) on anything else:

* a jump or a call is to a label, exactly (no offset, no computed
  target, no `rst`); a path does not run into data or off the end;
* the stack pointer is set once, by `ld sp,0` right after `rt_start`
  (only `di` may come before it), and is otherwise moved by `push`,
  `pop`, `call` and `ret` alone, balanced within a routine;
* an image that enables interrupts has `rt_isr` (and a `jp rt_isr`, the
  vector of interrupt mode 1 — where it is, is not checked), and in what `rt_isr`
  can reach an `ei` is the instruction before the final `ret`/`reti` —
  so the routine cannot be entered again before it has returned;
* non-maskable interrupts are not considered.
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

/-- The label a jump or a call goes to: with an offset, a number or a
register in its place there is none. -/
def target (i : Instr) : Option String :=
  match i.args.filter (fun x => match x with | .imm _ | .mem _ | .mhl | .mix0 | .miy0 => true | _ => false) with
  | [.imm (.sym s off)] => if off == 0 then some s else none
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
      | none => best := none
      | some (.ins i) =>
        let goto (l : String) (work : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
          (c.labels[l]?).map fun j => (j, d) :: work
        match i.op with
        | .push => work := (k + 1, d + 2) :: work
        | .pop => if d < 2 then best := none else work := (k + 1, d - 2) :: work
        | .rst => best := none
        | .call =>
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

/-- The items a routine can reach, through jumps and calls (`none`: a target that is not a label). -/
def reach (c : Ctx) (name : String) : Option (List Nat) := Id.run do
  let some start := c.labels[name]? | return none
  let mut work : List Nat := [start]
  let mut seen : Std.HashMap Nat Unit := {}
  let mut ok := true
  let mut steps := 0
  while !work.isEmpty && ok && steps < 200000 do
    steps := steps + 1
    let k := work.head!
    work := work.tail!
    if seen.contains k then continue
    seen := seen.insert k ()
    match c.items[k]? with
    | none => ok := false
    | some (.ins i) =>
      match i.op with
      | .ret | .reti | .retn => if isCond i then work := (k + 1) :: work
      | .jp | .jr | .djnz | .call =>
        match (target i).bind (c.labels[·]?) with
        | none => ok := false
        | some j =>
          work := j :: work
          if isCond i || i.op == .djnz || i.op == .call then work := (k + 1) :: work
      | .rst => ok := false
      | _ => work := (k + 1) :: work
    | some (.db _) | some (.dw _) | some (.ds _) => ok := false
    | some _ => work := (k + 1) :: work
  return if ok && steps < 200000 then some (seen.toList.map (·.1)) else none

/-- An interrupt routine that cannot be entered again before it
returns: in what it reaches, `ei` is the instruction before an
unconditional `ret`/`reti` (the interrupt is let in after the instruction
that follows `ei`). -/
def isrOnce (c : Ctx) : Bool :=
  match reach c "rt_isr" with
  | none => false
  | some ks =>
    ks.all fun k =>
      match c.items[k]? with
      | some (.ins i) =>
        i.op != .ei ||
          (match c.items[k + 1]? with
           | some (.ins j) => (j.op == .ret || j.op == .reti) && j.args.isEmpty
           | _ => false)
      | _ => true

/-- Where the program starts with its stack set: the item after
`rt_start: [di;] ld sp,0`. -/
def startAfterSp (c : Ctx) : Option Nat := do
  let k ← c.labels["rt_start"]?
  let ldSp0 (it : Option Item) : Bool := it == some (.ins ⟨.ld, [.sp, .imm (.num 0)]⟩)
  if ldSp0 c.items[k + 1]? then some (k + 2)
  else if c.items[k + 1]? == some (.ins ⟨.di, []⟩) && ldSp0 c.items[k + 2]? then some (k + 3)
  else none

/-- The bound of an image: the stack grows down from the top of memory
(`ld sp,0`), so it is to be compared with the room below 65536. -/
def ofItems (items : List Item) : Option Bound :=
  let c := Ctx.of items
  match startAfterSp c with
  | none => none
  | some k =>
    let c' : Ctx := { c with labels := c.labels.insert "rt_start'" k }
    let enables := items.any fun it => match it with | .ins i => i.op == .ei | _ => false
    let run : M (Option Bound) := do
      let some m ← depth c' (items.length + 1) "rt_start'" | return none
      if c'.labels.contains "rt_isr" then
        -- the vector of interrupt mode 1 is a jump to the routine
        if !items.contains (.ins ⟨.jp, [.imm (.sym "rt_isr" 0)]⟩) then return none
        if !isrOnce c' then return none
        let some i ← depth c' (items.length + 1) "rt_isr" | return none
        return some { main := m, interrupt := i + 2 }
      else if enables then return none
      else return some { main := m, interrupt := 0 }
    (run.run {}).1

end Ember.Z80.StackBound
