import Ember.Z80.IR

/-!
# Ember.Z80.Frame — static frames (plan M6.4)

Ember has no recursion, so every function's parameters, locals and
temporaries live at fixed addresses.  Frames are overlaid along the call
graph: a function's frame starts where the longest chain of its callers
ends, so two functions share memory exactly when neither can be active
while the other is.

`validate` checks a layout independently of how it was computed
(translation validation, plan M7.2): the frame of a function overlaps
neither the frame of any function it can reach through calls, nor a
global, and everything lies inside the RAM given.
-/

namespace Ember.Z80.IR

structure Layout where
  /-- Address of every global placed in RAM. -/
  globals : List (String × Nat) := []
  /-- Base address of every function's frame. -/
  frames : List (String × Nat) := []
  /-- First address after everything. -/
  top : Nat := 0
  deriving Inhabited, Repr

def Layout.areaAddr (l : Layout) : Area → Option Nat
  | .global g => l.globals.lookup g
  | .frame f => l.frames.lookup f

def Layout.addr (l : Layout) (s : Slot) : Nat := (l.areaAddr s.area).getD 0 + s.off

/-- Every function reachable from `f` through calls (not `f` itself:
there is no recursion). -/
partial def reach (p : Prog) (f : String) : List String := Id.run do
  let mut seen : List String := []
  let mut work := ((p.fn? f).map Fn.callees).getD []
  while !work.isEmpty do
    let g := work.head!
    work := work.tail!
    if seen.contains g then continue
    seen := g :: seen
    work := work ++ ((p.fn? g).map Fn.callees).getD []
  return seen

/-- Globals from `start` on (those `inRam` selects), then the frames.
`frameSize` is a function's frame with its temporaries. -/
def layout (p : Prog) (frameSize : String → Nat) (start : Nat)
    (inRam : Global → Bool := fun _ => true) : Layout := Id.run do
  let mut at_ := start
  let mut globals := #[]
  for g in p.globals do
    if inRam g then
      globals := globals.push (g.name, at_)
      at_ := at_ + g.size
  -- offsets of the frames from the start of the frame area: the longest
  -- chain of callers decides
  let mut base : List (String × Nat) := p.fns.map fun f => (f.name, 0)
  for _ in [0:p.fns.length] do
    let mut changed := false
    for f in p.fns do
      let b := (base.lookup f.name).getD 0
      for g in f.callees do
        let need := b + frameSize f.name
        if (base.lookup g).getD 0 < need then
          base := base.map fun (n, v) => if n == g then (n, need) else (n, v)
          changed := true
    if !changed then break
  let frames := base.map fun (n, v) => (n, at_ + v)
  let top := frames.foldl (fun m (n, v) => Nat.max m (v + frameSize n)) at_
  return { globals := globals.toList, frames, top }

def disjoint (a an b bn : Nat) : Bool := an == 0 || bn == 0 || a + an ≤ b || b + bn ≤ a

/-- The check of a layout (does not look at how it was made). -/
def validate (p : Prog) (l : Layout) (frameSize : String → Nat) (lo hi : Nat) : Except String Unit := do
  let globals := p.globals.filterMap fun g => (l.globals.lookup g.name).map fun a => (g.name, a, g.size)
  for (n, a, sz) in globals do
    unless lo ≤ a && a + sz ≤ hi do throw s!"global {n} at {a} (+{sz}) outside [{lo}, {hi})"
  for (n, a, sz) in globals do
    for (m, b, bz) in globals do
      if n != m && !disjoint a sz b bz then throw s!"globals {n} and {m} overlap"
  for f in p.fns do
    let some a := l.frames.lookup f.name | throw s!"no frame for {f.name}"
    let sz := frameSize f.name
    unless lo ≤ a && a + sz ≤ hi do throw s!"frame of {f.name} at {a} (+{sz}) outside [{lo}, {hi})"
    for (m, b, bz) in globals do
      if !disjoint a sz b bz then throw s!"frame of {f.name} overlaps global {m}"
    for g in reach p f.name do
      if g == f.name then throw s!"{f.name} is recursive"
      let some b := l.frames.lookup g | throw s!"no frame for {g}"
      if !disjoint a sz b (frameSize g) then
        throw s!"frames of {f.name} and {g} overlap, and {f.name} can call {g}"

end Ember.Z80.IR
