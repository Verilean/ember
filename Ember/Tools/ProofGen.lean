import Ember.Z80.Codegen
import Ember.Z80.Runtime
import Ember.Net.Main

/-!
# Writing out the stack's image for the kernel (`ember-z80 proof-files`)

The proofs of the image of the SLIP build of the stack for the test
harness (`Ember/Proof/Z80StackH*.lean`) need, as terms the kernel can
evaluate, what the compiler computes: the IR (`Z80StackIR`), the items
and the layout (`Z80StackHItems`), the assembled image (`Z80StackHAsm`),
what the generator gives for each function (`Z80StackHGen`), and a
theorem for each check of the plan (`Z80StackHPlan`).  This writes the
five files; each says how it is checked (a `#guard` that the IR and the
items are those of the compiler, a theorem by the kernel for the rest).
When the stack, the lowering or the generator changes, the `#guard`s or
the theorems fail and the files are written again.
-/

namespace Ember.Tools.ProofGen
open Ember Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

/-- `s` with every `a` replaced by `b`. -/
def replaceAll (s a b : String) : String := b.intercalate (s.splitOn a)

def oneLine {α : Type} [Repr α] (x : α) : String := (repr x).pretty 1000000

/-- The `repr` of an IR term, as the files write it (`IR.`…). -/
def irText {α : Type} [Repr α] (x : α) : String := replaceAll (oneLine x) "Ember.Z80.IR." "IR."

/-- An item as the files write it (`.ins { op := .ld, args := [.hl, …] }`). -/
def itemText (it : Item) : String :=
  ["Ember.Z80.Asm.Item.", "Ember.Z80.Asm.Op.", "Ember.Z80.Asm.Arg.", "Ember.Z80.Asm.Val."].foldl
    (fun s p => replaceAll s p ".") (oneLine it)

def listText (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def arrText (xs : List String) : String := "#[" ++ ", ".intercalate xs ++ "]"

def boolText (b : Bool) : String := if b then "true" else "false"

def bytesText (b : ByteArray) : String := arrText (b.toList.map fun x => toString x.toNat)

def fnText (f : IR.Fn) : String :=
  s!"def fn_{f.name} : IR.Fn :=\n" ++
  s!"  \{ name := {repr f.name}, regParam := {irText f.regParam}, frame := {f.frame}, body := #[\n" ++
  ",\n".intercalate (f.body.toList.map fun i => "      " ++ irText i) ++
  s!"], tmps := {irText f.tmps}, inlined := {repr f.inlined}, dead := {boolText f.dead} }\n"

def globalText (g : IR.Global) : String :=
  let init := match g.init with
    | some b => s!", init := some (ByteArray.mk {bytesText b})"
    | none => ""
  s!"\{ name := {repr g.name}, size := {g.size}{init}{if g.const then ", const := true" else ""} }"

def irFile (ir : IR.Prog) : String :=
  "import Ember.Proof.Z80PlanOf
import Ember.Net.Main

/-!
# Ember.Proof.Z80StackIR — the IR of the SLIP build of the stack, written out (plan M7.3)

`Stack.ir` is what `IR.lower` returns for `Ember.Net.prog` (the stack,
SLIP build), as a term: the kernel can run the code generator and the
checks of `Z80Check` on it, which it cannot on `IR.lower` itself.  That
it is the lowering is a `#guard` — evaluated when this file is built,
not proved.

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`).
-/

namespace Ember.Proof.Z80Gen.Stack
open Ember.Z80

" ++ "\n".intercalate (ir.fns.map fnText) ++ "
def ir : IR.Prog :=
  { globals :=
      [" ++ ",\n       ".intercalate (ir.globals.map globalText) ++ "],
    fns := " ++ listText (ir.fns.map fun f => s!"fn_{f.name}") ++ ",
    entry := " ++ ir.entry.quote ++ " }

def sameFn (a b : IR.Fn) : Bool :=
  a.name == b.name && a.regParam == b.regParam && a.frame == b.frame && a.body == b.body && a.tmps == b.tmps &&
    a.inlined == b.inlined && a.dead == b.dead

def sameGlobal (a b : IR.Global) : Bool :=
  a.name == b.name && a.size == b.size && a.const == b.const && a.init.map (·.toList) == b.init.map (·.toList)

def sameProg (p q : IR.Prog) : Bool :=
  p.entry == q.entry && p.fns.length == q.fns.length && (p.fns.zip q.fns).all (fun x => sameFn x.1 x.2) &&
    p.globals.length == q.globals.length && (p.globals.zip q.globals).all (fun x => sameGlobal x.1 x.2)

/-- The lowering of the SLIP build of the stack is `ir`. -/
def irIsLowering : Bool :=
  match Ember.Net.prog.check with
  | .ok q =>
    match IR.lower q with
    | .ok r => sameProg r ir
    | .error _ => false
  | .error _ => false

#guard irIsLowering

end Ember.Proof.Z80Gen.Stack
"

/-- `xs` in parts of `n`: a list this long is not written as one term. -/
def chunks {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  if h : n = 0 then [xs] else go xs (xs.length / n + 1) []
where
  go (xs : List α) : Nat → List (List α) → List (List α)
    | 0, acc => acc.reverse
    | fuel + 1, acc => if xs.isEmpty then acc.reverse else go (xs.drop n) fuel (xs.take n :: acc)

def pairText (p : String × Nat) : String := s!"({repr p.1}, {p.2})"

def itemsFile (img : Image) : String :=
  let parts := chunks 250 img.items
  "import Ember.Proof.Z80Image
import Ember.Proof.Z80StackIR
import Ember.Z80.Runtime

/-!
# Ember.Proof.Z80StackHItems — the items of the image of the stack for the test harness, written out (plan M7.3)

`StackH.items` is what `Codegen.build` assembles for the SLIP build of
the stack with the runtime of the test harness (`Runtime.harness`:
effects are ports of the model, no interrupts), without the passes on
the assembly.  That it is what `build` gives, and the layout what
`build` computes, are `#guard`s — evaluated when this file is built,
not proved.

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm

" ++ String.join ((List.range parts.length).zip parts |>.map fun (k, its) =>
    s!"def items{k} : List Item := [\n" ++ ",\n".intercalate (its.map fun it => "  " ++ itemText it) ++ "]\n\n") ++
  "/-- The items of the image (in parts: a list this long is not written as one term). -/
def items : List Item :=
  " ++ " ++ ".intercalate ((List.range parts.length).map fun k => s!"items{k}") ++ "

def layout : IR.Layout :=
  { globals := " ++ listText (img.layout.globals.map pairText) ++ ",
    frames := " ++ listText (img.layout.frames.map pairText) ++ ",
    top := " ++ toString img.layout.top ++ " }

/-- The items and the layout are those of the image `build` gives without the passes. -/
def isBuilt : Bool :=
  match Codegen.build Stack.ir Runtime.harness (passes := false) with
  | .ok img => img.items == items && img.layout.globals == layout.globals && img.layout.frames == layout.frames &&
      img.layout.top == layout.top
  | .error _ => false

#guard isBuilt

end Ember.Proof.Z80Gen.StackH
"

/-- The image assembled, in the stretches of `items` (`chunks 250`):
for each, its addresses and bytes, and a theorem of each pass on it. -/
def asmFile (items : List Item) (a : Assembled) : String := Id.run do
  let parts := chunks 250 items
  let n := parts.length
  -- the first item of each stretch, and the labels before it
  let starts := (List.range (n + 1)).map fun j => (parts.take j).foldl (· + ·.length) 0
  let isLab (it : Item) : Bool := match it with | .label _ | .equ .. => true | _ => false
  let labsBefore := (List.range (n + 1)).map fun j => ((items.take (starts.getD j 0)).filter isLab).length
  -- the address after the last item: where the bytes end
  let endPc := a.origin + a.bytes.size
  let addrAt (k : Nat) : Nat := if k < a.addrs.size then a.addrs[k]! else endPc
  let ls (j : Nat) : String :=
    if j == 0 then "[]" else if j == n then "asm.labels.reverse" else s!"(asm.labels.take {labsBefore.getD j 0}).reverse"
  let lsChunks := chunks 250 a.labels
  let cat (pre : String) (m : Nat) : String := " ++ ".intercalate ((List.range m).map fun k => s!"{pre}{k}")
  let mut t := "import Ember.Proof.Z80StackHGen
import Ember.Proof.Z80AsmChunks

/-!
# Ember.Proof.Z80StackHAsm — the image of the stack for the harness, assembled (plan M7.3)

`asm`: what `assemble` makes of `StackH.items`, written out, and
`assemble_items` — that it is, by the kernel, a stretch of the items at a
time (`Z80AsmChunks`): for each stretch of `items` (the parts `items0`,
…) a theorem that the first pass places it at the addresses written
here, from the address and the labels the stretch before ends with
(`placeN`), and one that the second pass gives the bytes written here
(`emitN`).  The checks of the image that need the assembled bytes and
labels (`Z80StackHPlan`, `Z80StackHRun`, `Z80StackHMachine`) take `asm`.
It imports `Z80StackHGen` (it needs nothing of it) so that the two are
not checked at once.

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

"
  for j in List.range n do
    let k0 := starts.getD j 0
    let k1 := starts.getD (j + 1) 0
    let ads := (List.range (k1 - k0)).map fun k => addrAt (k0 + k)
    t := t ++ s!"def addrs{j} : List Nat := {listText (ads.map toString)}\n\n"
    let b0 := addrAt k0 - a.origin
    let b1 := addrAt k1 - a.origin
    t := t ++ s!"def bytes{j} : List UInt8 := {listText ((a.bytes.toList.drop b0).take (b1 - b0) |>.map fun x => toString x.toNat)}\n\n"
  for (k, l) in (List.range lsChunks.length).zip lsChunks do
    t := t ++ s!"def labels{k} : List (String × Nat) := [\n  " ++ ",\n  ".intercalate (l.map pairText) ++ "]\n\n"
  t := t ++ "/-- The image, assembled. -/
def asm : Assembled :=
  { origin := " ++ toString a.origin ++ ",
    bytes := ByteArray.mk (" ++ cat "bytes" n ++ ").toArray,
    labels := " ++ cat "labels" lsChunks.length ++ ",
    addrs := (" ++ cat "addrs" n ++ ").toArray }

/-- The symbols, as the second pass looks them up. -/
def asmRes : String → Option Int := fun s => (asm.labels.reverse.lookup s).map Int.ofNat

"
  for j in List.range n do
    let pc0 := addrAt (starts.getD j 0)
    let pc1 := addrAt (starts.getD (j + 1) 0)
    t := t ++ s!"theorem place{j} : place items{j} {pc0} {ls j} = .ok (addrs{j} ++ [{pc1}], {ls (j + 1)}) := by\n  decide +kernel\n"
    t := t ++ s!"theorem emit{j} : emit asmRes items{j} (addrs{j} ++ [{pc1}]) = .ok bytes{j} := by\n  decide +kernel\n"
  -- the passes over all the items, from their stretches
  let mut pp := s!"place{n - 1}"
  let mut ep := s!"emit{n - 1}"
  for j in (List.range (n - 1)).reverse do
    let pc0 := addrAt (starts.getD j 0)
    let pc1 := addrAt (starts.getD (j + 1) 0)
    pp := s!"place_step items{j} _ {pc0} {pc1} {ls j} {ls (j + 1)} addrs{j} _ place{j}\n    ({pp})"
    ep := s!"emit_step' asmRes items{j} _ addrs{j} {pc1} _ bytes{j} _ (by decide) rfl emit{j}\n    ({ep})"
  t := t ++ s!"
theorem place_all : place items {a.origin} [] = .ok (({cat "addrs" n}) ++ [{endPc}], asm.labels.reverse) := by
  have h := {pp}
  simp only [List.append_assoc] at h ⊢
  exact h

theorem emit_all : emit (fun s => (asm.labels.reverse.lookup s).map Int.ofNat) items (({cat "addrs" n}) ++ [{endPc}]) =
    .ok ({cat "bytes" n}) := by
  have h := {ep}
  simp only [List.append_assoc] at h ⊢
  exact h

/-- **The image, assembled**: by the kernel, a stretch at a time. -/
theorem assemble_items : assemble items = .ok asm :=
  assemble_of items _ {endPc} asm.labels _ place_all (by decide) emit_all

end Ember.Proof.Z80Gen.StackH
"
  return t

/-- A pass cut into stretches: where each starts (an instruction), and
the state of the generator there; the last state is after the body. -/
structure Cuts where
  pre : GS
  stops : List (Nat × GS)

/-- What the generator gives for one function: the text of its `FnPart` and theorems. -/
structure Part where
  name : String
  /-- The instructions of the function. -/
  instrs : Nat
  cuts1 : Option Cuts := none
  cuts2 : Option Cuts := none
  missed : Array Bool
  live : Option (Array Bool)
  off : Nat
  len : Nat
  litsIn : Array (Nat × Nat)
  lits : Array (Nat × Nat)
  size : Nat

def litsText (l : Array (Nat × Nat)) : String := arrText (l.toList.map fun (a, b) => s!"({a}, {b})")

def boolsText (l : Array Bool) : String := arrText (l.toList.map boolText)

/-- What the code of a function does before its body (`Z80GenChunks.genPre`). -/
def genPre (f : IR.Fn) (isEntry : Bool) : GM Unit := do
  if isEntry then modify fun s => { s with out := s.out.push (.label "f_entry") }
  modify fun s => { s with out := s.out.push (.label (fnLabel f.name)) }
  match f.regParam with
  | some (n, sl) => store n (.slot sl)
  | none => pure ()

/-- Functions longer than this are checked a stretch at a time. -/
def cutAbove : Nat := 40
/-- Instructions in a stretch. -/
def stretch : Nat := 20

/-- The states of one pass at the cuts. -/
def cutsOf (f : IR.Fn) (spilled : Array Bool) (lits : Array (Nat × Nat)) (isEntry : Bool)
    (live : Option (Array Bool)) (n : Nat := stretch) : Except String Cuts := do
  let env : GEnv := { fn := f, spilled, tmpOff := (tmpLayout f spilled).1, live }
  let s0 : GS := { missed := Array.replicate f.tmps.size false, lits, reads := Array.replicate f.frame false }
  let ((), pre) ← ((genPre f isEntry).run env).run s0
  let body := f.body.toList
  let mut st := pre
  let mut out := #[]
  let mut k := 0
  while k < body.length do
    let ((), st') ← ((genBody f false k ((body.drop k).take n)).run env).run st
    k := min (k + n) body.length
    st := st'
    out := out.push (k, st)
  return { pre, stops := out.toList }

/-- The two passes of the generator on each function, as `genFns` runs them. -/
def parts (ir : IR.Prog) (genOff : Nat) (n : Nat := stretch) : Except String (List Part) := do
  let mut out := #[]
  let mut lits : Array (Nat × Nat) := #[]
  let mut off := genOff
  for f in ir.fns do
    if f.dead then throw s!"{f.name} is dead: Gens has no step for it"
    let (_, missed, _, _, live) ← genFn f (Array.replicate f.tmps.size true) lits
    let live := keepShared (sharedBytes ir f.name) live
    let (code, _, lits2, size, _) ← genFn f missed lits (f.name == ir.entry) live false
    let big := f.body.size > cutAbove
    let cuts1 ← if big then some <$> cutsOf f (Array.replicate f.tmps.size true) lits false none n else pure none
    let cuts2 ← if big then some <$> cutsOf f missed lits (f.name == ir.entry) live n else pure none
    out := out.push { name := f.name, instrs := f.body.size, cuts1, cuts2, missed, live, off, len := code.size,
                      litsIn := lits, lits := lits2, size }
    off := off + code.size
    lits := lits2
  return out.toList

def regsText (r : Regs) : String :=
  s!"\{ a := {irText r.a}, hl := {irText r.hl}, acc := {irText r.acc} }"

def regsListText (l : List (Nat × Regs)) : String := listText (l.map fun (n, r) => s!"({n}, {regsText r})")

/-- A state of the generator; its `out` as `out`. -/
def gsText (s : GS) (out : String) : String :=
  s!"\{ out := {out},\n    regs := {regsText s.regs},\n    missed := {boolsText s.missed}, lits := {litsText s.lits}, " ++
  s!"labels := {s.labels},\n    atLabel := {regsListText s.atLabel},\n    dead := {boolText s.dead}, " ++
  s!"reads := {boolsText s.reads}, addrTaken := {boolText s.addrTaken},\n    jumps := {regsListText s.jumps},\n" ++
  s!"    labelRegs := {regsListText s.labelRegs} }"

/-- Stretches checked in one module (a pass can be spread over modules;
measured, it does not lower the peak: each stretch's check compares the
generator's whole output so far, and costs about the same wherever it
is checked — so a pass is one module). -/
def stretchesAModule : Nat := 1000

/-- The stretches of pass `j` of `g` — states, a theorem a stretch, the
pass from them — in the modules they are spread over. -/
def cutsText (items : List Item) (g : Part) (j : Nat) (c : Cuts) (isEntry : Bool) : Except String (List String) := do
  let f := s!"Stack.fn_{g.name}"
  let tag := s!"{j}_{g.name}"
  let last := (c.stops.getLast?.map (·.2)).getD c.pre
  -- the items so far: pass 2's are those of the image, pass 1's written out
  let outOf (st : GS) : Except String String :=
    if j == 2 then
      if st.out.toList == (items.drop g.off).take st.out.size then pure s!"⟨(items.drop {g.off}).take {st.out.size}⟩"
      else throw s!"{g.name}: pass 2's items are not those of the image"
    else pure s!"⟨p1code_{g.name}.take {st.out.size}⟩"
  let env := if j == 1 then s!"fnEnv {f} (Array.replicate {f}.tmps.size true) none"
    else s!"fnEnv {f} g_{g.name}.missed g_{g.name}.live"
  let mut t := ""
  if j == 1 then
    t := t ++ s!"def p1code_{g.name} : List Item := [\n" ++ ",\n".intercalate (last.out.toList.map fun it => "  " ++ itemText it) ++ "]\n\n"
  t := t ++ s!"def e{tag} : GEnv := {env}\n\n"
  t := t ++ s!"def s{tag}_pre : GS :=\n  {gsText c.pre (← outOf c.pre)}\n\n"
  t := t ++ s!"theorem pre{tag} : runG (genPre {f} {boolText isEntry}) e{tag} (fnStart {f} {litsText g.litsIn}) = .ok ((), s{tag}_pre) := by\n  decide +kernel\n"
  let mut groups : Array String := #[]
  let mut prev := s!"s{tag}_pre"
  let mut k0 := 0
  let mut n := 0
  for (k, st) in c.stops do
    if n > 0 && n % stretchesAModule == 0 then
      groups := groups.push t
      t := ""
    t := t ++ s!"def s{tag}_{k} : GS :=\n  {gsText st (← outOf st)}\n\n"
    t := t ++ s!"theorem c{tag}_{k0} : runG (genBody {f} false {k0} (({f}.body.toList.drop {k0}).take {k - k0})) e{tag} {prev} =\n    .ok ((), s{tag}_{k}) := by\n  decide +kernel\n\n"
    prev := s!"s{tag}_{k}"
    k0 := k
    n := n + 1
  -- the body from its stretches
  let mut proof := s!"body_end _ _ _ _ {g.instrs} _ (by decide +kernel)"
  let mut k1 := g.instrs
  for (k, _) in c.stops.reverse.drop 1 ++ [(0, c.pre)] do
    proof := s!"body_step _ _ _ _ {k} {k1 - k} _ _ _ (by decide +kernel) c{tag}_{k}\n    ({proof})"
    k1 := k
  t := t ++ s!"theorem body{tag} : runG (genBody {f} false 0 ({f}.body.toList.drop 0)) e{tag} s{tag}_pre = .ok ((), {prev}) :=\n  {proof}\n"
  t := t ++ s!"theorem jumps{tag} : jumpsOk {prev} = true := by decide +kernel\n"
  let spilled := if j == 1 then s!"(Array.replicate {f}.tmps.size true)" else s!"g_{g.name}.missed"
  let live := if j == 1 then "none" else s!"g_{g.name}.live"
  t := t ++ s!"theorem gen{tag} : genFn {f} {spilled} {litsText g.litsIn} {boolText isEntry} {live} false =\n" ++
    s!"    .ok ({prev}.out, {prev}.missed, {prev}.lits, (tmpLayout {f} {spilled}).2,\n" ++
    s!"      if {prev}.addrTaken then none else some {prev}.reads) :=\n" ++
    s!"  genFn_of _ _ _ _ _ _ _ _ pre{tag} body{tag} jumps{tag}\n\n"
  return (groups.push t).toList

def partText (items : List Item) (entry : String) (g : Part) : Except String (List String) := do
  let live := match g.live with
    | some l => s!"some {boolsText l}"
    | none => "none"
  let isEntry := g.name == entry
  let gdef := s!"def g_{g.name} : FnPart :=\n" ++
    s!"  \{ f := Stack.fn_{g.name}, missed := {boolsText g.missed}, live := {live},\n" ++
    s!"    code := (items.drop {g.off}).take {g.len}, lits := {litsText g.lits}, size := {g.size} }\n\n"
  match g.cuts1, g.cuts2 with
  | some c1, some c2 =>
    let m := (← cutsText items g 1 c1 false) ++ (← cutsText items g 2 c2 isEntry)
    let last := s!"theorem p1_{g.name} : pass1B Stack.ir {litsText g.litsIn} g_{g.name} = true :=\n" ++
      s!"  pass1B_of gen1_{g.name} (by rw [shared_eq]; decide +kernel)\n" ++
      s!"theorem entry_{g.name} : (Stack.fn_{g.name}.name == Stack.ir.entry) = {boolText isEntry} := by decide +kernel\n" ++
      s!"theorem p2_{g.name} : pass2B Stack.ir {litsText g.litsIn} g_{g.name} = true :=\n" ++
      s!"  pass2B_of (g := g_{g.name}) rfl\n" ++
      s!"    ((congrArg (fun b => genFn Stack.fn_{g.name} g_{g.name}.missed {litsText g.litsIn} b g_{g.name}.live false)\n" ++
      s!"      entry_{g.name}).trans gen2_{g.name}) (by decide +kernel)\n"
    let n := m.length
    return (List.range n).zip m |>.map fun (i, t) =>
      (if i == 0 then gdef else "") ++ t ++ (if i + 1 == n then last else "")
  | _, _ =>
    return [gdef ++ s!"theorem p1_{g.name} : pass1B Stack.ir {litsText g.litsIn} g_{g.name} = true := by\n  unfold pass1B\n  rw [shared_eq]\n  decide +kernel\n" ++
      s!"theorem p2_{g.name} : pass2B Stack.ir {litsText g.litsIn} g_{g.name} = true := by decide +kernel\n"]

/-- The module of one function: the next in the chain of imports, so
that the kernel checks one function at a time (no two at once). -/
def fnFile (imports : List String) (body : String) (name : String) : String :=
  String.join (imports.map fun i => s!"import {i}\n") ++ "\n" ++
  s!"/-! The generator on `{name}` (written by `ember-z80 proof-files`; see `Z80StackHGen`). -/\n\n" ++
  "namespace Ember.Proof.Z80Gen.StackH\nopen Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen\n\nset_option maxRecDepth 100000\n" ++
  "-- one theorem at a time: checked at once, the kernel's work for each adds up\nset_option Elab.async false\n\n" ++
  body ++ "\nend Ember.Proof.Z80Gen.StackH\n"

def genFile (img : Image) (dropReasons notes : List String) (gs : List Part) (genOff acc : Nat) (lastMod : String) : String :=
  "import " ++ lastMod ++ "

/-!
# Ember.Proof.Z80StackHGen — the image of the stack for the harness: the generator, function by function (plan M7.3)

For each of the " ++ toString gs.length ++ " functions of the SLIP build the kernel runs the two
passes of the generator (`pass1B`, `pass2B`) and compares what they
give with `FnPart`: the temporaries read from their slot, where reads
of the frame start, the literals so far, the bytes of temporaries — and
the items, which are those of `StackH.items` at the function's place.
A module a function (`Z80StackHGen/F_<name>.lean`), each importing the
one before, so that the kernel checks one function at a time; a
function of more than " ++ toString cutAbove ++ " instructions a stretch of " ++ toString stretch ++ " at a time
(`Z80GenChunks`: the states of the generator between the stretches
written out), which keeps what the kernel holds at once small.
`gens_ok` chains them (`Gens`): `progEnvs` and `genProg` of `Stack.ir`
are known without the kernel running the generator over the program at
once.

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`); the kernel checks each.
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

/-- RAM from `0x8000`: the accumulator, the harness's count of idle
calls (the loop's own, no routine writes it), the globals, the frames,
the temporaries; the stack above, up to the top.  A routine of the
runtime uses two bytes of stack at most (`rt_cmp32`). -/
def img : ImgIn :=
  { ir := Stack.ir, layout,
    dropReasons := [" ++ ",\n      ".intercalate (dropReasons.map String.quote) ++ "],
    notes := " ++ listText (notes.map String.quote) ++ ",
    ramStart := 0x8000, stackLo := " ++ toString img.layout.top ++ ", stackHi := 65536, acc := " ++ toString acc ++
    ", rtK := 2, rt := [], items, genOff := " ++ toString genOff ++ " }

set_option maxRecDepth 100000

def gens : List FnPart :=
  " ++ listText (gs.map fun g => s!"g_{g.name}") ++ "

theorem fns_eq : Stack.ir.fns = gens.map (·.f) := rfl

/-- The generator, along the program. -/
theorem gens_ok : Gens Stack.ir #[] gens :=
  " ++ gs.foldr (fun g acc => s!"(.cons p1_{g.name} p2_{g.name} {acc})") "(.nil _)" ++ "

end Ember.Proof.Z80Gen.StackH
"

/-- Labels of the plan checked in the items at a time. -/
def labelStretch : Nat := 40

/-- `on_labels`, a stretch of the plan's labels at a time. -/
def labelsText (n : Nat) : String := Id.run do
  let p := "fun l => img.items.any (ImgIn.isLab l)"
  let mut t := ""
  let mut a := 0
  while a < n do
    t := t ++ s!"theorem on_labels_{a} : ((plan.labels.drop {a}).take {labelStretch}).all ({p}) = true := by\n  decide +kernel\n"
    a := a + labelStretch
  t := t ++ s!"theorem on_labels_len : plan.labels.length ≤ {a} := by decide +kernel\n"
  let mut proof := s!"all_drop_end _ _ {a} on_labels_len"
  let mut k := a
  while k > 0 do
    k := k - labelStretch
    proof := s!"all_drop_step _ _ {k} {labelStretch} on_labels_{k}\n    ({proof})"
  t := t ++ s!"theorem on_labels : (plan.labels.all {p}) = true := by\n  have h := {proof}\n  simpa using h\n"
  return t

def planFile (gs : List Part) (nLabels : Nat) : String :=
  "import Ember.Proof.Z80StackHGen
import Ember.Proof.Z80StackHAsm

/-!
# Ember.Proof.Z80StackHPlan — the image of the stack for the harness: the plan, checked (plan M7.3)

`okB` of the plan of the image, `fnStaticB` of each function in the
environment it is generated in, and what is computed of the assembled
image `asm` (`PartsOn`: the plan's labels, the literal pool, the symbols
of the areas and of the accumulator, the generated items in place, the
size) — by the kernel, a theorem each (one declaration at a time, the
kernel keeps less).  `img_ok`: so the setting of the proofs holds of the
image, and given the routines of the runtime every function does what
the IR's does (`ImgIn.ok_partsOn`).

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm Ember.Z80.Codegen
open Ember.Proof.Z80Enc Ember.Proof.IRSim

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def plan : Plan := mkPlan (img.planIn (envsOf gens))

theorem plan_okB : okB plan = true := by decide +kernel

" ++ String.join (gs.map fun g =>
    s!"theorem st_{g.name} : fnStaticB plan (genEnv g_{g.name}.f g_{g.name}.missed g_{g.name}.live) = true := by decide +kernel\n") ++ "
theorem plan_static : ∀ g, g ∈ gens → fnStaticB plan (genEnv g.f g.missed g.live) = true :=
  " ++ gs.foldr (fun g acc => s!"(List.forall_mem_cons.mpr ⟨st_{g.name}, {acc}⟩)") "(fun _ h => absurd h List.not_mem_nil)" ++ "

/-- The plan of the image, without the kernel running the generator over the program. -/
theorem img_plan : img.plan = plan := img.plan_parts gens fns_eq gens_ok

" ++ labelsText nLabels ++ "
theorem on_lits : plan.lits.all (ImgIn.litB asm img.ramStart) = true := by decide +kernel
theorem on_globals :
    (img.layout.globals.all fun e => asm.labels.reverse.lookup (areaSym (.global e.1)) == some e.2) = true := by
  decide +kernel
theorem on_frames :
    (img.layout.frames.all fun e => asm.labels.reverse.lookup (areaSym (.frame e.1)) == some e.2) = true := by
  decide +kernel
theorem on_code :
    decide ((img.items.drop img.genOff).take (gens.flatMap (·.code)).length = gens.flatMap (·.code)) = true := by
  decide +kernel
theorem on_acc : (img.items.all ImgIn.noAcc || asm.labels.reverse.lookup \"rt_acc\" == some img.acc) = true := by
  decide +kernel
theorem on_size : decide (asm.bytes.size < 65536) = true := by decide +kernel

/-- **The image of the stack for the harness, checked**: the setting of
the proofs holds of it, and given the routines of the runtime it calls
every function does what the IR's does. -/
theorem img_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble img.items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ (W : Type) (bus : W → UInt16 → UInt8) (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop),
        (∀ w, dev w .none = w) →
        (img.plan.toZ (img.around a addrs W bus dev wrel)).OK ∧
        (RtOK (img.plan.toZ (img.around a addrs W bus dev wrel)) →
          ∀ k g st1, Callee (img.plan.toZ (img.around a addrs W bus dev wrel)) g st1 (IR.Sem.callF k img.ctx g st1)) :=
  img.ok_partsOn gens asm fns_eq gens_ok plan_okB plan_static
    ⟨assemble_items, on_labels, on_lits, on_globals, on_frames, on_code, on_acc, on_size⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.img_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms img_ok

end Ember.Proof.Z80Gen.StackH
"

/-- The frames of the layout `sharedBytes` computes, written out, and that they are. -/
def sharedFile (ir : IR.Prog) : String :=
  let frames := (IR.layout ir (fun f => ((ir.fn? f).map (·.frame)).getD 0) 0).frames
  "import Ember.Proof.Z80GenChunks
import Ember.Proof.Z80StackHItems

/-!
The frames of the layout `sharedBytes Stack.ir` computes (from 0), and
`shared_eq`: the kernel computes that layout here, once; the checks of
the functions take `sharedOf` of these frames (written by `ember-z80
proof-files`; see `Z80StackHGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Codegen

def sharedFrames : List (String × Nat) := " ++ listText (frames.map pairText) ++ "

theorem shared_eq : sharedBytes Stack.ir = sharedOf Stack.ir sharedFrames :=
  sharedBytes_eq _ _ (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
"

/-- Write the five files into `dir`. -/
def write (dir : System.FilePath) (n : Nat := stretch) : IO UInt32 := do
  let fail (e : String) : IO UInt32 := do IO.eprintln s!"proof-files: {e}"; return 1
  let q ← match Net.prog.check with
    | .ok q => pure q
    | .error e => return ← fail e.toString
  let ir ← match IR.lower q with
    | .ok ir => pure ir
    | .error e => return ← fail e
  let img ← match Codegen.build ir Runtime.harness (passes := false) with
    | .ok img => pure img
    | .error e => return ← fail e
  let a ← match assemble img.items with
    | .ok a => pure a
    | .error e => return ← fail e
  let code ← match genProg ir false (sharedBytes ir) with
    | .ok c => pure c.items
    | .error e => return ← fail e
  -- where the generated items start
  let some genOff := (List.range img.items.length).find? fun j => (img.items.drop j).take code.length == code
    | return ← fail "the generated items are not in the image"
  let some acc := img.items.findSome? fun it => match it with | .equ "rt_acc" v => some v | _ => none
    | return ← fail "no rt_acc"
  let gs ← match parts ir genOff n with
    | .ok gs => pure gs
    | .error e => return ← fail e
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "Z80StackIR.lean") (irFile ir)
  IO.FS.writeFile (dir / "Z80StackHItems.lean") (itemsFile img)
  IO.FS.writeFile (dir / "Z80StackHAsm.lean") (asmFile img.items a)
  IO.FS.createDirAll (dir / "Z80StackHGen")
  IO.FS.writeFile (dir / "Z80StackHGen" / "Shared.lean") (sharedFile ir)
  let mut prev := ["Ember.Proof.Z80StackHGen.Shared"]
  for g in gs do
    let mods ← match partText img.items ir.entry g with
      | .ok t => pure t
      | .error e => return ← fail e
    -- the modules of a function: `F_<name>_<i>`, the last `F_<name>`
    for (i, body) in (List.range mods.length).zip mods do
      let m := if i + 1 == mods.length then s!"F_{g.name}" else s!"F_{g.name}_{i}"
      IO.FS.writeFile (dir / "Z80StackHGen" / s!"{m}.lean") (fnFile prev body g.name)
      prev := [s!"Ember.Proof.Z80StackHGen.{m}"]
  IO.FS.writeFile (dir / "Z80StackHGen.lean") (genFile img q.dropReasons q.notes gs genOff acc (prev.headD ""))
  let nLabels := 1 + ir.fns.foldl (fun n f => n + 1 + (f.body.toList.filter fun i => match i with | .label _ => true | _ => false).length) 0
  IO.FS.writeFile (dir / "Z80StackHPlan.lean") (planFile gs nLabels)
  IO.println s!"proof-files: {ir.fns.length} functions, {img.items.length} items, {a.bytes.size} bytes -> {dir}"
  return 0

end Ember.Tools.ProofGen
