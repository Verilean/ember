import Ember.Proof.Z80PassAbs

/-!
# Ember.Proof.Z80PassAbsGen — what is known of `A`'s registers, and the levels, computed (plan M7.3)

Outside the proofs: the list the walk of `Z80PassAbs` checks (one `AS`
per item of `A`: what the row before leaves; at the entry of a function
only called, what its calls have; at `ldir`'s row, what every round
keeps) and the levels of the functions.  Nothing here is trusted: the
kernel checks what it gives.
-/

namespace Ember.Proof.PassSim.AbsGen
open Ember.Z80 Ember.Z80.Asm Ember.Proof.PassSim

def labelOf (args : List Arg) : Option String :=
  match args.getLast? with
  | some (.imm (.sym l 0)) => some l
  | _ => none

/-- What every round of `ldir` keeps of what is known before the first: the sums. -/
def widen (b : AS) : AS :=
  match b with
  | none => none
  | some a =>
    (AF.norm { h0 := Itv.top, h1 := Itv.top, de := Itv.top, bc := (1, a.bc.2), hb := a.hbD, db := a.dbD })

/-- One pass, with what is known at the entries (`ent`). -/
def pass (la : List (String × Nat)) (xs : Array Item) (ra : Array Row) (ent : Std.HashMap String AS) :
    Array AS := Id.run do
  let mut out : Array AS := #[]
  for k in [0:xs.size] do
    let it := xs[k]!
    let b : AS :=
      if k = 0 then none
      else
        let pi := xs[k - 1]!
        match it, pi with
        | .label l, .ins ⟨.ret, []⟩ => ent.getD l none
        | .label _, _ => none
        | _, _ =>
          let blocked := (2 ≤ k && ra[k - 2]!.tag == .blkR) ||
            (4 ≤ k && (ra[k - 4]!.tag == .pack || ra[k - 4]!.tag == .copyR))
          if blocked then none else (absAfter la pi ra[k - 1]! out[k - 1]!).getD none
    out := out.push (if ra[k]!.tag == .ldir then widen b else b)
  return out

/-- What is known at each item of `A`, and the meeting points where it is not enough (index, item). -/
def mk (la : List (String × Nat)) (tA : List (String × Nat × List Item)) (lo hi : Nat) (xs : List Item)
    (rows : List Row) : Array AS × Array (Nat × Item) := Id.run do
  let xa := xs.toArray
  let ra := rows.toArray
  -- the labels some row other than a call goes to
  let mut other : Std.HashSet String := {}
  for k in [0:xa.size] do
    match ra[k]!.tag, xa[k]! with
    | .call, _ => pure ()
    | .jump, .ins ⟨_, args⟩ | .condRet, .ins ⟨_, args⟩ | .djnz, .ins ⟨_, args⟩ | .tail, .ins ⟨_, args⟩ =>
      if let some l := labelOf args then other := other.insert l
    | _, _ => pure ()
  let mut ent : Std.HashMap String AS := {}
  let mut out := pass la xa ra ent
  for _ in [0:4] do
    let mut e : Std.HashMap String (Option AS) := {}
    for k in [0:xa.size] do
      match ra[k]!.tag, xa[k]! with
      | .call, .ins ⟨.call, [.imm (.sym l 0)]⟩ =>
        let a := out[k]!
        e := e.insert l (match e.get? l with
          | none => some a
          | some (some b) => if a == b then some a else none
          | some none => none)
      | _, _ => pure ()
    ent := {}
    for (l, v) in e.toList do
      if !other.contains l then
        if let some a := v then ent := ent.insert l a
    out := pass la xa ra ent
  let mut bad : Array (Nat × Item) := #[]
  let lt := acTbl xs rows out.toList
  for k in [0:xa.size] do
    let prev : Option (Item × Row × AS) := if k = 0 then none else some (xa[k - 1]!, ra[k - 1]!, out[k - 1]!)
    if !absOK la tA lo hi prev xa[k]! ra[k]! out[k]! (out.toList.drop (k + 1)) then bad := bad.push (k, xa[k]!)
    else if !tgtOK lt xa[k]! ra[k]! out[k]! then bad := bad.push (k, xa[k]!)
  return (out, bad)

/-- The functions each calls, by the rows of calls (`call`, `tail`): the activations at the row, the
entry of the function called. -/
def edges (t : List (String × LInfo)) (xs : List Item) (rows : List Row) : List (Nat × Nat) := Id.run do
  let mut es : List (Nat × Nat) := []
  for (it, r) in xs.zip rows do
    if r.tag == .call || r.tag == .tail then
      match it with
      | .ins ⟨.call, [.imm (.sym l 0)]⟩ =>
        match lookupL t l with
        | some li => for e in r.act do es := (e, li.ia) :: es
        | none => pure ()
      | _ => pure ()
  return es

/-- **The levels**: a function above those it calls; `none` if the calls go round. -/
def levels (es : List (Nat × Nat)) : Option (List (Nat × Nat)) := Id.run do
  let nodes := (es.map (·.1) ++ es.map (·.2)).eraseDups
  let mut lv : Std.HashMap Nat Nat := {}
  for _ in [0:nodes.length + 2] do
    let mut ch := false
    for (a, b) in es do
      let want := lv.getD b 0 + 1
      if lv.getD a 0 < want then
        lv := lv.insert a want
        ch := true
    if !ch then return some (nodes.map fun n => (n, lv.getD n 0))
  return none

/-! ## The files -/

def itvText (i : Itv) : String := s!"({i.1}, {i.2})"

def optText : Option Nat → String
  | none => "none"
  | some v => s!"(some {v})"

def asText : AS → String
  | none => "none"
  | some a => s!"some ⟨{itvText a.h0}, {itvText a.h1}, {itvText a.de}, {itvText a.bc}, {optText a.hb}, {optText a.db}⟩"

/-- Where each part of the check starts: every `n` items. -/
def starts (len n : Nat) : List Nat := (List.range ((len + n - 1) / n)).map (· * n)

/-- The file of the list and the levels. -/
def absFile (acl : List AS) (lv : List (Nat × Nat)) (n : Nat) (len : Nat) : String := Id.run do
  let chunks := (List.range ((acl.length + 299) / 300)).map fun i => (acl.drop (i * 300)).take 300
  let mut out := "import Ember.Proof.Z80PassAbsWalk\nimport Ember.Proof.Z80PassCertD\n\n" ++
    "/-!\n# Ember.Proof.Z80PassAbsD — what is known of `StackH`'s registers, and the levels (plan M7.3)\n\n" ++
    "One `AS` per item of `StackH` (`Z80PassAbs`), the levels of the functions by their entries, and where\n" ++
    "the parts of the walk start.  Written by `ember-passcert` (`Ember.Proof.Z80PassAbsGen`); the kernel\n" ++
    "checks it (`Z80PassAbsD0` …).\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  let mut i := 0
  for ch in chunks do
    out := out ++ s!"def acl{i} : List AS := [\n  " ++ ", ".intercalate (ch.map asText) ++ "]\n\n"
    i := i + 1
  out := out ++ "def acl : List AS := " ++ " ++ ".intercalate ((List.range i).map fun j => s!"acl{j}") ++ "\n\n"
  out := out ++ s!"/-- The levels of the functions, by their entries. -/\ndef lv : List (Nat × Nat) := {lv}\n\n"
  out := out ++ s!"/-- Items a part of the walk goes over. -/\ndef apart : Nat := {n}\n\n"
  out := out ++ s!"/-- Where the parts start. -/\ndef astarts : List Nat := {starts len n}\n\n"
  out := out ++ "/-- The context of the walk. -/\ndef actx : ACtx := mkACtx StackH.items StackH.asm rows acl\n\n"
  out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

/-- A file of parts of the walk (by the kernel), importing the one before. -/
def absChunkFile (idx : Nat) (prev : String) (ps : List Nat) : String := Id.run do
  let mut out := s!"import {prev}\n\n" ++
    s!"/-!\n# Ember.Proof.Z80PassAbsD{idx} — parts of the walk over what is known (plan M7.3)\n\n" ++
    "The walk of `Z80PassAbsWalk` over parts of `StackH`'s items, by the kernel (`decide +kernel`), each\n" ++
    "from its start (`astarts`).  Written by `ember-passcert`.\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  for k in ps do
    out := out ++ s!"set_option maxRecDepth 100000 in\ntheorem awalk{k} : absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart\n    (prevA StackH.items rows acl {k}) (StackH.items.drop {k}) (rows.drop {k}) (acl.drop {k}) = true := by\n  decide +kernel\n\n"
  out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

/-- The file that puts the parts together (`AbsGlob`). -/
def absOkFile (prev : String) (ps : List Nat) : String := Id.run do
  let mut out := s!"import {prev}\nimport Ember.Proof.Z80PassCertDOK\n\n" ++
    "/-!\n# Ember.Proof.Z80PassAbsDOK — what is known of `StackH`'s registers, checked (plan M7.3)\n\n" ++
    "`absD_ok`: the list and levels of `Z80PassAbsD` checked (`AbsGlob`), from the parts of the walk by the\n" ++
    "kernel (`Z80PassAbsD0` …), which cover every item (`absRows_of_walks`).  Written by `ember-passcert`.\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  out := out ++ "set_option maxRecDepth 100000 in\ntheorem acl_len : acl.length = StackH.items.length := by decide +kernel\n\n"
  out := out ++ "theorem astarts_walk : ∀ p, p ∈ astarts →\n    absWalk actx.la actx.tA lo hi actx.lt actx.t lv apart (prevA StackH.items rows acl p) (StackH.items.drop p)\n      (rows.drop p) (acl.drop p) = true := by\n  intro p hp\n  simp only [astarts, List.mem_cons, List.not_mem_nil, or_false] at hp\n"
  out := out ++ "  rcases hp with " ++ " | ".intercalate (ps.map fun _ => "rfl") ++ "\n"
  for k in ps do
    out := out ++ s!"  · exact awalk{k}\n"
  out := out ++ "\ntheorem astarts_at : ∀ i (h : i < astarts.length), astarts[i]'h = apart * i := by\n  decide\n\n"
  out := out ++ "set_option maxRecDepth 100000 in\ntheorem astarts_reach : StackH.items.length ≤ apart * astarts.length := by decide +kernel\n\n"
  out := out ++ "theorem acl_first : acAt acl 0 = none := rfl\n\n"
  out := out ++ "theorem lv_top : hi + 4 + 2 * lvOf lv topE ≤ 65536 := by decide\n\n"
  out := out ++ "/-- **What is known of `StackH`'s registers, and the levels, checked.** -/\ntheorem absD_ok : AbsGlob StackH.items StackH.asm lo hi rows acl lv :=\n  ⟨absRows_of_walks actx lo hi lv _ rows acl rows_len acl_len apart astarts astarts_walk astarts_at (by decide)\n    astarts_reach, acl_len, rows_len, acl_first, lv_top⟩\n\n"
  out := out ++ "/-- info: 'Ember.Proof.PassSim.CertD.absD_ok' depends on axioms: [propext, Quot.sound] -/\n#guard_msgs in #print axioms absD_ok\n\n"
  out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

end Ember.Proof.PassSim.AbsGen
