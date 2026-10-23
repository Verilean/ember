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

end Ember.Proof.PassSim.AbsGen
