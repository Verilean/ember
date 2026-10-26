import Ember.Proof.Z80PassChk

/-!
# Ember.Proof.Z80PassCertGen — making a certificate for the two images (plan M7.3)

The rows of a certificate (`Row`, `Z80PassChk`) for the image without the
passes and the image with them: from the match of their items
(`alignOf`), the meeting points reachable from the first item, with
`H`, `L` free where a literal of the ROM may be in them, the activations
of functions, by a fixed point; and the files that hold it for the
kernel (`certFile`, `chunkFile`), written by `ember-passcert`.

Nothing here is trusted: the kernel checks the certificate (`check`,
`walk`), whatever made it.
-/

namespace Ember.Proof.PassSim.Gen
open Ember.Z80 Ember.Z80.Asm Ember.Proof.PassSim Ember.Proof.PassCheck

def ptr : List String := ["rt_ld32", "rt_st32", "rt_add32", "rt_sub32", "rt_or32", "rt_cmp32"]

def symOf : List Arg → Option String
  | [.imm (.sym l 0)] => some l
  | [_, .imm (.sym l 0)] => some l
  | _ => none

/-- What the computation looks at: both images' items, the match, the labels. -/
structure Ctx where
  xs : Array Item
  ys : Array Item
  al : Array (Kind × Option Nat)
  labA : Std.HashMap String Nat
  labB : Std.HashMap String Nat
  equs : List String

def Ctx.isLit (c : Ctx) (l : String) : Bool :=
  match c.labA[l]? with
  | some k => match c.xs[k + 1]? with | some (.db _) => true | _ => false
  | none => false

/-- The segment that starts at an item of `A`, from the match of the two images. -/
def tagOf (c : Ctx) (k : Nat) : Tag :=
  match c.al[k]? with
  | some (.pack, some _) => .pack
  | some (.retThr, some _) => .retThr
  | some (.condRet, some _) => .condRet
  | some (.tail, some _) => match c.xs[k]? with
    | some (.ins ⟨.call, [.imm (.sym f 0)]⟩) => if ptr.contains f then .tailBlk else .tail
    | _ => .none
  | some (.relax, some _) => .jump
  | some (.same, some _) =>
    match c.xs[k]? with
    | some (.ins i) =>
      match i with
      | ⟨.ret, _⟩ => .ret
      | ⟨.jp, _⟩ | ⟨.jr, _⟩ => .jump
      | ⟨.djnz, _⟩ => .djnz
      | ⟨.call, [.imm (.sym f 0)]⟩ => if ptr.contains f then .blk else .call
      | ⟨.halt, []⟩ => .halt
      | ⟨.ld, [.sp, .imm (.num 0)]⟩ => .ldsp
      | ⟨.ldir, []⟩ => .ldir
      | ⟨.ld, [.hl, .imm (.sym l 0)]⟩ =>
        if c.equs.contains l then .ord else
        if c.isLit l then
          match c.xs[k + 1]? with
          | some (.ins ⟨.call, [.imm (.sym f 0)]⟩) => if ptr.contains f then .blkR else .none
          | some (.ins ⟨.ld, [.de, _]⟩) => .copyR
          | _ => .none
        else .none
      | _ => if (Form.ofInstr? i).isSome then .ord else .none
    | some (.label _) | some (.equ ..) | some (.comment _) => .skipBoth
    | _ => .none
  | some (.drop, none) => match c.xs[k]? with
    | some (.label _) | some (.equ ..) | some (.comment _) => .skipA
    | _ => .none
  | _ => .none

structure St where
  kbs : Array Nat
  reach : Array Bool
  t : Array (Bool × Bool)
  act : Array (List Nat)
  tr : Std.HashMap Nat (Bool × Bool)
  errs : Array String
  changed : Bool

def orT (a b : Bool × Bool) : Bool × Bool := (a.1 || b.1, a.2 || b.2)

def St.add (s : St) (k kb : Nat) (t : Bool × Bool) (act : List Nat) : St := Id.run do
  let s := if s.reach[k]! && s.kbs[k]! != kb then { s with errs := s.errs.push s!"{k}: kb {s.kbs[k]!} vs {kb}" }
    else { s with kbs := s.kbs.set! k kb }
  let ot := s.t[k]!
  let oa := s.act[k]!
  let nt := orT ot t
  let na := act.foldl (fun a e => if a.contains e then a else a ++ [e]) oa
  if !s.reach[k]! || nt != ot || na.length != oa.length then
    return { s with reach := s.reach.set! k true, t := s.t.set! k nt, act := s.act.set! k na, changed := true }
  return s

def St.addTR (s : St) (e : Nat) (t : Bool × Bool) : St :=
  let o := s.tr.getD e (false, false)
  let n := orT o t
  if n != o then { s with tr := s.tr.insert e n, changed := true } else s

def St.err (s : St) (m : String) : St := { s with errs := s.errs.push m }

def go (c : Ctx) (s : St) (k kb : Nat) (t : Bool × Bool) (act : List Nat) : St := s.add k kb t act

def step (c : Ctx) (s : St) (k : Nat) : St := Id.run do
  if !s.reach[k]! then return s
  let kb := s.kbs[k]!
  let t := s.t[k]!
  let act := s.act[k]!
  let retc (s : St) : St := act.foldl (fun s e => s.addTR e t) s
  let lab (l : String) : Option Nat := c.labA[l]?
  match tagOf c k with
  | .skipBoth => return go c s (k + 1) (kb + 1) t act
  | .skipA => return go c s (k + 1) kb t act
  | .ord =>
    let some (.ins i) := c.xs[k]? | return s.err "ord?"
    let some f := Form.ofInstr? i | return s.err "ord form?"
    return go c s (k + 1) (kb + 1) (t.1 && !f.writesH, t.2 && !f.writesL) act
  | .jump =>
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "jump?"
    let some l := symOf args | return s.err "jump sym?"
    let some ja := lab l | return s.err s!"no label {l}"
    let some jb := c.labB[l]? | return s.err s!"no label B {l}"
    let s := go c s ja jb t act
    return if args.length == 2 then go c s (k + 1) (kb + 1) t act else s
  | .djnz =>
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "djnz?"
    let some l := symOf args | return s.err "djnz sym?"
    let some ja := lab l | return s.err s!"no label {l}"
    let some jb := c.labB[l]? | return s.err s!"no label B {l}"
    return go c (go c s ja jb t act) (k + 1) (kb + 1) t act
  | .call =>
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "call?"
    let some l := symOf args | return s.err "call sym?"
    let some ja := lab l | return s.err s!"no label {l}"
    let some jb := c.labB[l]? | return s.err s!"no label B {l}"
    let s := go c s ja jb t [ja]
    return go c s (k + 1) (kb + 1) (s.tr.getD ja (false, false)) act
  | .ret =>
    let s := retc s
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "ret?"
    return if args.length == 1 then go c s (k + 1) (kb + 1) t act else s
  | .retThr =>
    let s := retc s
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "retThr?"
    return if args.length == 2 then go c s (k + 1) (kb + 1) t act else s
  | .condRet =>
    let s := retc s
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "condRet?"
    let some l := symOf args | return s.err "condRet sym?"
    let some ja := lab l | return s.err s!"no label {l}"
    return go c s ja (kb + 1) t act
  | .halt => return s
  | .ldsp => return go c s (k + 1) (kb + 1) t [topE]
  | .ldir => return go c s (k + 1) (kb + 1) (false, false) act
  | .blk => return go c s (k + 1) (kb + 1) (false, false) act
  | .blkR => return go c s (k + 2) (kb + 2) (true, true) act
  | .copyR => return go c s (k + 4) (kb + 4) (true, true) act
  | .pack => return go c s (k + 4) (kb + 2) (false, false) act
  | .tail =>
    let some (.ins ⟨_, args⟩) := c.xs[k]? | return s.err "tail?"
    let some l := symOf args | return s.err "tail sym?"
    let some ja := lab l | return s.err s!"no label {l}"
    let some jb := c.labB[l]? | return s.err s!"no label B {l}"
    let s := go c s ja jb t [ja]
    return act.foldl (fun s e => s.addTR e (s.tr.getD ja (false, false))) s
  | .tailBlk => return s
  | .none => return s.err s!"{k}: reached, no tag {repr c.xs[k]?}"

/-- **The certificate**: the rows the runs meet at, from the first item on, by a fixed point (`H`, `L` free
and the activations grow; at most 100 rounds), and the functions that may return `H`, `L` free. -/
def mk (xs ys : List Item) : Except String (List Row × List (Nat × Bool × Bool)) := Id.run do
  let some al := alignOf xs ys | return .error "no align"
  let lab (zs : List Item) : Std.HashMap String Nat :=
    zs.zipIdx.foldl (fun m (it, k) => match it with | .label l => m.insert l k | _ => m) {}
  let equs : List String := xs.filterMap (fun it => match it with | .equ n _ => some n | _ => none)
  let c : Ctx := Ctx.mk xs.toArray ys.toArray al.toArray (lab xs) (lab ys) equs
  let n := xs.length
  let mut s : St := St.mk (Array.replicate n 0) (Array.replicate n false) (Array.replicate n (false, false)) (Array.replicate n [])
    (∅) #[] true
  s := go c s 0 0 (false, false) [topE]
  let mut it := 0
  while s.changed && it < 100 do
    s := { s with changed := false, errs := #[] }
    for k in [0:n] do
      s := step c s k
    it := it + 1
  if s.errs.size > 0 then return .error s!"{s.errs.toList.take 10}"
  let rows : List Row := (List.range n).map fun k =>
    if s.reach[k]! then
      { tag := tagOf c k, kb := s.kbs[k]!, th := s.t[k]!.1, tl := s.t[k]!.2,
        fi := (match c.xs[k]? with
          | some (.ins i) => ((Form.cands (argVal i)).findIdx? fun f => decide (f.instr = i)).getD 0
          | _ => 0),
        act := s.act[k]! }
    else {}
  let tr := s.tr.toList.filter (fun (_, t) => t.1 || t.2) |>.map fun (e, t) => (e, t.1, t.2)
  return .ok (rows, tr)



def tagName : Tag → String
  | .none => "none" | .skipBoth => "skipBoth" | .skipA => "skipA" | .ord => "ord" | .jump => "jump"
  | .djnz => "djnz" | .call => "call" | .ret => "ret" | .halt => "halt" | .ldsp => "ldsp" | .ldir => "ldir"
  | .pack => "pack" | .blk => "blk" | .blkR => "blkR" | .copyR => "copyR" | .retThr => "retThr"
  | .condRet => "condRet" | .tail => "tail" | .tailBlk => "tailBlk"

def rowText (r : Row) : String :=
  if r.tag = .none then "{}" else s!"⟨.{tagName r.tag}, {r.kb}, {r.fi}, {r.th}, {r.tl}, {r.act}⟩"

/-- Where each part of the check starts: every `n` items, with `B`'s index the walk has there. -/
def starts (rows : List Row) (n : Nat) : List (Nat × Nat) := Id.run do
  let mut kb := 0
  let mut out : Array (Nat × Nat) := #[]
  let mut k := 0
  for r in rows do
    if k % n == 0 then out := out.push (k, kb)
    if r.tag != .none then kb := r.kb
    k := k + 1
  return out.toList

/-- The file of the certificate. -/
def certFile (rows : List Row) (tr : List (Nat × Bool × Bool)) (n : Nat) (lo hi : Nat) : String := Id.run do
  let chunks := (List.range ((rows.length + 299) / 300)).map fun i => (rows.drop (i * 300)).take 300
  let mut out := "import Ember.Proof.Z80PassChkOK\nimport Ember.Proof.Z80StackHAsm\nimport Ember.Proof.Z80StackDAsm\n\n" ++
    "/-!\n# Ember.Proof.Z80PassCertD — a certificate for the stack's images (plan M7.3)\n\n" ++
    "The rows of a certificate (`Z80PassChk`) for `StackH` (without the passes) and `StackD` (as built\n" ++
    "by default), and where the parts of its check start.  Written by `ember-passcert`\n" ++
    "(`Ember.Proof.Z80PassCertGen`); the kernel checks it (`Z80PassCertD0` …).\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  let mut i := 0
  for ch in chunks do
    out := out ++ s!"def rows{i} : List Row := [\n  " ++ ", ".intercalate (ch.map rowText) ++ "]\n\n"
    i := i + 1
  out := out ++ "def rows : List Row := " ++ " ++ ".intercalate ((List.range i).map fun j => s!"rows{j}") ++ "\n\n"
  out := out ++ s!"def tr : List (Nat × Bool × Bool) := {tr}\n\n"
  out := out ++ s!"/-- The RAM kept equal: `[lo, hi)`. -/\ndef lo : Nat := {lo}\ndef hi : Nat := {hi}\n\n"
  out := out ++ s!"/-- Items a part of the check walks. -/\ndef part : Nat := {n}\n\n"
  out := out ++ s!"/-- Where the parts start (`A`'s index, `B`'s). -/\ndef starts : List (Nat × Nat) := {starts rows n}\n\n"
  out := out ++ "/-- The context of the check. -/\ndef ctx : Ctx := mkCtx StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr\n\n"
  out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

/-- A file of parts of the check (`walk`, by the kernel), importing the one before. -/
def chunkFile (idx : Nat) (prev : String) (ps : List (Nat × Nat)) (n : Nat) (last : Bool) : String := Id.run do
  let mut out := s!"import {prev}\n\n" ++
    s!"/-!\n# Ember.Proof.Z80PassCertD{idx} — parts of the check of the certificate (plan M7.3)\n\n" ++
    "The walk of the checker over parts of the stack's images, by the kernel (`decide +kernel`), each\n" ++
    "from its start (`starts`).  Written by `ember-passcert`.\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  for (k, kb) in ps do
    out := out ++ s!"set_option maxRecDepth 100000 in\ntheorem walk{k} : walk ctx part (prevOf StackH.items {k}) (StackH.items.drop {k}) (rows.drop {k})\n    (StackD.items.drop {kb}) {kb} = true := by\n  decide +kernel\n\n"
  if last then
    out := out ++ "end Ember.Proof.PassSim.CertD\n"
  else
    out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

/-- The file that puts the parts together: the certificate's rows checked (`RowsOK`). -/
def okFile (prev : String) (ps : List (Nat × Nat)) : String := Id.run do
  let mut out := s!"import {prev}\n\n" ++
    "/-!\n# Ember.Proof.Z80PassCertDOK — the certificate for the stack's images, checked (plan M7.3)\n\n" ++
    "`certD_ok`: the rows of `Z80PassCertD` checked (`RowsOK`), from the parts of the walk by the kernel\n" ++
    "(`Z80PassCertD0` …), which cover every item (`rows_of_walks`).  Written by `ember-passcert`.\n-/\n\n" ++
    "namespace Ember.Proof.PassSim.CertD\nopen Ember.Proof.PassSim Ember.Proof.Z80Gen\n\n"
  out := out ++ "set_option maxRecDepth 100000 in\ntheorem rows_len : rows.length = StackH.items.length := by decide +kernel\n\n"
  out := out ++ "theorem starts_walk : ∀ p, p ∈ starts →\n    walk ctx part (prevOf StackH.items p.1) (StackH.items.drop p.1) (rows.drop p.1) (StackD.items.drop p.2) p.2 = true := by\n  intro p hp\n  simp only [starts, List.mem_cons, List.not_mem_nil, or_false] at hp\n"
  out := out ++ "  rcases hp with " ++ " | ".intercalate (ps.map fun _ => "rfl") ++ "\n"
  for (k, _) in ps do
    out := out ++ s!"  · exact walk{k}\n"
  out := out ++ "\ntheorem starts_at : ∀ i (h : i < starts.length), (starts[i]'h).1 = part * i := by\n  decide\n\n"
  out := out ++ "set_option maxRecDepth 100000 in\ntheorem starts_reach : StackH.items.length ≤ part * starts.length := by decide +kernel\n\n"
  out := out ++ "set_option maxRecDepth 100000 in\ntheorem first : ∃ r rs, rows = r :: rs ∧ r.tag ≠ .none ∧ r.kb = 0 ∧ r.th = false ∧ r.tl = false ∧ topE ∈ r.act :=\n  ⟨_, _, rfl, by decide, rfl, rfl, rfl, by decide⟩\n\n"
  out := out ++ "/-- **The certificate's rows checked.** -/\ntheorem certD_ok : RowsOK StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr :=\n  ⟨rows_len, first, rows_of_walks' ctx _ _ rows part starts starts_walk starts_at (by decide) starts_reach rows_len⟩\n\n"
  out := out ++ "/-- info: 'Ember.Proof.PassSim.CertD.certD_ok' depends on axioms: [propext, Quot.sound] -/\n#guard_msgs in #print axioms certD_ok\n\n"
  out := out ++ "end Ember.Proof.PassSim.CertD\n"
  return out

end Ember.Proof.PassSim.Gen
