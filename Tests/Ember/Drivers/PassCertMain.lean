import Ember.Proof.Z80PassCertGen
import Ember.Proof.Z80PassAbsGen
import Ember.Proof.Z80StackHAsm
import Ember.Proof.Z80StackDAsm
import Ember.Tools.Z80

/-! `ember-passcert [DIR]`: the certificate for the stack's two images (without the passes, as built by
default) and the files of its check, written into `DIR` (`Ember/Proof`), and the list of what is known of `StackH`'s registers with the levels of its functions
(`Z80PassAbsD`, its check `Z80PassAbsD0` …, `Z80PassAbsDOK`).

`ember-passcert --safe PATH...`: `Need` of `Z80PassMaster` (what the segments take of `StackH`'s run at the
meeting points, which `absD_ok` gives) run on fixtures — `StackH` on each, `Need` checked at every
meeting point of the certificate it is at.  A test.

`ember-passcert --abs`: the list of what is known, computed, and the meeting points where it is not
enough. -/

open Ember Ember.Z80 Ember.Z80.Asm Ember.Proof.PassSim Ember.Proof.Z80Gen

/-- What of `Need` fails at a state at item `k` (empty: nothing); the forms by their operands
(`(hl)`: `Form.viaHL`, `(de)`: `Form.viaDE`). -/
def needFails (xs : Array Item) (labels : Std.HashSet String) (lo hi k : Nat) (s : Cpu) : Array String := Id.run do
  let inRam (x : Nat) : Bool := lo ≤ x && x < hi
  let mut v : Array String := #[]
  let top := if s.sp.toNat == 0 then 65536 else s.sp.toNat
  if hi + 4 > top then v := v.push "stack"
  let .ins i := xs[k]! | return v
  if i.args.contains .mhl && !inRam s.hl.toNat then v := v.push s!"(hl): {i.text}"
  if i.args.contains .mde && !inRam s.de.toNat then v := v.push s!"(de): {i.text}"
  if i.op == .ldir && !(inRam s.hl.toNat && inRam s.de.toNat) then v := v.push "ldir"
  match i with
  | ⟨.call, [.imm (.sym f 0)]⟩ =>
    if (ptrRoutine f).isSome then
      let lit := match xs[k - 1]? with
        | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => k > 0 && labels.contains l
        | _ => false
      if !lit && !(lo ≤ s.hl.toNat && s.hl.toNat + 4 ≤ hi) then v := v.push s!"call {f}"
  | _ => pure ()
  return v

def safeCheck (rows : List Row) (paths : List String) (lo hi : Nat) : IO UInt32 := do
  let xs := StackH.items.toArray
  let a := StackH.asm
  let rs := rows.toArray
  -- the meeting points at each address
  let mut pts : Std.HashMap Nat (Array Nat) := {}
  for k in [0:xs.size] do
    if rs[k]!.tag != .none then pts := pts.insert a.addrs[k]! ((pts.getD a.addrs[k]! #[]).push k)
  let labels : Std.HashSet String := xs.foldl (fun s it => match it with | .label l => s.insert l | _ => s) {}
  let mut steps := 0
  let mut checked := 0
  let mut ran := 0
  let mut halted := 0
  let mut fails : Std.HashMap String Nat := {}
  let mut ex : Array String := #[]
  for p in paths do
    for f in ← Tools.Z80.traceFiles p do
      let t ← Ember.Trace.Trace.readFile f
      if !Tools.NetCheck.supported t.header then continue
      ran := ran + 1
      let mut m : Machine :=
        { cpu := { (({} : Cpu).load 0 a.bytes) with ramStart := 0x8000 }, harness := true, inputs := t.inputs,
          program := 0 }
      let mut fuel := 200000000
      while fuel > 0 && !m.cpu.halted do
        steps := steps + 1
        for k in pts.getD m.cpu.pc.toNat #[] do
          checked := checked + 1
          for w in needFails xs labels lo hi k m.cpu do
            fails := fails.insert w (fails.getD w 0 + 1)
            if ex.size < 20 then ex := ex.push s!"{f}: item {k}: {w} (hl {m.cpu.hl}, de {m.cpu.de}, sp {m.cpu.sp})"
        m := m.step
        fuel := fuel - 1
      if m.cpu.halted then halted := halted + 1
  IO.println s!"passcert --safe: {ran} fixtures, {halted} halted, {steps} steps, {checked} meeting points checked; RAM [{lo}, {hi}); Need fails: {fails.toList}"
  for e in ex do IO.println s!"  {e}"
  return if fails.isEmpty && halted == ran then 0 else 1

def equOf (xs : List Item) (n : String) : Option Nat :=
  xs.findSome? fun it => match it with | .equ m v => if m == n then some v else none | _ => none

def main (args : List String) : IO UInt32 := do
  let some lo := equOf StackH.items "rt_ram" | IO.eprintln "no rt_ram"; return 1
  let some size := equOf StackH.items "rt_ram_size" | IO.eprintln "no rt_ram_size"; return 1
  let hi := lo + size
  match Gen.mk StackH.items StackD.items with
  | .error e => IO.eprintln s!"passcert: {e}"; return 1
  | .ok (rows, tr) =>
    if args.head? == some "--safe" then
      return ← safeCheck rows (args.drop 1) lo hi
    if args.head? == some "--abs" then
      let ctx := mkCtx StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr
      let (acl, bad) := AbsGen.mk ctx.la ctx.tA lo hi StackH.items rows
      IO.println s!"passcert --abs: {(acl.filter (·.isSome)).size} items with something known; {bad.size} meeting points where it is not enough"
      for (k, it) in bad do IO.println s!"  {k}: {repr it}"
      let es := AbsGen.edges ctx.t StackH.items rows
      match AbsGen.levels es with
      | some lv => IO.println s!"levels: {es.length} calls, level of no function {(lv.lookup topE).getD 0}, max {lv.foldl (fun m p => max m p.2) 0}"
      | none => IO.println "levels: the calls go round"
      return if bad.isEmpty then 0 else 1
    let dir : System.FilePath := args.headD "Ember/Proof"
    if !check StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr then
      IO.eprintln "passcert: the certificate does not pass the check"
      return 1
    let part := 150
    let ps := Gen.starts rows part
    IO.FS.writeFile (dir / "Z80PassCertD.lean") (Gen.certFile rows tr part lo hi)
    let groups := (List.range ((ps.length + 2) / 3)).map fun i => (ps.drop (i * 3)).take 3
    let mut prev := "Ember.Proof.Z80PassCertD"
    let mut i := 0
    for g in groups do
      IO.FS.writeFile (dir / s!"Z80PassCertD{i}.lean") (Gen.chunkFile i prev g part (i + 1 == groups.length))
      prev := s!"Ember.Proof.Z80PassCertD{i}"
      i := i + 1
    IO.FS.writeFile (dir / "Z80PassCertDOK.lean") (Gen.okFile prev ps)
    -- what is known of `StackH`'s registers, and the levels
    let actx := mkCtx StackH.items StackD.items StackH.asm StackD.asm lo hi rows tr
    let (acl, bad) := AbsGen.mk actx.la actx.tA lo hi StackH.items rows
    if !bad.isEmpty then
      IO.eprintln s!"passcert: what is known is not enough at {bad.size} meeting points"
      return 1
    let some lv := AbsGen.levels (AbsGen.edges actx.t StackH.items rows) | IO.eprintln "passcert: the calls go round"; return 1
    let apart := 300
    let aps := AbsGen.starts StackH.items.length apart
    IO.FS.writeFile (dir / "Z80PassAbsD.lean") (AbsGen.absFile acl.toList lv apart StackH.items.length)
    let agroups := (List.range ((aps.length + 2) / 3)).map fun i => (aps.drop (i * 3)).take 3
    let mut aprev := "Ember.Proof.Z80PassAbsD"
    let mut ai := 0
    for g in agroups do
      IO.FS.writeFile (dir / s!"Z80PassAbsD{ai}.lean") (AbsGen.absChunkFile ai aprev g)
      aprev := s!"Ember.Proof.Z80PassAbsD{ai}"
      ai := ai + 1
    IO.FS.writeFile (dir / "Z80PassAbsDOK.lean") (AbsGen.absOkFile aprev aps)
    IO.println s!"passcert: {rows.length} rows, {(rows.filter (·.tag != .none)).length} meeting points, {ps.length} parts in {groups.length} files, [{lo}, {hi}); {(acl.filter (·.isSome)).size} items with something known, {aps.length} parts of its walk in {agroups.length} files"
    return 0
