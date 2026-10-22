import Ember.Proof.Z80PassCertGen
import Ember.Proof.Z80StackHAsm
import Ember.Proof.Z80StackDAsm

/-! `ember-passcert [DIR]`: the certificate for the stack's two images (without the passes, as built by
default) and the files of its check, written into `DIR` (`Ember/Proof`). -/

open Ember.Z80.Asm Ember.Proof.PassSim Ember.Proof.Z80Gen

def equOf (xs : List Item) (n : String) : Option Nat :=
  xs.findSome? fun it => match it with | .equ m v => if m == n then some v else none | _ => none

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "Ember/Proof"
  let some lo := equOf StackH.items "rt_ram" | IO.eprintln "no rt_ram"; return 1
  let some size := equOf StackH.items "rt_ram_size" | IO.eprintln "no rt_ram_size"; return 1
  let hi := lo + size
  match Gen.mk StackH.items StackD.items with
  | .error e => IO.eprintln s!"passcert: {e}"; return 1
  | .ok (rows, tr) =>
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
    IO.println s!"passcert: {rows.length} rows, {(rows.filter (·.tag != .none)).length} meeting points, {ps.length} parts in {groups.length} files, [{lo}, {hi})"
    return 0
