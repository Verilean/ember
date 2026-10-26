import Ember.Lang.Examples
import Ember.Net.Main
import Ember.Net.Loop
import Ember.Net.Eth
import Ember.Lang.Pretty
import Ember.C.Compile
import Ember.C.DropChecks

/-!
# `ember-emit` — print the C of a registered program

`lake exe ember-emit NAME [--profile host64|rv32|sdcc-z80] [--ember]`
prints the emitted C (or, with `--ember`, the program as Ember source).
`lake exe ember-emit --golden` rewrites `Tests/Ember/golden/<name>.<profile>.c`
for every registered program and profile; the tests compare against them.
`--dropped` prints the C without its bounds checks (`C.dropUnit`), for the
programs in `dropped` only — those whose runs are proved never to trap
(`Ember.Proof.CDrop.stack_c_dropped`: the SLIP build); the golden files
are `<name>.dropped.<profile>.c`.
-/

namespace Ember.Tools.Emit
open Ember Ember.Lang Ember.C

/-- Programs known to the tools: the examples, the stack and the SLIP
loopback used to bring up a target. -/
def registry : IO (List (String × Prog)) :=
  pure (Examples.all ++ [("net", Net.prog), ("sliploop", Net.Loop.prog),
    ("net-eth", Net.Eth.prog), ("net-eth-dhcp", Net.Eth.progDhcp)])

/-- Programs of a test of the tools: emitted by name, without a golden file. -/
def extra : List (String × Prog) := [("trapnote", Examples.TrapNote.prog)]

def goldenDir : System.FilePath := "Tests/Ember/golden"

def goldenPath (name : String) (p : Profile) : System.FilePath :=
  goldenDir / s!"{name}.{p.name}.c"

def emitFor (prog : Prog) (p : Profile) : Except String String :=
  emitC prog { profile := p }

/-- The programs whose C may go without bounds checks: `stack_c_dropped`
is about the SLIP build (`Net.prog`), and no other. -/
def dropped : List String := ["net"]

def droppedPath (name : String) (p : Profile) : System.FilePath :=
  goldenDir / s!"{name}.dropped.{p.name}.c"

/-- The C of a registered program without its bounds checks; refused
unless the program is in `dropped`. -/
def emitDroppedFor (name : String) (prog : Prog) (p : Profile) : Except String String :=
  if dropped.contains name then emitDroppedC prog { profile := p }
  else .error s!"{name}: the bounds checks stay (no proof that its runs never trap; --dropped is for {dropped})"

def main (args : List String) : IO UInt32 := do
  let progs ← registry
  if args == ["--golden"] then
    IO.FS.createDirAll goldenDir
    for (n, prog) in progs do
      for p in Profile.all do
        match emitFor prog p with
        | .ok c => IO.FS.writeFile (goldenPath n p) c; IO.println s!"wrote {goldenPath n p}"
        | .error e => IO.eprintln s!"{n}: {e}"; return 1
        if dropped.contains n then
          match emitDroppedFor n prog p with
          | .ok c => IO.FS.writeFile (droppedPath n p) c; IO.println s!"wrote {droppedPath n p}"
          | .error e => IO.eprintln s!"{n}: {e}"; return 1
    return 0
  let rec go : List String → Option String → Profile → Bool → Bool → Option String × Profile × Bool × Bool
    | [], n, p, e, d => (n, p, e, d)
    | "--profile" :: q :: r, n, _, e, d => go r n ((Profile.ofName? q).getD .host64) e d
    | "--ember" :: r, n, p, _, d => go r n p true d
    | "--dropped" :: r, n, p, e, _ => go r n p e true
    | a :: r, _, p, e, d => go r (some a) p e d
  let (name, prof, asEmber, drop) := go args none .host64 false false
  let some n := name | IO.eprintln s!"usage: ember-emit NAME [--profile P] [--ember] [--dropped] | --golden\nprograms: {progs.map (·.1)}"; return 2
  let some prog := (progs ++ extra).lookup n | IO.eprintln s!"unknown program {n}; known: {progs.map (·.1)}"; return 2
  if asEmber then IO.println prog.pretty; return 0
  match (if drop then emitDroppedFor n prog prof else emitFor prog prof) with
  | .ok c => IO.print c; return 0
  | .error e => IO.eprintln e; return 1

end Ember.Tools.Emit
