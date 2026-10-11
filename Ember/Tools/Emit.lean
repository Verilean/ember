import Ember.Lang.Examples
import Ember.Net.Main
import Ember.Net.Loop
import Ember.Net.Eth
import Ember.Lang.Pretty
import Ember.C.Compile

/-!
# `ember-emit` — print the C of a registered program

`lake exe ember-emit NAME [--profile host64|rv32|sdcc-z80] [--ember]`
prints the emitted C (or, with `--ember`, the program as Ember source).
`lake exe ember-emit --golden` rewrites `Tests/Ember/golden/<name>.<profile>.c`
for every registered program and profile; the tests compare against them.
-/

namespace Ember.Tools.Emit
open Ember Ember.Lang Ember.C

/-- Programs known to the tools: the examples, the stack and the SLIP
loopback used to bring up a target. -/
def registry : IO (List (String × Prog)) :=
  pure (Examples.all ++ [("net", Net.prog), ("sliploop", Net.Loop.prog),
    ("net-eth", Net.Eth.prog), ("net-eth-dhcp", Net.Eth.progDhcp)])

def goldenDir : System.FilePath := "Tests/Ember/golden"

def goldenPath (name : String) (p : Profile) : System.FilePath :=
  goldenDir / s!"{name}.{p.name}.c"

def emitFor (prog : Prog) (p : Profile) : Except String String :=
  emitC prog { profile := p }

def main (args : List String) : IO UInt32 := do
  let progs ← registry
  if args == ["--golden"] then
    IO.FS.createDirAll goldenDir
    for (n, prog) in progs do
      for p in Profile.all do
        match emitFor prog p with
        | .ok c => IO.FS.writeFile (goldenPath n p) c; IO.println s!"wrote {goldenPath n p}"
        | .error e => IO.eprintln s!"{n}: {e}"; return 1
    return 0
  let rec go : List String → Option String → Profile → Bool → Option String × Profile × Bool
    | [], n, p, e => (n, p, e)
    | "--profile" :: q :: r, n, _, e => go r n ((Profile.ofName? q).getD .host64) e
    | "--ember" :: r, n, p, _ => go r n p true
    | a :: r, _, p, e => go r (some a) p e
  let (name, prof, asEmber) := go args none .host64 false
  let some n := name | IO.eprintln s!"usage: ember-emit NAME [--profile P] [--ember] | --golden\nprograms: {progs.map (·.1)}"; return 2
  let some prog := progs.lookup n | IO.eprintln s!"unknown program {n}; known: {progs.map (·.1)}"; return 2
  if asEmber then IO.println prog.pretty; return 0
  match emitFor prog prof with
  | .ok c => IO.print c; return 0
  | .error e => IO.eprintln e; return 1

end Ember.Tools.Emit
