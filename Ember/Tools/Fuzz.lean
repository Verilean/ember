import Ember.Lang.Gen
import Ember.Lang.Pretty
import Ember.Tools.Cc

/-!
# `ember-fuzz` — the interpreter against the emitted C (M2.8)

`lake exe ember-fuzz [COUNT] [--seed S] [--opt O0|O2|both] [--profile P]
[--no-san] [--plant]`

COUNT random programs (with random inputs) are emitted, compiled in
batches of 100 with the host harness — strict warnings, `-O0` and `-O2`,
UBSan and ASan — and their traces compared with the interpreter's:
every line except `note`s must agree, and a trap must happen in both or
neither.  A diverging program is shrunk (statements removed, expressions
replaced by operands) and printed, and saved under `Tests/Ember/regress/`.

`--plant` turns on the emitter's planted bug (the truncating cast of
`+` is dropped) to check that the fuzzer finds and shrinks it.
-/

namespace Ember.Tools.Fuzz
open Ember Ember.Lang Ember.Trace

structure Opts where
  count   : Nat := 100
  seed    : Nat := 1
  opts    : List String := ["-O0", "-O2"]
  san     : Bool := true
  plant   : Bool := false
  profile : Profile := .host64
  quiet   : Bool := false
  /-- Stop at the first divergence (after shrinking it). -/
  stopFirst : Bool := true

partial def parse : List String → Opts → Opts
  | [], o => o
  | "--seed" :: n :: r, o => parse r { o with seed := n.toNat?.getD 1 }
  | "--opt" :: "both" :: r, o => parse r { o with opts := ["-O0", "-O2"] }
  | "--opt" :: v :: r, o => parse r { o with opts := ["-" ++ v] }
  | "--no-san" :: r, o => parse r { o with san := false }
  | "--plant" :: r, o => parse r { o with plant := true }
  | "--quiet" :: r, o => parse r { o with quiet := true }
  | "--all" :: r, o => parse r { o with stopFirst := false }
  | "--profile" :: p :: r, o => parse r { o with profile := (Profile.ofName? p).getD .host64 }
  | a :: r, o => parse r { o with count := a.toNat?.getD o.count }

/-- Lines that must agree: everything but the note of a trap (whose
text says where, differently in each implementation; that both trapped
is compared apart).  The program's own notes, with their values, must
agree. -/
def comparable (t : Trace) : Array Line :=
  t.lines.filter fun l => match l.ev with | .note s => !s.startsWith "trap" | _ => true

def agree (a b : Trace) : Bool :=
  comparable a == comparable b && Cc.trapped a == Cc.trapped b

def flagsFor (o : Opts) (opt : String) : Array String :=
  #[opt] ++ (if o.san then #["-fsanitize=undefined,address", "-fno-sanitize-recover=all"] else #[])

def interp (p : Prog) (ins : Array Input) : Except String Trace :=
  match p.run ins with
  | .ok r => .ok r.trace
  | .error e => .error e.toString

/-- Compile and run one program alone; `true` when C and interpreter disagree. -/
def diverges (o : Opts) (opt : String) (dir : System.FilePath) (p : Prog) (ins : Array Input) : IO Bool := do
  let .ok it := interp p ins | return false
  let .ok c := Cc.emit "p" p { profile := o.profile, bugDropCast := o.plant, lines := false } | return false
  let b : Cc.Build := { dir, flags := flagsFor o opt, strict := !o.plant }
  match ← Cc.build b [("p", c)] with
  | .error _ => return false
  | .ok exe =>
    let inp := dir / "in.trace"
    Cc.writeInputs inp {} ins
    let (t, _) ← Cc.run exe 0 inp
    return !agree it t

structure Stats where
  programs : Nat := 0
  traps    : Nat := 0
  failures : Nat := 0

def report (o : Opts) (opt : String) (seed : Nat) (p : Prog) (ins : Array Input) (why : String) : IO Unit := do
  IO.println s!"DIVERGENCE seed={seed} {opt}: {why}"
  let dir : System.FilePath := s!".lake/ember-fuzz/shrink-{seed}"
  let small ← Gen.shrinkProg (diverges o opt dir · ins) p
  IO.println s!"shrunk from {Gen.progSize p} to {Gen.progSize small} statements:\n{small.pretty}"
  if let (.ok it, .ok c) := (interp small ins, Cc.emit "p" small { profile := o.profile, bugDropCast := o.plant, lines := false }) then
    IO.println s!"interpreter:\n{it.print}"
    IO.println s!"C:\n{c}"
  if !o.plant then
    IO.FS.createDirAll "Tests/Ember/regress"
    IO.FS.writeFile s!"Tests/Ember/regress/lang-{seed}.txt"
      s!"-- ember-fuzz seed {seed} {opt}: {why}\n{small.pretty}\n-- inputs\n{(Trace.ofSteps {} (ins.map (·, []))).print}"

/-- Fuzz a batch of programs at one optimisation level. -/
def batch (o : Opts) (opt : String) (seeds : List Nat) (st : Stats) : IO (Stats × Option Nat) := do
  let dir : System.FilePath := s!".lake/ember-fuzz/{opt}-{seeds.head!}"
  IO.FS.createDirAll dir
  let mut units := #[]
  let mut cases := #[]
  for s in seeds do
    let (p, ins) := Gen.sample s
    match interp p ins, Cc.emit s!"p{s}" p { profile := o.profile, bugDropCast := o.plant, lines := false } with
    | .ok it, .ok c =>
      units := units.push (s!"p{s}", c)
      cases := cases.push (s, p, ins, it)
    | .error e, _ | _, .error e => IO.println s!"seed {s}: generator produced a bad program: {e}"; return (st, some s)
  match ← Cc.build { dir, flags := flagsFor o opt, strict := !o.plant } units.toList with
  | .error e => IO.println s!"build failed for seeds {seeds.head!}..: {e.take 3000}"; return ({ st with failures := st.failures + 1 }, some seeds.head!)
  | .ok exe =>
    let mut list := ""
    for i in [0:cases.size] do
      let (s, _, ins, _) := cases[i]!
      Cc.writeInputs (dir / s!"in{s}.trace") {} ins
      list := list ++ s!"{i} {dir / s!"in{s}.trace"} {dir / s!"out{s}.trace"}\n"
    IO.FS.writeFile (dir / "batch.txt") list
    let r ← IO.Process.output { cmd := exe.toString, args := #["--batch", (dir / "batch.txt").toString] }
    if r.exitCode != 0 then
      IO.println s!"harness batch failed (sanitizer?):\n{r.stderr.take 2000}"
    let mut st := st
    for i in [0:cases.size] do
      let (s, p, ins, it) := cases[i]!
      st := { st with programs := st.programs + 1, traps := st.traps + (if Cc.trapped it then 1 else 0) }
      let outp := dir / s!"out{s}.trace"
      let ok ← if ← outp.pathExists then
          match Trace.parse (← IO.FS.readFile outp) with
          | .ok t => pure (agree it t)
          | .error _ => pure false
        else pure false
      if !ok then
        st := { st with failures := st.failures + 1 }
        report o opt s p ins (if r.exitCode != 0 then "harness aborted (sanitizer)" else "traces differ")
        if o.stopFirst then return (st, some s)
    return (st, none)

def main (args : List String) : IO UInt32 := do
  let o := parse args {}
  unless ← Cc.available do
    IO.println "ember-fuzz: no C compiler ($CC or gcc); run inside nix-shell"
    return 2
  let mut total : Stats := {}
  for opt in o.opts do
    let mut st : Stats := {}
    let mut i := 0
    while i < o.count do
      let seeds := (List.range (min 100 (o.count - i))).map (o.seed * 1000003 + i + ·)
      let (st', stop) ← batch o opt seeds st
      st := st'
      i := i + seeds.length
      if stop.isSome && o.stopFirst then break
    if !o.quiet || st.failures > 0 then
      IO.println s!"{opt}{if o.san then " +UBSan/ASan" else ""}{if o.plant then " (planted bug)" else ""}: {st.programs} programs, {st.traps} trapping, {st.failures} divergences"
    total := { programs := total.programs + st.programs, traps := total.traps + st.traps,
               failures := total.failures + st.failures }
    if total.failures > 0 && o.stopFirst then break
  return if total.failures == 0 then 0 else 1

end Ember.Tools.Fuzz
