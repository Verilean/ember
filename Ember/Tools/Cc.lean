import Ember.C.Compile
import Ember.Lang.Eval
import Ember.Trace.Text
import Ember.Trace.Diff

/-!
# Ember.Tools.Cc — compile emitted C with the host harness and run it

Used by the differential tests (M2.7), the fuzzer (M2.8) and `ember-net`
(M3).  The C compiler is `$CC` (default `gcc`); tests skip when it is not
installed.
-/

namespace Ember.Tools.Cc
open Ember Ember.Lang Ember.C Ember.Trace

def cc : IO String := do return (← IO.getEnv "CC").getD "gcc"

def available : IO Bool := do
  try
    let r ← IO.Process.output { cmd := ← cc, args := #["--version"] }
    return r.exitCode == 0
  catch _ => return false

/-- Warnings the emitted C must be free of (design §3, M2 exit criteria). -/
def strictFlags : Array String :=
  #["-std=c99", "-Wall", "-Wextra", "-Wconversion", "-Werror", "-pedantic",
    -- nix's cc wrapper defines _FORTIFY_SOURCE, whose #warning fires at -O0
    "-Wno-cpp"]

structure Build where
  dir   : System.FilePath
  /-- Extra flags (`-O2`, sanitizers, …). -/
  flags : Array String := #["-O0"]
  strict : Bool := true

/-- Write the units and the program table, compile them with the harness. -/
def build (b : Build) (units : List (String × String)) (exe := "harness") : IO (Except String System.FilePath) := do
  IO.FS.createDirAll b.dir
  let mut files : Array String := #[]
  for (name, text) in units do
    let p := b.dir / (name ++ ".c")
    IO.FS.writeFile p text
    files := files.push p.toString
  let gp := b.dir / "ember_glue.c"
  IO.FS.writeFile gp (glue (units.map (·.1 ++ "_")))
  files := files.push gp.toString
  let out := b.dir / exe
  let args := (if b.strict then strictFlags else #["-std=c99", "-w"]) ++ b.flags ++
    #["-Iruntime/common", "-o", out.toString, "Tests/Ember/host/harness.c"] ++ files
  let r ← IO.Process.output { cmd := ← cc, args }
  if r.exitCode != 0 then return .error s!"{r.stderr}\n(command: {← cc} {" ".intercalate (args.toList.take 12)} ...)"
  return .ok out

/-- Emit a program with the name prefix `<name>_`. -/
def emit (name : String) (p : Prog) (o : Opts := {}) : Except String String :=
  emitC p { o with namePrefix := name ++ "_" }

/-- Run program `k` of a harness on a trace's inputs; trace and exit code. -/
def run (exe : System.FilePath) (k : Nat) (inputs : System.FilePath) : IO (Trace × UInt32) := do
  let r ← IO.Process.output { cmd := exe.toString, args := #["-p", toString k, inputs.toString] }
  match Trace.parse r.stdout with
  | .ok t => return (t, r.exitCode)
  | .error e => throw (IO.userError s!"harness output: {e}\n{r.stdout.take 400}{r.stderr}")

/-- Inputs as a trace file the harness can read. -/
def writeInputs (p : System.FilePath) (h : Header) (inputs : Array Input) : IO Unit :=
  IO.FS.writeFile p (Trace.ofSteps h (inputs.map (·, []))).print

/-- Did a run end in a trap?  (Its last line is `note trap …`.) -/
def trapped (t : Trace) : Bool :=
  match t.lines.back? with
  | some ⟨_, .note n⟩ => n.startsWith "trap "
  | _ => false

end Ember.Tools.Cc
