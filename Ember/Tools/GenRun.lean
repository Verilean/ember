import Ember.Spec.Gen
import Ember.Trace.Text

/-!
# `ember-gen` — generated sessions against the reference stack

`lake exe ember-gen [icmp|udp|tcp|all] [COUNT] [--seed N] [--quiet]`

For each protocol, COUNT sessions; each is run as generated, mutated, and
re-chunked, and must satisfy `Gen.properties` (TCP sessions additionally
check their echo).  A failing input stream is shrunk and written to
`Tests/Ember/regress/` as a trace fixture.
-/

namespace Ember.Tools.GenRun
open Ember Ember.Spec Ember.Trace

def regressDir : System.FilePath := "Tests/Ember/regress"

def saveRegress (name : String) (cfg : Config) (ins : Array Input) (why : String) : IO Unit := do
  IO.FS.createDirAll regressDir
  let t := Spec.run cfg ins
  let p := regressDir / (name ++ ".trace")
  let lines := t.print.splitOn "\n"
  IO.FS.writeFile p (lines.head! ++ s!"\n# shrunk by ember-gen: {why}\n" ++ "\n".intercalate lines.tail!)
  IO.println s!"  wrote {p} ({ins.size} inputs)"

structure Stats where
  sessions : Nat := 0
  inputs   : Nat := 0
  failures : Nat := 0

def checkOne (name : String) (s : Gen.Session) (st : Stats) : IO Stats := do
  let st := { st with sessions := st.sessions + 1, inputs := st.inputs + s.inputs.size }
  match Gen.properties s with
  | none => return st
  | some why =>
    IO.println s!"FAIL {name}: {why}"
    let bad (xs : Array Input) := (Gen.properties { s with inputs := xs }).isSome
    saveRegress name s.cfg (Gen.shrink bad s.inputs) why
    return { st with failures := st.failures + 1 }

def runProto (proto : String) (count seed : Nat) : IO Stats := do
  let mut st : Stats := {}
  let mut rng := Rng.ofSeed (seed + proto.length * 1000003)
  for i in [0:count] do
    let name := s!"{proto}-{seed}-{i}"
    let (r, rng') := (do
      let base ← match proto with
        | "icmp" => (Except.ok <$> Gen.ping : RandM _)
        | "udp" => Except.ok <$> Gen.udp
        | _ => Gen.tcp
      match base with
      | .error e => return Except.error e
      | .ok s => return .ok (s, ← Gen.mutate s, ← Gen.rechunk s)).run rng
    rng := rng'
    match r with
    | .error (why, ins) =>
      IO.println s!"FAIL {name}: {why}"
      saveRegress name {} ins why
      st := { st with sessions := st.sessions + 1, failures := st.failures + 1 }
    | .ok (s, m, c) =>
      st ← checkOne name s st
      st ← checkOne (name ++ "-mut") m st
      st ← checkOne (name ++ "-chunk") c st
  return st

structure Opts where
  protos : List String := ["icmp", "udp", "tcp"]
  count  : Nat := 100
  seed   : Nat := 1
  quiet  : Bool := false

def parse : List String → Opts → Opts
  | [], o => o
  | "--seed" :: n :: r, o => parse r { o with seed := n.toNat?.getD 1 }
  | "--quiet" :: r, o => parse r { o with quiet := true }
  | "all" :: r, o => parse r { o with protos := ["icmp", "udp", "tcp"] }
  | a :: r, o => match a.toNat? with
    | some n => parse r { o with count := n }
    | none => parse r { o with protos := [a] }

def main (args : List String) : IO UInt32 := do
  let o := parse args {}
  let mut bad := 0
  for p in o.protos do
    let st ← runProto p o.count o.seed
    bad := bad + st.failures
    if !o.quiet || st.failures > 0 then
      IO.println s!"{p}: {st.sessions} sessions, {st.inputs} inputs, {st.failures} failures"
  return if bad == 0 then 0 else 1

end Ember.Tools.GenRun
