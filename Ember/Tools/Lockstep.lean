import Ember.Tools.NetCheck
import Ember.Tools.Cc
import Ember.Tools.Fuzz
import Ember.Tools.GenRun
import Ember.Spec.Gen

/-!
# `ember-lockstep` — Spec = Ember interpreter = host C (M3)

```
lake exe ember-lockstep FILE.trace ...
lake exe ember-lockstep --gen [icmp|udp|tcp|all] [COUNT] [--seed S] [--c] [--opt O2]
```

For each input stream (the inputs of a trace file, or a generated session
and its mutated and re-chunked variants): the Spec and the Ember stack in
the interpreter run in lockstep with their states compared after every
input, and their traces compared (observable lines and drop reasons).
With `--c` the Ember stack's emitted C, built with the host harness
(strict warnings, UBSan/ASan), must produce the interpreter's trace too.
A failing stream is shrunk and saved in `Tests/Ember/regress/`.
-/

namespace Ember.Tools.Lockstep
open Ember Ember.Trace Ember.Lang

structure Opts where
  files : List String := []
  gen   : Option String := none
  count : Nat := 100
  seed  : Nat := 1
  withC : Bool := false
  opt   : String := "-O2"
  quiet : Bool := false

partial def parse : List String → Opts → Opts
  | [], o => o
  | "--gen" :: p :: r, o =>
    if ["icmp", "udp", "tcp", "all"].contains p then parse r { o with gen := some p }
    else parse (p :: r) { o with gen := some "all" }
  | "--gen" :: [], o => { o with gen := some "all" }
  | "--seed" :: n :: r, o => parse r { o with seed := n.toNat?.getD 1 }
  | "--c" :: r, o => parse r { o with withC := true }
  | "--opt" :: v :: r, o => parse r { o with opt := v }
  | "--quiet" :: r, o => parse r { o with quiet := true }
  | a :: r, o => match a.toNat? with
    | some n => parse r { o with count := n }
    | none => parse r { o with files := o.files ++ [a] }

/-- A compiled host harness running the Ember stack. -/
def buildC (opt : String) : IO (Except String System.FilePath) := do
  match Cc.emit "net" NetCheck.netProg with
  | .error e => return .error e
  | .ok c => Cc.build { dir := s!".lake/ember-net{opt}", flags := #[opt, "-fsanitize=undefined,address",
      "-fno-sanitize-recover=all"] } [("net", c)]

structure Stats where
  streams : Nat := 0
  inputs  : Nat := 0
  failures : Nat := 0

def saveRegress (name0 : String) (ins : Array Input) (why : String) : IO Unit := do
  let name := name0.map fun c => if c == '/' || c == '.' then '_' else c
  let bad (xs : Array Input) := (NetCheck.check xs).1.isSome
  let small := if bad ins then Spec.Gen.shrink bad ins else ins
  IO.FS.createDirAll "Tests/Ember/regress"
  let t := Spec.run {} small
  let lines := t.print.splitOn "\n"
  IO.FS.writeFile s!"Tests/Ember/regress/{name}.trace"
    (lines.head! ++ s!"\n# ember-lockstep: {why.take 300 |>.replace "\n" " "}\n" ++ "\n".intercalate lines.tail!)
  IO.println s!"  saved Tests/Ember/regress/{name}.trace ({small.size} inputs)"

/-- Check a batch of streams; with a harness, the C too. -/
def checkBatch (_o : Opts) (exe : Option System.FilePath) (named : Array (String × Array Input)) (st : Stats) : IO Stats := do
  let mut st := st
  let mut interp : Array (String × Array Input × Trace) := #[]
  for (name, ins) in named do
    st := { st with streams := st.streams + 1, inputs := st.inputs + ins.size }
    let (r, t) := NetCheck.check ins
    match r with
    | some why =>
      st := { st with failures := st.failures + 1 }
      IO.println s!"FAIL {name}: Spec vs Ember interpreter\n{why.take 3000}"
      saveRegress name ins why
    | none => interp := interp.push (name, ins, t)
  if let some exe := exe then
    let dir : System.FilePath := ".lake/ember-net-batch"
    IO.FS.createDirAll dir
    let mut list := ""
    for i in [0:interp.size] do
      let (_, ins, _) := interp[i]!
      Cc.writeInputs (dir / s!"in{i}.trace") {} ins
      list := list ++ s!"0 {dir / s!"in{i}.trace"} {dir / s!"out{i}.trace"}\n"
    IO.FS.writeFile (dir / "batch.txt") list
    let r ← IO.Process.output { cmd := exe.toString, args := #["--batch", (dir / "batch.txt").toString] }
    if r.exitCode != 0 then IO.println s!"harness failed:\n{r.stderr.take 2000}"
    for i in [0:interp.size] do
      let (name, ins, it) := interp[i]!
      let outp := dir / s!"out{i}.trace"
      let ct ← if ← outp.pathExists then pure (Trace.parse (← IO.FS.readFile outp)).toOption else pure none
      let ok := match ct with
        | some ct => Fuzz.agree it ct
        | none => false
      if !ok then
        st := { st with failures := st.failures + 1 }
        IO.println s!"FAIL {name}: Ember interpreter vs host C"
        if let some ct := ct then IO.println (diff it ct { observable := false }).report
        saveRegress (name ++ "-c") ins "interpreter vs C"
      IO.FS.removeFile (dir / s!"in{i}.trace") <|> pure ()
      IO.FS.removeFile outp <|> pure ()
  return st

def generated (o : Opts) (exe : Option System.FilePath) (proto : String) : IO Stats := do
  let mut st : Stats := {}
  let mut rng := Rng.ofSeed (o.seed + proto.length * 7919)
  let mut i := 0
  while i < o.count do
    let n := min 200 (o.count - i)
    let mut batch : Array (String × Array Input) := #[]
    for j in [0:n] do
      let (r, rng') := (do
        let base ← match proto with
          | "icmp" => (Except.ok <$> Spec.Gen.ping : RandM _)
          | "udp" => Except.ok <$> Spec.Gen.udp
          | _ => Spec.Gen.tcp
        match base with
        | .error e => return Except.error e
        | .ok s => return .ok (s, ← Spec.Gen.mutate s, ← Spec.Gen.rechunk s)).run rng
      rng := rng'
      let name := s!"net-{proto}-{o.seed}-{i + j}"
      match r with
      | .error (why, _) => IO.println s!"generator: {why}"
      | .ok (s, m, c) =>
        batch := batch.push (name, s.inputs) |>.push (name ++ "-mut", m.inputs) |>.push (name ++ "-chunk", c.inputs)
    st ← checkBatch o exe batch st
    i := i + n
  return st

partial def traceFiles (d : System.FilePath) : IO (Array System.FilePath) := do
  if !(← d.isDir) then return #[d]
  let mut out := #[]
  for e in ← d.readDir do
    if ← e.path.isDir then out := out ++ (← traceFiles e.path)
    else if e.path.extension == some "trace" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  let o := parse args {}
  let exe ← if o.withC then
      if !(← Cc.available) then IO.println "no C compiler; --c ignored"; pure none
      else match ← buildC o.opt with
        | .ok e => pure (some e)
        | .error e => IO.println s!"building the Ember stack's C failed:\n{e}"; return 1
    else pure none
  let mut bad := 0
  if !o.files.isEmpty then
    let mut named := #[]
    let mut skipped := 0
    for f in o.files do
      for p in ← traceFiles f do
        let t ← Trace.readFile p
        if NetCheck.supported t.header then named := named.push (p.toString, t.inputs)
        else skipped := skipped + 1
    let st ← checkBatch o exe named {}
    IO.println s!"files: {st.streams} streams ({skipped} skipped: not SLIP/MTU 296), {st.failures} failures{if exe.isSome then " (Spec = interpreter = C)" else ""}"
    bad := bad + st.failures
  if let some g := o.gen then
    for p in (if g == "all" then ["icmp", "udp", "tcp"] else [g]) do
      let st ← generated o exe p
      IO.println s!"generated {p}: {st.streams} streams, {st.inputs} inputs, {st.failures} failures{if exe.isSome then " (Spec = interpreter = C, lockstep)" else " (lockstep)"}"
      bad := bad + st.failures
  return if bad == 0 then 0 else 1

end Ember.Tools.Lockstep
