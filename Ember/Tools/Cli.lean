import Ember.Trace.Diff
import Ember.Util.Pcap
import Ember.Spec.Stack

/-!
# Command-line tools: `ember-diff`, `ember-pcap`, `ember-replay`
-/

namespace Ember.Tools
open Ember Ember.Trace

/-- `ember-diff A.trace B.trace [--observable | --drops] [--context N] [--first-only] [--all]`
(`--drops`: observable events and drop reasons);
exit status 0 when the traces agree, 1 when they differ, 2 on bad usage. -/
def diffMain (args : List String) : IO UInt32 := do
  let rec go : List String → DiffOpts → List String → Except String (DiffOpts × List String)
    | [], o, fs => .ok (o, fs.reverse)
    | "--observable" :: r, o, fs => go r { o with observable := true } fs
    | "--drops" :: r, o, fs => go r { o with observable := true, drops := true } fs
    | "--context" :: n :: r, o, fs => match n.toNat? with
      | some v => go r { o with context := v } fs
      | none => .error s!"bad --context {n}"
    | "--first-only" :: r, o, fs => go r { o with firstOnly := true } fs
    | "--all" :: r, o, fs => go r { o with all := true } fs
    | a :: r, o, fs => if a.startsWith "--" then .error s!"unknown option {a}" else go r o (a :: fs)
  match go args { observable := false } [] with
  | .error e => IO.eprintln e; return 2
  | .ok (o, [fa, fb]) =>
    let a ← Trace.readFile fa
    let b ← Trace.readFile fb
    let r := diff a b o
    IO.println r.report
    return if r.equal then 0 else 1
  | .ok _ =>
    IO.eprintln "usage: ember-diff A.trace B.trace [--observable | --drops] [--context N] [--first-only] [--all]"
    return 2

/-- `ember-pcap X.trace > X.pcap` -/
def pcapMain (args : List String) : IO UInt32 := do
  match args with
  | [f] =>
    let t ← Trace.readFile f
    let out ← IO.getStdout
    out.write (Pcap.ofTrace t)
    out.flush
    return 0
  | _ => IO.eprintln "usage: ember-pcap X.trace > X.pcap"; return 2

def specConfigOf (h : Header) : Spec.Config := Spec.Config.ofHeader h

/-- `ember-replay [--write] F.trace...`: run each fixture's inputs through
`Ember.Spec` and compare with its observable events; `--write` rewrites
the fixture with the Spec's full trace (for regenerating goldens). -/
def replayMain (args : List String) : IO UInt32 := do
  let write := args.contains "--write"
  let files := args.filter (· != "--write")
  let mut bad := 0
  for f in files do
    let t ← Trace.readFile f
    let r := Spec.run (specConfigOf t.header) t.inputs
    let r := { r with header := { r.header with profile := t.header.profile, build := t.header.build } }
    if write then
      IO.FS.writeFile f r.print
      IO.println s!"wrote {f}"
    else
      let d := diff t r { observable := true }
      if d.equal then IO.println s!"ok   {f}"
      else
        bad := bad + 1
        IO.println s!"FAIL {f}\n{d.report}"
  return if bad == 0 then 0 else 1

end Ember.Tools
