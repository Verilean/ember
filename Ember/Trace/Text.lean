import Ember.Trace.Event
import Ember.Util.Str

/-!
# Ember.Trace.Text — printer and parser for the §3.1 format

`parse ∘ print = id` on every trace (tested in `Tests.Ember.TraceTests`).
-/

namespace Ember.Trace

def Header.print (h : Header) : String :=
  s!"# ember-trace v1  impl={h.impl}  build={h.build}  profile={h.profile}  link={h.link}" ++
    (if h.mtu == 296 then "" else s!"  mtu={h.mtu}") ++ (if h.dhcp then "  dhcp=on" else "") ++
    (if h.mask.isEmpty then "" else "  mask=" ++ ",".intercalate h.mask)

def Event.payload : Event → String
  | .rx b | .tx b => Bytes.toHex b
  | .tick => ""
  | .pkt s | .tcb s | .note s => s
  | .drop r => "reason=" ++ r

def Line.print (l : Line) : String :=
  let p := l.ev.payload
  let base := Str.padRight (toString l.step) 6 ++ " " ++ Str.padRight l.ev.kind 4
  if p.isEmpty then Str.trimR base else base ++ " " ++ p

def Trace.print (t : Trace) : String :=
  t.header.print ++ "\n" ++ String.join (t.lines.toList.map (·.print ++ "\n"))

def Header.parse (s : String) : Header := Id.run do
  let mut h : Header := {}
  for w in Str.words s do
    match w.splitOn "=" with
    | ["impl", v] => h := { h with impl := v }
    | ["build", v] => h := { h with build := v }
    | ["profile", v] => h := { h with profile := v }
    | ["link", v] => h := { h with link := v }
    | ["mtu", v] => h := { h with mtu := v.toNat?.getD 296 }
    | ["dhcp", v] => h := { h with dhcp := v == "on" }
    | ["mask", v] => h := { h with mask := (v.splitOn ",").filter (· ≠ "") }
    | _ => pure ()
  return h

/-- Strip a trailing `# comment` (only used on `rx`/`tx` lines, whose
payload is hex and cannot contain `#`). -/
private def stripComment (s : String) : String :=
  match s.splitOn "#" with
  | a :: _ => a
  | [] => s

/-- Text after the first `n` whitespace-separated words, verbatim. -/
private def afterWords (s : String) (n : Nat) : String := Id.run do
  let mut rest := Str.trimL s
  for _ in [0:n] do
    rest := (rest.dropWhile (fun c => !c.isWhitespace)).toString
    rest := Str.trimL rest
  return rest

def Line.parse (lineNo : Nat) (s : String) : Except String Line := do
  let ws := Str.words s
  match ws with
  | stepS :: kind :: _ =>
    let some step := stepS.toNat? | throw s!"line {lineNo}: bad step number '{stepS}'"
    let rest := afterWords s 2
    let ev ← match kind with
      | "rx" | "tx" =>
        match Bytes.ofHex (stripComment rest) with
        | some b => pure (if kind == "rx" then Event.rx b else Event.tx b)
        | none => throw s!"line {lineNo}: bad hex in {kind} line"
      | "tick" => pure Event.tick
      | "pkt" => pure (Event.pkt rest)
      | "tcb" => pure (Event.tcb rest)
      | "note" => pure (Event.note rest)
      | "drop" =>
        if rest.startsWith "reason=" then pure (Event.drop (rest.drop 7).toString)
        else throw s!"line {lineNo}: drop without reason="
      | k => throw s!"line {lineNo}: unknown event kind '{k}'"
    return ⟨step, ev⟩
  | _ => throw s!"line {lineNo}: expected '<step> <kind> ...'"

def Trace.parse (s : String) : Except String Trace := do
  let mut t : Trace := {}
  let mut n := 0
  for raw in s.splitOn "\n" do
    n := n + 1
    let l := Str.trimR raw
    if (Str.trim l).isEmpty then continue
    if l.startsWith "#" then
      if (Str.trimL (l.drop 1).toString).startsWith "ember-trace" then
        t := { t with header := Header.parse l }
      continue
    t := { t with lines := t.lines.push (← Line.parse n l) }
  return t

def Trace.readFile (p : System.FilePath) : IO Trace := do
  match Trace.parse (← IO.FS.readFile p) with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"{p}: {e}")

end Ember.Trace
