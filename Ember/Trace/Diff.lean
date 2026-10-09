import Ember.Trace.Text
import Ember.Util.Pretty
import Ember.Spec.Checksum

/-!
# Ember.Trace.Diff — first-divergence comparison of two traces

Traces are compared line by line, on the observable events only
(`--observable`) or on all of them.  The report names the first
differing line of each trace, shows context from both, and decodes the
differing packets field by field (`ipv4.ttl: 64 vs 63`), so a divergence
is explained rather than just located.
-/

namespace Ember.Trace
open Ember

structure DiffOpts where
  observable : Bool := true
  context    : Nat := 3
  firstOnly  : Bool := false
  all        : Bool := false
  /-- Fields to normalise in both traces (see `Header.mask`). -/
  mask       : List String := []

structure DiffResult where
  equal  : Bool
  report : String
  /-- Index (into the compared lines) of the first difference. -/
  first  : Option Nat := none

private def payloadBytes : Event → Option ByteArray
  | .rx b | .tx b => some b
  | _ => none

/-- Field-by-field explanation of two differing `rx`/`tx` payloads. -/
def explainBytes (link : String) (a b : ByteArray) : List String := Id.run do
  let la := a.data
  let lb := b.data
  let mut out : Array String := #[]
  let n := min la.size lb.size
  let firstByte := (List.range n).find? fun i => la[i]! != lb[i]!
  match firstByte with
  | some i => out := out.push s!"first differing byte at offset {i}: {Bytes.hex8 la[i]!} vs {Bytes.hex8 lb[i]!}"
  | none => if la.size != lb.size then
      out := out.push s!"lengths differ: {la.size} vs {lb.size} bytes (common prefix equal)"
  let fa := Pretty.frames link a
  let fb := Pretty.frames link b
  if fa.length != fb.length then
    out := out.push s!"frame count differs: {fa.length} vs {fb.length}"
  for (x, y) in fa.zip fb do
    let ga := Pretty.fields link x
    let gb := Pretty.fields link y
    for (k, v) in ga do
      match gb.lookup k with
      | some w => if v != w then out := out.push s!"{k}: {v} vs {w}"
      | none => out := out.push s!"{k}: {v} vs (absent)"
    for (k, w) in gb do
      if (ga.lookup k).isNone then out := out.push s!"{k}: (absent) vs {w}"
  return out.toList

def explain (link : String) (a b : Line) : List String :=
  match payloadBytes a.ev, payloadBytes b.ev with
  | some x, some y => explainBytes link x y
  | _, _ =>
    if a.ev.kind != b.ev.kind then [s!"event kind: {a.ev.kind} vs {b.ev.kind}"]
    else if a.step != b.step then [s!"step: {a.step} vs {b.step}"]
    else [s!"payload: '{a.ev.payload}' vs '{b.ev.payload}'"]

private def contextOf (t : Trace) (target : Option Line) (n : Nat) : List String := Id.run do
  let some l := target | return ["  (end of trace)"]
  -- locate the full-trace line index of `l` (first equal line, by step)
  let ls := t.lines
  let idx := (ls.findIdx? fun x => x == l).getD 0
  let lo := idx - min idx n
  let hi := min ls.size (idx + n + 1)
  let mut out := #[]
  for i in [lo:hi] do
    out := out.push ((if i == idx then "> " else "  ") ++ ls[i]!.print)
  return out.toList

/-- Zero the IP identification of a packet whose header checksum is
valid, and recompute the checksum; a packet with a bad checksum is left
alone so that the error still shows. -/
def maskIpId (p : ByteArray) : ByteArray :=
  if p.size < 20 then p else
  let ihl := ((Bytes.get p 0) &&& 0x0F).toNat * 4
  if ihl < 20 || ihl > p.size || !Spec.Checksum.verifies (Spec.Checksum.sum p 0 ihl) then p
  else
    let q := Bytes.set16 (Bytes.set16 p 4 0) 10 0
    Bytes.set16 q 10 (Spec.Checksum.checksum q 0 ihl)

def normalize (link : String) (mask : List String) (l : Line) : Line :=
  if !mask.contains "ipv4.id" then l else
  let fix (b : ByteArray) : ByteArray :=
    if link == "eth" then
      if b.size ≥ 34 && Bytes.get16 b 12 == 0x0800 then b.extract 0 14 ++ maskIpId (b.extract 14 b.size)
      else b
    else (Pretty.frames link b).foldl (fun acc f => acc ++ Spec.Slip.encode (maskIpId f)) .empty
  match l.ev with
  | .rx b => { l with ev := .rx (fix b) }
  | .tx b => { l with ev := .tx (fix b) }
  | _ => l

def diff (a b : Trace) (o : DiffOpts := {}) : DiffResult := Id.run do
  let mask := o.mask ++ a.header.mask ++ b.header.mask
  let sel (t : Trace) := (if o.observable then t.observable else t.lines).map (normalize t.header.link mask)
  let xs := sel a
  let ys := sel b
  let link := a.header.link
  let n := max xs.size ys.size
  let mut report : Array String := #[]
  let mut first : Option Nat := none
  let mut count := 0
  for i in [0:n] do
    let x := xs[i]?
    let y := ys[i]?
    if x == y then continue
    count := count + 1
    if first.isNone then first := some i
    let showL (l : Option Line) := (l.map (·.print)).getD "(end of trace)"
    if o.firstOnly then
      report := report.push s!"#{i}: A: {showL x} | B: {showL y}"
      break
    report := report.push s!"difference at {if o.observable then "observable " else ""}event #{i}"
    report := report.push s!"  A: {showL x}"
    report := report.push s!"  B: {showL y}"
    if let (some x', some y') := (x, y) then
      for e in explain link x' y' do report := report.push ("    " ++ e)
    if o.context > 0 then
      report := report.push s!"  context A ({a.header.impl}):"
      for c in contextOf a x o.context do report := report.push ("    " ++ c)
      report := report.push s!"  context B ({b.header.impl}):"
      for c in contextOf b y o.context do report := report.push ("    " ++ c)
    if !o.all then break
  if count == 0 then
    return { equal := true, report := s!"traces agree ({xs.size} {if o.observable then "observable " else ""}events)" }
  return { equal := false, report := "\n".intercalate report.toList, first }

end Ember.Trace
