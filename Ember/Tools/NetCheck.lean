import Ember.Net.Main
import Ember.Spec.Stack
import Ember.Lang.Eval
import Ember.Trace.Diff
import Ember.Trace.Text

/-!
# Ember.Tools.NetCheck — `Ember.Net` against `Ember.Spec`

* `compare`: the observable lines and the `drop` reasons of both traces
  (the Net program has no `pkt`/`tcb` lines; its notes are its own);
* `lockstep` (plan M3, debug aid): both implementations consume the same
  inputs and their *states* are compared after every input — TCB fields,
  the echo buffer, the IP identification, the ISS counter, the SLIP
  receiver — so a divergence is caught where it starts.
-/

namespace Ember.Tools.NetCheck
open Ember Ember.Lang Ember.Trace

/-- The Net program, checked once. -/
def netProg : Prog := match Net.prog.check with
  | .ok p => p
  | .error _ => Net.prog

/-- Is a trace's configuration one the Ember stack implements (SLIP, MTU 296)? -/
def supported (h : Header) : Bool := h.link == "slip" && h.mtu == 296 && !h.dhcp

def comparable (t : Trace) : Trace :=
  { t with lines := t.lines.filter fun l => match l.ev with
      | .rx _ | .tx _ | .tick | .drop _ => true
      | _ => false }

def runNet (inputs : Array Input) : Lang.Result :=
  runMachine (Machine.init netProg inputs) { impl := "ember-interp" } (fuel := 1000000)

def runSpec (inputs : Array Input) : Trace := Spec.run {} inputs

/-- `none` when the Ember stack agrees with the Spec on these inputs. -/
def compare (inputs : Array Input) : Option String :=
  let s := comparable (runSpec inputs)
  let r := runNet inputs
  if let some e := r.error then some s!"Ember stack trapped: {e}" else
  let d := diff s (comparable r.trace) { observable := false, context := 2 }
  if d.equal then none else some d.report

/-! ## Lockstep -/

def u (v : Option Val) : Nat := (v.map Val.toNat).getD 0

def field (m : Machine) (g f : String) : Nat :=
  match m.global? g, m.prog.struct? (if g == "t" then "Tcb" else "Seg") with
  | some (.record _ fs), some sd =>
    match sd.fields.findIdx? (·.1 == f) with
    | some i => (fs[i]?.map Val.toNat).getD 0
    | none => 0
  | _, _ => 0

def arrBytes (m : Machine) (g : String) (n : Nat) : List Nat :=
  match m.global? g with
  | some (.arr xs) => (xs.toList.take n).map Val.toNat
  | _ => []

/-- The projection of both states onto the fields they share. -/
def specView (s : Spec.State) : List (String × String) :=
  let t := s.tcb
  [("t.st", toString t.st.code), ("t.rip", toString t.rip.toNat), ("t.rport", toString t.rport.toNat),
   ("t.snd_una", toString t.sndUna.toNat), ("t.snd_nxt", toString t.sndNxt.toNat),
   ("t.rcv_nxt", toString t.rcvNxt.toNat), ("t.pend", toString (t.pending.toList.map (·.toNat))),
   ("t.sent", toString t.sent), ("t.fin_sent", toString (if t.finSent then 1 else 0)),
   ("t.peer_mss", toString t.peerMss), ("t.our_mss", toString t.ourMss), ("t.last_wnd", toString t.lastWnd),
   ("t.rt_timer", toString t.rtTimer), ("t.retries", toString t.retries), ("t.tw_timer", toString t.twTimer),
   ("t.idle", toString t.idle), ("t.close_req", toString (if t.closeReq then 1 else 0)),
   ("iss", toString s.iss.toNat), ("ip_id", toString s.ipId.toNat),
   ("slip.len", toString s.slip.buf.size), ("slip.esc", toString (if s.slip.esc then 1 else 0)),
   ("slip.over", toString (if s.slip.over then 1 else 0)),
   ("slip.buf", toString (s.slip.buf.toList.map (·.toNat)))]

def netView (m : Machine) : List (String × String) :=
  let f := field m "t"
  let plen := f "pend_len"
  let len := u (m.global? "len")
  [("t.st", toString (f "st")), ("t.rip", toString (f "rip")), ("t.rport", toString (f "rport")),
   ("t.snd_una", toString (f "snd_una")), ("t.snd_nxt", toString (f "snd_nxt")),
   ("t.rcv_nxt", toString (f "rcv_nxt")), ("t.pend", toString (arrBytes m "pend" plen)),
   ("t.sent", toString (f "sent")), ("t.fin_sent", toString (f "fin_sent")),
   ("t.peer_mss", toString (f "peer_mss")), ("t.our_mss", toString (f "our_mss")),
   ("t.last_wnd", toString (f "last_wnd")), ("t.rt_timer", toString (f "rt_timer")),
   ("t.retries", toString (f "retries")), ("t.tw_timer", toString (f "tw_timer")),
   ("t.idle", toString (f "idle")), ("t.close_req", toString (f "close_req")),
   ("iss", toString (u (m.global? "iss"))), ("ip_id", toString (u (m.global? "ip_id"))),
   ("slip.len", toString len), ("slip.esc", toString (u (m.global? "esc"))),
   ("slip.over", toString (u (m.global? "over"))), ("slip.buf", toString (arrBytes m "buf" len))]

/-- The trace of a machine's world (as `runMachine` builds it). -/
def worldTrace (m : Machine) (h : Header) : Trace := Id.run do
  let w := m.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    let e0 : Event := match w.inputs[i]! with | .rx b => .rx b | .tick => .tick
    lines := lines.push ⟨i, e0⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  return { header := h, lines }

/-- Run both side by side, comparing states after every input; the first
divergence, if any, and the Ember stack's trace. -/
def lockstepTrace (inputs : Array Input) : Option String × Trace := Id.run do
  let mut s := Spec.State.init {}
  let mut m := Machine.init netProg inputs
  -- the first call boots the Net program (tcb_reset) before it reads input
  for i in [0:inputs.size] do
    let (s', _) := Spec.step s inputs[i]!
    s := s'
    -- call the entry until input i is consumed
    let mut calls := 0
    while m.world.normalize.pos ≤ i && calls < 100000 do
      let (e?, m') := m.callFn' netProg.entry
      m := m'
      calls := calls + 1
      if let some e := e? then return (some s!"input {i}: Ember stack trapped: {e}", worldTrace m {})
    let a := specView s
    let b := netView m
    let diffs := (a.zip b).filter fun ((_, x), (_, y)) => x != y
    if !diffs.isEmpty then
      let what := ", ".intercalate (diffs.map fun ((k, x), (_, y)) => s!"{k}: spec {x} vs ember {y}")
      return (some s!"states differ after input {i} ({match inputs[i]! with | .tick => "tick" | .rx b => s!"rx {b.size} bytes"}): {what}", worldTrace m {})
  return (none, worldTrace m { impl := "ember-interp" })

def lockstep (inputs : Array Input) : Option String := (lockstepTrace inputs).1

/-- Lockstep and trace comparison in one run of each implementation. -/
def check (inputs : Array Input) : Option String × Trace :=
  let (l, t) := lockstepTrace inputs
  match l with
  | some e => (some e, t)
  | none =>
    let d := diff (comparable (runSpec inputs)) (comparable t) { observable := false, context := 2 }
    (if d.equal then none else some d.report, t)

end Ember.Tools.NetCheck
