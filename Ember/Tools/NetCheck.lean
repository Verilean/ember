import Ember.Net.Main
import Ember.Net.Eth
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

def checked (p : Prog) : Prog := match p.check with
  | .ok q => q
  | .error _ => p

/-- The Net program (SLIP), checked once. -/
def netProg : Prog := checked Net.prog
def ethProg : Prog := checked Net.Eth.prog
def ethDhcpProg : Prog := checked Net.Eth.progDhcp

/-- Is a trace's configuration the SLIP build's (MTU 296)?  The one the
targets run. -/
def supported (h : Header) : Bool := h.link == "slip" && h.mtu == 296 && !h.dhcp

/-- The builds of the Ember stack, by the name of their C unit. -/
def builds : List (String × Prog) :=
  [("net", netProg), ("neteth", ethProg), ("netdhcp", ethDhcpProg), ("neteth296", checked (Net.Eth.progFor false 296))]

/-- The build for a trace's configuration: its index in `builds`. -/
def buildIndex (h : Header) : Option Nat :=
  if supported h then some 0
  else if h.link == "eth" && h.mtu == 576 then some (if h.dhcp then 2 else 1)
  else if h.link == "eth" && h.mtu == 296 && !h.dhcp then some 3
  else none

/-- Is there an Ember build for the configuration? -/
def implemented (h : Header) : Bool := (buildIndex h).isSome

def progFor (h : Header) : Prog := ((buildIndex h).bind fun k => builds[k]?.map (·.2)).getD netProg

def comparable (t : Trace) : Trace :=
  { t with lines := t.lines.filter fun l => match l.ev with
      | .rx _ | .tx _ | .tick | .drop _ => true
      | _ => false }

def runNet (inputs : Array Input) (h : Header := {}) : Lang.Result :=
  runMachine (Machine.init (progFor h) inputs) { h with impl := "ember-interp" } (fuel := 1000000)

def runSpec (inputs : Array Input) (h : Header := {}) : Trace := Spec.run (Spec.Config.ofHeader h) inputs

/-- `none` when the Ember stack agrees with the Spec on these inputs. -/
def compare (inputs : Array Input) (h : Header := {}) : Option String :=
  let s := comparable (runSpec inputs h)
  let r := runNet inputs h
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
   -- (while listening the field is not in use: the Spec sets it at the SYN, the Ember stack at the reset)
   ("t.peer_mss", toString t.peerMss), ("t.our_mss", if t.st.code == 0 then "-" else toString t.ourMss),
   ("t.last_wnd", toString t.lastWnd),
   ("t.rt_timer", toString t.rtTimer), ("t.retries", toString t.retries), ("t.tw_timer", toString t.twTimer),
   ("t.idle", toString t.idle), ("t.close_req", toString (if t.closeReq then 1 else 0)),
   ("iss", toString s.iss.toNat), ("ip_id", toString s.ipId.toNat),
   ("ip", toString s.ip.toNat)] ++
  (match s.cfg.link with
   | .slip =>
     [("slip.len", toString s.slip.buf.size), ("slip.esc", toString (if s.slip.esc then 1 else 0)),
      ("slip.over", toString (if s.slip.over then 1 else 0)),
      ("slip.buf", toString (s.slip.buf.toList.map (·.toNat))),
      ("tick_due", toString (if s.tickDue then 1 else 0))]
   | .eth =>
     [("arp", toString (s.arp.entries.toList.map fun (e : UInt32 × ByteArray) =>
        (e.1.toNat, e.2.toList.map fun (b : UInt8) => b.toNat))),
      ("arp.next", toString s.arp.next),
      ("dhcp.phase", toString (match s.dhcp.phase with | .init => 0 | .selecting => 1 | .requesting => 2 | .bound => 3)),
      ("dhcp.xid", toString s.dhcp.xid.toNat), ("dhcp.server", toString s.dhcp.server.toNat),
      ("dhcp.offered", toString s.dhcp.offered.toNat), ("dhcp.timer", toString s.dhcp.timer)])

def netView (m : Machine) (eth := false) : List (String × String) :=
  let f := field m "t"
  let plen := f "pend_len"
  let len := u (m.global? "len")
  let g (x : String) := toString (u (m.global? x))
  [("t.st", toString (f "st")), ("t.rip", toString (f "rip")), ("t.rport", toString (f "rport")),
   ("t.snd_una", toString (f "snd_una")), ("t.snd_nxt", toString (f "snd_nxt")),
   ("t.rcv_nxt", toString (f "rcv_nxt")), ("t.pend", toString (arrBytes m "pend" plen)),
   ("t.sent", toString (f "sent")), ("t.fin_sent", toString (f "fin_sent")),
   ("t.peer_mss", toString (f "peer_mss")), ("t.our_mss", if f "st" == 0 then "-" else toString (f "our_mss")),
   ("t.last_wnd", toString (f "last_wnd")), ("t.rt_timer", toString (f "rt_timer")),
   ("t.retries", toString (f "retries")), ("t.tw_timer", toString (f "tw_timer")),
   ("t.idle", toString (f "idle")), ("t.close_req", toString (f "close_req")),
   ("iss", toString (u (m.global? "iss"))), ("ip_id", toString (u (m.global? "ip_id"))),
   ("ip", g "OUR_IP")] ++
  (if !eth then
     [("slip.len", toString len), ("slip.esc", g "esc"), ("slip.over", g "over"),
      ("slip.buf", toString (arrBytes m "buf" len)), ("tick_due", g "tick_due")]
   else
     let n := u (m.global? "arp_n")
     let ips := arrBytes m "arp_ip" n
     let macs := arrBytes m "arp_mac" (6 * n)
     [("arp", toString ((List.range n).map fun k => (ips.getD k 0, (macs.drop (6 * k)).take 6))),
      ("arp.next", g "arp_next"), ("dhcp.phase", g "d_phase"), ("dhcp.xid", g "d_xid"),
      ("dhcp.server", g "d_server"), ("dhcp.offered", g "d_offered"), ("dhcp.timer", g "d_timer")])

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
def lockstepTrace (inputs : Array Input) (h : Header := {}) : Option String × Trace := Id.run do
  let netProg := progFor h
  let mut s := Spec.State.init (Spec.Config.ofHeader h)
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
      if let some e := e? then return (some s!"input {i}: Ember stack trapped: {e}", worldTrace m h)
    let a := specView s
    let b := netView m (h.link == "eth")
    let diffs := (a.zip b).filter fun ((_, x), (_, y)) => x != y
    if !diffs.isEmpty then
      let what := ", ".intercalate (diffs.map fun ((k, x), (_, y)) => s!"{k}: spec {x} vs ember {y}")
      return (some s!"states differ after input {i} ({match inputs[i]! with | .tick => "tick" | .rx b => s!"rx {b.size} bytes"}): {what}", worldTrace m h)
  return (none, worldTrace m { h with impl := "ember-interp" })

def lockstep (inputs : Array Input) (h : Header := {}) : Option String := (lockstepTrace inputs h).1

/-- Lockstep and trace comparison in one run of each implementation. -/
def check (inputs : Array Input) (h : Header := {}) : Option String × Trace :=
  let (l, t) := lockstepTrace inputs h
  match l with
  | some e => (some e, t)
  | none =>
    let d := diff (comparable (runSpec inputs h)) (comparable t) { observable := false, context := 2 }
    (if d.equal then none else some d.report, t)

end Ember.Tools.NetCheck
