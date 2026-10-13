import Ember.Util.Bytes

/-!
# Ember.Trace.Event

The one trace format shared by every Ember implementation (plan §3.1):

```
# ember-trace v1  impl=spec  build=<sha>  profile=host64  link=slip
0      rx   c0 45 00 00 54 ...
0      pkt  rx ipv4 10.0.0.2>10.0.0.1 icmp echo-req id=1 seq=1 len=84
0      tx   c0 45 00 00 54 ...
17     tick
17     drop reason=bad-ip-checksum
```

`rx`, `tx` and `tick` are *observable*; `pkt`, `tcb`, `drop` and `note`
are *diagnostic*.  The first column is the step number: the index of the
input (an `rx` chunk or a `tick`) being consumed.
-/

namespace Ember.Trace

inductive Event where
  | rx   (bytes : ByteArray)
  | tx   (bytes : ByteArray)
  | tick
  | pkt  (text : String)
  | tcb  (text : String)
  | drop (reason : String)
  | note (text : String)
  deriving Inhabited

instance : BEq Event where
  beq
    | .rx a, .rx b | .tx a, .tx b => a.toList == b.toList
    | .tick, .tick => true
    | .pkt a, .pkt b | .tcb a, .tcb b | .drop a, .drop b | .note a, .note b => a == b
    | _, _ => false

def Event.isObservable : Event → Bool
  | .rx _ | .tx _ | .tick => true
  | _ => false

def Event.kind : Event → String
  | .rx _ => "rx" | .tx _ => "tx" | .tick => "tick"
  | .pkt _ => "pkt" | .tcb _ => "tcb" | .drop _ => "drop" | .note _ => "note"

/-- Is the text of a `note` that of a trap, not of a note of the program?
A trap is written `trap` or `trap <where>`, differently by each
implementation; a note of the program is `<name> <value>`, the value in
decimal.  So `trapdoor 1` is a program's note, and so is `trap 1` (a
note the program named `trap`): only `trap` alone, or followed by
something that is not a number, is a trap. -/
def isTrapNote (s : String) : Bool :=
  s == "trap" || (s.startsWith "trap " &&
    (let r := (s.drop 5).toString; r.isEmpty || !r.all Char.isDigit))

structure Line where
  step : Nat
  ev   : Event
  deriving Inhabited, BEq

structure Header where
  impl    : String := "spec"
  build   : String := "dev"
  profile : String := "host64"
  link    : String := "slip"
  /-- Fields normalised before comparison (`ipv4.id`): set on fixtures
  recorded from Linux, whose IP identification is not reproducible. -/
  mask    : List String := []
  /-- Stack configuration: MTU (printed when not 296) and DHCP client. -/
  mtu     : Nat := 296
  dhcp    : Bool := false
  deriving Inhabited, BEq, Repr

structure Trace where
  header : Header := {}
  lines  : Array Line := #[]
  deriving Inhabited

/-- Inputs of a stack: a chunk of link bytes, or one timer tick. -/
inductive Input where
  | rx (bytes : ByteArray)
  | tick
  deriving Inhabited

instance : BEq Input where
  beq
    | .rx a, .rx b => a.toList == b.toList
    | .tick, .tick => true
    | _, _ => false

def Trace.observable (t : Trace) : Array Line :=
  t.lines.filter (·.ev.isObservable)

/-- The input sequence recorded in a trace (its `rx` and `tick` lines). -/
def Trace.inputs (t : Trace) : Array Input :=
  t.lines.filterMap fun l => match l.ev with
    | .rx b => some (.rx b)
    | .tick => some .tick
    | _ => none

/-- Build a trace from inputs and, per input, the events it produced. -/
def Trace.ofSteps (h : Header) (steps : Array (Input × List Event)) : Trace := Id.run do
  let mut ls : Array Line := #[]
  for i in [0:steps.size] do
    let (inp, evs) := steps[i]!
    let e : Event := match inp with | .rx b => .rx b | .tick => .tick
    ls := ls.push ⟨i, e⟩
    for ev in evs do ls := ls.push ⟨i, ev⟩
  return { header := h, lines := ls }

end Ember.Trace
