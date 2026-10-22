import Ember.Z80.Machine
import Ember.Z80.IRSem
import Ember.Z80.Codegen
import Ember.Net.Layout

/-!
# Ember.Z80.TcbObs — `tcb` lines read from the RAM at the head of the harness's loop

An observation mode of its own, apart from `Target.runHarness` (whose
trace it does not change): the machine runs as the harness runs it, and
at every **head of the loop** — the CPU at the label `rt_main` with its
stack empty and not halted (`obsAt`) — the observer takes the machine.
The first such point is before the first call of `main`; it is left
out.  Each of the others follows a call of `main`, which reads one input
item (a byte or a tick); for it the observer writes one line:

* **position** — the line's step is the number of the input whose item
  that call read (`Machine.cur`);
* **text** — `tcb` with the fields of `Spec.Tcp.Tcb.describe`, in its
  order and words, read from the connection record `t` in the RAM
  (`describeAt`: the state, `snd.una`, `snd.nxt`, `rcv.nxt`, the length
  of the pending bytes, `sent`, the retransmission timer and the
  retries);
* **count and order** — one line per item, in the order of the items;
  the observer fails unless it saw exactly one head of the loop more
  than there are items (`run`).

The address of `t` and of `rt_main` come from the image as built
(`addrsOf`), which checks first that the program's `t` is the record
`Tcb` of `Ember.Net` (the same fields, types and order) — another
program, or another layout of the record, is refused, not misread.

These are snapshots between items: the Spec writes its `tcb` lines
inside an item (`logTcb`), none for some items, two for others (a byte
that ends a frame, then a tick that waited for it).  The observer's
line for an item is the state after the item — what the Spec's last
line for it says, when there is one — not the Spec's lines.
-/

namespace Ember.Z80.TcbObs
open Ember Ember.Trace
open Ember.Z80.IR.Sem (rd)

/-- The name of a state by its code, as `Spec.Tcp.St.toString` names it. -/
def stName (c : UInt8) : String :=
  if c = 0 then "LISTEN" else if c = 1 then "SYN-RCVD" else if c = 2 then "ESTABLISHED"
  else if c = 3 then "CLOSE-WAIT" else if c = 4 then "LAST-ACK" else if c = 5 then "FIN-WAIT-1"
  else if c = 6 then "FIN-WAIT-2" else if c = 7 then "CLOSING" else if c = 8 then "TIME-WAIT" else "?"

/-- What a `tcb` line says of the record `Tcb` at `a` (35 bytes,
little-endian, the fields in the order of `Ember.Net.Tcb`). -/
def describeAt (m : ByteArray) (a : Nat) : String :=
  s!"state={stName (UInt8.ofNat (rd m a 1))} snd.una={UInt32.ofNat (rd m (a + 7) 4)} snd.nxt={UInt32.ofNat (rd m (a + 11) 4)} rcv.nxt={UInt32.ofNat (rd m (a + 15) 4)} pending={rd m (a + 19) 2} sent={rd m (a + 21) 2} rt={rd m (a + 30) 1}/{rd m (a + 31) 1}"

/-- The head of the loop: the CPU at `lh`, its stack empty, not halted. -/
def obsAt (lh : Nat) (m : Machine) : Bool := m.cpu.pc.toNat == lh && m.cpu.sp == 0 && !m.cpu.halted

/-- The machine at every head of the loop until the CPU halts (at most
`fuel` steps; the machine where it stopped when it did not halt).  What
the observer means, for the proofs; not run: it keeps every machine it
returns, the RAM of each (`scan` is what runs). -/
def obsList (lh : Nat) : Nat → Machine → Except Machine (List Machine)
  | fuel, m =>
    if m.cpu.halted then .ok []
    else match fuel with
      | 0 => .error m
      | f + 1 => (obsList lh f m.step).map fun l => if obsAt lh m then m :: l else l

/-- The number of input items: a byte of a chunk, or a tick. -/
def itemCount (inputs : Array Input) : Nat :=
  (inputs.toList.map fun x => match x with | .rx b => b.size | .tick => 1).sum

/-- The observer's line for the machine `m` at a head of the loop. -/
def lineAt (tAddr : Nat) (m : Machine) : Line := ⟨m.cur, .tcb (describeAt m.cpu.mem tAddr)⟩

/-- `obsList` as it runs: one step at a time (a loop, the call in tail
position), the line of each head of the loop written there and only the
lines kept, last first, after `acc`; the machine itself is not kept, so
its RAM is updated in place.  `scan_eq` (`Z80StackHTcbObs`): the lines
of the machines `obsList` gives, reversed, the same stop. -/
def scan (lh tAddr : Nat) : Nat → Machine → List Line → Except Machine (List Line)
  | fuel, m, acc =>
    if m.cpu.halted then .ok acc
    else match fuel with
      | 0 => .error m
      | f + 1 =>
        let acc := if obsAt lh m then lineAt tAddr m :: acc else acc
        scan lh tAddr f m.step acc

/-- What `run` gives, from `obsList`: the definition the proofs read
(`run_eq`: the same). -/
def runList (m : Machine) (k : Nat) (inputs : Array Input) (tAddr lh : Nat) (maxSteps : Nat := 200000000) :
    Except String (List Line) :=
  match obsList lh maxSteps { m with harness := true, inputs := inputs, program := UInt8.ofNat k } with
  | .error m => .error s!"still running after {maxSteps} instructions (pc={m.cpu.pc})"
  | .ok ms =>
    if ms.length = itemCount inputs + 1 then
      .ok ((ms.drop 1).map fun m => ⟨m.cur, .tcb (describeAt m.cpu.mem tAddr)⟩)
    else .error s!"tcb observer: {ms.length} heads of the loop for {itemCount inputs} items"

/-- The `tcb` lines of program `k` of a harness image on the inputs: one
per item, from the record at `tAddr`, the head of the loop at `lh`
(`scan`; the memory it keeps is the lines). -/
def run (m : Machine) (k : Nat) (inputs : Array Input) (tAddr lh : Nat) (maxSteps : Nat := 200000000) :
    Except String (List Line) :=
  match scan lh tAddr maxSteps { m with harness := true, inputs := inputs, program := UInt8.ofNat k } [] with
  | .error m => .error s!"still running after {maxSteps} instructions (pc={m.cpu.pc})"
  | .ok acc =>
    let ls := acc.reverse
    if ls.length = itemCount inputs + 1 then .ok (ls.drop 1)
    else .error s!"tcb observer: {ls.length} heads of the loop for {itemCount inputs} items"

/-- The address of `t` and of the head of the loop in an image of `p`:
refused unless `t` is the record `Tcb` of `Ember.Net` and placed. -/
def addrsOf (p : Lang.Prog) (img : Codegen.Image) : Except String (Nat × Nat) := do
  unless p.struct? "Tcb" == some Net.Tcb do throw "tcb observer: the record Tcb is not Ember.Net's"
  unless (p.global? "t").map (·.ty) == some (.record "Tcb") do throw "tcb observer: no global t of type Tcb"
  let some t := img.layout.globals.lookup "t" | throw "tcb observer: t is not in the layout"
  let some lh := img.labels.lookup "rt_main" | throw "tcb observer: no rt_main"
  return (t, lh)

end Ember.Z80.TcbObs
