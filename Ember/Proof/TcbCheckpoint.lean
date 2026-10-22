import Ember.Proof.Driver
import Ember.Z80.TcbObs

/-!
# Ember.Proof.TcbCheckpoint — the connection's state between input items (plan M7.3, `tcb` lines)

The Spec writes a `tcb` line (`Spec.Tcp.logTcb`) with the text
`Tcb.describe` of its control block at the end of some TCP actions: a
segment through `Tcp.input`, a tick through `Tcp.tick`.  The Ember
program writes no such line; its trace has transmissions, drops and
notes.  Here, the state those lines describe, where the Ember program
holds it:

* **the observation point** — between two input items, after a call of
  `main` (`mainIter`): the global `t` holds the connection record and
  `pend` the echo buffer (`TcpHolds`), and the two hold the Spec's
  control block after the same items (`TcbRel`, `StRel`: `MainInv`,
  `main_run`);
* **the fields and their order** — `RawTcb.describe` writes, of the
  record, what `Tcb.describe` writes of the control block: the state by
  its name, `snd.una`, `snd.nxt`, `rcv.nxt`, the length of the pending
  bytes, `sent`, the retransmission timer and the retries, in that order,
  in the same words (`TcbRel.describe_eq`);
* `tcb_checkpoint` — **after every item, not only the last**, the record
  the Ember semantics holds describes as the Spec's control block after
  the same items.

What this is not: a `tcb` line is written inside a step, and one item
can write two (`Spec.byteInput`: a byte ends a frame, `Tcp.input` logs,
then a tick that waited for the end of the frame logs again; or a tick
that gives up a frame runs `tickInput` twice), so the state after the
item is the state of the last line it wrote, not of every line.  And
items are not inputs: a chunk of bytes is one item per byte.  Not here
either: the lines themselves (the program writes none), the IR's memory
and the Z80's RAM at these points.
-/

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem
open Ember.Z80.TcbObs (stName)

/-- What a `tcb` line says of the connection record: `Tcb.describe`'s
fields, in its order and words. -/
def RawTcb.describe (r : RawTcb) : String :=
  s!"state={stName r.st} snd.una={r.snd_una} snd.nxt={r.snd_nxt} rcv.nxt={r.rcv_nxt} pending={r.pend_len.toNat} sent={r.sent.toNat} rt={r.rt_timer.toNat}/{r.retries.toNat}"

theorem stName_code (s : Spec.Tcp.St) : stName (UInt8.ofNat s.code) = s.toString := by
  cases s <;> rfl

/-- **The record describes as the control block it holds.** -/
theorem TcbRel.describe_eq {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    r.describe = T.describe := by
  unfold RawTcb.describe Spec.Tcp.Tcb.describe
  rw [h.st, stName_code, h.una, h.nxt, h.rcv, h.plen, h.sent, h.rt, h.re]

/-- The Spec's state after the first `k` items of the input. -/
def specAfter (inputs : Array Trace.Input) (k : Nat) : Spec.State :=
  (runTagged ((later inputs 0).take k) ⟨Spec.State.init {}, #[], 0, []⟩).s

/-- **The connection between input items**: after `j + 1` calls of
`main` (the first boots and reads the first item; each reads one), the
globals `t` and `pend` of the Ember semantics hold a connection record
and an echo buffer that hold the Spec's control block after the same
items — and the record describes as it does. -/
theorem tcb_checkpoint (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (inputs : Array Trace.Input) (n j : Nat) :
    ∃ (st' : St) (r : RawTcb) (pd : ByteArray),
      mainIter (n + 4716) p (j + 1) (Sem.initial Net.prog inputs) = some st' ∧
      st'.globals.lookup "t" = some r.val ∧ st'.globals.lookup "pend" = some (bufVal pd) ∧
      TcbRel r pd (specAfter inputs (j + 1)).tcb ∧
      r.describe = (specAfter inputs (j + 1)).tcb.describe := by
  obtain ⟨st', w', hit, hinv, _, _⟩ := main_run p hP hR hp inputs n j
  exact ⟨st', w'.r, w'.pd, hit, hinv.net.holds.t, hinv.net.holds.pend, hinv.net.rel.tcb,
    hinv.net.rel.tcb.describe_eq⟩

/-- info: 'Ember.Proof.Refine.tcb_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcb_checkpoint

-- the names are the Spec's
#guard (List.range 9).all fun c =>
  [Spec.Tcp.St.listen, .synRcvd, .established, .closeWait, .lastAck, .finWait1, .finWait2, .closing,
    .timeWait].any fun s => s.code = c && stName (UInt8.ofNat c) == s.toString

end Ember.Proof.Refine
