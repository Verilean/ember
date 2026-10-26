import Ember.Spec.Tcp.Timer

/-!
# Ember.Proof.Tcp — invariants of the TCP state machine (plan M5.3)

About `Tcp.input` (a segment arrives) and `Tcp.tick`, the two actions
that change the control block; `Ember.Proof.Stack` lifts the results to
`Spec.step`.

* `Inv` is an inductive invariant of the control block (`input_inv`,
  `tick_inv`).  It contains `snd.una ≤ snd.nxt` in the precise form
  `snd.nxt − snd.una = sent + (1 for an unacknowledged SYN or FIN)`
  (`Inv.seqGe`, `Inv.flight_le`), that the echo buffer never exceeds its
  capacity, and that it holds data only in ESTABLISHED, CLOSE-WAIT and
  LAST-ACK.
* Delivery: a segment adds bytes to the echo buffer only in ESTABLISHED,
  or in SYN-RCVD when its ACK completes the handshake (`input_delivery`,
  `input_pending`); a tick never does (`tick_pending`).
* Acceptance: a segment that is not `acceptable` changes nothing in the
  connection (`input_not_acceptable`), and an accepted one advances
  `rcv.nxt` by at most the window, widened by what the segment itself
  acknowledges, plus one for a FIN (`input_window`).

Method.  `wp m Q c` runs the action `m` from `c` and states `Q` of the
result; simp lemmas for the primitives turn a `wp` goal about straight
line code into a statement about an updated record.  `input` is too
long for that in one piece (its three `if`s with a continuation would be
unfolded 18 times), so it is first written as its numbered steps in
continuation-passing style (`input_eq`, by `rfl`), and each step gets
its lemma once.
-/

namespace Ember.Spec.Tcp
open Ember

/-! ## Running a `TcpM` action -/

/-- `m`, run from `c`, returns a value and a state satisfying `Q`. -/
def wp (m : TcpM α) (Q : α → Ctx → Prop) (c : Ctx) : Prop := Q (m.run c).1 (m.run c).2

@[simp] theorem wp_pure (a : α) (Q : α → Ctx → Prop) (c : Ctx) : wp (pure a) Q c ↔ Q a c := Iff.rfl

@[simp] theorem wp_bind (m : TcpM α) (f : α → TcpM β) (Q : β → Ctx → Prop) (c : Ctx) :
    wp (m >>= f) Q c ↔ wp m (fun a c' => wp (f a) Q c') c := Iff.rfl

@[simp] theorem wp_get (Q : Ctx → Ctx → Prop) (c : Ctx) : wp get Q c ↔ Q c c := Iff.rfl

@[simp] theorem wp_modify (f : Ctx → Ctx) (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (modify f) Q c ↔ Q () (f c) := Iff.rfl

@[simp] theorem wp_set (c' : Ctx) (Q : Unit → Ctx → Prop) (c : Ctx) : wp (set c') Q c ↔ Q () c' := Iff.rfl

@[simp] theorem wp_map (f : α → β) (m : TcpM α) (Q : β → Ctx → Prop) (c : Ctx) :
    wp (f <$> m) Q c ↔ wp m (fun a c' => Q (f a) c') c := Iff.rfl

theorem wp_ite (b : Prop) [Decidable b] (m₁ m₂ : TcpM α) (Q : α → Ctx → Prop) (c : Ctx) :
    wp (if b then m₁ else m₂) Q c ↔ if b then wp m₁ Q c else wp m₂ Q c := by
  split <;> rfl

@[simp] theorem wp_dropR (r : String) (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (dropR r) Q c ↔ Q () { c with diag := c.diag.push (.drop r) } := Iff.rfl

@[simp] theorem wp_send (dst : UInt32) (s : Seg) (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (send dst s) Q c ↔ Q () { c with out := c.out.push (dst, emit c.ourIp dst s) } := Iff.rfl

@[simp] theorem wp_closeConn (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp closeConn Q c ↔ Q () { c with tcb := {} } := Iff.rfl

@[simp] theorem wp_logTcb (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp logTcb Q c ↔ Q () { c with diag := c.diag.push (.tcb c.tcb.describe) } := Iff.rfl

@[simp] theorem wp_sendSeg (flags : UInt8) (seq : UInt32) (data : ByteArray) (mss : Option UInt16)
    (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (sendSeg flags seq data mss) Q c ↔
      Q () { c with
        out := c.out.push (c.tcb.rip, emit c.ourIp c.tcb.rip
          { sport := echoPort, dport := c.tcb.rport, seq, ack := c.tcb.rcvNxt, flags,
            wnd := UInt16.ofNat c.tcb.wnd, mss, data }),
        tcb := { c.tcb with lastWnd := c.tcb.wnd } } := Iff.rfl

theorem wp_sendSynAck (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp sendSynAck Q c ↔
      wp (sendSeg (SYN ||| ACK) c.tcb.sndUna .empty (some (UInt16.ofNat c.tcb.ourMss))) Q c := by
  simp only [sendSynAck, wp_bind, wp_get]

/-- `sendReset` only appends to the output queue. -/
theorem wp_sendReset (dst : UInt32) (s : Seg) (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (sendReset dst s) Q c ↔ Q () { c with out := ((sendReset dst s).run c).2.out } := by
  unfold sendReset
  split <;> rfl

theorem wp_armTimer (was : Bool) (Q : Unit → Ctx → Prop) (c : Ctx) :
    wp (armTimer was) Q c ↔
      if was then Q () c else Q () { c with tcb := { c.tcb with rtTimer := rto 0, retries := 0 } } := by
  cases was <;> rfl

/-- A postcondition may be weakened. -/
theorem wp_mono {m : TcpM α} {Q Q' : α → Ctx → Prop} {c : Ctx} (h : wp m Q c)
    (hq : ∀ a c', Q a c' → Q' a c') : wp m Q' c := hq _ _ h

/-- The derived `==` on states is equality. -/
@[simp] theorem st_beq (a b : St) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem st_bne (a b : St) : (a != b) = decide (a ≠ b) := by
  cases a <;> cases b <;> rfl

/-- The simp set that runs a `TcpM` action symbolically. -/
macro "wp_simp" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [$ds,*, wp_ite, wp_bind, wp_get, wp_modify, wp_set, wp_sendSeg, wp_pure, wp_map, wp_dropR,
    wp_send, wp_closeConn, wp_logTcb,
    st_beq, st_bne, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.not_eq_true,
    bne_iff_ne, beq_iff_eq, ne_eq, gt_iff_lt, ge_iff_le, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, decide_eq_false_iff_not, Nat.not_lt, reduceCtorEq, or_false,
    false_or, or_true, true_or, true_and, and_true, false_and, and_false, not_true_eq_false,
    not_false_eq_true, false_implies, true_implies, implies_true])

/-! ## `input` as its steps

Steps 5–7 of `Tcp.input`, each taking the rest of the processing as a
continuation `k` — which is how `do` notation compiles the original, so
that `input_eq` below holds by `rfl`. -/

/-- Step 5 of `input`: ACK processing, then `k`. -/
def ackStep (src : UInt32) (s : Seg) (t : Tcb) (k : TcpM Unit) : TcpM Unit := do
  if t.st == .synRcvd then
    if s.ack != t.sndNxt then
      sendReset src s
      dropR "bad-ack-in-syn-rcvd"
      return
    modify fun c => { c with tcb := { c.tcb with st := .established, sndUna := s.ack,
                                                 rtTimer := 0, retries := 0 } }
    k
  else
    if !(← ackInput s) then logTcb; return
    k

/-- Step 6 of `input`: data, then `k ackNow inOrder`. -/
def dataStep (s : Seg) (k : Bool → Bool → TcpM Unit) : TcpM Unit := do
  let t ← (·.tcb) <$> get
  if (s.data.size > 0 || has s.flags FIN) && !seqGe t.rcvNxt s.seq then
    sendSeg ACK t.sndNxt
    dropR "out-of-order"
    logTcb
    return
  if s.data.size > 0 then
    if t.st == .established || t.st == .finWait1 || t.st == .finWait2 then
      let skip := dist t.rcvNxt s.seq
      let fresh := s.data.extract skip s.data.size
      let take := min fresh.size t.wnd
      let keep := if t.st == .established then t.pending ++ fresh.extract 0 take else t.pending
      modify fun c => { c with tcb := { c.tcb with pending := keep,
                                                   rcvNxt := t.rcvNxt + UInt32.ofNat take } }
      k true (take == fresh.size)
    else k false true
  else k false true

/-- Step 7 of `input`: FIN, then `k ackNow`. -/
def finStep (s : Seg) (ackNow inOrder : Bool) (k : Bool → TcpM Unit) : TcpM Unit := do
  let t ← (·.tcb) <$> get
  if has s.flags FIN && inOrder && s.seq + UInt32.ofNat s.data.size == t.rcvNxt then
    let nst := match t.st with
      | .established => some St.closeWait
      | .finWait1 => some .closing
      | .finWait2 => some .timeWait
      | _ => none
    if let some nst := nst then
      let tw := if nst == .timeWait then timeWaitTicks else t.twTimer
      modify fun c => { c with tcb := { c.tcb with st := nst, rcvNxt := t.rcvNxt + 1, twTimer := tw } }
      k true
    else k ackNow
  else k ackNow

/-- Steps 2–8 of `input` for an acceptable segment of the connection. -/
def connStep (src : UInt32) (s : Seg) (t : Tcb) : TcpM Unit := do
  if has s.flags RST then
    closeConn
    modify fun c => { c with diag := c.diag.push (.note "connection reset by peer") }
    logTcb
    return
  if has s.flags SYN then
    send t.rip { sport := echoPort, dport := t.rport, seq := t.sndNxt, ack := 0, flags := RST, wnd := 0 }
    closeConn
    dropR "syn-in-window"
    logTcb
    return
  if !has s.flags ACK then dropR "no-ack"; return
  ackStep src s t <| dataStep s fun ackNow inOrder => finStep s ackNow inOrder fun ackNow => do
    output ackNow
    logTcb

theorem input_eq (src : UInt32) (s : Seg) : input src s = (do
    if s.dport != echoPort then
      if !has s.flags RST then sendReset src s
      dropR "tcp-port-closed"
      return
    let t := (← get).tcb
    if t.st == .listen || src != t.rip || s.sport != t.rport then
      listenInput src s
      logTcb
      return
    modify fun c => { c with tcb := { c.tcb with idle := 0 } }
    if !acceptable t s then
      if has s.flags RST then dropR "rst-out-of-window"; return
      if t.st == .synRcvd && has s.flags SYN && !has s.flags ACK && s.seq + 1 == t.rcvNxt then
        sendSynAck
        dropR "duplicate-syn"
        return
      sendSeg ACK t.sndNxt
      dropR "out-of-window"
      return
    connStep src s t) := by
  rfl

/-! ## The invariant -/

/-- Sequence space taken by an unacknowledged SYN or FIN of ours. -/
def ctl (st : St) : Nat :=
  match st with
  | .synRcvd | .finWait1 | .closing | .lastAck => 1
  | _ => 0

theorem ctl_le_one (st : St) : ctl st ≤ 1 := by
  cases st <;> decide

/-- The invariant of the control block. -/
structure Inv (t : Tcb) : Prop where
  /-- The peer's MSS came from a 16-bit option (or is the default 536). -/
  peerMss : t.peerMss ≤ 65535
  /-- The echo buffer never exceeds its capacity (one segment). -/
  pendingCap : t.pending.size ≤ t.cap
  /-- What was sent is part of the buffer. -/
  sentPending : t.sent ≤ t.pending.size
  /-- `snd.nxt − snd.una` is exactly what is in flight: the sent bytes of
  the buffer plus an unacknowledged SYN or FIN. -/
  flight : dist t.sndNxt t.sndUna = t.sent + ctl t.st
  /-- The application holds data only in these states. -/
  holds : 0 < t.pending.size → t.st = .established ∨ t.st = .closeWait ∨ t.st = .lastAck
  /-- Before the close starts, no close was requested and no FIN sent
  (needed for the idle close to leave ESTABLISHED at once). -/
  fresh : t.st = .synRcvd ∨ t.st = .established → t.closeReq = false ∧ t.finSent = false

/-- M5.3: `snd.una ≤ snd.nxt`, as the Spec compares sequence numbers. -/
theorem Inv.seqGe {t : Tcb} (h : Inv t) : seqGe t.sndNxt t.sndUna = true := by
  have h1 := h.peerMss
  have h2 := h.pendingCap
  have h3 := h.sentPending
  have h4 := h.flight
  have h5 := ctl_le_one t.st
  show decide (dist t.sndNxt t.sndUna < 0x80000000) = true
  rw [decide_eq_true_eq]
  simp only [Tcb.cap] at h2
  omega

/-- What is in flight is at most one buffer and a SYN or FIN. -/
theorem Inv.flight_le {t : Tcb} (h : Inv t) : dist t.sndNxt t.sndUna ≤ t.cap + 1 := by
  have h2 := h.pendingCap
  have h3 := h.sentPending
  have h4 := h.flight
  have h5 := ctl_le_one t.st
  omega

/-! ### Preservation -/

/-- Close a goal of sequence-number arithmetic: everything to `Nat`, then `omega`. -/
macro "seq_omega" : tactic => `(tactic| (
  simp only [dist, ctl, Tcb.cap, Tcb.wnd, UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat',
    UInt32.toNat_one, UInt32.toNat_zero, Nat.reducePow, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_empty] at *
  omega))

/-- Prove `Inv` of an explicitly updated control block, field by field. -/
macro "inv_leaf" : tactic => `(tactic| (
  constructor <;> (try dsimp only [Tcb.cap, Tcb.wnd, ctl] at *) <;>
    first | with_reducible assumption | omega | seq_omega | decide | (simp_all; done)))

/-- Split on the connection state and rewrite the invariant's fields with it. -/
macro "cases_st" c:term:max hst:ident "with" hs:(ppSpace colGt ident)* : tactic => `(tactic|
  cases $hst:ident : Tcb.st (Ctx.tcb $c) <;>
    simp only [$hst:ident, reduceCtorEq, or_false, false_or, or_true, true_or, true_and, false_and,
      false_implies, true_implies, not_true_eq_false, not_false_eq_true, ne_eq, imp_false] at $[$hs]*)

theorem output_inv (a : Bool) (c : Ctx) (h : Inv c.tcb) : wp (output a) (fun _ c' => Inv c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have b2 := c.tcb.sndUna.toNat_lt
  have b3 := c.tcb.sndNxt.toNat_lt
  cases_st c hst with h4 h5 h6 <;> wp_simp [output, wp_armTimer, hst] <;> repeat' split
  all_goals inv_leaf

theorem listenInput_inv (src : UInt32) (s : Seg) (c : Ctx) (h : Inv c.tcb) :
    wp (listenInput src s) (fun _ c' => Inv c'.tcb) c := by
  have hiss := c.iss.toNat_lt
  wp_simp [listenInput, wp_sendSynAck, wp_sendReset]
  repeat' split
  all_goals first | exact h | skip
  all_goals (try (rename_i m _; have := m.toNat_lt))
  all_goals inv_leaf

theorem ackInput_inv (s : Seg) (c : Ctx) (h : Inv c.tcb) (hsyn : c.tcb.st ≠ .synRcvd) :
    wp (ackInput s) (fun _ c' => Inv c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have b1 := s.ack.toNat_lt
  have b2 := c.tcb.sndUna.toNat_lt
  have b3 := c.tcb.sndNxt.toNat_lt
  cases_st c hst with hsyn h4 h5 h6 <;> wp_simp [ackInput, hst] <;> repeat' split
  all_goals inv_leaf

theorem ackStep_inv (src : UInt32) (s : Seg) (t : Tcb) (k : TcpM Unit)
    (hk : ∀ c, Inv c.tcb → wp k (fun _ c' => Inv c'.tcb) c) (c : Ctx) (h : Inv c.tcb)
    (ht : t.st = c.tcb.st) (hn : t.sndNxt = c.tcb.sndNxt) :
    wp (ackStep src s t k) (fun _ c' => Inv c'.tcb) c := by
  by_cases hsyn : c.tcb.st = .synRcvd
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have b1 := s.ack.toNat_lt
    simp only [hsyn, reduceCtorEq, or_false, true_implies, imp_false] at h4 h5 h6
    wp_simp [ackStep, ht, hn, hsyn, wp_sendReset]
    split
    · exact ⟨h1, h2, h3, by rw [hsyn]; exact h4, by rw [hsyn]; simpa using h5, by rw [hsyn]; simpa using h6⟩
    · apply hk
      rename_i hack
      have b3 := c.tcb.sndNxt.toNat_lt
      simp only [Classical.not_not.mp hack]
      inv_leaf
  · wp_simp [ackStep, ht, hsyn]
    refine wp_mono (ackInput_inv s c h hsyn) ?_
    intro b c' hc'
    cases b
    · exact hc'
    · exact hk c' hc'

theorem dataStep_inv (s : Seg) (k : Bool → Bool → TcpM Unit)
    (hk : ∀ a i c, Inv c.tcb → wp (k a i) (fun _ c' => Inv c'.tcb) c) (c : Ctx) (h : Inv c.tcb) :
    wp (dataStep s k) (fun _ c' => Inv c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases_st c hst with h4 h5 h6 <;> wp_simp [dataStep, hst] <;> repeat' split
  all_goals first | apply hk | skip
  all_goals inv_leaf

theorem finStep_inv (s : Seg) (a i : Bool) (k : Bool → TcpM Unit)
    (hk : ∀ a c, Inv c.tcb → wp (k a) (fun _ c' => Inv c'.tcb) c) (c : Ctx) (h : Inv c.tcb) :
    wp (finStep s a i k) (fun _ c' => Inv c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases_st c hst with h4 h5 h6 <;> wp_simp [finStep, hst] <;> repeat' split
  all_goals first | apply hk | skip
  all_goals inv_leaf

/-- The closed connection (LISTEN) satisfies the invariant. -/
theorem inv_default : Inv {} := by
  constructor <;> decide

/-- `Inv` reads only these fields. -/
theorem Inv.frame {t t' : Tcb} (h : Inv t) (e1 : t'.peerMss = t.peerMss) (e2 : t'.ourMss = t.ourMss)
    (e3 : t'.pending = t.pending) (e4 : t'.sent = t.sent) (e5 : t'.sndNxt = t.sndNxt)
    (e6 : t'.sndUna = t.sndUna) (e7 : t'.st = t.st) (e8 : t'.closeReq = t.closeReq)
    (e9 : t'.finSent = t.finSent) : Inv t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  constructor <;> simp only [Tcb.cap, e1, e2, e3, e4, e5, e6, e7, e8, e9] <;> assumption

theorem connStep_inv (src : UInt32) (s : Seg) (t : Tcb) (c : Ctx) (h : Inv c.tcb)
    (ht : t.st = c.tcb.st) (hn : t.sndNxt = c.tcb.sndNxt) :
    wp (connStep src s t) (fun _ c' => Inv c'.tcb) c := by
  wp_simp [connStep]
  repeat' split
  all_goals first | exact inv_default | exact h | skip
  refine ackStep_inv src s t _ (fun c hc => ?_) c h ht hn
  refine dataStep_inv s _ (fun a i c hc => ?_) c hc
  refine finStep_inv s a i _ (fun a c hc => ?_) c hc
  wp_simp [wp_pure]
  exact output_inv a c hc

/-- M5.3: the invariant survives the arrival of any segment. -/
theorem input_inv (src : UInt32) (s : Seg) (c : Ctx) (h : Inv c.tcb) :
    Inv ((input src s).run c).2.tcb := by
  show wp (input src s) (fun _ c' => Inv c'.tcb) c
  rw [input_eq]
  wp_simp [wp_sendReset, wp_sendSynAck]
  repeat' split
  all_goals first
    | exact h
    | exact listenInput_inv src s c h
    | exact h.frame rfl rfl rfl rfl rfl rfl rfl rfl rfl
    | skip
  exact connStep_inv src s c.tcb _ (h.frame rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl

/-- M5.3: the invariant survives a tick. -/
theorem tick_inv (c : Ctx) (h : Inv c.tcb) : Inv (tick.run c).2.tcb := by
  show wp tick (fun _ c' => Inv c'.tcb) c
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have b2 := c.tcb.sndUna.toNat_lt
  have b3 := c.tcb.sndNxt.toNat_lt
  cases_st c hst with h4 h5 h6 <;>
    wp_simp [tick, rexmit, output, wp_armTimer, wp_sendSynAck, hst] <;> repeat' split
  all_goals first | exact inv_default | inv_leaf

/-! ## Delivery to the application -/

/-- `p'` is what is left of `p` after dropping a prefix (acknowledged bytes). -/
def Suffix (p p' : ByteArray) : Prop := ∃ k, p' = p.extract k p.size

theorem Suffix.refl (p : ByteArray) : Suffix p p := ⟨0, ByteArray.extract_zero_size.symm⟩

theorem Suffix.empty (p : ByteArray) : Suffix p .empty := ⟨p.size, ByteArray.extract_same.symm⟩

theorem Suffix.extract (p : ByteArray) (k : Nat) : Suffix p (p.extract k p.size) := ⟨k, rfl⟩

theorem Suffix.trans {p q r : ByteArray} (h1 : Suffix p q) (h2 : Suffix q r) : Suffix p r := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  refine ⟨k + j, ?_⟩
  rw [ByteArray.extract_extract, ByteArray.size_extract]
  congr 1
  omega

/-- Close a `Suffix` goal between a buffer and itself, the empty buffer or a tail of it. -/
macro "suffix_leaf" : tactic => `(tactic| with_reducible first
  | exact Suffix.refl _ | exact Suffix.empty _ | exact Suffix.extract _ _)

theorem output_pending (a : Bool) (c : Ctx) :
    wp (output a) (fun _ c' => c'.tcb.pending = c.tcb.pending) c := by
  wp_simp [output, wp_armTimer]
  repeat' split
  all_goals first | rfl | trivial

theorem ackInput_pending (s : Seg) (c : Ctx) :
    wp (ackInput s)
      (fun _ c' => Suffix c.tcb.pending c'.tcb.pending ∧
        (c.tcb.st ≠ .established → c'.tcb.st ≠ .established)) c := by
  cases hst : c.tcb.st <;> wp_simp [ackInput, hst] <;> repeat' split
  all_goals first
    | suffix_leaf
    | exact ⟨by suffix_leaf, by simp [hst]⟩

theorem finStep_pending (p : ByteArray) (s : Seg) (a i : Bool) (k : Bool → TcpM Unit)
    (hk : ∀ a c, Suffix p c.tcb.pending → wp (k a) (fun _ c' => Suffix p c'.tcb.pending) c)
    (c : Ctx) (h : Suffix p c.tcb.pending) :
    wp (finStep s a i k) (fun _ c' => Suffix p c'.tcb.pending) c := by
  wp_simp [finStep]
  repeat' split
  all_goals exact hk _ _ h

theorem dataStep_pending (p : ByteArray) (s : Seg) (k : Bool → Bool → TcpM Unit)
    (hk : ∀ a i c, Suffix p c.tcb.pending → wp (k a i) (fun _ c' => Suffix p c'.tcb.pending) c)
    (c : Ctx) (h : Suffix p c.tcb.pending) (hne : c.tcb.st ≠ .established) :
    wp (dataStep s k) (fun _ c' => Suffix p c'.tcb.pending) c := by
  wp_simp [dataStep, hne]
  repeat' split
  all_goals first | exact h | exact hk _ _ _ h

theorem ackStep_pending (p : ByteArray) (src : UInt32) (s : Seg) (t : Tcb) (k : TcpM Unit)
    (hk : ∀ c, Suffix p c.tcb.pending → c.tcb.st ≠ .established →
      wp k (fun _ c' => Suffix p c'.tcb.pending) c)
    (c : Ctx) (h : Suffix p c.tcb.pending) (ht : t.st = c.tcb.st) (hsyn : c.tcb.st ≠ .synRcvd)
    (hne : c.tcb.st ≠ .established) :
    wp (ackStep src s t k) (fun _ c' => Suffix p c'.tcb.pending) c := by
  wp_simp [ackStep, ht, hsyn]
  refine wp_mono (ackInput_pending s c) ?_
  intro b c' ⟨h1, h2⟩
  cases b
  · exact h.trans h1
  · exact hk c' (h.trans h1) (h2 hne)

theorem connStep_pending (src : UInt32) (s : Seg) (t : Tcb) (c : Ctx) (ht : t.st = c.tcb.st)
    (hsyn : c.tcb.st ≠ .synRcvd) (hne : c.tcb.st ≠ .established) :
    wp (connStep src s t) (fun _ c' => Suffix c.tcb.pending c'.tcb.pending) c := by
  wp_simp [connStep]
  repeat' split
  all_goals first | suffix_leaf | skip
  refine ackStep_pending _ src s t _ (fun c1 h1 hn1 => ?_) c (Suffix.refl _) ht hsyn hne
  refine dataStep_pending _ s _ (fun a i c2 h2 => ?_) c1 h1 hn1
  refine finStep_pending _ s a i _ (fun a c3 h3 => ?_) c2 h2
  wp_simp [wp_pure]
  exact wp_mono (output_pending a c3) fun _ c4 h4 => by rw [h4]; exact h3

/-- M5.3: a segment that arrives when the connection is neither in
SYN-RCVD nor in ESTABLISHED delivers nothing to the application: the
echo buffer afterwards is what was left of it (acknowledged bytes
dropped from the front). -/
theorem input_pending (src : UInt32) (s : Seg) (c : Ctx) (hsyn : c.tcb.st ≠ .synRcvd)
    (hne : c.tcb.st ≠ .established) :
    Suffix c.tcb.pending ((input src s).run c).2.tcb.pending := by
  show wp (input src s) (fun _ c' => Suffix c.tcb.pending c'.tcb.pending) c
  rw [input_eq]
  wp_simp [wp_sendReset, wp_sendSynAck]
  repeat' split
  all_goals first | suffix_leaf | skip
  · wp_simp [listenInput, wp_sendReset, wp_sendSynAck]
    repeat' split
    all_goals suffix_leaf
  · exact connStep_pending src s c.tcb _ rfl hsyn hne

/-- In SYN-RCVD only the ACK that completes the handshake can bring data
with it; any other segment leaves the echo buffer as it was. -/
theorem input_pending_synRcvd (src : UInt32) (s : Seg) (c : Ctx) (hsyn : c.tcb.st = .synRcvd)
    (hack : s.ack ≠ c.tcb.sndNxt) :
    Suffix c.tcb.pending ((input src s).run c).2.tcb.pending := by
  show wp (input src s) (fun _ c' => Suffix c.tcb.pending c'.tcb.pending) c
  rw [input_eq]
  wp_simp [listenInput, connStep, ackStep, wp_sendReset, wp_sendSynAck, hsyn, hack]
  repeat' split
  all_goals suffix_leaf

/-- M5.3: data is delivered to the application only in ESTABLISHED.  If
a segment adds bytes to the echo buffer (the buffer afterwards is not a
suffix of the buffer before), the connection was in ESTABLISHED, or in
SYN-RCVD with this segment's ACK completing the handshake — in which
case it is in ESTABLISHED by the time the data is taken (`dataStep`
appends only in that state, `dataStep_pending`). -/
theorem input_delivery (src : UInt32) (s : Seg) (c : Ctx) :
    Suffix c.tcb.pending ((input src s).run c).2.tcb.pending ∨ c.tcb.st = .established ∨
      (c.tcb.st = .synRcvd ∧ s.ack = c.tcb.sndNxt) := by
  by_cases hest : c.tcb.st = .established
  · exact Or.inr (Or.inl hest)
  · by_cases hsyn : c.tcb.st = .synRcvd
    · by_cases hack : s.ack = c.tcb.sndNxt
      · exact Or.inr (Or.inr ⟨hsyn, hack⟩)
      · exact Or.inl (input_pending_synRcvd src s c hsyn hack)
    · exact Or.inl (input_pending src s c hsyn hest)

/-- A tick delivers nothing either. -/
theorem tick_pending (c : Ctx) : Suffix c.tcb.pending (tick.run c).2.tcb.pending := by
  show wp tick (fun _ c' => Suffix c.tcb.pending c'.tcb.pending) c
  wp_simp [tick, rexmit, output, wp_armTimer, wp_sendSynAck]
  simp only [Suffix.refl, Suffix.empty, ite_self]

/-! ## Acceptance and the receive window -/

/-- M5.3: a segment that is not for the connection, or is not
`acceptable` (outside the receive window), changes nothing in an existing
connection except the idle counter and the window recorded as last
announced (it is answered with an ACK, a SYN-ACK or a reset). -/
theorem input_not_acceptable (src : UInt32) (s : Seg) (c : Ctx) (hl : c.tcb.st ≠ .listen)
    (h : ¬ (s.dport = echoPort ∧ src = c.tcb.rip ∧ s.sport = c.tcb.rport ∧ acceptable c.tcb s = true)) :
    ((input src s).run c).2.tcb =
      { c.tcb with idle := ((input src s).run c).2.tcb.idle,
                   lastWnd := ((input src s).run c).2.tcb.lastWnd } := by
  show wp (input src s) (fun _ c' => c'.tcb = { c.tcb with idle := c'.tcb.idle, lastWnd := c'.tcb.lastWnd }) c
  rw [input_eq]
  wp_simp [listenInput, wp_sendReset, wp_sendSynAck, hl]
  repeat' split
  all_goals first | rfl | trivial | (exfalso; simp_all; done)

/-- Where the connection stands after ACK processing, relative to its
state `t0` when the segment arrived: `rcv.nxt` and the buffer capacity
are unchanged and at most `m` bytes have left the buffer. -/
def Mid (t0 : Tcb) (m : Nat) (t : Tcb) : Prop :=
  t.rcvNxt = t0.rcvNxt ∧ t.cap = t0.cap ∧ t0.pending.size ≤ t.pending.size + m ∧
    t.pending.size ≤ t.cap

/-- The connection was closed, or `rcv.nxt` advanced by at most the room
in the buffer plus `bound`. -/
def Win (t0 : Tcb) (bound : Nat) (t : Tcb) : Prop :=
  t.st = .listen ∨ dist t.rcvNxt t0.rcvNxt + t0.pending.size ≤ t0.cap + bound

theorem output_rcvNxt (a : Bool) (c : Ctx) :
    wp (output a) (fun _ c' => c'.tcb.rcvNxt = c.tcb.rcvNxt) c := by
  wp_simp [output, wp_armTimer]
  repeat' split
  all_goals first | rfl | trivial

theorem finStep_win (t0 : Tcb) (m f : Nat) (s : Seg) (a i : Bool) (k : Bool → TcpM Unit)
    (hf : has s.flags FIN = true → 1 ≤ f)
    (hk : ∀ a c, dist c.tcb.rcvNxt t0.rcvNxt + t0.pending.size ≤ t0.cap + (m + f) →
      wp (k a) (fun _ c' => Win t0 (m + f) c'.tcb) c)
    (c : Ctx) (h : dist c.tcb.rcvNxt t0.rcvNxt + t0.pending.size ≤ t0.cap + m) :
    wp (finStep s a i k) (fun _ c' => Win t0 (m + f) c'.tcb) c := by
  have b1 := c.tcb.rcvNxt.toNat_lt
  have b2 := t0.rcvNxt.toNat_lt
  cases hst : c.tcb.st <;> wp_simp [finStep, hst] <;> repeat' split
  all_goals apply hk
  all_goals (try dsimp only)
  all_goals first
    | omega
    | (rename_i hfin; have := hf hfin.1.1; seq_omega)

theorem dataStep_win (t0 : Tcb) (m f : Nat) (s : Seg) (k : Bool → Bool → TcpM Unit)
    (hk : ∀ a i c, dist c.tcb.rcvNxt t0.rcvNxt + t0.pending.size ≤ t0.cap + m →
      wp (k a i) (fun _ c' => Win t0 (m + f) c'.tcb) c)
    (c : Ctx) (h : Mid t0 m c.tcb) :
    wp (dataStep s k) (fun _ c' => Win t0 (m + f) c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have b1 := c.tcb.rcvNxt.toNat_lt
  have b2 := t0.rcvNxt.toNat_lt
  wp_simp [dataStep]
  repeat' split
  all_goals first | apply hk | right
  all_goals (try dsimp only)
  all_goals (rw [h1]; seq_omega)

theorem Mid.win {t0 t : Tcb} {m : Nat} (h : Mid t0 m t) (f : Nat) : Win t0 (m + f) t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have b2 := t0.rcvNxt.toNat_lt
  right
  rw [h1]
  seq_omega

theorem ackInput_win (s : Seg) (c : Ctx) (h : Inv c.tcb) :
    wp (ackInput s)
      (fun b c' => (b = false ∧ c'.tcb.st = .listen) ∨
        Mid c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent) c'.tcb) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases hst : c.tcb.st <;> wp_simp [ackInput, hst] <;> repeat' split
  all_goals (try simp only [Mid, Tcb.cap, eq_self, true_and])
  all_goals first
    | (constructor <;> seq_omega)
    | (right; constructor <;> seq_omega)

theorem ackStep_win (f : Nat) (src : UInt32) (s : Seg) (t : Tcb) (k : TcpM Unit) (c : Ctx)
    (hk : ∀ c', Mid c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent) c'.tcb →
      wp k (fun _ c'' => Win c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent + f) c''.tcb) c')
    (h : Inv c.tcb) (ht : t.st = c.tcb.st) :
    wp (ackStep src s t k)
      (fun _ c' => Win c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent + f) c'.tcb) c := by
  have hmid : Mid c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent) c.tcb :=
    ⟨rfl, rfl, Nat.le_add_right _ _, h.pendingCap⟩
  by_cases hsyn : c.tcb.st = .synRcvd
  · wp_simp [ackStep, ht, hsyn, wp_sendReset]
    split
    · exact hmid.win f
    · exact hk _ ⟨rfl, rfl, Nat.le_add_right _ _, h.pendingCap⟩
  · wp_simp [ackStep, ht, hsyn]
    refine wp_mono (ackInput_win s c h) ?_
    intro b c' hc'
    cases b
    · rcases hc' with hc' | hc'
      · exact Or.inl hc'.2
      · exact hc'.win f
    · rcases hc' with hc' | hc'
      · exact absurd hc'.1 (by decide)
      · exact hk c' hc'

theorem connStep_win (f : Nat) (src : UInt32) (s : Seg) (t : Tcb) (c : Ctx)
    (hf : has s.flags FIN = true → 1 ≤ f) (h : Inv c.tcb) (ht : t.st = c.tcb.st) :
    wp (connStep src s t)
      (fun _ c' => Win c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent + f) c'.tcb) c := by
  have hmid : Mid c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent) c.tcb :=
    ⟨rfl, rfl, Nat.le_add_right _ _, h.pendingCap⟩
  wp_simp [connStep]
  repeat' split
  all_goals first | exact Or.inl rfl | exact hmid.win _ | skip
  refine ackStep_win _ src s t _ c (fun c1 h1 => ?_) h ht
  refine dataStep_win _ _ _ s _ (fun a i c2 h2 => ?_) c1 h1
  refine finStep_win _ _ _ s a i _ hf (fun a c3 h3 => ?_) c2 h2
  wp_simp [wp_pure]
  exact wp_mono (output_rcvNxt a c3) fun _ c4 h4 => Or.inr (by rw [h4]; exact h3)

/-- M5.3: what a segment can make the connection accept.  Unless the
connection is closed, `rcv.nxt` advances by at most the receive window,
plus the bytes of the echo buffer this segment acknowledges (they are
freed before its data is taken), plus one for a FIN. -/
theorem input_window (src : UInt32) (s : Seg) (c : Ctx) (h : Inv c.tcb) (hl : c.tcb.st ≠ .listen) :
    ((input src s).run c).2.tcb.st = .listen ∨
      dist ((input src s).run c).2.tcb.rcvNxt c.tcb.rcvNxt ≤
        c.tcb.wnd + min (dist s.ack c.tcb.sndUna) c.tcb.sent + (if has s.flags FIN then 1 else 0) := by
  have hmid : Mid c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent) c.tcb :=
    ⟨rfl, rfl, Nat.le_add_right _ _, h.pendingCap⟩
  have key : ∀ f : Nat, (has s.flags FIN = true → 1 ≤ f) → wp (input src s)
      (fun _ c' => Win c.tcb (min (dist s.ack c.tcb.sndUna) c.tcb.sent + f) c'.tcb) c := by
    intro f hf
    rw [input_eq]
    wp_simp [listenInput, wp_sendReset, wp_sendSynAck, hl]
    repeat' split
    all_goals first | exact hmid.win _ | skip
    exact connStep_win f src s c.tcb _ hf (h.frame rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl
  have hcap := h.pendingCap
  rcases key (if has s.flags FIN then 1 else 0) (fun hfin => by rw [if_pos hfin]; exact Nat.le_refl 1)
    with key | key
  · exact Or.inl key
  · right
    simp only [Tcb.wnd]
    omega

/-! ## Axioms -/

/-- info: 'Ember.Spec.Tcp.input_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms input_eq

/-- info: 'Ember.Spec.Tcp.input_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms input_inv

/-- info: 'Ember.Spec.Tcp.tick_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tick_inv

/-- info: 'Ember.Spec.Tcp.Inv.seqGe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Inv.seqGe

/-- info: 'Ember.Spec.Tcp.input_delivery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms input_delivery

/-- info: 'Ember.Spec.Tcp.tick_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tick_pending

/-- info: 'Ember.Spec.Tcp.input_not_acceptable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms input_not_acceptable

/-- info: 'Ember.Spec.Tcp.input_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms input_window

end Ember.Spec.Tcp
