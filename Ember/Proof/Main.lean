import Ember.Proof.NetStep
import Ember.Proof.TcpBound

/-!
# Ember.Proof.Main — `main`, one input item (plan M5.6)
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

def main_fn : Fn := checked_fn% Net.prog, "main"
#guard (Net.prog.check.toOption.bind (·.fn? "main")) == some main_fn

/-! ## The code of `main`, with what it calls as hypotheses -/

theorem main_cond (p : Prog) (st : St) (k : UInt16) (lit : Nat) (kv : UInt16)
    (h : mask .w16 (UInt64.ofNat lit) = kv.toUInt64) :
    evalE p st [("k", u16 k)] (.bin .eq (.var "k") (.lit lit (some .w16))) = some (.bool (k == kv)) := by
  have e1 : evalE p st [("k", u16 k)] (.var "k") = some (u16 k) := by simp [evalE, lookup, List.lookup]
  simp only [evalE_bin, evalE_lit, e1, Sem.binop, h, toUInt64_eq_iff]

theorem main_booted (p : Prog) (st : St) (env : Env) (hb : st.globals.lookup "booted" = some (.bool true))
    (he : env.lookup "booted" = none) :
    evalE p st env (.un .lnot (.var "booted")) = some (.bool false) := by
  simp [evalE_un, evalE, lookup, hb, he]

theorem main_len (p : Prog) (st : St) (k L : UInt16) (hlen : st.globals.lookup "len" = some (u16 L)) :
    evalE p st [("k", u16 k)] (.bin .eq (.var "len") (.lit 0 (some .w16))) = some (.bool (L == 0)) := by
  have e1 : evalE p st [("k", u16 k)] (.var "len") = some (u16 L) := by simp [evalE, lookup, List.lookup, hlen]
  have k0 : mask .w16 (UInt64.ofNat 0) = (0 : UInt16).toUInt64 := rfl
  simp only [evalE_bin, evalE_lit, e1, Sem.binop, k0, toUInt64_eq_iff]

theorem main_due (p : Prog) (st : St) (k : UInt16) (d : Bool)
    (hdue : st.globals.lookup "tick_due" = some (.bool d)) :
    evalE p st [("k", u16 k)] (.var "tick_due") = some (.bool d) := by
  simp [evalE, lookup, List.lookup, hdue]

/-- The statements of `main`, as far as they do not depend on the case. -/
macro "main_sym" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [$ds,*, Sem.call, main_fn, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_decl_none,
    execS_eff, execS_assign, evalArgs, Sem.effect, storeResult, assign_var, Val.toBool,
    zeroOf, List.lookup, setFirst, execS_ret_none, List.map, List.zip, List.zipWith, Bool.false_eq_true, if_false,
    beq_self_eq_true, if_true, List.length_nil, List.length_cons, Nat.sub_self, List.drop_zero, evalE_blit,
    evalE_un, Bool.not_true, Bool.not_false, Option.isSome_some, reduceCtorEq, String.reduceBEq, lookup_setG_ne,
    ne_eq, String.reduceEq, not_false_eq_true, not_true_eq_false, Bool.and_true, Bool.and_false, Bool.true_and,
    Bool.false_and])

/-- Nothing left to read. -/
theorem main_none (p : Prog) (hp : p.fn? "main" = some main_fn) (st : St)
    (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk : k = 0xFFFF) (m : Nat) :
    Sem.call (m + 20) p st "main" [] = .ok none { st with world := w' } := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  rw [show (Val.int .w16 k.toUInt64) = u16 k from rfl, c1]
  simp [hk, Val.toBool, execB_succ, execL_cons, execL_nil, execS_at, execS_ret_none]

/-- A tick with no frame half received: `tcp_tick()`. -/
theorem main_tick_now (p : Prog) (hp : p.fn? "main" = some main_fn) (ht : p.fn? "tcp_tick" = some tcp_tick)
    (st : St) (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk : k = 0x0100) (hlen : st.globals.lookup "len" = some (u16 0)) (m : Nat)
    (st2 : St) (hc : Sem.call (m + 4) p { st with world := w' } "tcp_tick" [] = .ok none st2) :
    Sem.call (m + 20) p st "main" [] = .ok none st2 := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have k2 : mask .w16 (UInt64.ofNat 256) = (0x0100 : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  have c2 := main_cond p { st with world := w' } k 256 0x0100 k2
  have c3 := main_len p { st with world := w' } k 0 hlen
  have hcall := execS_call_val p { st with world := w' } [("k", u16 k)] (m + 4) none "tcp_tick" [] ht
    (by simp [tcp_tick]) (by simp [evalArgs]) hc
  have hk1 : (k == 0xFFFF) = false := by rw [hk]; rfl
  have hk2 : (k == 0x0100) = true := by rw [hk]; rfl
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  main_sym [c1, c2, c3, hcall, hk1, hk2]

/-- A tick in the middle of a frame: it waits. -/
theorem main_tick_defer (p : Prog) (hp : p.fn? "main" = some main_fn) (st : St)
    (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk : k = 0x0100) (L : UInt16) (hlen : st.globals.lookup "len" = some (u16 L))
    (hL : L ≠ 0) (hdue : st.globals.lookup "tick_due" = some (.bool false)) (m : Nat) :
    Sem.call (m + 20) p st "main" [] = .ok none (setG { st with world := w' } "tick_due" (.bool true)) := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have k2 : mask .w16 (UInt64.ofNat 256) = (0x0100 : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  have c2 := main_cond p { st with world := w' } k 256 0x0100 k2
  have c3 := main_len p { st with world := w' } k L hlen
  have c4 := main_due p { st with world := w' } k false hdue
  have hL' : (L == 0) = false := by simpa using hL
  have hk1 : (k == 0xFFFF) = false := by rw [hk]; rfl
  have hk2 : (k == 0x0100) = true := by rw [hk]; rfl
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  main_sym [c1, c2, c3, c4, hL', hdue, hk1, hk2]

/-- The state after a frame is given up: the decoder skips the rest of it. -/
def giveUpSt (st : St) : St :=
  setG (setG (setG (setG st "over" (.bool true)) "len" (u16 0)) "esc" (.bool false)) "tick_due" (.bool false)

/-- A second tick in the middle of a frame: the frame is given up, both ticks happen. -/
theorem main_tick_giveup (p : Prog) (hp : p.fn? "main" = some main_fn) (ht : p.fn? "tcp_tick" = some tcp_tick)
    (st : St) (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk : k = 0x0100) (L : UInt16) (hlen : st.globals.lookup "len" = some (u16 L))
    (hL : L ≠ 0) (hdue : st.globals.lookup "tick_due" = some (.bool true))
    (ve vo : Val) (hesc : st.globals.lookup "esc" = some ve) (hover : st.globals.lookup "over" = some vo) (m : Nat)
    (st3 st4 : St) (hc1 : Sem.call (m + 2) p (giveUpSt { st with world := w' }) "tcp_tick" [] = .ok none st3)
    (hc2 : Sem.call (m + 1) p st3 "tcp_tick" [] = .ok none st4) :
    Sem.call (m + 20) p st "main" [] = .ok none st4 := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have k2 : mask .w16 (UInt64.ofNat 256) = (0x0100 : UInt16).toUInt64 := rfl
  have k0 : mask .w16 (UInt64.ofNat 0) = (0 : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  have c2 := main_cond p { st with world := w' } k 256 0x0100 k2
  have c3 := main_len p { st with world := w' } k L hlen
  have c4 := main_due p { st with world := w' } k true hdue
  have hL' : (L == 0) = false := by simpa using hL
  have hcall1 := execS_call_val p (giveUpSt { st with world := w' }) [("k", u16 k)] (m + 2) none "tcp_tick" [] ht
    (by simp [tcp_tick]) (by simp [evalArgs]) hc1
  have hcall2 := execS_call_val p st3 [("k", u16 k)] (m + 1) none "tcp_tick" [] ht
    (by simp [tcp_tick]) (by simp [evalArgs]) hc2
  have hk1 : (k == 0xFFFF) = false := by rw [hk]; rfl
  have hk2 : (k == 0x0100) = true := by rw [hk]; rfl
  unfold giveUpSt at hcall1
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  main_sym [c1, c2, c3, c4, hL', hdue, hk1, hk2, hlen, hesc, hover, evalE_lit, k0, hcall1, hcall2]

/-- A byte: `slip_rx`, and nothing else unless a tick waits and the frame has ended. -/
theorem main_byte (p : Prog) (hp : p.fn? "main" = some main_fn) (hs : p.fn? "slip_rx" = some slip_rx) (st : St)
    (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk1 : k ≠ 0xFFFF) (hk2 : k ≠ 0x0100) (m : Nat) (st2 : St)
    (hc : Sem.call (m + 11) p { st with world := w' } "slip_rx" [u8 k.toUInt8] = .ok none st2)
    (d : Bool) (L : UInt16) (hdue : st2.globals.lookup "tick_due" = some (.bool d))
    (hlen : st2.globals.lookup "len" = some (u16 L)) (hno : (d && L == 0) = false) :
    Sem.call (m + 20) p st "main" [] = .ok none st2 := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have k2 : mask .w16 (UInt64.ofNat 256) = (0x0100 : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  have c2 := main_cond p { st with world := w' } k 256 0x0100 k2
  have c3 := main_len p st2 k L hlen
  have c4 := main_due p st2 k d hdue
  have hk1' : (k == 0xFFFF) = false := by simpa using hk1
  have hk2' : (k == 0x0100) = false := by simpa using hk2
  have ha : evalArgs p { st with world := w' } [("k", u16 k)] [.cast .w8 (.var "k")] = some [u8 k.toUInt8] := by
    simp [evalArgs, evalE_cast, evalE, lookup, List.lookup, mask8_u16]
  have hcall := execS_call_val p { st with world := w' } [("k", u16 k)] (m + 11) none "slip_rx" _ hs
    (by simp [slip_rx]) ha hc
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  main_sym [c1, c2, c3, c4, hk1', hk2', hcall, evalE_bin, Sem.binop, hno]

/-- A byte that ends the frame a tick waits for: `slip_rx`, then `tcp_tick`. -/
theorem main_byte_tick (p : Prog) (hp : p.fn? "main" = some main_fn) (hs : p.fn? "slip_rx" = some slip_rx)
    (ht : p.fn? "tcp_tick" = some tcp_tick) (st : St)
    (hb : st.globals.lookup "booted" = some (.bool true)) (k : UInt16) (w' : World)
    (hnx : st.world.next = (k, w')) (hk1 : k ≠ 0xFFFF) (hk2 : k ≠ 0x0100) (m : Nat) (st2 : St)
    (hc : Sem.call (m + 11) p { st with world := w' } "slip_rx" [u8 k.toUInt8] = .ok none st2)
    (hdue : st2.globals.lookup "tick_due" = some (.bool true))
    (hlen : st2.globals.lookup "len" = some (u16 0)) (st4 : St)
    (hc2 : Sem.call (m + 5) p (setG st2 "tick_due" (.bool false)) "tcp_tick" [] = .ok none st4) :
    Sem.call (m + 20) p st "main" [] = .ok none st4 := by
  have k1 : mask .w16 (UInt64.ofNat 65535) = (0xFFFF : UInt16).toUInt64 := rfl
  have k2 : mask .w16 (UInt64.ofNat 256) = (0x0100 : UInt16).toUInt64 := rfl
  have c1 := main_cond p { st with world := w' } k 65535 0xFFFF k1
  have c2 := main_cond p { st with world := w' } k 256 0x0100 k2
  have c3 := main_len p st2 k 0 hlen
  have c4 := main_due p st2 k true hdue
  have hk1' : (k == 0xFFFF) = false := by simpa using hk1
  have hk2' : (k == 0x0100) = false := by simpa using hk2
  have ha : evalArgs p { st with world := w' } [("k", u16 k)] [.cast .w8 (.var "k")] = some [u8 k.toUInt8] := by
    simp [evalArgs, evalE_cast, evalE, lookup, List.lookup, mask8_u16]
  have hcall := execS_call_val p { st with world := w' } [("k", u16 k)] (m + 11) none "slip_rx" _ hs
    (by simp [slip_rx]) ha hc
  have hcall2 := execS_call_val p (setG st2 "tick_due" (.bool false)) [("k", u16 k)] (m + 5) none "tcp_tick" [] ht
    (by simp [tcp_tick]) (by simp [evalArgs]) hc2
  main_sym [hp, main_booted p st [] hb rfl, hnx]
  main_sym [c1, c2, c3, c4, hk1', hk2', hcall, evalE_bin, Sem.binop, hdue, hcall2]

end Ember.Proof.Refine

/-! ## The Spec, one input item -/

namespace Ember.Spec
open Ember Ember.Trace

section
variable {Q : Bool → Slip.Dec → Config → Prop}

theorem txFrame_due (frame : ByteArray) : Pres (fun s => Q s.tickDue s.slip s.cfg) (txFrame frame) := by
  unfold txFrame
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact txFrame_due _)

theorem sendIp_due (proto : UInt8) (dst : UInt32) (payload : ByteArray) :
    Pres (fun s => Q s.tickDue s.slip s.cfg) (sendIp proto dst payload) := by
  unfold sendIp
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact sendIp_due _ _ _)

theorem runTcp_due (act : Tcp.TcpM Unit) : Pres (fun s => Q s.tickDue s.slip s.cfg) (runTcp act) := by
  unfold runTcp
  refine Pres.bind_getS fun st h => ?_
  generalize StateT.run act
    { tcb := st.1.tcb, iss := st.1.iss, ourIp := st.1.ip, mss := mssFor st.1.cfg.mtu } = r
  obtain ⟨u, c⟩ := r
  refine Pres.bind (P := fun s => Q s.tickDue s.slip s.cfg)
    (Pres.modifyS (f := fun s => { s with tcb := c.tcb, iss := c.iss }) fun _ h => h) (fun _ => ?_) st h
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact runTcp_due _)

theorem dhcpApply_due (o : Dhcp.Out) : Pres (fun s => Q s.tickDue s.slip s.cfg) (dhcpApply o) := by
  unfold dhcpApply
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact dhcpApply_due _)

theorem udpInput_due (h : Ipv4.Hdr) (p : ByteArray) : Pres (fun s => Q s.tickDue s.slip s.cfg) (udpInput h p) := by
  unfold udpInput
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact udpInput_due _ _)

theorem ipInput_due (pkt : ByteArray) : Pres (fun s => Q s.tickDue s.slip s.cfg) (ipInput pkt) := by
  unfold ipInput
  pres

macro_rules | `(tactic| pres_call) => `(tactic| exact ipInput_due _)

theorem ethInput_due (f : ByteArray) : Pres (fun s => Q s.tickDue s.slip s.cfg) (ethInput f) := by
  unfold ethInput
  pres
  all_goals with_reducible exact Pres.modifyS (fun _ h => h)

macro_rules | `(tactic| pres_call) => `(tactic| exact ethInput_due _)

theorem frameInput_due (f : ByteArray) : Pres (fun s => Q s.tickDue s.slip s.cfg) (frameInput f) := by
  unfold frameInput
  pres

theorem tickInput_due : Pres (fun s => Q s.tickDue s.slip s.cfg) tickInput := by
  unfold tickInput
  pres

end
end Ember.Spec

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

theorem byteM_pres {P : Spec.Tcp.Tcb → Prop} (hin : Spec.KeepsInput P) (c : UInt8) :
    Spec.Pres (fun s => P s.tcb) (byteM c) := Spec.slipByte_pres hin c

theorem byteM_due (b : Bool) (c : UInt8) : Spec.Pres (fun s => s.tickDue = b) (byteM c) := by
  have h1 := Spec.frameInput_due (Q := fun x _ _ => x = b)
  unfold byteM Spec.slipByte
  pres
  all_goals first | exact h1 _ | with_reducible exact Spec.Pres.modifyS (fun _ h => h)

/-- What `Spec.input (.rx bytes)` does with each byte on a SLIP link: the
decoder and the frame it may complete (`byteM`), then a tick that waited
for the end of the frame. -/
abbrev byteT (c : UInt8) : Spec.StackM Unit := Spec.byteInput c

/-- The Spec's action for the item `main` reads: nothing, a tick, a byte. -/
def itemM (k : UInt16) : Spec.StackM Unit :=
  if k = 0xFFFF then pure () else if k = 0x0100 then Spec.tickArrives else byteT k.toUInt8

/-! ### The cases of a tick and of a byte -/

theorem tickArrives_now (s : Spec.State) (es : Array Trace.Event) (hslip : s.cfg.link = .slip)
    (h0 : s.slip.buf.size = 0) : (Spec.tickArrives).run (s, es) = (Spec.tickInput).run (s, es) := by
  unfold Spec.tickArrives
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  simp only [hslip, h0, beq_self_eq_true, if_true]

theorem tickArrives_defer (s : Spec.State) (es : Array Trace.Event) (hslip : s.cfg.link = .slip)
    (h0 : s.slip.buf.size ≠ 0) (hd : s.tickDue = false) :
    ((Spec.tickArrives).run (s, es)).2 = ({ s with tickDue := true }, es) := by
  unfold Spec.tickArrives
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  have h0' : (s.slip.buf.size == 0) = false := by simpa using h0
  simp only [hslip, h0', hd, Bool.false_eq_true, if_false, Bool.not_false, if_true]
  rfl

theorem tickArrives_giveup (s : Spec.State) (es : Array Trace.Event) (hslip : s.cfg.link = .slip)
    (h0 : s.slip.buf.size ≠ 0) (hd : s.tickDue = true) :
    ((Spec.tickArrives).run (s, es)).2
      = ((Spec.tickInput).run
          ((Spec.tickInput).run ({ s with slip := { over := true }, tickDue := false }, es)).2).2 := by
  unfold Spec.tickArrives
  have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  have h0' : (s.slip.buf.size == 0) = false := by simpa using h0
  simp only [hslip, h0', hd, Bool.false_eq_true, if_false, Bool.not_true]
  rfl

theorem byteT_plain (c : UInt8) (s : Spec.State) (es : Array Trace.Event)
    (h : (((byteM c).run (s, es)).2.1.tickDue && ((byteM c).run (s, es)).2.1.slip.buf.size == 0) = false) :
    ((byteT c).run (s, es)).2 = ((byteM c).run (s, es)).2 := by
  unfold byteT Spec.byteInput
  have hfull : (byteM c).run (s, es) = ((), ((byteM c).run (s, es)).2) := rfl
  rw [run_bind_eq _ _ _ _ _ hfull]
  generalize ((byteM c).run (s, es)).2 = r at h ⊢
  obtain ⟨s1, es1⟩ := r
  have hg : (Spec.getS).run (s1, es1) = (s1, (s1, es1)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  simp only at h
  simp only [h, Bool.false_eq_true, if_false]
  rfl

theorem byteT_tick (c : UInt8) (s : Spec.State) (es : Array Trace.Event)
    (h : (((byteM c).run (s, es)).2.1.tickDue && ((byteM c).run (s, es)).2.1.slip.buf.size == 0) = true) :
    ((byteT c).run (s, es)).2
      = ((Spec.tickInput).run ({ ((byteM c).run (s, es)).2.1 with tickDue := false },
          ((byteM c).run (s, es)).2.2)).2 := by
  unfold byteT Spec.byteInput
  have hfull : (byteM c).run (s, es) = ((), ((byteM c).run (s, es)).2) := rfl
  rw [run_bind_eq _ _ _ _ _ hfull]
  generalize ((byteM c).run (s, es)).2 = r at h ⊢
  obtain ⟨s1, es1⟩ := r
  have hg : (Spec.getS).run (s1, es1) = (s1, (s1, es1)) := rfl
  rw [run_bind_eq _ _ _ _ _ hg]
  simp only at h
  simp only [h, if_true]
  rfl

/-! ## The invariant of `main` -/

theorem World.normalize_frame (w : World) : w.normalize.frame = w.frame := by
  fun_induction World.normalize w <;> simp_all

theorem World.next_frame (w : World) : w.next.2.frame = w.frame := by
  unfold World.next
  dsimp only
  split
  · split <;> simp [World.normalize_frame]
  · simp [World.normalize_frame]

/-- `NetInv` in a state that differs in what the invariant does not read,
or in the decoder's globals (then against the Spec's decoder `s'.slip`). -/
theorem NetInv.rebuild {st : St} {s : Spec.State} {w : TW} {mtu : UInt16} {ourIp : UInt32} {N : Nat}
    (h : NetInv st s w mtu ourIp N) (st' : St) (s' : Spec.State) (hc : SameConsts st st')
    (h6 : ∀ x, x = "t" ∨ x = "sg" ∨ x = "pend" ∨ x = "buf" ∨ x = "ip_id" ∨ x = "iss" →
      st'.globals.lookup x = st.globals.lookup x)
    (hf : st'.world.frame = .empty)
    (hlen : st'.globals.lookup "len" = some (u16 (UInt16.ofNat s'.slip.buf.size)))
    (hesc : st'.globals.lookup "esc" = some (.bool s'.slip.esc))
    (hover : st'.globals.lookup "over" = some (.bool s'.slip.over))
    (hpre : w.b.extract 0 s'.slip.buf.size = s'.slip.buf) (hle : s'.slip.buf.size ≤ mtu.toNat)
    (e1 : s'.tcb = s.tcb) (e2 : s'.iss = s.iss) (e3 : s'.ipId = s.ipId) (e4 : s'.ip = s.ip) (e5 : s'.cfg = s.cfg) :
    NetInv st' s' w mtu ourIp N := by
  obtain ⟨hh, hrel, hrx, hK, hip, h296, hmtu⟩ := h
  obtain ⟨⟨b, hbuf, hsz, _, _, _, _, hmtuG, _⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hKin, hdo⟩ := hrx
  have hbw : b = w.b := bufVal_inj (Option.some.inj (hbuf.symm.trans hh.buf))
  subst hbw
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hh.evs⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, tcpConsts_same hK hc,
    by rw [hc "OUR_IP" (by decide)]; exact hip, h296, by rw [e5]; exact hmtu⟩
  · rw [h6 "t" (by simp)]; exact hh.t
  · rw [h6 "sg" (by simp)]; exact hh.sg
  · rw [h6 "pend" (by simp)]; exact hh.pend
  · rw [h6 "buf" (by simp)]; exact hh.buf
  · rw [h6 "ip_id" (by simp)]; exact hh.ip_id
  · rw [h6 "iss" (by simp)]; exact hh.iss
  · rw [e1]; exact hrel.tcb
  · rw [e2]; exact hrel.iss
  · rw [e3]; exact hrel.id
  · rw [e4]; exact hrel.ip
  · rw [e5]; exact hrel.mss
  · rw [e5]; exact hrel.slip
  · rw [e5]; exact hrel.dhcp
  · refine ⟨⟨w.b, ?_, hsz, hle, hlen, hesc, hover, ?_, hpre⟩, ⟨b0, ?_, hN⟩, hN', hf, ?_, inConsts_same hKin hc, ?_⟩
    · rw [h6 "buf" (by simp)]; exact hbuf
    · rw [hc "MTU" (by decide)]; exact hmtuG
    · rw [h6 "buf" (by simp)]; exact hb0
    · rw [h6 "ip_id" (by simp)]; exact hid
    · rw [hc "D_OVERSIZE" (by decide)]; exact hdo

/-- **The invariant of `main`** between two input items: `NetInv`, the
stack has booted, the waiting tick is the Spec's, and the Spec's control
block satisfies its invariants. -/
structure MainInv (st : St) (s : Spec.State) (w : TW) (mtu : UInt16) (ourIp : UInt32) (N : Nat) : Prop where
  net : NetInv st s w mtu ourIp N
  booted : st.globals.lookup "booted" = some (.bool true)
  due : st.globals.lookup "tick_due" = some (.bool s.tickDue)
  inv : Spec.Tcp.Inv s.tcb
  bnd : Spec.Tcp.Bnd s.tcb

theorem ofNat16_eq_zero (k : Nat) (h : k < 65536) : (UInt16.ofNat k == 0) = (k == 0) := by
  by_cases h0 : k = 0
  · subst h0; rfl
  · have : UInt16.ofNat k ≠ 0 := by
      intro e
      have e' := congrArg UInt16.toNat e
      rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt h] at e'
      exact h0 e'
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

theorem sameConsts_setG_due (st : St) (v : Val) : SameConsts st (setG st "tick_due" v) := by
  intro x hx
  have : x ≠ "tick_due" := fun e => hx (by rw [e]; decide)
  exact lookup_setG_ne _ _ _ _ (Ne.symm this)

theorem lookup_giveUp_ne (st : St) (x : String) (h1 : x ≠ "tick_due") (h2 : x ≠ "esc") (h3 : x ≠ "len")
    (h4 : x ≠ "over") : (giveUpSt st).globals.lookup x = st.globals.lookup x := by
  unfold giveUpSt
  rw [lookup_setG_ne _ _ _ _ (Ne.symm h1), lookup_setG_ne _ _ _ _ (Ne.symm h2), lookup_setG_ne _ _ _ _ (Ne.symm h3),
    lookup_setG_ne _ _ _ _ (Ne.symm h4)]

theorem sameConsts_giveUp (st : St) : SameConsts st (giveUpSt st) := by
  intro x hx
  exact lookup_giveUp_ne st x (fun e => hx (by rw [e]; decide)) (fun e => hx (by rw [e]; decide))
    (fun e => hx (by rw [e]; decide)) (fun e => hx (by rw [e]; decide))

/-- **One call of `main`.**  From `MainInv`, `main()` does not trap; it
reads one input item `k` and ends in a state that satisfies `MainInv`
against the Spec's state after the same item (`itemM k`: nothing, a tick
as `Spec.tickArrives` treats it, a byte as the loop of `Spec.input`
does); the two traces get the same transmissions and drops. -/
theorem main_step (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (st : St) (s : Spec.State) (w : TW) (mtu : UInt16) (ourIp : UInt32) (N : Nat)
    (hinv : MainInv st s w mtu ourIp N) (es : Array Trace.Event) (n : Nat) :
    ∃ (st' : St) (w' : TW) (X : List Trace.Event),
      Sem.call (n + mtu.toNat + 4420) p st "main" [] = .ok none st' ∧
      MainInv st' ((itemM st.world.next.1).run (s, es)).2.1 w' mtu ourIp N ∧
      st'.world = X.foldl World.emit st.world.next.2 ∧
      ((itemM st.world.next.1).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X.filter keep := by
  obtain ⟨hnet, hb, hdue, hI, hBd⟩ := hinv
  generalize hnx : st.world.next = nx
  obtain ⟨k, w0⟩ := nx
  have hm := mtu.toNat_lt
  have hfuel : n + mtu.toNat + 4420 = n + mtu.toNat + 4400 + 20 := by omega
  have hslip := hnet.rel.slip
  obtain ⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtuG, hpre⟩ := hnet.rx.1
  have hbw : b = w.b := bufVal_inj (Option.some.inj (hbuf.symm.trans hnet.holds.buf))
  subst hbw
  have hw0 : w0.frame = .empty := by
    have := World.next_frame st.world
    rw [hnx] at this
    exact this.trans hnet.rx.2.2.2.1
  have hnet1 : NetInv { st with world := w0 } s w mtu ourIp N :=
    hnet.rebuild { st with world := w0 } s (fun _ _ => rfl) (fun _ _ => rfl) hw0 hlen hesc hover hpre hle
      rfl rfl rfl rfl rfl
  have hid255 : ∀ t : Spec.Tcp.Tcb, Spec.Tcp.Bnd t → t.idle < 255 ∧ t.retries < 255 := fun t h =>
    ⟨Nat.lt_trans h.idle (by decide), Nat.lt_of_le_of_lt h.retries (by decide)⟩
  show ∃ (st' : St) (w' : TW) (X : List Trace.Event),
      Sem.call (n + mtu.toNat + 4420) p st "main" [] = .ok none st' ∧
      MainInv st' ((itemM k).run (s, es)).2.1 w' mtu ourIp N ∧
      st'.world = X.foldl World.emit w0 ∧
      ((itemM k).run (s, es)).2.2.toList.filter keep = es.toList.filter keep ++ X.filter keep
  by_cases hk1 : k = 0xFFFF
  · -- nothing to read
    rw [show itemM k = pure () from if_pos hk1]
    exact ⟨_, w, [], by rw [hfuel]; exact main_none p hp st hb k w0 hnx hk1 _, ⟨hnet1, hb, hdue, hI, hBd⟩, rfl,
      by show es.toList.filter keep = _; simp⟩
  by_cases hk2 : k = 0x0100
  · -- a tick
    rw [show itemM k = Spec.tickArrives from by unfold itemM; rw [if_neg hk1, if_pos hk2]]
    by_cases h0 : s.slip.buf.size = 0
    · -- no frame half received
      have hlen0 : st.globals.lookup "len" = some (u16 0) := by rw [hlen, h0]; rfl
      obtain ⟨st2, w2, X, hcall, hnet2, hworld, htr, hso⟩ := tick_step p hP hR _ s w mtu ourIp N hnet1 hI
        (hid255 _ hBd).1 (hid255 _ hBd).2 h0 es (n + mtu.toNat + 2404)
      rw [tickArrives_now s es hslip h0]
      refine ⟨st2, w2, X, ?_, ⟨hnet2, ?_, ?_, ?_, ?_⟩, hworld, htr⟩
      · rw [hfuel]
        exact main_tick_now p hp hP.tcp_tick st hb k w0 hnx hk2 hlen0 _ st2
          (by rw [← hcall])
      · rw [hso "booted" (by decide)]; exact hb
      · rw [hso "tick_due" (by decide), Spec.tickInput_due (Q := fun x _ _ => x = s.tickDue) (s, es) rfl]; exact hdue
      · exact Spec.tickInput_pres Spec.Tcp.tick_inv (s, es) hI
      · exact Spec.tickInput_pres Spec.Tcp.tick_bnd (s, es) hBd
    · have hL : UInt16.ofNat s.slip.buf.size ≠ 0 := by
        have hz := ofNat16_eq_zero s.slip.buf.size (by omega)
        intro e
        rw [e] at hz
        exact h0 (beq_iff_eq.mp (hz.symm.trans (by decide)))
      cases hd : s.tickDue
      · -- the tick waits
        rw [hd] at hdue
        rw [tickArrives_defer s es hslip h0 hd]
        refine ⟨_, w, [], by rw [hfuel]; exact main_tick_defer p hp st hb k w0 hnx hk2 _ hlen hL hdue _, ⟨?_, ?_, ?_, hI, hBd⟩,
          rfl, by simp⟩
        · exact hnet1.rebuild _ _ (sameConsts_setG_due _ _)
            (fun x hx => lookup_setG_ne _ _ _ _ (by rcases hx with h | h | h | h | h | h <;> rw [h] <;> decide))
            hw0 (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hlen)
            (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hesc)
            (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hover) hpre hle rfl rfl rfl rfl rfl
        · rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hb
        · exact lookup_setG _ _ _ _ hdue
      · -- a second tick: the frame is given up
        rw [hd] at hdue
        rw [tickArrives_giveup s es hslip h0 hd]
        obtain ⟨s2, hs2⟩ : ∃ s2, s2 = ({ s with slip := { over := true }, tickDue := false } : Spec.State) := ⟨_, rfl⟩
        rw [← hs2, show ((Spec.tickInput).run (s2, es)).2
          = (((Spec.tickInput).run (s2, es)).2.1, ((Spec.tickInput).run (s2, es)).2.2) from rfl]
        have hlenG : (giveUpSt { st with world := w0 }).globals.lookup "len" = some (u16 0) := by
          unfold giveUpSt
          rw [lookup_setG_ne _ _ _ _ (by decide), lookup_setG_ne _ _ _ _ (by decide)]
          exact lookup_setG _ _ _ _ (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hlen)
        have hescG : (giveUpSt { st with world := w0 }).globals.lookup "esc" = some (.bool false) := by
          unfold giveUpSt
          rw [lookup_setG_ne _ _ _ _ (by decide)]
          exact lookup_setG _ _ _ _ (by
            rw [lookup_setG_ne _ _ _ _ (by decide), lookup_setG_ne _ _ _ _ (by decide)]; exact hesc)
        have hoverG : (giveUpSt { st with world := w0 }).globals.lookup "over" = some (.bool true) := by
          unfold giveUpSt
          rw [lookup_setG_ne _ _ _ _ (by decide), lookup_setG_ne _ _ _ _ (by decide),
            lookup_setG_ne _ _ _ _ (by decide)]
          exact lookup_setG _ _ _ _ hover
        have hdueG : (giveUpSt { st with world := w0 }).globals.lookup "tick_due" = some (.bool false) := by
          unfold giveUpSt
          exact lookup_setG _ _ _ _ (by
            rw [lookup_setG_ne _ _ _ _ (by decide), lookup_setG_ne _ _ _ _ (by decide),
              lookup_setG_ne _ _ _ _ (by decide)]; exact hdue)
        have hnet2 : NetInv (giveUpSt { st with world := w0 }) s2 w mtu ourIp N := by
          rw [hs2]
          exact hnet1.rebuild _ _ (sameConsts_giveUp _)
            (fun x hx => by
              have hx' : x ≠ "tick_due" ∧ x ≠ "esc" ∧ x ≠ "len" ∧ x ≠ "over" := by
                rcases hx with h | h | h | h | h | h <;> rw [h] <;> decide
              exact lookup_giveUp_ne _ x hx'.1 hx'.2.1 hx'.2.2.1 hx'.2.2.2)
            hw0 hlenG hescG hoverG (extract_empty w.b 0) (Nat.zero_le _) rfl rfl rfl rfl rfl
        have hI2 : Spec.Tcp.Inv s2.tcb := by rw [hs2]; exact hI
        have hB2 : Spec.Tcp.Bnd s2.tcb := by rw [hs2]; exact hBd
        obtain ⟨st3, w3, X3, hc3, hnet3, hw3, htr3, hso3⟩ := tick_step p hP hR _ s2 w mtu ourIp N hnet2 hI2
          (hid255 _ hB2).1 (hid255 _ hB2).2 (by rw [hs2]; rfl) es (n + mtu.toNat + 2402)
        have hI3 := Spec.tickInput_pres Spec.Tcp.tick_inv (s2, es) hI2
        have hB3 := Spec.tickInput_pres Spec.Tcp.tick_bnd (s2, es) hB2
        have hsl3 := Spec.tickInput_due (Q := fun x d _ => x = false ∧ d.buf.size = 0) (s2, es)
          (by rw [hs2]; exact ⟨rfl, rfl⟩)
        obtain ⟨st4, w4, X4, hc4, hnet4, hw4, htr4, hso4⟩ := tick_step p hP hR st3 _ w3 mtu ourIp N hnet3 hI3
          (hid255 _ hB3).1 (hid255 _ hB3).2 hsl3.2 ((Spec.tickInput).run (s2, es)).2.2 (n + mtu.toNat + 2401)
        have hd4 := Spec.tickInput_due (Q := fun x _ _ => x = false)
          (((Spec.tickInput).run (s2, es)).2.1, ((Spec.tickInput).run (s2, es)).2.2) hsl3.1
        refine ⟨st4, w4, X3 ++ X4, ?_, ⟨hnet4, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [hfuel]
          exact main_tick_giveup p hp hP.tcp_tick st hb k w0 hnx hk2 _ hlen hL hdue _ _ hesc hover _ st3 st4
            (by rw [← hc3]) (by rw [← hc4])
        · rw [hso4 "booted" (by decide), hso3 "booted" (by decide),
            lookup_giveUp_ne _ _ (by decide) (by decide) (by decide) (by decide)]
          exact hb
        · exact (hso4 "tick_due" (by decide)).trans (((hso3 "tick_due" (by decide)).trans hdueG).trans
            (congrArg (fun v => some (Val.bool v)) hd4.symm))
        · exact Spec.tickInput_pres Spec.Tcp.tick_inv _ hI3
        · exact Spec.tickInput_pres Spec.Tcp.tick_bnd _ hB3
        · rw [hw4, hw3, List.foldl_append]; rfl
        · refine Eq.trans htr4 ?_
          rw [htr3, List.filter_append, List.append_assoc]
  · -- a byte
    rw [show itemM k = byteT k.toUInt8 from by unfold itemM; rw [if_neg hk1, if_neg hk2]]
    obtain ⟨st2, w2, X2, hc2, hnet2, hw2, htr2, hso2⟩ := slip_rx_step p hP hR _ s w mtu ourIp N hnet1 k.toUInt8 es
      (n + 11)
    have hc2' : Sem.call (n + mtu.toNat + 4400 + 11) p { st with world := w0 } "slip_rx" [u8 k.toUInt8]
        = .ok none st2 := by
      rw [show n + mtu.toNat + 4400 + 11 = n + 11 + mtu.toNat + 4400 by omega]; exact hc2
    have hdue2 : st2.globals.lookup "tick_due" = some (.bool s.tickDue) := by
      rw [hso2 "tick_due" (by decide)]; exact hdue
    have hb2 : st2.globals.lookup "booted" = some (.bool true) := by
      rw [hso2 "booted" (by decide)]; exact hb
    have hd1 := byteM_due s.tickDue k.toUInt8 (s, es) rfl
    have hI1 := byteM_pres Spec.Tcp.input_inv k.toUInt8 (s, es) hI
    have hB1 := byteM_pres Spec.Tcp.input_bnd k.toUInt8 (s, es) hBd
    obtain ⟨b2, hbuf2, hsz2, hle2, hlen2, hesc2, hover2, hmtuG2, hpre2⟩ := hnet2.rx.1
    have hbw2 : b2 = w2.b := bufVal_inj (Option.some.inj (hbuf2.symm.trans hnet2.holds.buf))
    subst hbw2
    have hz := ofNat16_eq_zero ((byteM k.toUInt8).run (s, es)).2.1.slip.buf.size (by omega)
    cases hcond : (((byteM k.toUInt8).run (s, es)).2.1.tickDue
        && ((byteM k.toUInt8).run (s, es)).2.1.slip.buf.size == 0) with
    | false =>
      rw [byteT_plain _ s es hcond]
      refine ⟨st2, w2, X2, ?_, ⟨hnet2, hb2, by rw [hd1]; exact hdue2, hI1, hB1⟩, hw2, htr2⟩
      rw [hfuel]
      exact main_byte p hp hP.slip_rx st hb k w0 hnx hk1 hk2 _ st2 hc2' s.tickDue _ hdue2 hlen2
        (by rw [hz, ← hd1]; exact hcond)
    | true =>
      have hcond' := hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond'
      have hst : s.tickDue = true := by rw [← hd1]; exact hcond'.1
      rw [byteT_tick _ s es hcond]
      have hnet3 : NetInv (setG st2 "tick_due" (.bool false))
          { ((byteM k.toUInt8).run (s, es)).2.1 with tickDue := false } w2 mtu ourIp N :=
        hnet2.rebuild _ _ (sameConsts_setG_due _ _)
          (fun x hx => lookup_setG_ne _ _ _ _ (by rcases hx with h | h | h | h | h | h <;> rw [h] <;> decide))
          hnet2.rx.2.2.2.1 (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hlen2)
          (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hesc2)
          (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hover2) hpre2 hle2 rfl rfl rfl rfl rfl
      obtain ⟨st4, w4, X4, hc4, hnet4, hw4, htr4, hso4⟩ := tick_step p hP hR _ _ w2 mtu ourIp N hnet3 hI1
        (hid255 _ hB1).1 (hid255 _ hB1).2 hcond'.2 ((byteM k.toUInt8).run (s, es)).2.2 (n + mtu.toNat + 2405)
      have hd4 := Spec.tickInput_due (Q := fun x _ _ => x = false)
        ({ ((byteM k.toUInt8).run (s, es)).2.1 with tickDue := false }, ((byteM k.toUInt8).run (s, es)).2.2) rfl
      refine ⟨st4, w4, X2 ++ X4, ?_, ⟨hnet4, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hfuel]
        exact main_byte_tick p hp hP.slip_rx hP.tcp_tick st hb k w0 hnx hk1 hk2 _ st2 hc2' (by rw [hdue2, hst])
          (by rw [hlen2, hcond'.2]; rfl) st4 (by rw [← hc4])
      · rw [hso4 "booted" (by decide), lookup_setG_ne _ _ _ _ (by decide)]; exact hb2
      · exact (hso4 "tick_due" (by decide)).trans ((lookup_setG _ _ _ _ hdue2).trans
          (congrArg (fun v => some (Val.bool v)) hd4.symm))
      · exact Spec.tickInput_pres Spec.Tcp.tick_inv _ hI1
      · exact Spec.tickInput_pres Spec.Tcp.tick_bnd _ hB1
      · rw [hw4, List.foldl_append, ← hw2]; rfl
      · refine Eq.trans htr4 ?_
        rw [htr2, List.filter_append, List.append_assoc]

/-- info: 'Ember.Proof.Refine.main_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_step

/-! ## The first call: boot -/

/-- The first call of `main` resets the control block and goes on as any other call. -/
theorem main_boot (p : Prog) (hp : p.fn? "main" = some main_fn) (hr : p.fn? "tcb_reset" = some tcb_reset)
    (st : St) (hb : st.globals.lookup "booted" = some (.bool false)) (m : Nat) (st1 : St)
    (hc : Sem.call (m + 32) p st "tcb_reset" [] = .ok none st1) (v : Val)
    (hb1 : st1.globals.lookup "booted" = some v) :
    Sem.call (m + 40) p st "main" [] = Sem.call (m + 40) p (setG st1 "booted" (.bool true)) "main" [] := by
  have hcall := execS_call_val p st [] (m + 32) none "tcb_reset" [] hr (by simp [tcb_reset]) (by simp [evalArgs]) hc
  have e1 : evalE p st [] (.un .lnot (.var "booted")) = some (.bool true) := by
    simp [evalE_un, evalE, lookup, hb]
  have e2 := main_booted p (setG st1 "booted" (.bool true)) [] (lookup_setG _ _ _ _ hb1) rfl
  main_sym [hp, e1, e2, hcall, hb1]

/-- The constants of the TCP part in the stack's initial state. -/
theorem net_tcp_consts (inputs : Array Trace.Input) : TcpConsts (Sem.initial Net.prog inputs) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def RawTcb.zero : RawTcb := ⟨0, 0, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, false⟩
def RawSeg.zero : RawSeg := ⟨0, 0, 0, 0, 0, 0, false, 0, 0, 0⟩

/-- The stack's state after the boot part of the first call of `main`. -/
def bootSt (inputs : Array Trace.Input) : St :=
  setG (with_t (Sem.initial Net.prog inputs) RawTcb.reset) "booted" (.bool true)

/-- The TCP state after boot (`b`: the packet buffer). -/
def bootW (b : ByteArray) : TW :=
  { r := RawTcb.reset, sg := RawSeg.zero, pd := ⟨Array.replicate 256 0⟩, b := b, id := 1, iss := Spec.issInit, evs := [] }

theorem initial_t (inputs : Array Trace.Input) :
    (Sem.initial Net.prog inputs).globals.lookup "t" = some RawTcb.zero.val := rfl

/-- **Boot, the code**: the first call of `main`, from the initial state,
is a call of `main` from `bootSt`. -/
theorem boot_call (p : Prog) (hP : TcpAll p) (hp : p.fn? "main" = some main_fn) (inputs : Array Trace.Input)
    (m : Nat) :
    Sem.call (m + 40) p (Sem.initial Net.prog inputs) "main" [] = Sem.call (m + 40) p (bootSt inputs) "main" [] := by
  have hc := tcb_reset_refines p hP.sTcb hP.tcb_reset (Sem.initial Net.prog inputs) _ (initial_t inputs)
    (net_tcp_consts inputs).LISTEN (net_tcp_consts inputs).OUR_MSS RawTcb.zero (m + 2)
  rw [show with_t (Sem.initial Net.prog inputs) RawTcb.zero = Sem.initial Net.prog inputs from
    setG_same _ _ _ (initial_t inputs)] at hc
  exact main_boot p hp hP.tcb_reset _ rfl m _ hc (.bool false) (by rw [lookup_with_t_ne _ _ _ (by decide)]; rfl)

/-- **Boot, the invariant**: `bootSt` satisfies `MainInv` against the Spec's initial state. -/
theorem boot_inv (inputs : Array Trace.Input) :
    ∃ w, MainInv (bootSt inputs) (Spec.State.init {}) w 296 Spec.ourIpDefault 296 := by
  have hlk : ∀ x, x ≠ "t" → x ≠ "booted" →
      (bootSt inputs).globals.lookup x = (Sem.initial Net.prog inputs).globals.lookup x := by
    intro x h1 h2
    unfold bootSt
    rw [lookup_setG_ne _ _ _ _ (Ne.symm h2), lookup_with_t_ne _ _ _ h1]
  have hsame : SameConsts (Sem.initial Net.prog inputs) (bootSt inputs) := fun x hx =>
    hlk x (fun e => hx (by rw [e]; decide)) (fun e => hx (by rw [e]; decide))
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtuG, hpre⟩, ⟨b0, hb0, hN⟩, hN', hfr, hid, hKin, hdo⟩ :=
    rx_initial inputs
  have hpd : (Sem.initial Net.prog inputs).globals.lookup "pend" = some (bufVal ⟨Array.replicate 256 0⟩) := by
    have hz : mask .w8 (UInt64.ofNat 0) = (0 : UInt8).toUInt64 := rfl
    have : List.lookup "pend" (Sem.initial Net.prog inputs).globals
        = some (.arr ((Array.range 256).map fun _ => Val.int .w8 (mask .w8 (UInt64.ofNat 0)))) := rfl
    rw [this, hz, bufVal]
    congr 2
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  have hsize : (ByteArray.mk (Array.replicate 256 0)).size = 256 := by simp [ByteArray.size]
  refine ⟨bootW b, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, ⟨reset_rel _ hsize, rfl, rfl, rfl, by decide, rfl, rfl⟩,
    ⟨⟨b, ?_, hsz, hle, ?_, ?_, ?_, ?_, hpre⟩, ⟨b0, ?_, hN⟩, hN', hfr, ?_, inConsts_same hKin hsame, ?_⟩,
    tcpConsts_same (net_tcp_consts inputs) hsame, ?_, by omega, rfl⟩, ?_, ?_, Spec.Tcp.inv_default,
    Spec.Tcp.bnd_default⟩
  · unfold bootSt
    rw [lookup_setG_ne _ _ _ _ (by decide)]
    exact lookup_with_t _ _ _ (initial_t inputs)
  · rw [hlk _ (by decide) (by decide)]; rfl
  · rw [hlk _ (by decide) (by decide)]; exact hpd
  · rw [hlk _ (by decide) (by decide)]; exact hbuf
  · rw [hlk _ (by decide) (by decide)]; exact hid
  · rw [hlk _ (by decide) (by decide)]; rfl
  · rw [hlk _ (by decide) (by decide)]; exact hbuf
  · rw [hlk _ (by decide) (by decide)]; exact hlen
  · rw [hlk _ (by decide) (by decide)]; exact hesc
  · rw [hlk _ (by decide) (by decide)]; exact hover
  · rw [hlk _ (by decide) (by decide)]; exact hmtuG
  · rw [hlk _ (by decide) (by decide)]; exact hb0
  · rw [hlk _ (by decide) (by decide)]; exact hid
  · rw [hlk _ (by decide) (by decide)]; exact hdo
  · rw [hlk _ (by decide) (by decide)]; rfl
  · unfold bootSt
    exact lookup_setG _ _ _ (.bool false) (by rw [lookup_with_t_ne _ _ _ (by decide)]; rfl)
  · rw [hlk _ (by decide) (by decide)]; rfl

/-- info: 'Ember.Proof.Refine.boot_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boot_inv

end Ember.Proof.Refine
