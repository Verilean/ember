import Ember.Proof.RefineRx

/-!
# Ember.Proof.RefineTcp — TCP: the records, the small functions, and sending a segment (plan M5.5)

The first part of the TCP code (`Ember/Net/Tcp.lean`):

* the connection record `t` and the segment record `sg` as Lean
  structures (`RawTcb`, `RawSeg`), with a lemma for reading and for
  writing each field;
* `tcb_reset`, `cap`, `wnd`, `seg_len`;
* `tcp_emit`: the segment it builds in the packet buffer — data copied
  from the echo buffer by a loop, header, MSS option, checksum — is
  `Spec.Tcp.emit`, sent in `Spec.Ipv4.packet`.

The state machine (`tcp_segment`, `output`, `tcp_tick`, …) is not here.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-! ## Records -/

/-- A field of a record variable. -/
theorem evalE_field (p : Prog) (st : St) (env : Env) (x r f : String) (fs : Array Val) (i : Nat)
    (hx : lookup st env x = some (.record r fs)) (hi : fieldIndex p r f = some i) :
    evalE p st env (.field (.var x) f) = fs[i]? := by
  simp only [evalE, hx, hi]

/-- `x.f := v` for a global record that no local hides. -/
theorem assign_field (p : Prog) (st : St) (env : Env) (x r f : String) (fs : Array Val) (i : Nat) (v : Val)
    (hl : env.lookup x = none) (hg : st.globals.lookup x = some (.record r fs))
    (hi : fieldIndex p r f = some i) (hlt : i < fs.size) :
    assign p st env (.field (.var x) f) v = some (setG st x (.record r (fs.set! i v)), env) := by
  have hget : fs[i]? = some fs[i] := by simp [hlt]
  simp only [assign, update, hl, hg, hi, hget, setG]

/-! ## 32-bit arithmetic -/

theorem mask32_u16 (x : UInt16) : mask .w32 x.toUInt64 = x.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [toNat_mask32, UInt16.toNat_toUInt64, UInt32.toNat_toUInt64, UInt16.toNat_toUInt32]
  omega

theorem mask32_add (x y : UInt32) : mask .w32 (x.toUInt64 + y.toUInt64) = (x + y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [toNat_mask32, UInt32.toNat_toUInt64, UInt64.toNat_add, UInt32.toNat_add]
  omega

theorem mask32_sub (x y : UInt32) : mask .w32 (x.toUInt64 - y.toUInt64) = (x - y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [toNat_mask32, UInt32.toNat_toUInt64, UInt64.toNat_sub, UInt32.toNat_sub]
  omega

theorem toUInt64_lt_iff32 (x y : UInt32) : decide (x.toUInt64 < y.toUInt64) = decide (x < y) := by
  have : x.toUInt64 < y.toUInt64 ↔ x < y := by
    rw [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]; simp
  simp [this]

theorem toUInt64_lt_iff8 (x y : UInt8) : decide (x.toUInt64 < y.toUInt64) = decide (x < y) := by
  have : x.toUInt64 < y.toUInt64 ↔ x < y := by
    rw [UInt64.lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]; simp
  simp [this]

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## The connection record `t` and the segment record `sg` -/

/-- The record `t` of the stack, field by field. -/
structure RawTcb where
  st : UInt8
  rip : UInt32
  rport : UInt16
  snd_una : UInt32
  snd_nxt : UInt32
  rcv_nxt : UInt32
  pend_len : UInt16
  sent : UInt16
  fin_sent : Bool
  peer_mss : UInt16
  our_mss : UInt16
  last_wnd : UInt16
  rt_timer : UInt8
  retries : UInt8
  tw_timer : UInt8
  idle : UInt8
  close_req : Bool

/-- The value the semantics has for it. -/
def RawTcb.val (r : RawTcb) : Val :=
  .record "Tcb" #[u8 r.st, u32 r.rip, u16 r.rport, u32 r.snd_una, u32 r.snd_nxt, u32 r.rcv_nxt, u16 r.pend_len, u16 r.sent, Val.bool r.fin_sent, u16 r.peer_mss, u16 r.our_mss, u16 r.last_wnd, u8 r.rt_timer, u8 r.retries, u8 r.tw_timer, u8 r.idle, Val.bool r.close_req]

theorem RawTcb.get_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "st") = some (u8 r.st) := by
  have hi : Sem.fieldIndex p "Tcb" "st" = some 0 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "st" _ 0 h hi]
  simp

theorem RawTcb.set_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt8) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "st") (u8 x)
      = some (setG st "t" ({ r with st := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "st" = some 0 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "st" _ 0 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "rip") = some (u32 r.rip) := by
  have hi : Sem.fieldIndex p "Tcb" "rip" = some 1 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "rip" _ 1 h hi]
  simp

theorem RawTcb.set_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt32) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "rip") (u32 x)
      = some (setG st "t" ({ r with rip := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "rip" = some 1 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "rip" _ 1 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "rport") = some (u16 r.rport) := by
  have hi : Sem.fieldIndex p "Tcb" "rport" = some 2 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "rport" _ 2 h hi]
  simp

theorem RawTcb.set_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "rport") (u16 x)
      = some (setG st "t" ({ r with rport := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "rport" = some 2 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "rport" _ 2 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "snd_una") = some (u32 r.snd_una) := by
  have hi : Sem.fieldIndex p "Tcb" "snd_una" = some 3 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "snd_una" _ 3 h hi]
  simp

theorem RawTcb.set_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt32) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "snd_una") (u32 x)
      = some (setG st "t" ({ r with snd_una := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "snd_una" = some 3 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "snd_una" _ 3 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "snd_nxt") = some (u32 r.snd_nxt) := by
  have hi : Sem.fieldIndex p "Tcb" "snd_nxt" = some 4 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "snd_nxt" _ 4 h hi]
  simp

theorem RawTcb.set_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt32) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "snd_nxt") (u32 x)
      = some (setG st "t" ({ r with snd_nxt := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "snd_nxt" = some 4 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "snd_nxt" _ 4 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "rcv_nxt") = some (u32 r.rcv_nxt) := by
  have hi : Sem.fieldIndex p "Tcb" "rcv_nxt" = some 5 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "rcv_nxt" _ 5 h hi]
  simp

theorem RawTcb.set_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt32) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "rcv_nxt") (u32 x)
      = some (setG st "t" ({ r with rcv_nxt := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "rcv_nxt" = some 5 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "rcv_nxt" _ 5 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "pend_len") = some (u16 r.pend_len) := by
  have hi : Sem.fieldIndex p "Tcb" "pend_len" = some 6 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "pend_len" _ 6 h hi]
  simp

theorem RawTcb.set_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "pend_len") (u16 x)
      = some (setG st "t" ({ r with pend_len := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "pend_len" = some 6 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "pend_len" _ 6 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "sent") = some (u16 r.sent) := by
  have hi : Sem.fieldIndex p "Tcb" "sent" = some 7 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "sent" _ 7 h hi]
  simp

theorem RawTcb.set_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "sent") (u16 x)
      = some (setG st "t" ({ r with sent := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "sent" = some 7 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "sent" _ 7 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "fin_sent") = some (Val.bool r.fin_sent) := by
  have hi : Sem.fieldIndex p "Tcb" "fin_sent" = some 8 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "fin_sent" _ 8 h hi]
  simp

theorem RawTcb.set_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : Bool) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "fin_sent") (Val.bool x)
      = some (setG st "t" ({ r with fin_sent := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "fin_sent" = some 8 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "fin_sent" _ 8 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "peer_mss") = some (u16 r.peer_mss) := by
  have hi : Sem.fieldIndex p "Tcb" "peer_mss" = some 9 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "peer_mss" _ 9 h hi]
  simp

theorem RawTcb.set_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "peer_mss") (u16 x)
      = some (setG st "t" ({ r with peer_mss := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "peer_mss" = some 9 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "peer_mss" _ 9 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "our_mss") = some (u16 r.our_mss) := by
  have hi : Sem.fieldIndex p "Tcb" "our_mss" = some 10 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "our_mss" _ 10 h hi]
  simp

theorem RawTcb.set_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "our_mss") (u16 x)
      = some (setG st "t" ({ r with our_mss := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "our_mss" = some 10 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "our_mss" _ 10 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "last_wnd") = some (u16 r.last_wnd) := by
  have hi : Sem.fieldIndex p "Tcb" "last_wnd" = some 11 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "last_wnd" _ 11 h hi]
  simp

theorem RawTcb.set_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt16) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "last_wnd") (u16 x)
      = some (setG st "t" ({ r with last_wnd := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "last_wnd" = some 11 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "last_wnd" _ 11 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "rt_timer") = some (u8 r.rt_timer) := by
  have hi : Sem.fieldIndex p "Tcb" "rt_timer" = some 12 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "rt_timer" _ 12 h hi]
  simp

theorem RawTcb.set_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt8) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "rt_timer") (u8 x)
      = some (setG st "t" ({ r with rt_timer := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "rt_timer" = some 12 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "rt_timer" _ 12 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "retries") = some (u8 r.retries) := by
  have hi : Sem.fieldIndex p "Tcb" "retries" = some 13 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "retries" _ 13 h hi]
  simp

theorem RawTcb.set_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt8) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "retries") (u8 x)
      = some (setG st "t" ({ r with retries := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "retries" = some 13 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "retries" _ 13 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "tw_timer") = some (u8 r.tw_timer) := by
  have hi : Sem.fieldIndex p "Tcb" "tw_timer" = some 14 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "tw_timer" _ 14 h hi]
  simp

theorem RawTcb.set_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt8) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "tw_timer") (u8 x)
      = some (setG st "t" ({ r with tw_timer := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "tw_timer" = some 14 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "tw_timer" _ 14 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "idle") = some (u8 r.idle) := by
  have hi : Sem.fieldIndex p "Tcb" "idle" = some 15 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "idle" _ 15 h hi]
  simp

theorem RawTcb.set_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : UInt8) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "idle") (u8 x)
      = some (setG st "t" ({ r with idle := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "idle" = some 15 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "idle" _ 15 _ hl h hi (by simp)]
  simp [RawTcb.val]

theorem RawTcb.get_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (h : lookup st env "t" = some r.val) :
    evalE p st env (.field (.var "t") "close_req") = some (Val.bool r.close_req) := by
  have hi : Sem.fieldIndex p "Tcb" "close_req" = some 16 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "t" "Tcb" "close_req" _ 16 h hi]
  simp

theorem RawTcb.set_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (r : RawTcb)
    (x : Bool) (hl : env.lookup "t" = none) (h : st.globals.lookup "t" = some r.val) :
    assign p st env (.field (.var "t") "close_req") (Val.bool x)
      = some (setG st "t" ({ r with close_req := x } : RawTcb).val, env) := by
  have hi : Sem.fieldIndex p "Tcb" "close_req" = some 16 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "t" "Tcb" "close_req" _ 16 _ hl h hi (by simp)]
  simp [RawTcb.val]


/-- The record `sg` of the stack, field by field. -/
structure RawSeg where
  src : UInt32
  sport : UInt16
  dport : UInt16
  seq : UInt32
  ack : UInt32
  flags : UInt8
  has_mss : Bool
  mss : UInt16
  doff : UInt16
  dlen : UInt16

/-- The value the semantics has for it. -/
def RawSeg.val (r : RawSeg) : Val :=
  .record "Seg" #[u32 r.src, u16 r.sport, u16 r.dport, u32 r.seq, u32 r.ack, u8 r.flags, Val.bool r.has_mss, u16 r.mss, u16 r.doff, u16 r.dlen]

theorem RawSeg.get_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "src") = some (u32 r.src) := by
  have hi : Sem.fieldIndex p "Seg" "src" = some 0 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "src" _ 0 h hi]
  simp

theorem RawSeg.set_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt32) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "src") (u32 x)
      = some (setG st "sg" ({ r with src := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "src" = some 0 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "src" _ 0 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "sport") = some (u16 r.sport) := by
  have hi : Sem.fieldIndex p "Seg" "sport" = some 1 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "sport" _ 1 h hi]
  simp

theorem RawSeg.set_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt16) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "sport") (u16 x)
      = some (setG st "sg" ({ r with sport := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "sport" = some 1 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "sport" _ 1 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "dport") = some (u16 r.dport) := by
  have hi : Sem.fieldIndex p "Seg" "dport" = some 2 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "dport" _ 2 h hi]
  simp

theorem RawSeg.set_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt16) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "dport") (u16 x)
      = some (setG st "sg" ({ r with dport := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "dport" = some 2 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "dport" _ 2 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "seq") = some (u32 r.seq) := by
  have hi : Sem.fieldIndex p "Seg" "seq" = some 3 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "seq" _ 3 h hi]
  simp

theorem RawSeg.set_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt32) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "seq") (u32 x)
      = some (setG st "sg" ({ r with seq := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "seq" = some 3 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "seq" _ 3 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "ack") = some (u32 r.ack) := by
  have hi : Sem.fieldIndex p "Seg" "ack" = some 4 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "ack" _ 4 h hi]
  simp

theorem RawSeg.set_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt32) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "ack") (u32 x)
      = some (setG st "sg" ({ r with ack := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "ack" = some 4 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "ack" _ 4 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "flags") = some (u8 r.flags) := by
  have hi : Sem.fieldIndex p "Seg" "flags" = some 5 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "flags" _ 5 h hi]
  simp

theorem RawSeg.set_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt8) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "flags") (u8 x)
      = some (setG st "sg" ({ r with flags := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "flags" = some 5 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "flags" _ 5 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "has_mss") = some (Val.bool r.has_mss) := by
  have hi : Sem.fieldIndex p "Seg" "has_mss" = some 6 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "has_mss" _ 6 h hi]
  simp

theorem RawSeg.set_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : Bool) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "has_mss") (Val.bool x)
      = some (setG st "sg" ({ r with has_mss := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "has_mss" = some 6 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "has_mss" _ 6 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "mss") = some (u16 r.mss) := by
  have hi : Sem.fieldIndex p "Seg" "mss" = some 7 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "mss" _ 7 h hi]
  simp

theorem RawSeg.set_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt16) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "mss") (u16 x)
      = some (setG st "sg" ({ r with mss := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "mss" = some 7 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "mss" _ 7 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "doff") = some (u16 r.doff) := by
  have hi : Sem.fieldIndex p "Seg" "doff" = some 8 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "doff" _ 8 h hi]
  simp

theorem RawSeg.set_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt16) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "doff") (u16 x)
      = some (setG st "sg" ({ r with doff := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "doff" = some 8 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "doff" _ 8 _ hl h hi (by simp)]
  simp [RawSeg.val]

theorem RawSeg.get_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (h : lookup st env "sg" = some r.val) :
    evalE p st env (.field (.var "sg") "dlen") = some (u16 r.dlen) := by
  have hi : Sem.fieldIndex p "Seg" "dlen" = some 9 := by rw [Sem.fieldIndex, hS]; rfl
  rw [evalE_field p st env "sg" "Seg" "dlen" _ 9 h hi]
  simp

theorem RawSeg.set_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (r : RawSeg)
    (x : UInt16) (hl : env.lookup "sg" = none) (h : st.globals.lookup "sg" = some r.val) :
    assign p st env (.field (.var "sg") "dlen") (u16 x)
      = some (setG st "sg" ({ r with dlen := x } : RawSeg).val, env) := by
  have hi : Sem.fieldIndex p "Seg" "dlen" = some 9 := by rw [Sem.fieldIndex, hS]; rfl
  rw [assign_field p st env "sg" "Seg" "dlen" _ 9 _ hl h hi (by simp)]
  simp [RawSeg.val]


/-- The state with `t` holding `r`. -/
def with_t (st : St) (r : RawTcb) : St := setG st "t" r.val

theorem lookup_with_t (st : St) (r : RawTcb) (v0 : Val) (h0 : st.globals.lookup "t" = some v0) :
    (with_t st r).globals.lookup "t" = some r.val := lookup_setG st _ _ _ h0

theorem lookup_with_t_ne (st : St) (r : RawTcb) (x : String) (hx : x ≠ "t") :
    (with_t st r).globals.lookup x = st.globals.lookup x := lookup_setG_ne st _ _ _ (Ne.symm hx)

theorem RawTcb.getW_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "st") = some (u8 r.st) :=
  RawTcb.get_st p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt8) :
    assign p (with_t st r) env (.field (.var "t") "st") (u8 x)
      = some (with_t st { r with st := x }, env) := by
  rw [RawTcb.set_st p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "rip") = some (u32 r.rip) :=
  RawTcb.get_rip p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt32) :
    assign p (with_t st r) env (.field (.var "t") "rip") (u32 x)
      = some (with_t st { r with rip := x }, env) := by
  rw [RawTcb.set_rip p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "rport") = some (u16 r.rport) :=
  RawTcb.get_rport p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "rport") (u16 x)
      = some (with_t st { r with rport := x }, env) := by
  rw [RawTcb.set_rport p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "snd_una") = some (u32 r.snd_una) :=
  RawTcb.get_snd_una p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt32) :
    assign p (with_t st r) env (.field (.var "t") "snd_una") (u32 x)
      = some (with_t st { r with snd_una := x }, env) := by
  rw [RawTcb.set_snd_una p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "snd_nxt") = some (u32 r.snd_nxt) :=
  RawTcb.get_snd_nxt p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt32) :
    assign p (with_t st r) env (.field (.var "t") "snd_nxt") (u32 x)
      = some (with_t st { r with snd_nxt := x }, env) := by
  rw [RawTcb.set_snd_nxt p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "rcv_nxt") = some (u32 r.rcv_nxt) :=
  RawTcb.get_rcv_nxt p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt32) :
    assign p (with_t st r) env (.field (.var "t") "rcv_nxt") (u32 x)
      = some (with_t st { r with rcv_nxt := x }, env) := by
  rw [RawTcb.set_rcv_nxt p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "pend_len") = some (u16 r.pend_len) :=
  RawTcb.get_pend_len p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "pend_len") (u16 x)
      = some (with_t st { r with pend_len := x }, env) := by
  rw [RawTcb.set_pend_len p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "sent") = some (u16 r.sent) :=
  RawTcb.get_sent p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "sent") (u16 x)
      = some (with_t st { r with sent := x }, env) := by
  rw [RawTcb.set_sent p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "fin_sent") = some (Val.bool r.fin_sent) :=
  RawTcb.get_fin_sent p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : Bool) :
    assign p (with_t st r) env (.field (.var "t") "fin_sent") (Val.bool x)
      = some (with_t st { r with fin_sent := x }, env) := by
  rw [RawTcb.set_fin_sent p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "peer_mss") = some (u16 r.peer_mss) :=
  RawTcb.get_peer_mss p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "peer_mss") (u16 x)
      = some (with_t st { r with peer_mss := x }, env) := by
  rw [RawTcb.set_peer_mss p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "our_mss") = some (u16 r.our_mss) :=
  RawTcb.get_our_mss p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "our_mss") (u16 x)
      = some (with_t st { r with our_mss := x }, env) := by
  rw [RawTcb.set_our_mss p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "last_wnd") = some (u16 r.last_wnd) :=
  RawTcb.get_last_wnd p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt16) :
    assign p (with_t st r) env (.field (.var "t") "last_wnd") (u16 x)
      = some (with_t st { r with last_wnd := x }, env) := by
  rw [RawTcb.set_last_wnd p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "rt_timer") = some (u8 r.rt_timer) :=
  RawTcb.get_rt_timer p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt8) :
    assign p (with_t st r) env (.field (.var "t") "rt_timer") (u8 x)
      = some (with_t st { r with rt_timer := x }, env) := by
  rw [RawTcb.set_rt_timer p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "retries") = some (u8 r.retries) :=
  RawTcb.get_retries p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt8) :
    assign p (with_t st r) env (.field (.var "t") "retries") (u8 x)
      = some (with_t st { r with retries := x }, env) := by
  rw [RawTcb.set_retries p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "tw_timer") = some (u8 r.tw_timer) :=
  RawTcb.get_tw_timer p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt8) :
    assign p (with_t st r) env (.field (.var "t") "tw_timer") (u8 x)
      = some (with_t st { r with tw_timer := x }, env) := by
  rw [RawTcb.set_tw_timer p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "idle") = some (u8 r.idle) :=
  RawTcb.get_idle p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : UInt8) :
    assign p (with_t st r) env (.field (.var "t") "idle") (u8 x)
      = some (with_t st { r with idle := x }, env) := by
  rw [RawTcb.set_idle p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]

theorem RawTcb.getW_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) :
    evalE p (with_t st r) env (.field (.var "t") "close_req") = some (Val.bool r.close_req) :=
  RawTcb.get_close_req p hS _ env r (by simp only [lookup, hl]; exact lookup_with_t st r v0 h0)

theorem RawTcb.setW_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "t" = none) (h0 : st.globals.lookup "t" = some v0) (r : RawTcb) (x : Bool) :
    assign p (with_t st r) env (.field (.var "t") "close_req") (Val.bool x)
      = some (with_t st { r with close_req := x }, env) := by
  rw [RawTcb.set_close_req p hS _ env r x hl (lookup_with_t st r v0 h0)]
  simp only [with_t, setG_setG]


/-- The state with `sg` holding `r`. -/
def with_sg (st : St) (r : RawSeg) : St := setG st "sg" r.val

theorem lookup_with_sg (st : St) (r : RawSeg) (v0 : Val) (h0 : st.globals.lookup "sg" = some v0) :
    (with_sg st r).globals.lookup "sg" = some r.val := lookup_setG st _ _ _ h0

theorem lookup_with_sg_ne (st : St) (r : RawSeg) (x : String) (hx : x ≠ "sg") :
    (with_sg st r).globals.lookup x = st.globals.lookup x := lookup_setG_ne st _ _ _ (Ne.symm hx)

theorem RawSeg.getW_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "src") = some (u32 r.src) :=
  RawSeg.get_src p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt32) :
    assign p (with_sg st r) env (.field (.var "sg") "src") (u32 x)
      = some (with_sg st { r with src := x }, env) := by
  rw [RawSeg.set_src p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "sport") = some (u16 r.sport) :=
  RawSeg.get_sport p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt16) :
    assign p (with_sg st r) env (.field (.var "sg") "sport") (u16 x)
      = some (with_sg st { r with sport := x }, env) := by
  rw [RawSeg.set_sport p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "dport") = some (u16 r.dport) :=
  RawSeg.get_dport p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt16) :
    assign p (with_sg st r) env (.field (.var "sg") "dport") (u16 x)
      = some (with_sg st { r with dport := x }, env) := by
  rw [RawSeg.set_dport p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "seq") = some (u32 r.seq) :=
  RawSeg.get_seq p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt32) :
    assign p (with_sg st r) env (.field (.var "sg") "seq") (u32 x)
      = some (with_sg st { r with seq := x }, env) := by
  rw [RawSeg.set_seq p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "ack") = some (u32 r.ack) :=
  RawSeg.get_ack p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt32) :
    assign p (with_sg st r) env (.field (.var "sg") "ack") (u32 x)
      = some (with_sg st { r with ack := x }, env) := by
  rw [RawSeg.set_ack p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "flags") = some (u8 r.flags) :=
  RawSeg.get_flags p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt8) :
    assign p (with_sg st r) env (.field (.var "sg") "flags") (u8 x)
      = some (with_sg st { r with flags := x }, env) := by
  rw [RawSeg.set_flags p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "has_mss") = some (Val.bool r.has_mss) :=
  RawSeg.get_has_mss p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : Bool) :
    assign p (with_sg st r) env (.field (.var "sg") "has_mss") (Val.bool x)
      = some (with_sg st { r with has_mss := x }, env) := by
  rw [RawSeg.set_has_mss p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "mss") = some (u16 r.mss) :=
  RawSeg.get_mss p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt16) :
    assign p (with_sg st r) env (.field (.var "sg") "mss") (u16 x)
      = some (with_sg st { r with mss := x }, env) := by
  rw [RawSeg.set_mss p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "doff") = some (u16 r.doff) :=
  RawSeg.get_doff p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt16) :
    assign p (with_sg st r) env (.field (.var "sg") "doff") (u16 x)
      = some (with_sg st { r with doff := x }, env) := by
  rw [RawSeg.set_doff p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]

theorem RawSeg.getW_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) :
    evalE p (with_sg st r) env (.field (.var "sg") "dlen") = some (u16 r.dlen) :=
  RawSeg.get_dlen p hS _ env r (by simp only [lookup, hl]; exact lookup_with_sg st r v0 h0)

theorem RawSeg.setW_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (env : Env) (v0 : Val)
    (hl : env.lookup "sg" = none) (h0 : st.globals.lookup "sg" = some v0) (r : RawSeg) (x : UInt16) :
    assign p (with_sg st r) env (.field (.var "sg") "dlen") (u16 x)
      = some (with_sg st { r with dlen := x }, env) := by
  rw [RawSeg.set_dlen p hS _ env r x hl (lookup_with_sg st r v0 h0)]
  simp only [with_sg, setG_setG]


/-! ## `tcb_reset` -/

def tcb_reset : Fn := checked_fn% Net.prog, "tcb_reset"
#guard (Net.prog.check.toOption.bind (·.fn? "tcb_reset")) == some tcb_reset

/-- The connection record of a closed connection (`Spec.Tcp.Tcb`'s defaults). -/
def RawTcb.reset : RawTcb :=
  { st := 0, rip := 0, rport := 0, snd_una := 0, snd_nxt := 0, rcv_nxt := 0, pend_len := 0, sent := 0,
    fin_sent := false, peer_mss := 536, our_mss := 256, last_wnd := 0, rt_timer := 0, retries := 0,
    tw_timer := 0, idle := 0, close_req := false }

/-- **`tcb_reset`** puts the connection record back to LISTEN with every
field at its default; nothing else changes. -/
theorem tcb_reset_refines (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb)
    (hp : p.fn? "tcb_reset" = some tcb_reset) (st : St) (v0 : Val) (h0 : st.globals.lookup "t" = some v0)
    (hL : st.globals.lookup "LISTEN" = some (u8 0)) (hM : st.globals.lookup "OUR_MSS" = some (u16 256))
    (r : RawTcb) (n : Nat) :
    Sem.call (n + 30) p (with_t st r) "tcb_reset" [] = .ok none (with_t st RawTcb.reset) := by
  have eL : ∀ r', evalE p (with_t st r') [] (.var "LISTEN") = some (u8 0) := by
    intro r'; simp only [evalE, lookup, List.lookup, lookup_with_t_ne st r' "LISTEN" (by decide), hL]
  have eM : ∀ r', evalE p (with_t st r') [] (.var "OUR_MSS") = some (u16 256) := by
    intro r'; simp only [evalE, lookup, List.lookup, lookup_with_t_ne st r' "OUR_MSS" (by decide), hM]
  have eb : ∀ (S : St) (b : Bool), evalE p S [] (.blit b) = some (.bool b) := by
    intro S b; simp only [evalE]
  have e32 : ∀ (S : St) (k : Nat), evalE p S [] (.lit k (some .w32)) = some (u32 (UInt32.ofNat k)) := by
    intro S k; rw [evalE_lit, mask32_ofNat]
  simp only [Sem.call, hp, tcb_reset, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, List.map, List.zip,
    List.zipWith, eL, eM, eb, e32, evalE_lit16, evalE_lit8, RawTcb.setW_st p hS st [] v0 rfl h0, RawTcb.setW_rip p hS st [] v0 rfl h0, RawTcb.setW_rport p hS st [] v0 rfl h0, RawTcb.setW_snd_una p hS st [] v0 rfl h0, RawTcb.setW_snd_nxt p hS st [] v0 rfl h0, RawTcb.setW_rcv_nxt p hS st [] v0 rfl h0, RawTcb.setW_pend_len p hS st [] v0 rfl h0, RawTcb.setW_sent p hS st [] v0 rfl h0, RawTcb.setW_fin_sent p hS st [] v0 rfl h0, RawTcb.setW_peer_mss p hS st [] v0 rfl h0, RawTcb.setW_our_mss p hS st [] v0 rfl h0, RawTcb.setW_last_wnd p hS st [] v0 rfl h0, RawTcb.setW_rt_timer p hS st [] v0 rfl h0, RawTcb.setW_retries p hS st [] v0 rfl h0, RawTcb.setW_tw_timer p hS st [] v0 rfl h0, RawTcb.setW_idle p hS st [] v0 rfl h0, RawTcb.setW_close_req p hS st [] v0 rfl h0]
  rfl

/-! ## `cap`, `wnd`, `seg_len` -/

def cap : Fn := checked_fn% Net.prog, "cap"
#guard (Net.prog.check.toOption.bind (·.fn? "cap")) == some cap
def wnd : Fn := checked_fn% Net.prog, "wnd"
#guard (Net.prog.check.toOption.bind (·.fn? "wnd")) == some wnd
def seg_len : Fn := checked_fn% Net.prog, "seg_len"
#guard (Net.prog.check.toOption.bind (·.fn? "seg_len")) == some seg_len

/-- The echo buffer's capacity: the smaller MSS. -/
def RawTcb.cap (r : RawTcb) : UInt16 := if r.our_mss < r.peer_mss then r.our_mss else r.peer_mss

/-- The receive window: the room left in the echo buffer. -/
def RawTcb.wnd (r : RawTcb) : UInt16 := r.cap - r.pend_len

/-- Sequence space of the segment: data, SYN, FIN. -/
def RawSeg.len (s : RawSeg) : UInt32 :=
  s.dlen.toUInt32 + (if s.flags &&& 2 != 0 then 1 else 0) + (if s.flags &&& 1 != 0 then 1 else 0)

theorem cap_refines (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (hp : p.fn? "cap" = some cap)
    (st : St) (r : RawTcb) (ht : st.globals.lookup "t" = some r.val) (n : Nat) :
    Sem.call (n + 8) p st "cap" [] = .ok (some (u16 r.cap)) st := by
  have hl : lookup st [] "t" = some r.val := by simp only [lookup, List.lookup]; exact ht
  have g1 := RawTcb.get_our_mss p hS st [] r hl
  have g2 := RawTcb.get_peer_mss p hS st [] r hl
  have ec : evalE p st [] (.bin .lt (.field (.var "t") "our_mss") (.field (.var "t") "peer_mss"))
      = some (.bool (decide (r.our_mss < r.peer_mss))) := by
    simp only [evalE_bin, g1, g2, Sem.binop, toUInt64_lt_iff]
  simp only [Sem.call, hp, cap, execB_succ, execL_cons, execL_nil, execS_at, List.map, List.zip, List.zipWith]
  by_cases h : r.our_mss < r.peer_mss
  · simp only [h, decide_true] at ec
    simp only [execS_ite_true, ec, execB_succ, execL_cons, execS_at, execS_ret_some, g1, RawTcb.cap, h, if_true]
  · simp only [h, decide_false] at ec
    simp only [execS_ite_false, ec, execB_succ, execL_cons, execL_nil, execS_at, execS_ret_some, g2, RawTcb.cap, h,
      if_false, List.length_nil, Nat.sub_self, List.drop_zero]

theorem execS_cap (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (hp : p.fn? "cap" = some cap)
    (st : St) (env : Env) (r : RawTcb) (ht : st.globals.lookup "t" = some r.val) (dst : Option Expr) (n : Nat) :
    execS (n + 9) p st env (.call dst "cap" []) = storeResult p st env dst (some (u16 r.cap)) :=
  execS_call_val p st env (n + 8) dst "cap" [] hp (by simp [cap]) (by simp [evalArgs])
    (cap_refines p hS hp st r ht n)

theorem wnd_refines (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (hc : p.fn? "cap" = some cap)
    (hp : p.fn? "wnd" = some wnd) (st : St) (r : RawTcb) (ht : st.globals.lookup "t" = some r.val) (n : Nat) :
    Sem.call (n + 20) p st "wnd" [] = .ok (some (u16 r.wnd)) st := by
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have hl : lookup st [("c", u16 r.cap)] "t" = some r.val := by simp [lookup, List.lookup, ht]
  have g1 := RawTcb.get_pend_len p hS st [("c", u16 r.cap)] r hl
  have ev : evalE p st [("c", u16 r.cap)] (.bin .sub (.var "c") (.field (.var "t") "pend_len"))
      = some (u16 r.wnd) := by
    have e1 : evalE p st [("c", u16 r.cap)] (.var "c") = some (u16 r.cap) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, e1, g1, Sem.binop, mask16_sub, RawTcb.wnd]
  simp only [Sem.call, hp, wnd, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, hz, List.map,
    List.zip, List.zipWith]
  rw [execS_cap p hS hc st _ r ht]
  simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, execS_ret_some, ev]

theorem execS_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (hc : p.fn? "cap" = some cap)
    (hp : p.fn? "wnd" = some wnd) (st : St) (env : Env) (r : RawTcb) (ht : st.globals.lookup "t" = some r.val)
    (dst : Option Expr) (n : Nat) :
    execS (n + 21) p st env (.call dst "wnd" []) = storeResult p st env dst (some (u16 r.wnd)) :=
  execS_call_val p st env (n + 20) dst "wnd" [] hp (by simp [wnd]) (by simp [evalArgs])
    (wnd_refines p hS hc hp st r ht n)

theorem seg_len_refines (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (hp : p.fn? "seg_len" = some seg_len)
    (st : St) (s : RawSeg) (hsg : st.globals.lookup "sg" = some s.val)
    (hSYN : st.globals.lookup "F_SYN" = some (u8 2)) (hFIN : st.globals.lookup "F_FIN" = some (u8 1)) (n : Nat) :
    Sem.call (n + 12) p st "seg_len" [] = .ok (some (u32 s.len)) st := by
  have gl : ∀ (l : UInt32) (x : String) (v : Val), x ≠ "l" → st.globals.lookup x = some v →
      lookup st [("l", u32 l)] x = some v := by
    intro l x v hx h
    have : (x == "l") = false := by simp [hx]
    simp only [lookup, List.lookup, this, h]
  have ecast : evalE p st [] (.cast .w32 (.field (.var "sg") "dlen")) = some (u32 s.dlen.toUInt32) := by
    rw [evalE, RawSeg.get_dlen p hS st [] s (by simp only [lookup, List.lookup]; exact hsg)]
    simp only [mask32_u16]
  have eflag : ∀ (l : UInt32) (c : String) (k : UInt8), c ≠ "l" → st.globals.lookup c = some (u8 k) →
      evalE p st [("l", u32 l)] (.bin .ne (.bin .band (.field (.var "sg") "flags") (.var c)) (.lit 0 (some .w8)))
        = some (.bool (s.flags &&& k != 0)) := by
    intro l c k hc hk
    have e1 := RawSeg.get_flags p hS st [("l", u32 l)] s (gl l "sg" _ (by decide) hsg)
    have e2 : evalE p st [("l", u32 l)] (.var c) = some (u8 k) := by rw [evalE_var]; exact gl l c _ hc hk
    simp only [evalE_bin, e1, e2, evalE_lit8, Sem.binop, mask8_and, toUInt64_ne_iff8]
    rfl
  have einc : ∀ l : UInt32, evalE p st [("l", u32 l)] (.bin .add (.var "l") (.lit 1 (some .w32)))
      = some (u32 (l + 1)) := by
    intro l
    have e1 : evalE p st [("l", u32 l)] (.var "l") = some (u32 l) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, e1, evalE_lit, mask32_ofNat, Sem.binop, mask32_add]
    rfl
  have eret : ∀ l : UInt32, evalE p st [("l", u32 l)] (.var "l") = some (u32 l) := by
    intro l; simp [evalE, lookup, List.lookup]
  have step : ∀ (m : Nat) (l : UInt32) (c : String) (k : UInt8) (sp sp' : Span), c ≠ "l" →
      st.globals.lookup c = some (u8 k) →
      execS (m + 6) p st [("l", u32 l)]
        (.ite (.bin .ne (.bin .band (.field (.var "sg") "flags") (.var c)) (.lit 0 (some .w8)))
          [.at sp' (.assign (.var "l") (.bin .add (.var "l") (.lit 1 (some .w32))))] [])
        = .ok st [("l", u32 (l + (if s.flags &&& k != 0 then 1 else 0)))] .normal := by
    intro m l c k sp sp' hc hk
    rw [execS_ite, eflag l c k hc hk]
    cases hb : (s.flags &&& k != 0) with
    | true =>
      simp only [Val.toBool, if_true, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, einc, assign_var,
        List.lookup, beq_self_eq_true, setFirst, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
    | false =>
      simp only [Val.toBool, Bool.false_eq_true, if_false, execB_succ, execL_nil, List.length_cons,
        List.length_nil, Nat.sub_self, List.drop_zero, UInt32.add_zero]
  simp only [Sem.call, hp, seg_len, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_some, ecast, List.map,
    List.zip, List.zipWith]
  rw [step _ _ "F_SYN" 2 default _ (by decide) hSYN]
  simp only []
  rw [step _ _ "F_FIN" 1 default _ (by decide) hFIN]
  simp only [execS_ret_some, eret, RawSeg.len]

/-! ## `tcp_emit`: the data is copied into the packet buffer -/

def tcp_emit : Fn := checked_fn% Net.prog, "tcp_emit"
#guard (Net.prog.check.toOption.bind (·.fn? "tcp_emit")) == some tcp_emit

/-- One step of the copy: byte `src + i` of the echo buffer goes to `dst + i`. -/
def cpStep (pd : ByteArray) (dst src : Nat) (acc : ByteArray) (i : Nat) : ByteArray :=
  Bytes.set acc (dst + i) (Bytes.get pd (src + i))

/-- The packet buffer with `n` bytes of `pd` copied in. -/
def cpIn (b pd : ByteArray) (dst src n : Nat) : ByteArray := (List.range' 0 n).foldl (cpStep pd dst src) b

theorem cpIn_spec (b pd : ByteArray) (dst src : Nat) : ∀ n, dst + n ≤ b.size →
    (cpIn b pd dst src n).size = b.size ∧
      (∀ j, j < n → Bytes.get (cpIn b pd dst src n) (dst + j) = Bytes.get pd (src + j)) ∧
      (∀ i, i < dst ∨ dst + n ≤ i → Bytes.get (cpIn b pd dst src n) i = Bytes.get b i) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun i _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨hs, hj, hi⟩ := ih (by omega)
    have hstep : cpIn b pd dst src (n + 1) = cpStep pd dst src (cpIn b pd dst src n) n := by
      simp only [cpIn, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
        Nat.one_mul]
    rw [hstep]
    simp only [cpStep]
    refine ⟨by rw [Bytes.size_set, hs], ?_, ?_⟩
    · intro j hjn
      rw [Bytes.get_set, hs]
      by_cases hjj : j = n
      · subst hjj
        have : dst + j < b.size := by omega
        simp only [true_and, this, if_true]
      · have : ¬ (dst + n = dst + j) := by omega
        simp only [this, false_and, if_false]
        exact hj j (by omega)
    · intro i hii
      rw [Bytes.get_set]
      have : ¬ (dst + n = i) := by omega
      simp only [this, false_and, if_false]
      exact hi i (by omega)

/-- The body of the copy loop of `tcp_emit`. -/
def cpBody : List Stmt :=
  match tcp_emit.body with
  | [_, _, .at _ (.forRange _ _ _ _ body), _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => body
  | _ => []

/-- One iteration of the copy. -/
theorem cp_body (p : Prog) (off so : UInt16) (envL : Env) (hoff : envL.lookup "off" = some (u16 off))
    (hso : envL.lookup "src_off" = some (u16 so)) (hnb : envL.lookup "buf" = none)
    (hnp : envL.lookup "pend" = none) (st : St) (B pd : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal B)) (hpd : st.globals.lookup "pend" = some (bufVal pd))
    (i : Nat) (h1 : so.toNat + i < pd.size) (h2 : 20 + off.toNat + i < B.size) (h3 : B.size < 65536)
    (h4 : pd.size < 65536) (m : Nat) :
    execB (m + 6) p st (("i", u16 (UInt16.ofNat i)) :: envL) cpBody
      = .ok (setG st "buf" (bufVal (cpStep pd (20 + off.toNat) so.toNat B i)))
          (("i", u16 (UInt16.ofNat i)) :: envL) .normal := by
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have ei : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.var "i") = some (u16 (UInt16.ofNat i)) := by
    simp [evalE, lookup, List.lookup]
  have eoff : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.var "off") = some (u16 off) := by
    simp [evalE, lookup, List.lookup, hoff]
  have eso : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.var "src_off") = some (u16 so) := by
    simp [evalE, lookup, List.lookup, hso]
  have epd : lookup st (("i", u16 (UInt16.ofNat i)) :: envL) "pend" = some (bufVal pd) := by
    simp [lookup, List.lookup, hnp, hpd]
  have esrc : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.bin .add (.var "src_off") (.var "i"))
      = some (u16 (so + UInt16.ofNat i)) := by
    simp only [evalE_bin, eso, ei, Sem.binop, mask16_add]
  have edst : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL)
      (.bin .add (.bin .add (.lit 20 (some .w16)) (.var "off")) (.var "i"))
      = some (u16 (UInt16.ofNat 20 + off + UInt16.ofNat i)) := by
    simp only [evalE_bin, evalE_lit16, eoff, ei, Sem.binop, mask16_add]
  have hs : (so + UInt16.ofNat i).toNat = so.toNat + i := by
    simp only [UInt16.toNat_add, ht i (by omega)]; omega
  have hd : (UInt16.ofNat 20 + off + UInt16.ofNat i).toNat = 20 + off.toNat + i := by
    simp only [UInt16.toNat_add, ht i (by omega), ht 20 (by omega)]; omega
  have hidx : (u16 (so + UInt16.ofNat i)).toNat = so.toNat + i := by
    show (so + UInt16.ofNat i).toUInt64.toNat = _
    rw [UInt16.toNat_toUInt64, hs]
  have ev : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL)
      (.index (.var "pend") (.bin .add (.var "src_off") (.var "i"))) = some (u8 (Bytes.get pd (so.toNat + i))) := by
    rw [evalE, evalE_var, epd, esrc]
    simp only [bufVal, hidx, bufVal_get pd _ h1]
  have ea := assign_buf p st (("i", u16 (UInt16.ofNat i)) :: envL) B _ (UInt16.ofNat 20 + off + UInt16.ofNat i)
    (Bytes.get pd (so.toNat + i)) (by simp [List.lookup, hnb]) hb edst (by rw [hd]; exact h2)
  rw [hd, withBuf_eq] at ea
  simp only [cpBody, tcp_emit, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, ev, ea, cpStep,
    List.length_cons, Nat.sub_self, List.drop_zero]

/-- The copy loop of `tcp_emit`. -/
theorem cp_loop (p : Prog) (off so : UInt16) (envL : Env) (hoff : envL.lookup "off" = some (u16 off))
    (hso : envL.lookup "src_off" = some (u16 so)) (hnb : envL.lookup "buf" = none)
    (hnp : envL.lookup "pend" = none) (pd : ByteArray) (h4 : pd.size < 65536) (hi : Nat) :
    ∀ (k cur : Nat) (st : St) (B : ByteArray) (v0 : Val) (d : Nat),
      st.globals.lookup "buf" = some (bufVal B) → st.globals.lookup "pend" = some (bufVal pd) → cur + k = hi →
      so.toNat + hi ≤ pd.size → 20 + off.toNat + hi ≤ B.size → B.size < 65536 →
      ∃ v, forLoop (k + 7 + d) p st (("i", v0) :: envL) "i" .w16 cur hi cpBody
          = .ok (setG st "buf" (bufVal ((List.range' cur k).foldl (cpStep pd (20 + off.toNat) so.toNat) B)))
              (("i", v) :: envL) .normal := by
  intro k
  induction k with
  | zero =>
    intro cur st B v0 d hb _ hk _ _ _
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 7 + d = (6 + d) + 1 by omega, forLoop_succ]
    simp [this, setG_same st _ _ hb]
  | succ k ih =>
    intro cur st B v0 d hb hpd hk h1 h2 h3
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    have hsz : (cpStep pd (20 + off.toNat) so.toNat B cur).size = B.size := by simp [cpStep]
    obtain ⟨v, hv⟩ := ih (cur + 1) (setG st "buf" (bufVal (cpStep pd (20 + off.toNat) so.toNat B cur)))
      (cpStep pd (20 + off.toNat) so.toNat B cur) (u16 (UInt16.ofNat cur)) d (lookup_setG st _ _ _ hb)
      (by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact hpd) (by omega) h1 (by omega) (by omega)
    refine ⟨v, ?_⟩
    rw [show k + 1 + 7 + d = (k + 7 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 7 + d = (k + 1 + d) + 6 by omega,
      cp_body p off so envL hoff hso hnb hnp st B pd hb hpd cur (by omega) (by omega) h3 h4 (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 6 = k + 7 + d by omega, hv, setG_setG]
    simp [List.range'_succ]

@[simp] theorem size_cpIn (b pd : ByteArray) (dst src n : Nat) : (cpIn b pd dst src n).size = b.size := by
  have : ∀ (l : List Nat) (acc : ByteArray), (l.foldl (cpStep pd dst src) acc).size = acc.size := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x t ih => intro acc; rw [List.foldl_cons, ih]; simp [cpStep]
  exact this _ b

/-- The data offset of a segment: 24 with the MSS option, 20 without. -/
def tcpOff (mss : Bool) : UInt16 := if mss then 24 else 20

/-- The MSS option, when the segment carries it. -/
def tcpOpt (mss : Bool) (ourMss : UInt16) (b : ByteArray) : ByteArray :=
  if mss then Bytes.set16 (Bytes.set (Bytes.set b 40 2) 41 4) 42 ourMss else b

@[simp] theorem size_tcpOpt (mss : Bool) (ourMss : UInt16) (b : ByteArray) : (tcpOpt mss ourMss b).size = b.size := by
  simp only [tcpOpt]; split <;> simp

/-- The packet buffer after `tcp_emit` has written the segment, before
its checksum: the writes of the function, in its order. -/
def tcpSeg0 (b pd : ByteArray) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (w : UInt16)
    (mss : Bool) (ourMss : UInt16) (so n : Nat) : ByteArray :=
  let b := cpIn b pd (20 + (tcpOff mss).toNat) so n
  let b := Bytes.set16 b 20 sport
  let b := Bytes.set16 b 22 dport
  let b := Bytes.set32 b 24 seq
  let b := Bytes.set32 b 28 ack
  let b := Bytes.set b 32 (if mss then 96 else 80)
  let b := Bytes.set b 33 flags
  let b := Bytes.set16 b 34 w
  let b := Bytes.set16 b 36 0
  let b := Bytes.set16 b 38 0
  tcpOpt mss ourMss b

@[simp] theorem size_tcpSeg0 (b pd : ByteArray) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8)
    (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : Nat) :
    (tcpSeg0 b pd sport dport seq ack flags w mss ourMss so n).size = b.size := by
  simp [tcpSeg0]

/-- The first `if` of `tcp_emit` (the data offset) and the second (the MSS option). -/
def emitIte1 : Stmt :=
  match tcp_emit.body with
  | [_, .at _ s, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => s
  | _ => .brk

def emitIte2 : Stmt :=
  match tcp_emit.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, .at _ s, _, _, _, _, _, _, _] => s
  | _ => .brk

def emitFor : Stmt :=
  match tcp_emit.body with
  | [_, _, .at _ s, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => s
  | _ => .brk

/-- A program with the TCP functions (the list grows with the proofs). -/
structure TcpProg (p : Prog) : Prop extends RxProg p where
  sTcb : p.struct? "Tcb" = some Net.Tcb
  sSeg : p.struct? "Seg" = some Net.Seg
  tcb_reset : p.fn? "tcb_reset" = some tcb_reset
  cap : p.fn? "cap" = some cap
  wnd : p.fn? "wnd" = some wnd
  seg_len : p.fn? "seg_len" = some seg_len
  tcp_emit : p.fn? "tcp_emit" = some tcp_emit

/-- The segment `tcp_emit` leaves in the packet buffer, checksum included. -/
def tcpSegBuf (b pd : ByteArray) (src dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8)
    (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : UInt16) : ByteArray :=
  let B := tcpSeg0 b pd sport dport seq ack flags w mss ourMss so.toNat n.toNat
  Bytes.set16 B 36 (~~~ Spec.Checksum.sum B 20 (tcpOff mss + n).toNat
    (Spec.Checksum.pseudo src dst 6 (tcpOff mss + n).toNat))

set_option maxHeartbeats 2000000 in
/-- `tcp_emit` from a state whose `buf` is set. -/
theorem tcp_emit_core (p : Prog) (hP : TcpProg p) (st : St) (vb : Val)
    (hb0 : st.globals.lookup "buf" = some vb) (b pd : ByteArray)
    (hpd : st.globals.lookup "pend" = some (bufVal pd)) (r : RawTcb) (ht : st.globals.lookup "t" = some r.val)
    (id : UInt16) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (httl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault))
    (dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (w : UInt16) (mss : Bool)
    (so n : UInt16) (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ b.size) (hso : so.toNat + n.toNat ≤ pd.size)
    (hsz : b.size < 65536) (h44 : 44 ≤ b.size) (hpsz : pd.size < 65536) (d : Nat) :
    Sem.call (d + n.toNat + 300) p (withBuf st b) "tcp_emit"
        [u32 dst, u16 sport, u16 dport, u32 seq, u32 ack, u8 flags, u16 w, .bool mss, u16 so, u16 n]
      = .ok none (txOut
          (stIp st (ipHeader (tcpSegBuf b pd ourIp dst sport dport seq ack flags w mss r.our_mss so n) 6 id ourIp dst
            (tcpOff mss + n) Spec.ttlDefault) (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 6 id ourIp dst
            ((tcpSegBuf b pd ourIp dst sport dport seq ack flags w mss r.our_mss so n).extract 20
              (20 + (tcpOff mss + n).toNat))))) := by
  have ht' : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have hoffN : (tcpOff mss).toNat = if mss then 24 else 20 := by cases mss <;> rfl
  have hoff24 : (tcpOff mss).toNat ≤ 24 := by rw [hoffN]; split <;> omega
  have hoff20 : 20 ≤ (tcpOff mss).toNat := by rw [hoffN]; split <;> omega
  have htot : (tcpOff mss + n).toNat = (tcpOff mss).toNat + n.toNat := by
    rw [UInt16.toNat_add]; omega
  -- the state: only `buf` changes
  have lbuf : ∀ B : ByteArray, (withBuf st B).globals.lookup "buf" = some (bufVal B) :=
    fun B => lookup_setG st _ _ _ hb0
  have lne : ∀ (B : ByteArray) (x : String), x ≠ "buf" → (withBuf st B).globals.lookup x = st.globals.lookup x :=
    fun B x hx => lookup_setG_ne st _ _ _ (Ne.symm hx)
  let env0 : Env := [("dst", u32 dst), ("sport", u16 sport), ("dport", u16 dport), ("seq", u32 seq), ("ack", u32 ack), ("flags", u8 flags), ("w", u16 w), ("mss", Val.bool mss), ("src_off", u16 so), ("n", u16 n)]
  let envO : Env := ("off", u16 (tcpOff mss)) :: env0
  have evar : ∀ (S : St) (env : Env) (x : String) (v : Val), env.lookup x = some v →
      evalE p S env (.var x) = some v := by
    intro S env x v h; simp [evalE, lookup, h]
  have eglob : ∀ (S : St) (env : Env) (x : String) (v : Val), S.globals.lookup x = some v → env.lookup x = none →
      evalE p S env (.var x) = some v := by
    intro S env x v h h'; simp [evalE, lookup, h, h']
  -- the data offset
  have f_off : ∀ (m : Nat) (B : ByteArray), execS (m + 5) p (withBuf st B) (("off", u16 (UInt16.ofNat 20)) :: env0)
      emitIte1 = .ok (withBuf st B) envO .normal := by
    intro m B
    have ec : evalE p (withBuf st B) (("off", u16 (UInt16.ofNat 20)) :: env0) (.var "mss") = some (.bool mss) :=
      evar _ _ _ _ (by simp [env0, List.lookup])
    simp only [emitIte1, tcp_emit]
    cases mss with
    | true =>
      simp only [execS_ite_true, ec, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, evalE_lit16,
        assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, List.length_cons, Nat.sub_self,
        List.drop_zero, envO, env0]
      rfl
    | false =>
      simp only [execS_ite_false, ec, execB_succ, execL_nil, List.length_cons, Nat.sub_self, List.drop_zero,
        envO, env0]
      rfl
  simp only [emitIte1, tcp_emit] at f_off
  -- the copy
  have hsB : ∀ B : ByteArray, withBuf st B = setG st "buf" (bufVal B) := fun B => rfl
  have f_cp : execS (d + n.toNat + 295) p (withBuf st b) envO emitFor
      = .ok (withBuf st (cpIn b pd (20 + (tcpOff mss).toNat) so.toNat n.toNat)) envO .normal := by
    obtain ⟨v, hv⟩ := cp_loop p (tcpOff mss) so envO (by simp [envO, env0, List.lookup]) (by simp [envO, env0, List.lookup]) (by simp [envO, env0, List.lookup]) (by simp [envO, env0, List.lookup]) pd hpsz n.toNat n.toNat 0 (withBuf st b) b
      (.int .w16 (UInt64.ofNat 0)) (d + 287) (lbuf b) (by rw [lne b _ (by decide)]; exact hpd) (by omega) hso
      (by omega) hsz
    rw [show n.toNat + 7 + (d + 287) = d + n.toNat + 294 by omega] at hv
    have t0 : (u16 (UInt16.ofNat 0)).toNat = 0 := rfl
    have tn : (u16 n).toNat = n.toNat := by
      show n.toUInt64.toNat = _
      rw [UInt16.toNat_toUInt64]
    simp only [cpBody, tcp_emit] at hv
    simp only [emitFor, tcp_emit, execS_forRange, evalE_lit16, evar (withBuf st b) envO "n" (u16 n) (by simp [envO, env0, List.lookup]),
      Option.getD, t0, tn, hv, List.drop]
    simp only [withBuf_eq, setG_setG, cpIn]
  simp only [emitFor, tcp_emit] at f_cp
  -- writes
  have G16 : ∀ (k : Nat) (e : Expr) (v : UInt16), k < 65535 →
      (∀ B, evalE p (withBuf st B) envO e = some (u16 v)) →
      ∀ (B : ByteArray) (m : Nat), k + 1 < B.size →
        execS (m + 9) p (withBuf st B) envO (.call none "set16" [.lit k (some .w16), e])
          = .ok (withBuf st (Bytes.set16 B k v)) envO .normal := by
    intro k e v hk he B m hB
    rw [execS_set16 p hP.set16 _ envO B (lbuf B) _ _ (UInt16.ofNat k) v m (by rw [ht' k (by omega)]; omega)
      (by rw [ht' k (by omega)]; omega) (evalE_lit16 ..) (he B), withBuf_withBuf, ht' k (by omega)]
  have G32 : ∀ (k : Nat) (e : Expr) (v : UInt32), k < 65532 →
      (∀ B, evalE p (withBuf st B) envO e = some (u32 v)) →
      ∀ (B : ByteArray) (m : Nat), k + 3 < B.size →
        execS (m + 21) p (withBuf st B) envO (.call none "set32" [.lit k (some .w16), e])
          = .ok (withBuf st (Bytes.set32 B k v)) envO .normal := by
    intro k e v hk he B m hB
    rw [execS_set32 p hP.set32 hP.set16 _ envO B (lbuf B) _ _ (UInt16.ofNat k) v m
      (by rw [ht' k (by omega)]; omega) (by rw [ht' k (by omega)]; omega) (evalE_lit16 ..) (he B),
      withBuf_withBuf, ht' k (by omega)]
  have GA : ∀ (B : ByteArray) (k : Nat) (x : UInt8), k < B.size → k < 65536 →
      assign p (withBuf st B) envO (.index (.var "buf") (.lit k (some .w16))) (u8 x)
        = some (withBuf st (Bytes.set B k x), envO) := by
    intro B k x hk hk'
    rw [assign_buf_lit p _ envO B k x (by simp [envO, env0, List.lookup]) (lbuf B) hk hk', ← withBuf_eq, withBuf_withBuf]
  have c20 := G16 20 (.var "sport") sport (by omega) (fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup]))
  have c22 := G16 22 (.var "dport") dport (by omega) (fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup]))
  have c24 := G32 24 (.var "seq") seq (by omega) (fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup]))
  have c28 := G32 28 (.var "ack") ack (by omega) (fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup]))
  have c34 := G16 34 (.var "w") w (by omega) (fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup]))
  have c36 := G16 36 (.lit 0 (some .w16)) (UInt16.ofNat 0) (by omega) (fun B => evalE_lit16 ..)
  have c38 := G16 38 (.lit 0 (some .w16)) (UInt16.ofNat 0) (by omega) (fun B => evalE_lit16 ..)
  have e_hl : ∀ B, evalE p (withBuf st B) envO
      (.cast .w8 (.bin .mul (.bin .div (.var "off") (.lit 4 (some .w16))) (.lit 16 (some .w16))))
      = some (u8 (if mss then 96 else 80)) := by
    intro B
    have eo : evalE p (withBuf st B) envO (.var "off") = some (u16 (tcpOff mss)) := evar _ _ _ _ (by simp [envO, env0, List.lookup])
    rw [evalE, evalE_bin, evalE_bin, eo, evalE_lit, evalE_lit]
    cases mss <;> rfl
  have e_fl : ∀ B, evalE p (withBuf st B) envO (.var "flags") = some (u8 flags) :=
    fun B => evar _ _ _ _ (by simp [envO, env0, List.lookup])
  -- the MSS option
  have f_opt : ∀ (m : Nat) (B : ByteArray), 43 < B.size → execS (m + 15) p (withBuf st B) envO emitIte2
      = .ok (withBuf st (tcpOpt mss r.our_mss B)) envO .normal := by
    intro m B hB
    have ec : evalE p (withBuf st B) envO (.var "mss") = some (.bool mss) := evar _ _ _ _ (by simp [envO, env0, List.lookup])
    simp only [emitIte2, tcp_emit]
    cases mss with
    | true =>
      have eo : ∀ B', evalE p (withBuf st B') envO (.field (.var "t") "our_mss") = some (u16 r.our_mss) := by
        intro B'
        exact RawTcb.get_our_mss p hP.sTcb _ envO r (by
          simp only [lookup, show envO.lookup "t" = none from (by simp [envO, env0, List.lookup])]
          rw [lne B' _ (by decide)]; exact ht)
      have c42 := G16 42 (.field (.var "t") "our_mss") r.our_mss (by omega) eo
      rw [execS_ite_true _ _ _ _ _ _ _ ec]
      simp (disch := first | omega | (simp only [Bytes.size_set, Bytes.size_set16]; omega)) only
        [execB_succ, execL_cons, execL_nil, execS_at, execS_assign, evalE_lit8, GA, c42,
         List.length_cons, Nat.sub_self, List.drop_zero, if_true, tcpOpt]
      rfl
    | false =>
      simp only [execS_ite_false, ec, execB_succ, execL_nil, List.length_cons, Nat.sub_self, List.drop_zero,
        Bool.false_eq_true, if_false, tcpOpt]
  simp only [emitIte2, tcp_emit] at f_opt
  -- the checksum and the send
  obtain ⟨total, htotal⟩ : ∃ x : UInt16, x = tcpOff mss + n := ⟨_, rfl⟩
  have htotN : total.toNat = (tcpOff mss).toNat + n.toNat := by rw [htotal, htot]
  have e_total : ∀ B, evalE p (withBuf st B) envO (.bin .add (.var "off") (.var "n")) = some (u16 total) := by
    intro B
    simp only [evalE_bin, evar (withBuf st B) envO "off" (u16 (tcpOff mss)) (by simp [envO, env0, List.lookup]),
      evar (withBuf st B) envO "n" (u16 n) (by simp [envO, env0, List.lookup]), Sem.binop, mask16_add, htotal]
  let envT : Env := ("total", u16 total) :: envO
  obtain ⟨P, hPdef⟩ : ∃ x : UInt16, x = Spec.Checksum.pseudo ourIp dst (UInt8.ofNat 6) total.toNat := ⟨_, rfl⟩
  let envP : Env := ("p", u16 P) :: envT
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have f_p : ∀ (m : Nat) (B : ByteArray), execS (m + 41) p (withBuf st B) (("p", u16 0) :: envT)
      (.call (some (.var "p")) "pseudo" [.var "OUR_IP", .var "dst", .lit 6 (some .w8), .var "total"])
      = .ok (withBuf st B) envP .normal := by
    intro m B
    rw [execS_pseudo p hP.add16 hP.pseudo _ _ _ _ _ _ _ ourIp dst (UInt8.ofNat 6) total m
      (eglob _ _ "OUR_IP" _ (by rw [lne B _ (by decide)]; exact hip) (by simp [envT, envO, env0, List.lookup]))
      (evar _ _ "dst" _ (by simp [envT, envO, env0, List.lookup])) (evalE_lit8 ..)
      (evar _ _ "total" _ (by simp [envT, List.lookup]))]
    simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, envP, hPdef]
  have f_s : ∀ B : ByteArray, 20 + total.toNat ≤ B.size → B.size ≤ 65536 →
      execS (d + n.toNat + 280) p (withBuf st B) (("s", u16 0) :: envP)
        (.call (some (.var "s")) "csum" [.lit 20 (some .w16), .var "total", .var "p"])
      = .ok (withBuf st B) (("s", u16 (Spec.Checksum.sum B 20 total.toNat P)) :: envP) .normal := by
    intro B h1 h2
    rw [execS_csum p hP.csum hP.get16 hP.add16 _ _ B (lbuf B) _ _ _ _ (UInt16.ofNat 20) total P
      (by rw [ht' 20 (by omega)]; omega) h2 (evalE_lit16 ..)
      (evar _ _ "total" _ (by simp [envP, envT, List.lookup])) (evar _ _ "p" _ (by simp [envP, List.lookup]))
      _ (d + n.toNat + 219 - total.toNat / 2) (by omega)]
    simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht' 20 (by omega)]
  have c36' : ∀ (B : ByteArray) (s' : UInt16) (m : Nat), 36 + 1 < B.size →
      execS (m + 9) p (withBuf st B) (("s", u16 s') :: envP)
        (.call none "set16" [.lit 36 (some .w16), .un .bnot (.var "s")])
      = .ok (withBuf st (Bytes.set16 B 36 (~~~ s'))) (("s", u16 s') :: envP) .normal := by
    intro B s' m hB
    have ec : evalE p (withBuf st B) (("s", u16 s') :: envP) (.un .bnot (.var "s")) = some (u16 (~~~ s')) := by
      simp only [evalE, lookup, List.lookup, beq_self_eq_true, mask16_not]
    rw [execS_set16 p hP.set16 _ _ B (lbuf B) _ _ (UInt16.ofNat 36) (~~~ s') m
      (by rw [ht' 36 (by omega)]; omega) (by rw [ht' 36 (by omega)]; omega) (evalE_lit16 ..) ec,
      withBuf_withBuf, ht' 36 (by omega)]
  have f_ip : ∀ (B : ByteArray) (s' : UInt16), 20 + total.toNat ≤ B.size → B.size < 65536 →
      execS (d + n.toNat + 278) p (withBuf st B) (("s", u16 s') :: envP)
        (.call none "ip_send" [.lit 6 (some .w8), .var "dst", .var "total"])
      = .ok (txOut (stIp (withBuf st B) (ipHeader B (UInt8.ofNat 6) id ourIp dst total Spec.ttlDefault) (id + 1))
            ((withBuf st B).world.frame ++ Spec.Slip.encode
              (Spec.Ipv4.packet (UInt8.ofNat 6) id ourIp dst (B.extract 20 (20 + total.toNat)))))
          (("s", u16 s') :: envP) .normal := by
    intro B s' h1 h2
    exact execS_ip_send p hP.toIpProg _ _ B id (lbuf B) (by rw [lne B _ (by decide)]; exact hid) ourIp
      (by rw [lne B _ (by decide)]; exact hip) (by rw [lne B _ (by decide)]; exact httl) _ _ _ _ dst total
      (evalE_lit8 ..) (evar _ _ "dst" _ (by simp [envP, envT, envO, env0, List.lookup]))
      (evar _ _ "total" _ (by simp [envP, envT, List.lookup])) h1 h2 _
      (d + n.toNat + 127 - total.toNat) (by omega)
  simp only [envP, envT, envO, env0] at f_off f_cp c20 c22 c24 c28 c34 c36 c38 e_hl e_fl f_opt e_total f_p f_s c36' f_ip GA
  simp (disch := first | omega | (simp only [size_tcpOpt, size_cpIn, Bytes.size_set, Bytes.size_set16, size_set32]; omega)) only
    [Sem.call, hP.tcp_emit, tcp_emit, execB_succ, execL_cons, execL_nil, execS_at, List.map, List.zip, List.zipWith,
     execS_decl_some, execS_decl_none, execS_assign, evalE_lit16, hz, f_off, f_cp, c20, c22, c24, c28, e_hl, e_fl, GA,
     c34, c36, c38, f_opt, e_total, f_p, f_s, c36', f_ip]
  rw [withBuf_eq, stIp_setG_buf, hPdef, htotal]
  rfl

/-! ## The segment `tcp_emit` builds is `Spec.Tcp.emit` -/

/-- The header `Spec.Tcp.emit` assembles, before the checksum. -/
def tcpHdr (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (w : UInt16) (mss : Option UInt16) :
    List UInt8 :=
  let opts := match mss with
    | some m => [2, 4] ++ Bytes.be16 m
    | none => []
  Bytes.be16 sport ++ Bytes.be16 dport ++ Bytes.be32 seq ++ Bytes.be32 ack ++
    [UInt8.ofNat (((20 + opts.length) / 4) * 16), flags] ++ Bytes.be16 w ++ [0, 0, 0, 0] ++ opts

theorem tcpSeg0_bytes (b pd : ByteArray) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (w : UInt16)
    (mss : Bool) (ourMss : UInt16) (so n : Nat) (hn : 20 + (tcpOff mss).toNat + n ≤ b.size)
    (hso : so + n ≤ pd.size) :
    (pd.extract so (so + n)).size = n ∧
      (Bytes.ofList (tcpHdr sport dport seq ack flags w (if mss then some ourMss else none))).size
        = (tcpOff mss).toNat ∧
      ∀ j, j < (tcpOff mss).toNat + n →
        Bytes.get (tcpSeg0 b pd sport dport seq ack flags w mss ourMss so n) (20 + j)
          = Bytes.get (Bytes.ofList (tcpHdr sport dport seq ack flags w (if mss then some ourMss else none))
              ++ pd.extract so (so + n)) j := by
  have hds : (pd.extract so (so + n)).size = n := by rw [ByteArray.size_extract]; omega
  cases mss with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have hoffv : (tcpOff false).toNat = 20 := rfl
    rw [hoffv] at hn ⊢
    have hL : (Bytes.ofList (tcpHdr sport dport seq ack flags w none)).size = 20 := by simp [tcpHdr, Bytes.be16, Bytes.be32]
    refine ⟨hds, hL, ?_⟩
    intro j hj
    rw [Bytes.get_append, hL]
    by_cases hh : j < 20
    · rw [if_pos hh, Bytes.get_ofList]
      have g20 : 20 < b.size := by omega
      have g21 : 21 < b.size := by omega
      have g22 : 22 < b.size := by omega
      have g23 : 23 < b.size := by omega
      have g24 : 24 < b.size := by omega
      have g25 : 25 < b.size := by omega
      have g26 : 26 < b.size := by omega
      have g27 : 27 < b.size := by omega
      have g28 : 28 < b.size := by omega
      have g29 : 29 < b.size := by omega
      have g30 : 30 < b.size := by omega
      have g31 : 31 < b.size := by omega
      have g32 : 32 < b.size := by omega
      have g33 : 33 < b.size := by omega
      have g34 : 34 < b.size := by omega
      have g35 : 35 < b.size := by omega
      have g36 : 36 < b.size := by omega
      have g37 : 37 < b.size := by omega
      have g38 : 38 < b.size := by omega
      have g39 : 39 < b.size := by omega
      have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [tcpSeg0, tcpOpt, tcpOff, Bytes.get_set, Bytes.get_set16, Bytes.set32, tcpHdr, Bytes.be16, Bytes.be32,
          g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39]
    · rw [if_neg hh]
      have hcp := (cpIn_spec b pd (20 + 20) so n (by omega)).2.1 (j - 20) (by omega)
      have e1 : Bytes.get (tcpSeg0 b pd sport dport seq ack flags w false ourMss so n) (20 + j)
          = Bytes.get (cpIn b pd (20 + 20) so n) (20 + j) := by
        simp (disch := omega) only [tcpSeg0, tcpOpt, tcpOff, get_set_ne, Bytes.get_set16_ne, get_set32_ne,
          if_true, Bool.false_eq_true, if_false]
        rfl
      rw [e1, show 20 + j = 20 + 20 + (j - 20) by omega, hcp,
        get_extract pd so _ (j - 20) (by omega) (by omega)]
  | true =>
    simp only [if_true]
    have hoffv : (tcpOff true).toNat = 24 := rfl
    rw [hoffv] at hn ⊢
    have hL : (Bytes.ofList (tcpHdr sport dport seq ack flags w (some ourMss))).size = 24 := by simp [tcpHdr, Bytes.be16, Bytes.be32]
    refine ⟨hds, hL, ?_⟩
    intro j hj
    rw [Bytes.get_append, hL]
    by_cases hh : j < 24
    · rw [if_pos hh, Bytes.get_ofList]
      have g20 : 20 < b.size := by omega
      have g21 : 21 < b.size := by omega
      have g22 : 22 < b.size := by omega
      have g23 : 23 < b.size := by omega
      have g24 : 24 < b.size := by omega
      have g25 : 25 < b.size := by omega
      have g26 : 26 < b.size := by omega
      have g27 : 27 < b.size := by omega
      have g28 : 28 < b.size := by omega
      have g29 : 29 < b.size := by omega
      have g30 : 30 < b.size := by omega
      have g31 : 31 < b.size := by omega
      have g32 : 32 < b.size := by omega
      have g33 : 33 < b.size := by omega
      have g34 : 34 < b.size := by omega
      have g35 : 35 < b.size := by omega
      have g36 : 36 < b.size := by omega
      have g37 : 37 < b.size := by omega
      have g38 : 38 < b.size := by omega
      have g39 : 39 < b.size := by omega
      have g40 : 40 < b.size := by omega
      have g41 : 41 < b.size := by omega
      have g42 : 42 < b.size := by omega
      have g43 : 43 < b.size := by omega
      have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [tcpSeg0, tcpOpt, tcpOff, Bytes.get_set, Bytes.get_set16, Bytes.set32, tcpHdr, Bytes.be16, Bytes.be32,
          g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43]
    · rw [if_neg hh]
      have hcp := (cpIn_spec b pd (20 + 24) so n (by omega)).2.1 (j - 24) (by omega)
      have e1 : Bytes.get (tcpSeg0 b pd sport dport seq ack flags w true ourMss so n) (20 + j)
          = Bytes.get (cpIn b pd (20 + 24) so n) (20 + j) := by
        simp (disch := omega) only [tcpSeg0, tcpOpt, tcpOff, get_set_ne, Bytes.get_set16_ne, get_set32_ne,
          if_true, Bool.false_eq_true, if_false]
        rfl
      rw [e1, show 20 + j = 20 + 24 + (j - 24) by omega, hcp,
        get_extract pd so _ (j - 24) (by omega) (by omega)]

theorem emit_eq (src dst : UInt32) (s : Spec.Tcp.Seg) :
    Spec.Tcp.emit src dst s =
      Bytes.set16 (Bytes.ofList (tcpHdr s.sport s.dport s.seq s.ack s.flags s.wnd s.mss) ++ s.data) 16
        (Spec.Checksum.checksum (Bytes.ofList (tcpHdr s.sport s.dport s.seq s.ack s.flags s.wnd s.mss) ++ s.data) 0
          (Bytes.ofList (tcpHdr s.sport s.dport s.seq s.ack s.flags s.wnd s.mss) ++ s.data).size
          (Spec.Checksum.pseudo src dst 6
            (Bytes.ofList (tcpHdr s.sport s.dport s.seq s.ack s.flags s.wnd s.mss) ++ s.data).size)) := rfl

/-- **The segment `tcp_emit` leaves at `buf[20, …)` is `Spec.Tcp.emit`**
of the same fields, with the data taken from the echo buffer: header,
MSS option, data and checksum, byte for byte. -/
theorem tcpSegBuf_extract (b pd : ByteArray) (src dst : UInt32) (sport dport : UInt16) (seq ack : UInt32)
    (flags : UInt8) (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : UInt16)
    (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ b.size) (hso : so.toNat + n.toNat ≤ pd.size)
    (hsz : b.size < 65536) :
    (tcpSegBuf b pd src dst sport dport seq ack flags w mss ourMss so n).extract 20
        (20 + (tcpOff mss + n).toNat)
      = Spec.Tcp.emit src dst (Spec.Tcp.Seg.mk sport dport seq ack flags w (if mss then some ourMss else none)
          (pd.extract so.toNat (so.toNat + n.toNat))) := by
  have htot : (tcpOff mss + n).toNat = (tcpOff mss).toNat + n.toNat := by
    rw [UInt16.toNat_add]; omega
  have hoff20 : 20 ≤ (tcpOff mss).toNat := by cases mss <;> decide
  obtain ⟨hds, hL, key⟩ := tcpSeg0_bytes b pd sport dport seq ack flags w mss ourMss so.toNat n.toNat hn hso
  rw [emit_eq, htot]
  simp only [tcpSegBuf, htot]
  have hs0 := size_tcpSeg0 b pd sport dport seq ack flags w mss ourMss so.toNat n.toNat
  generalize tcpSeg0 b pd sport dport seq ack flags w mss ourMss so.toNat n.toNat = B0 at key hs0 ⊢
  generalize hdd : Bytes.ofList (tcpHdr sport dport seq ack flags w (if mss then some ourMss else none))
    ++ pd.extract so.toNat (so.toNat + n.toNat) = dd at key ⊢
  have hdds : dd.size = (tcpOff mss).toNat + n.toNat := by rw [← hdd, ByteArray.size_append, hL, hds]
  have hsum : ∀ ini, Spec.Checksum.sum B0 20 ((tcpOff mss).toNat + n.toNat) ini
      = Spec.Checksum.sum dd 0 ((tcpOff mss).toNat + n.toNat) ini := by
    intro ini
    apply Spec.Checksum.sum_congr
    intro i hi
    rw [Nat.zero_add, key i hi]
  rw [hdds]
  simp only [Spec.Checksum.checksum, hsum]
  generalize (~~~ Spec.Checksum.sum dd 0 ((tcpOff mss).toNat + n.toNat)
    (Spec.Checksum.pseudo src dst 6 ((tcpOff mss).toNat + n.toNat))) = c
  apply Bytes.ext_get
  · rw [ByteArray.size_extract, Bytes.size_set16, hs0, Bytes.size_set16, hdds]; omega
  · intro j hj
    have hj' : j < (tcpOff mss).toNat + n.toNat := by
      rw [ByteArray.size_extract, Bytes.size_set16, hs0] at hj; omega
    rw [get_extract _ 20 _ j (by omega) (by rw [Bytes.size_set16, hs0]; omega), Bytes.get_set16,
      Bytes.get_set16, hs0, hdds]
    by_cases h17 : j = 17
    · subst h17
      have : 36 + 1 < b.size := by omega
      have : 16 + 1 < (tcpOff mss).toNat + n.toNat := by omega
      simp [*]
    · by_cases h16 : j = 16
      · subst h16
        have : 36 < b.size := by omega
        have : 16 < (tcpOff mss).toNat + n.toNat := by omega
        simp [*]
      · have e1 : ¬ (36 + 1 = 20 + j) := by omega
        have e2 : ¬ (36 = 20 + j) := by omega
        have e3 : ¬ (16 + 1 = j) := by omega
        have e4 : ¬ (16 = j) := by omega
        simp only [e1, e2, e3, e4, false_and, if_false]
        exact key j hj'

@[simp] theorem size_tcpSegBuf (b pd : ByteArray) (src dst : UInt32) (sport dport : UInt16) (seq ack : UInt32)
    (flags : UInt8) (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : UInt16) :
    (tcpSegBuf b pd src dst sport dport seq ack flags w mss ourMss so n).size = b.size := by
  simp [tcpSegBuf]

/-- The packet buffer after `tcp_emit`. -/
def tcpOutBuf (b pd : ByteArray) (id : UInt16) (src dst : UInt32) (sport dport : UInt16) (seq ack : UInt32)
    (flags : UInt8) (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : UInt16) : ByteArray :=
  ipHeader (tcpSegBuf b pd src dst sport dport seq ack flags w mss ourMss so n) 6 id src dst (tcpOff mss + n)
    Spec.ttlDefault

@[simp] theorem size_tcpOutBuf (b pd : ByteArray) (id : UInt16) (src dst : UInt32) (sport dport : UInt16)
    (seq ack : UInt32) (flags : UInt8) (w : UInt16) (mss : Bool) (ourMss : UInt16) (so n : UInt16) :
    (tcpOutBuf b pd id src dst sport dport seq ack flags w mss ourMss so n).size = b.size := by
  simp [tcpOutBuf]

/-- **`tcp_emit` sends `Spec.Tcp.emit`** in the Spec's IPv4 packet: the
segment with these fields, the MSS option when asked for (our MSS from
the connection record), and `n` bytes of the echo buffer from `so` on as
data; the identification counter moves on. -/
theorem tcp_emit_refines (p : Prog) (hP : TcpProg p) (st : St) (b pd : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hpd : st.globals.lookup "pend" = some (bufVal pd))
    (r : RawTcb) (ht : st.globals.lookup "t" = some r.val)
    (id : UInt16) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (httl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault))
    (dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (w : UInt16) (mss : Bool)
    (so n : UInt16) (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ b.size) (hso : so.toNat + n.toNat ≤ pd.size)
    (hsz : b.size < 65536) (h44 : 44 ≤ b.size) (hpsz : pd.size < 65536) (d : Nat) :
    Sem.call (d + n.toNat + 300) p st "tcp_emit"
        [u32 dst, u16 sport, u16 dport, u32 seq, u32 ack, u8 flags, u16 w, .bool mss, u16 so, u16 n]
      = .ok none (txOut
          (stIp st (tcpOutBuf b pd id ourIp dst sport dport seq ack flags w mss r.our_mss so n) (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 6 id ourIp dst
            (Spec.Tcp.emit ourIp dst (Spec.Tcp.Seg.mk sport dport seq ack flags w
              (if mss then some r.our_mss else none) (pd.extract so.toNat (so.toNat + n.toNat))))))) := by
  have h0 : withBuf st b = st := setG_same st _ _ hb
  have := tcp_emit_core p hP st _ hb b pd hpd r ht id hid ourIp hip httl dst sport dport seq ack flags w mss so n
    hn hso hsz h44 hpsz d
  rw [h0, tcpSegBuf_extract b pd ourIp dst sport dport seq ack flags w mss r.our_mss so n hn hso hsz] at this
  exact this

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.tcp_emit_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tcp_emit_refines

end Ember.Proof.Refine
