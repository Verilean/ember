import Ember.Proof.RefineTcpSt

/-!
# Ember.Proof.RefineTcpOut — TCP: what the connection sends (plan M5.5)

The sending half of `Ember/Net/Tcp.lean`, each function as a function on
`TW` (`RefineTcpSt.lean`): `send_seg`, `send_syn_ack`, `send_reset`,
`rexmit`, `output`; and `acceptable`.

```
output_tw :  call … (tcpSt st w) "output" [ackNow] = .ok none (tcpSt st (outputW w ourIp ackNow))
```

`outputW` and the others are the code transcribed — the same tests in
the same order — so these theorems say that the Ember code computes a
plain Lean function; that this function is `Spec.Tcp.output` under the
relation between the two control blocks is the next layer, not here.

The proofs run the code with `tcp_sym`, the simp set `tcpsym`: one case
split per `if`, then the whole body in one step.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

theorem evalE_lit32 (p : Prog) (st : St) (env : Env) (k : Nat) :
    evalE p st env (.lit k (some .w32)) = some (u32 (UInt32.ofNat k)) := by
  rw [evalE_lit, mask32_ofNat]

theorem evalE_blit (p : Prog) (st : St) (env : Env) (b : Bool) : evalE p st env (.blit b) = some (.bool b) := by
  rw [evalE]

theorem evalE_cast (p : Prog) (st : St) (env : Env) (w : Width) (a : Expr) :
    evalE p st env (.cast w a) =
      match evalE p st env a with
      | some (.int _ v) => some (.int w (mask w v))
      | some (.bool b) => some (.int w (if b then 1 else 0))
      | _ => none := by
  rw [evalE]; rfl

theorem evalE_un (p : Prog) (st : St) (env : Env) (op : UnOp) (a : Expr) :
    evalE p st env (.un op a) =
      match op, evalE p st env a with
      | .lnot, some (.bool b) => some (.bool !b)
      | .bnot, some (.int w v) => some (.int w (mask w (~~~ v)))
      | .neg, some (.int w v) => some (.int w (mask w (0 - v)))
      | _, _ => none := by
  cases op <;> simp only [evalE] <;> (try rfl) <;> (split <;> rfl)

attribute [tcpsym] execB_succ execL_cons execL_nil execS_at execS_decl_some execS_decl_none execS_assign
  execS_ret_none execS_ret_some evalE_bin evalE_var evalE_lit16 evalE_lit8
  evalE_lit32 evalE_blit evalE_cast evalE_un Sem.binop Sem.lookup storeResult assign_var setFirst
  mask16_add mask16_sub mask16_and mask16_not mask16_toUInt64 mask16_mul mask32_add mask32_sub mask8_and
  mask32_u16 mask16_u8 toUInt64_eq_iff toUInt64_eq_iff8 toUInt64_eq_iff32 toUInt64_lt_iff toUInt64_lt_iff8
  toUInt64_lt_iff32 List.length_cons List.length_nil Nat.sub_self List.drop_zero

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

attribute [tcpsym] toUInt64_ne_iff toUInt64_ne_iff8 toUInt64_ne_iff32 execS_ite_true execS_ite_false

/-- Execute TCP code symbolically (`tcpsym`), with the facts given. -/
macro "tcp_sym" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [tcpsym, List.lookup, String.reduceBEq, UInt8.reduceOfNat, UInt16.reduceOfNat,
      UInt32.reduceOfNat, Nat.sub_zero, Option.isSome_some, Nat.reduceAdd, Nat.reduceSub, List.drop_succ_cons, decide_true, decide_false, beq_self_eq_true, Bool.false_eq_true, if_true,
      if_false, ite_true, ite_false, $ts,*])

/-! ## The small functions on `tcpSt` -/

@[tcpsym] theorem x_cap (p : Prog) (hP : TcpProg p) (st : St) (hB : TcpBase st) (w : TW) (env : Env)
    (dst : Option Expr) (n : Nat) :
    execS (n + 9) p (tcpSt st w) env (.call dst "cap" [])
      = storeResult p (tcpSt st w) env dst (some (u16 w.r.cap)) :=
  execS_cap p hP.sTcb hP.cap _ env w.r (lookup_tcpSt_t st hB w) dst n

@[tcpsym] theorem x_wnd (p : Prog) (hP : TcpProg p) (st : St) (hB : TcpBase st) (w : TW) (env : Env)
    (dst : Option Expr) (n : Nat) :
    execS (n + 21) p (tcpSt st w) env (.call dst "wnd" [])
      = storeResult p (tcpSt st w) env dst (some (u16 w.r.wnd)) :=
  execS_wnd p hP.sTcb hP.cap hP.wnd _ env w.r (lookup_tcpSt_t st hB w) dst n

@[tcpsym] theorem x_seg_len (p : Prog) (hP : TcpProg p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (env : Env) (dst : Option Expr) (n : Nat) :
    execS (n + 13) p (tcpSt st w) env (.call dst "seg_len" [])
      = storeResult p (tcpSt st w) env dst (some (u32 w.sg.len)) :=
  execS_call_val p _ env (n + 12) dst "seg_len" [] hP.seg_len (by simp [seg_len]) (by simp [evalArgs])
    (seg_len_refines p hP.sSeg hP.seg_len _ w.sg (lookup_tcpSt_sg st hB w) (c_F_SYN st hK w) (c_F_FIN st hK w) n)

@[tcpsym] theorem x_tcb_reset (p : Prog) (hP : TcpProg p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (w : TW) (env : Env) (n : Nat) :
    execS (n + 31) p (tcpSt st w) env (.call none "tcb_reset" [])
      = .ok (tcpSt st { w with r := RawTcb.reset }) env .normal := by
  have h := tcb_reset_refines p hP.sTcb hP.tcb_reset (tcpSt st w) _ (lookup_tcpSt_t st hB w)
    (c_LISTEN st hK w) (c_OUR_MSS st hK w) w.r n
  have e1 : with_t (tcpSt st w) w.r = tcpSt st w := setG_same _ _ _ (lookup_tcpSt_t st hB w)
  have e2 : with_t (tcpSt st w) RawTcb.reset = tcpSt st { w with r := RawTcb.reset } := setG_tcpSt_t st w _
  rw [e1, e2] at h
  exact execS_call_val p _ env (n + 30) none "tcb_reset" [] hP.tcb_reset (by simp [tcb_reset])
    (by simp [evalArgs]) h

/-! ## `tcp_emit` on `tcpSt` -/

/-- The buffers the TCP code relies on have their sizes. -/
structure TWok (w : TW) : Prop where
  b44 : 44 ≤ w.b.size
  b64 : w.b.size < 65536
  pd : w.pd.size = 256

/-- `tcp_emit`: a segment goes out, the packet buffer holds it, the
identification moves on. -/
def emitW (w : TW) (ourIp dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (wn : UInt16)
    (mss : Bool) (so n : UInt16) : TW :=
  { w with
    b := tcpOutBuf w.b w.pd w.id ourIp dst sport dport seq ack flags wn mss w.r.our_mss so n,
    id := w.id + 1,
    evs := w.evs ++ [.tx (Spec.Slip.encode (Spec.Ipv4.packet 6 w.id ourIp dst
      (Spec.Tcp.emit ourIp dst (Spec.Tcp.Seg.mk sport dport seq ack flags wn
        (if mss then some w.r.our_mss else none) (w.pd.extract so.toNat (so.toNat + n.toNat))))))] }

theorem world_frame_eta (W : World) (h : W.frame = .empty) : ({ W with frame := .empty } : World) = W := by
  cases W; simp_all

theorem frame_tcpSt (st : St) (hB : TcpBase st) (w : TW) : (tcpSt st w).world.frame = .empty := by
  rw [world_tcpSt, foldl_emit_frame, hB.frame]

theorem txOut_tcpSt (st : St) (hB : TcpBase st) (w : TW) (f : ByteArray) :
    txOut (tcpSt st w) ((tcpSt st w).world.frame ++ f) = tcpSt st { w with evs := w.evs ++ [.tx f] } := by
  have he : (ByteArray.empty ++ f) = f := by
    apply ByteArray.ext; simp [ByteArray.data_append]
  rw [frame_tcpSt st hB w, he]
  have hw : ((w.evs.foldl World.emit st.world).emit (.tx f)).frame = .empty := by
    show (w.evs.foldl World.emit st.world).frame = _
    rw [foldl_emit_frame, hB.frame]
  simp only [txOut, tcpSt, setG, foldl_emit_append, world_frame_eta _ hw]

theorem stIp_tcpSt (st : St) (w : TW) (B : ByteArray) (I : UInt16) :
    stIp (tcpSt st w) B I = tcpSt st { w with b := B, id := I } := by
  simp only [stIp]
  rw [setG_tcpSt_ip_id, setG_tcpSt_buf]

theorem tcp_emit_tw (p : Prog) (hP : TcpProg p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (ourIp : UInt32)
    (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (wn : UInt16) (mss : Bool)
    (so n : UInt16) (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ w.b.size) (hso : so.toNat + n.toNat ≤ 256)
    (d : Nat) :
    Sem.call (d + n.toNat + 300) p (tcpSt st w) "tcp_emit"
        [u32 dst, u16 sport, u16 dport, u32 seq, u32 ack, u8 flags, u16 wn, .bool mss, u16 so, u16 n]
      = .ok none (tcpSt st (emitW w ourIp dst sport dport seq ack flags wn mss so n)) := by
  rw [tcp_emit_refines p hP (tcpSt st w) w.b w.pd (lookup_tcpSt_buf st hB w) (lookup_tcpSt_pend st hB w) w.r
    (lookup_tcpSt_t st hB w) w.id (lookup_tcpSt_ip_id st hB w) ourIp (c_OUR_IP st ourIp hip w) (c_TTL st hK w)
    dst sport dport seq ack flags wn mss so n hn (by rw [hw.pd]; exact hso) hw.b64 hw.b44
    (by rw [hw.pd]; omega) d]
  rw [stIp_tcpSt]
  have := txOut_tcpSt st hB
    { w with b := tcpOutBuf w.b w.pd w.id ourIp dst sport dport seq ack flags wn mss w.r.our_mss so n,
             id := w.id + 1 }
  simp only [world_tcpSt] at this ⊢
  rw [this]
  rfl

/-! ## `send_seg` -/

def send_seg : Fn := checked_fn% Net.prog, "send_seg"
#guard (Net.prog.check.toOption.bind (·.fn? "send_seg")) == some send_seg

/-- `send_seg`: a segment from the connection's endpoint; the window
announced is recorded. -/
def sendSegW (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (mss : Bool) : TW :=
  let w' := emitW w ourIp w.r.rip 7 w.r.rport seq w.r.rcv_nxt flags w.r.wnd mss so n
  { w' with r := { w'.r with last_wnd := w.r.wnd } }

def send_syn_ack : Fn := checked_fn% Net.prog, "send_syn_ack"
#guard (Net.prog.check.toOption.bind (·.fn? "send_syn_ack")) == some send_syn_ack
def send_reset : Fn := checked_fn% Net.prog, "send_reset"
#guard (Net.prog.check.toOption.bind (·.fn? "send_reset")) == some send_reset
def output_fn : Fn := checked_fn% Net.prog, "output"
#guard (Net.prog.check.toOption.bind (·.fn? "output")) == some output_fn
def rexmit : Fn := checked_fn% Net.prog, "rexmit"
#guard (Net.prog.check.toOption.bind (·.fn? "rexmit")) == some rexmit
def acceptable : Fn := checked_fn% Net.prog, "acceptable"
#guard (Net.prog.check.toOption.bind (·.fn? "acceptable")) == some acceptable
def listen_input : Fn := checked_fn% Net.prog, "listen_input"
#guard (Net.prog.check.toOption.bind (·.fn? "listen_input")) == some listen_input
def ack_input : Fn := checked_fn% Net.prog, "ack_input"
#guard (Net.prog.check.toOption.bind (·.fn? "ack_input")) == some ack_input
def tcp_segment : Fn := checked_fn% Net.prog, "tcp_segment"
#guard (Net.prog.check.toOption.bind (·.fn? "tcp_segment")) == some tcp_segment
def parse_mss : Fn := checked_fn% Net.prog, "parse_mss"
#guard (Net.prog.check.toOption.bind (·.fn? "parse_mss")) == some parse_mss
def tcp_input : Fn := checked_fn% Net.prog, "tcp_input"
#guard (Net.prog.check.toOption.bind (·.fn? "tcp_input")) == some tcp_input
def tcp_tick : Fn := checked_fn% Net.prog, "tcp_tick"
#guard (Net.prog.check.toOption.bind (·.fn? "tcp_tick")) == some tcp_tick
def rto_fn : Fn := checked_fn% Net.prog, "rto"
#guard (Net.prog.check.toOption.bind (·.fn? "rto")) == some rto_fn

/-- A program with all of the TCP code. -/
structure TcpAll (p : Prog) : Prop extends TcpProg p where
  send_seg : p.fn? "send_seg" = some send_seg
  send_syn_ack : p.fn? "send_syn_ack" = some send_syn_ack
  send_reset : p.fn? "send_reset" = some send_reset
  output : p.fn? "output" = some output_fn
  rexmit : p.fn? "rexmit" = some rexmit
  acceptable : p.fn? "acceptable" = some acceptable
  listen_input : p.fn? "listen_input" = some listen_input
  ack_input : p.fn? "ack_input" = some ack_input
  tcp_segment : p.fn? "tcp_segment" = some tcp_segment
  parse_mss : p.fn? "parse_mss" = some parse_mss
  tcp_input : p.fn? "tcp_input" = some tcp_input
  tcp_tick : p.fn? "tcp_tick" = some tcp_tick
  rto : p.fn? "rto" = some rto_fn

theorem send_seg_tw (p : Prog) (hP : TcpAll p) (st : St)
    (hB : TcpBase st) (hK : TcpConsts st) (ourIp : UInt32)
    (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (flags : UInt8) (seq : UInt32) (so n : UInt16) (mss : Bool)
    (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ w.b.size) (hso : so.toNat + n.toNat ≤ 256) (d : Nat) :
    Sem.call (d + n.toNat + 340) p (tcpSt st w) "send_seg" [u8 flags, u32 seq, u16 so, u16 n, .bool mss]
      = .ok none (tcpSt st (sendSegW w ourIp flags seq so n mss)) := by
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have hemit : execS (d + n.toNat + 335) p (tcpSt st w)
      [("w", u16 w.r.wnd), ("flags", u8 flags), ("seq", u32 seq), ("src_off", u16 so), ("n", u16 n),
        ("mss", Val.bool mss)]
      (.call none "tcp_emit" [.field (.var "t") "rip", .var "ECHO_PORT", .field (.var "t") "rport", .var "seq",
        .field (.var "t") "rcv_nxt", .var "flags", .var "w", .var "mss", .var "src_off", .var "n"])
      = .ok (tcpSt st (emitW w ourIp w.r.rip 7 w.r.rport seq w.r.rcv_nxt flags w.r.wnd mss so n))
          [("w", u16 w.r.wnd), ("flags", u8 flags), ("seq", u32 seq), ("src_off", u16 so), ("n", u16 n),
            ("mss", Val.bool mss)] .normal := by
    have hc := tcp_emit_tw p hP.toTcpProg st hB hK ourIp hip w hw w.r.rip 7 w.r.rport seq w.r.rcv_nxt flags w.r.wnd mss so n
      hn hso (d + 34)
    rw [show d + 34 + n.toNat + 300 = d + n.toNat + 334 by omega] at hc
    exact execS_call_val p _ _ (d + n.toNat + 334) none "tcp_emit" _ hP.tcp_emit (by simp [tcp_emit])
      (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) hc
  simp only [Sem.call, hP.send_seg, send_seg, List.map, List.zip, List.zipWith]
  tcp_sym [hz, hP.toTcpProg, hB, hK, hP.sTcb, hemit]
  rfl

/-- A call of `send_seg` as a statement. -/
theorem x_send_seg (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (ourIp : UInt32)
    (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (env : Env) (args : List Expr)
    (flags : UInt8) (seq : UInt32) (so n : UInt16) (mss : Bool)
    (he : evalArgs p (tcpSt st w) env args = some [u8 flags, u32 seq, u16 so, u16 n, .bool mss])
    (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ w.b.size) (hso : so.toNat + n.toNat ≤ 256) (m d : Nat)
    (hm : m = d + n.toNat + 341) :
    execS m p (tcpSt st w) env (.call none "send_seg" args)
      = .ok (tcpSt st (sendSegW w ourIp flags seq so n mss)) env .normal := by
  subst hm
  exact execS_call_val p _ env _ none "send_seg" args hP.send_seg (by simp [send_seg]) he
    (send_seg_tw p hP st hB hK ourIp hip w hw flags seq so n mss hn hso d)

/-- A call of `tcp_emit` as a statement. -/
theorem x_tcp_emit (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (ourIp : UInt32)
    (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (env : Env) (args : List Expr)
    (dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8) (wn : UInt16) (mss : Bool)
    (so n : UInt16)
    (he : evalArgs p (tcpSt st w) env args
      = some [u32 dst, u16 sport, u16 dport, u32 seq, u32 ack, u8 flags, u16 wn, .bool mss, u16 so, u16 n])
    (hn : 20 + (tcpOff mss).toNat + n.toNat ≤ w.b.size) (hso : so.toNat + n.toNat ≤ 256) (m d : Nat)
    (hm : m = d + n.toNat + 301) :
    execS m p (tcpSt st w) env (.call none "tcp_emit" args)
      = .ok (tcpSt st (emitW w ourIp dst sport dport seq ack flags wn mss so n)) env .normal := by
  subst hm
  exact execS_call_val p _ env _ none "tcp_emit" args hP.tcp_emit (by simp [tcp_emit]) he
    (tcp_emit_tw p hP.toTcpProg st hB hK ourIp hip w hw dst sport dport seq ack flags wn mss so n hn hso d)

theorem mask8_or (x y : UInt8) : mask .w8 (x.toUInt64 ||| y.toUInt64) = (x ||| y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hlt : x.toNat ||| y.toNat < 2 ^ 8 := Nat.or_lt_two_pow hx hy
  simp only [toNat_mask8, UInt8.toNat_toUInt64, UInt64.toNat_or, UInt8.toNat_or]
  omega

attribute [tcpsym] mask8_or

/-! ## `send_syn_ack`, `send_reset` -/

theorem tcpOff_true : (tcpOff true).toNat = 24 := rfl
theorem tcpOff_false : (tcpOff false).toNat = 20 := rfl

theorem send_syn_ack_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (d : Nat) :
    Sem.call (d + 350) p (tcpSt st w) "send_syn_ack" []
      = .ok none (tcpSt st (sendSegW w ourIp (2 ||| 16) w.r.snd_una 0 0 true)) := by
  have hcall := x_send_seg p hP st hB hK ourIp hip w hw []
    [.bin .bor (.var "F_SYN") (.var "F_ACK"), .field (.var "t") "snd_una", .lit 0 (some .w16),
      .lit 0 (some .w16), .blit true] (2 ||| 16) w.r.snd_una (UInt16.ofNat 0) (UInt16.ofNat 0) true
    (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) (by rw [tcpOff_true]; have := hw.b44; simp; omega) (by simp)
    (d + 347) (d + 6) (by simp)
  simp only [Sem.call, hP.send_syn_ack, send_syn_ack, List.map, List.zip, List.zipWith]
  tcp_sym [hcall]
  try rfl

/-- `send_reset`: the RFC 793 reset for the segment in `sg`. -/
def resetW (w : TW) (ourIp : UInt32) : TW :=
  if w.sg.flags &&& 16 != 0 then
    emitW w ourIp w.sg.src w.sg.dport w.sg.sport w.sg.ack 0 4 0 false 0 0
  else
    emitW w ourIp w.sg.src w.sg.dport w.sg.sport 0 (w.sg.seq + w.sg.len) (4 ||| 16) 0 false 0 0

theorem send_reset_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (d : Nat) :
    Sem.call (d + 350) p (tcpSt st w) "send_reset" [] = .ok none (tcpSt st (resetW w ourIp)) := by
  have hz : zeroOf p (Ty.int .w32) = u32 0 := rfl
  have hsz : 20 + (tcpOff false).toNat + (UInt16.ofNat 0).toNat ≤ w.b.size := by
    rw [tcpOff_false]; have := hw.b44; simp; omega
  simp only [Sem.call, hP.send_reset, send_reset, List.map, List.zip, List.zipWith]
  rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 16 != 0) with hf | hf
  · have hcall := x_tcp_emit p hP st hB hK ourIp hip w hw []
      [.field (.var "sg") "src", .field (.var "sg") "dport", .field (.var "sg") "sport", .field (.var "sg") "ack",
        .lit 0 (some .w32), .var "F_RST", .lit 0 (some .w16), .blit false, .lit 0 (some .w16), .lit 0 (some .w16)]
      w.sg.src w.sg.dport w.sg.sport w.sg.ack (UInt32.ofNat 0) 4 (UInt16.ofNat 0) false (UInt16.ofNat 0)
      (UInt16.ofNat 0) (by tcp_sym [evalArgs, hP.sSeg, hB, hK]) hsz (by simp) (d + 343) (d + 42) (by simp)
    tcp_sym [hP.sSeg, hB, hK, hf, hcall]
    simp only [resetW, hf, if_true]
    try rfl
  · have hcall := x_tcp_emit p hP st hB hK ourIp hip w hw [("l", u32 w.sg.len)]
      [.field (.var "sg") "src", .field (.var "sg") "dport", .field (.var "sg") "sport", .lit 0 (some .w32),
        .bin .add (.field (.var "sg") "seq") (.var "l"), .bin .bor (.var "F_RST") (.var "F_ACK"),
        .lit 0 (some .w16), .blit false, .lit 0 (some .w16), .lit 0 (some .w16)]
      w.sg.src w.sg.dport w.sg.sport (UInt32.ofNat 0) (w.sg.seq + w.sg.len) (4 ||| 16) (UInt16.ofNat 0) false
      (UInt16.ofNat 0) (UInt16.ofNat 0) (by tcp_sym [evalArgs, hP.sSeg, hB, hK]) hsz (by simp) (d + 341) (d + 40)
      (by simp)
    tcp_sym [hz, hP.toTcpProg, hP.sSeg, hB, hK, hf, hcall]
    simp only [resetW, hf, if_false, Bool.false_eq_true]
    try rfl

/-- A call of `send_syn_ack` as a statement. -/
theorem x_send_syn_ack (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (env : Env)
    (d : Nat) :
    execS (d + 351) p (tcpSt st w) env (.call none "send_syn_ack" [])
      = .ok (tcpSt st (sendSegW w ourIp (2 ||| 16) w.r.snd_una 0 0 true)) env .normal :=
  execS_call_val p _ env _ none "send_syn_ack" [] hP.send_syn_ack (by simp [send_syn_ack]) (by simp [evalArgs])
    (send_syn_ack_tw p hP st hB hK ourIp hip w hw d)

/-- A call of `send_reset` as a statement. -/
theorem x_send_reset (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w) (env : Env)
    (d : Nat) :
    execS (d + 351) p (tcpSt st w) env (.call none "send_reset" []) = .ok (tcpSt st (resetW w ourIp)) env .normal :=
  execS_call_val p _ env _ none "send_reset" [] hP.send_reset (by simp [send_reset]) (by simp [evalArgs])
    (send_reset_tw p hP st hB hK ourIp hip w hw d)

/-! ## `rexmit` -/

/-- The flags of a retransmission: ACK, PSH with data, FIN when it was sent. -/
def rexFlags (r : RawTcb) : UInt8 :=
  let f : UInt8 := if 0 < r.sent then 16 ||| 8 else 16
  if r.fin_sent then f ||| 1 else f

/-- `rexmit`: everything unacknowledged is sent again. -/
def rexmitW (w : TW) (ourIp : UInt32) : TW :=
  if w.r.st == 1 then sendSegW w ourIp (2 ||| 16) w.r.snd_una 0 0 true
  else sendSegW w ourIp (rexFlags w.r) w.r.snd_una 0 w.r.sent false

theorem rexmit_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (hs : 40 + w.r.sent.toNat ≤ w.b.size) (hs' : w.r.sent.toNat ≤ 256) (d : Nat) :
    Sem.call (d + 710) p (tcpSt st w) "rexmit" [] = .ok none (tcpSt st (rexmitW w ourIp)) := by
  simp only [Sem.call, hP.rexmit, rexmit, List.map, List.zip, List.zipWith]
  rcases Bool.eq_false_or_eq_true (w.r.st == 1) with h1 | h1
  · have hcall : execS (d + 703) p (tcpSt st w) [] (.call none "send_syn_ack" []) = _ :=
      x_send_syn_ack p hP st hB hK ourIp hip w hw [] (d + 352)
    tcp_sym [hP.sTcb, hB, hK, h1, hcall]
    simp only [rexmitW, h1, if_true]
    try rfl
  · have hcall : ∀ F : UInt8, execS (d + 703) p (tcpSt st w) [("flags", u8 F)]
        (.call none "send_seg" [.var "flags", .field (.var "t") "snd_una", .lit 0 (some .w16),
          .field (.var "t") "sent", .blit false])
        = .ok (tcpSt st (sendSegW w ourIp F w.r.snd_una 0 w.r.sent false)) [("flags", u8 F)] .normal := by
      intro F
      exact x_send_seg p hP st hB hK ourIp hip w hw _ _ F w.r.snd_una (UInt16.ofNat 0) w.r.sent false
        (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) (by rw [tcpOff_false]; omega) (by simp; omega) _
        (d + 362 - w.r.sent.toNat) (by omega)
    rcases Classical.em (0 < w.r.sent) with h2 | h2 <;>
      rcases Bool.eq_false_or_eq_true w.r.fin_sent with h3 | h3 <;>
      · tcp_sym [hP.sTcb, hB, hK, h1, h2, h3, hcall]
        simp only [rexmitW, rexFlags, h1, h2, h3, if_true, if_false, Bool.false_eq_true]
        try rfl

@[tcpsym] theorem zero8 (p : Prog) : zeroOf p (Ty.int .w8) = u8 0 := rfl
@[tcpsym] theorem zero16 (p : Prog) : zeroOf p (Ty.int .w16) = u16 0 := rfl
@[tcpsym] theorem zero32 (p : Prog) : zeroOf p (Ty.int .w32) = u32 0 := rfl
@[tcpsym] theorem zeroB (p : Prog) : zeroOf p Ty.bool = .bool false := rfl

/-! ## `acceptable` -/

/-- RFC 9293's acceptability test of the segment in `sg`. -/
def accW (w : TW) : Bool :=
  if w.r.wnd == 0 then w.sg.seq == w.r.rcv_nxt
  else if w.sg.len == 0 then decide (w.sg.seq - w.r.rcv_nxt < w.r.wnd.toUInt32)
  else decide (w.sg.seq - w.r.rcv_nxt < w.r.wnd.toUInt32) ||
    decide (w.sg.seq + w.sg.len - 1 - w.r.rcv_nxt < w.r.wnd.toUInt32)

theorem acceptable_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (d : Nat) :
    Sem.call (d + 40) p (tcpSt st w) "acceptable" [] = .ok (some (.bool (accW w))) (tcpSt st w) := by
  simp only [Sem.call, hP.acceptable, acceptable, List.map, List.zip, List.zipWith]
  rcases Bool.eq_false_or_eq_true (w.r.wnd == 0) with h1 | h1
  · tcp_sym [hP.toTcpProg, hP.sTcb, hP.sSeg, hB, hK, h1]
    simp only [accW, h1, if_true]
  · rcases Bool.eq_false_or_eq_true (w.sg.len == 0) with h2 | h2
    · tcp_sym [hP.toTcpProg, hP.sTcb, hP.sSeg, hB, hK, h1, h2]
      simp only [accW, h1, h2, if_true, if_false, Bool.false_eq_true]
    · tcp_sym [hP.toTcpProg, hP.sTcb, hP.sSeg, hB, hK, h1, h2]
      simp only [accW, h1, h2, if_false, Bool.false_eq_true]

/-- `tcp_sym` with the Boolean simplifications, and only the facts given. -/
macro "tcp_sym_b" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [tcpsym, List.lookup, String.reduceBEq, UInt8.reduceOfNat, UInt16.reduceOfNat,
      UInt32.reduceOfNat, Nat.sub_zero, UInt64.add_zero, Option.isSome_some, Nat.reduceAdd, Nat.reduceSub,
      List.drop_succ_cons, decide_true, decide_false,
      beq_self_eq_true, Bool.false_eq_true, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
      if_true, if_false, ite_true, ite_false, $ts,*])

/-- `tcp_sym` with every hypothesis as a rewrite rule too. -/
macro "tcp_sym_all" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [tcpsym, List.lookup, String.reduceBEq, UInt8.reduceOfNat, UInt16.reduceOfNat,
      UInt32.reduceOfNat, Nat.sub_zero, UInt64.add_zero, Option.isSome_some, Nat.reduceAdd, Nat.reduceSub, List.drop_succ_cons, decide_true, decide_false,
      beq_self_eq_true, Bool.false_eq_true, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
      if_true, if_false, ite_true, ite_false, $ts,*, *])

/-! ## `output` -/

theorem bool32 (b : Bool) : (if b = true then (1 : UInt64) else 0) = (if b then (1 : UInt32) else 0).toUInt64 := by
  cases b <;> rfl

theorem mask32_toUInt64 (x : UInt32) : mask .w32 x.toUInt64 = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [toNat_mask32, UInt32.toNat_toUInt64]
  omega

theorem mask32_add_one (x : UInt32) : mask .w32 (x.toUInt64 + 1) = (x + 1).toUInt64 := mask32_add x 1

attribute [tcpsym] bool32 mask32_toUInt64 mask32_add_one

/-- The end of `output`: a pure ACK when one is owed, or a window update. -/
def outRest (w : TW) (ourIp : UInt32) (ackNow : Bool) : TW :=
  if w.r.st == 0 || w.r.st == 1 then w
  else if ackNow || (w.r.last_wnd == 0 && decide (0 < w.r.wnd)) then
    sendSegW w ourIp 16 w.r.snd_nxt 0 0 false
  else w

/-- `output`: new echo data, with FIN when the application has closed;
otherwise what `outRest` sends. -/
def outputW (w : TW) (ourIp : UInt32) (ackNow : Bool) : TW :=
  let r := w.r
  let unsent := r.pend_len - r.sent
  let closing := (r.st == 3 || r.close_req) && !r.fin_sent
  if (r.st == 2 || r.st == 3) && (decide (0 < unsent) || closing) then
    let f1 : UInt8 := if 0 < unsent then 16 ||| 8 else 16
    let flags : UInt8 := if closing then f1 ||| 1 else f1
    let r1 : RawTcb := if closing then { r with st := if r.st == 3 then 4 else 5, fin_sent := true } else r
    let r2 : RawTcb :=
      { r1 with sent := r.pend_len, snd_nxt := r.snd_nxt + unsent.toUInt32 + (if closing then 1 else 0) }
    let w3 := sendSegW { w with r := r2 } ourIp flags r.snd_nxt r.sent unsent false
    if r.snd_una != r.snd_nxt then w3 else { w3 with r := { w3.r with rt_timer := 3, retries := 0 } }
  else outRest w ourIp ackNow

set_option maxHeartbeats 8000000 in
theorem output_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (hU1 : 40 + (w.r.pend_len - w.r.sent).toNat ≤ w.b.size)
    (hU2 : w.r.sent.toNat + (w.r.pend_len - w.r.sent).toNat ≤ 256) (ackNow : Bool) (d : Nat) :
    Sem.call (d + 800) p (tcpSt st w) "output" [.bool ackNow] = .ok none (tcpSt st (outputW w ourIp ackNow)) := by
  simp only [Sem.call, hP.output, output_fn, List.map, List.zip, List.zipWith]
  have hwr : ∀ r' : RawTcb, TWok { w with r := r' } := fun r' => ⟨hw.b44, hw.b64, hw.pd⟩
  have hcall : ∀ (r' : RawTcb) (F : UInt8) (was closing : Bool),
      execS (d + 778) p (tcpSt st { w with r := r' })
        [("from_off", u16 w.r.sent), ("seq", u32 w.r.snd_nxt), ("flags", u8 F), ("was", .bool was),
          ("closing", .bool closing), ("unsent", u16 (w.r.pend_len - w.r.sent)), ("ack_now", .bool ackNow)]
        (.call none "send_seg" [.var "flags", .var "seq", .var "from_off", .var "unsent", .blit false])
      = .ok (tcpSt st (sendSegW { w with r := r' } ourIp F w.r.snd_nxt w.r.sent (w.r.pend_len - w.r.sent) false))
          [("from_off", u16 w.r.sent), ("seq", u32 w.r.snd_nxt), ("flags", u8 F), ("was", .bool was),
            ("closing", .bool closing), ("unsent", u16 (w.r.pend_len - w.r.sent)), ("ack_now", .bool ackNow)]
          .normal := by
    intro r' F was closing
    exact x_send_seg p hP st hB hK ourIp hip _ (hwr r') _ _ F w.r.snd_nxt w.r.sent (w.r.pend_len - w.r.sent) false
      (by tcp_sym [evalArgs]) (by rw [tcpOff_false]; exact hU1) hU2 _
      (d + 437 - (w.r.pend_len - w.r.sent).toNat) (by omega)
  have hcallR : execS (d + 789) p (tcpSt st w) [("w", u16 w.r.wnd), ("ack_now", .bool ackNow)]
      (.call none "send_seg" [.var "F_ACK", .field (.var "t") "snd_nxt", .lit 0 (some .w16), .lit 0 (some .w16),
        .blit false])
      = .ok (tcpSt st (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false)) [("w", u16 w.r.wnd), ("ack_now", .bool ackNow)]
          .normal :=
    x_send_seg p hP st hB hK ourIp hip w hw _ _ 16 w.r.snd_nxt (UInt16.ofNat 0) (UInt16.ofNat 0) false
      (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) (by rw [tcpOff_false]; have := hw.b44; simp; omega) (by simp) _
      (d + 448) (by simp)
  rcases Bool.eq_false_or_eq_true (w.r.st == 2) with hs2 | hs2
  · have hst : w.r.st = 2 := by simpa using hs2
    have hs3 : (w.r.st == 3) = false := by rw [hst]; rfl
    have hs0 : (w.r.st == 0) = false := by rw [hst]; rfl
    have hs1 : (w.r.st == 1) = false := by rw [hst]; rfl
    clear hst
    rcases Classical.em (0 < w.r.pend_len - w.r.sent) with hU | hU <;>
      rcases Bool.eq_false_or_eq_true w.r.close_req with hcr | hcr <;>
      rcases Bool.eq_false_or_eq_true w.r.fin_sent with hfs | hfs <;>
      rcases Bool.eq_false_or_eq_true (w.r.snd_una != w.r.snd_nxt) with hwas | hwas <;>
      rcases Bool.eq_false_or_eq_true (ackNow || (w.r.last_wnd == 0 && decide (0 < w.r.wnd))) with hrest | hrest <;>
      (tcp_sym_all [hP.toTcpProg, hP.sTcb, outputW, outRest, UInt32.add_zero]; try (with_reducible rfl))
  · rcases Bool.eq_false_or_eq_true (w.r.st == 3) with hs3 | hs3
    · have hst : w.r.st = 3 := by simpa using hs3
      have hs0 : (w.r.st == 0) = false := by rw [hst]; rfl
      have hs1 : (w.r.st == 1) = false := by rw [hst]; rfl
      clear hst
      rcases Classical.em (0 < w.r.pend_len - w.r.sent) with hU | hU <;>
      rcases Bool.eq_false_or_eq_true w.r.close_req with hcr | hcr <;>
      rcases Bool.eq_false_or_eq_true w.r.fin_sent with hfs | hfs <;>
      rcases Bool.eq_false_or_eq_true (w.r.snd_una != w.r.snd_nxt) with hwas | hwas <;>
      rcases Bool.eq_false_or_eq_true (ackNow || (w.r.last_wnd == 0 && decide (0 < w.r.wnd))) with hrest | hrest <;>
      (tcp_sym_all [hP.toTcpProg, hP.sTcb, outputW, outRest, UInt32.add_zero]; try (with_reducible rfl))
    · rcases Bool.eq_false_or_eq_true (w.r.st == 0 || w.r.st == 1) with hls | hls <;>
      rcases Bool.eq_false_or_eq_true (ackNow || (w.r.last_wnd == 0 && decide (0 < w.r.wnd))) with hrest | hrest <;>
      (tcp_sym_all [hP.toTcpProg, hP.sTcb, outputW, outRest, UInt32.add_zero]; try (with_reducible rfl))

end Ember.Proof.Refine
