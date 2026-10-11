import Ember.Proof.RefineTcpParse

/-!
# Ember.Proof.RefineTcpTick — TCP: the clock (plan M5.5)

`rto` (the back-off schedule, a loop) and `tcp_tick`: TIME-WAIT, the
FIN-WAIT-2 timeout, the retransmission timer with `rexmit` and the
give-up reset, the idle close.

With this file every function of `Ember/Net/Tcp.lean` has its theorem of
the raw layer: the code computes a Lean function on `TW`
(`tcpInputW` for a segment, `tickW` for a tick).
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## `rto`: the back-off schedule -/

/-- One doubling, capped at 48. -/
def rtoStep (r : UInt16) : UInt16 := if 48 < r * 2 then 48 else r * 2

def rtoIter : Nat → UInt16 → UInt16
  | 0, r => r
  | n + 1, r => rtoIter n (rtoStep r)

def rtoBody : List Stmt :=
  match rto_fn.body with
  | [_, .at _ (.forRange _ _ _ _ body), _] => body
  | _ => []

theorem rto_body (p : Prog) (st : St) (vi : Val) (r : UInt16) (k : UInt8) (m : Nat) :
    execB (m + 9) p st [("i", vi), ("r", u16 r), ("k", u8 k)] rtoBody
      = .ok st [("i", vi), ("r", u16 (rtoStep r)), ("k", u8 k)] .normal := by
  simp only [rtoBody, rto_fn]
  rcases Classical.em (48 < r * 2) with h | h
  · tcp_sym_b [h, rtoStep]
  · tcp_sym_b [h, rtoStep]

theorem rto_loop (p : Prog) (st : St) (k : UInt8) (hi : Nat) :
    ∀ (n cur : Nat) (r : UInt16) (v0 : Val) (d : Nat), cur + n = hi →
      ∃ v, forLoop (n + 10 + d) p st [("i", v0), ("r", u16 r), ("k", u8 k)] "i" .w8 cur hi rtoBody
          = .ok st [("i", v), ("r", u16 (rtoIter n r)), ("k", u8 k)] .normal := by
  intro n
  induction n with
  | zero =>
    intro cur r v0 d hk
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 10 + d = (9 + d) + 1 by omega, forLoop_succ]
    simp [this, rtoIter]
  | succ n ih =>
    intro cur r v0 d hk
    have hlt : cur < hi := by omega
    obtain ⟨v, hv⟩ := ih (cur + 1) (rtoStep r) (.int .w8 (UInt64.ofNat cur)) d (by omega)
    refine ⟨v, ?_⟩
    rw [show n + 1 + 10 + d = (n + 10 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true]
    rw [show n + 10 + d = (n + 1 + d) + 9 by omega, rto_body p st _ r k (n + 1 + d)]
    simp only []
    rw [show n + 1 + d + 9 = n + 10 + d by omega, hv]
    simp [rtoIter]

theorem mask8_u16 (x : UInt16) : mask .w8 x.toUInt64 = x.toUInt8.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask8, UInt16.toNat_toUInt64, UInt8.toNat_toUInt64, UInt16.toNat_toUInt8]

/-- **`rto k`**: 3 doubled `k` times, capped at 48. -/
theorem rto_refines (p : Prog) (hp : p.fn? "rto" = some rto_fn) (st : St) (k : UInt8) (d : Nat) :
    Sem.call (d + 300) p st "rto" [u8 k] = .ok (some (u8 (rtoIter k.toNat 3).toUInt8)) st := by
  have hk := k.toNat_lt
  obtain ⟨v, hv⟩ := rto_loop p st k k.toNat k.toNat 0 3 (.int .w8 (UInt64.ofNat 0)) (d + 285 - k.toNat) (by omega)
  rw [show k.toNat + 10 + (d + 285 - k.toNat) = d + 295 by omega] at hv
  have t0 : (u8 0).toNat = 0 := rfl
  have tk : (u8 k).toNat = k.toNat := by
    show k.toUInt64.toNat = _
    rw [UInt8.toNat_toUInt64]
  simp only [rtoBody, rto_fn] at hv
  simp only [Sem.call, hp, rto_fn, List.map, List.zip, List.zipWith]
  tcp_sym_b [execS_forRange, Option.getD, t0, tk, hv, List.drop, mask8_u16]

theorem x_rto (p : Prog) (hp : p.fn? "rto" = some rto_fn) (st : St) (env : Env) (dst : Option Expr) (e : Expr)
    (k : UInt8) (he : evalE p st env e = some (u8 k)) (d : Nat) :
    execS (d + 301) p st env (.call dst "rto" [e])
      = storeResult p st env dst (some (u8 (rtoIter k.toNat 3).toUInt8)) :=
  execS_call_val p st env _ dst "rto" [e] hp (by simp [rto_fn]) (by simp [evalArgs, he]) (rto_refines p hp st k d)

theorem x_rexmit (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (hs : 40 + w.r.sent.toNat ≤ w.b.size) (hs' : w.r.sent.toNat ≤ 256) (env : Env) (d : Nat) :
    execS (d + 711) p (tcpSt st w) env (.call none "rexmit" []) = .ok (tcpSt st (rexmitW w ourIp)) env .normal :=
  execS_call_val p _ env _ none "rexmit" [] hP.rexmit (by simp [rexmit]) (by simp [evalArgs])
    (rexmit_tw p hP st hB hK ourIp hip w hw hs hs' d)

theorem toUInt64_le_iff8 (x y : UInt8) : decide (x.toUInt64 ≤ y.toUInt64) = decide (x ≤ y) := by
  have : x.toUInt64 ≤ y.toUInt64 ↔ x ≤ y := by
    rw [UInt64.le_iff_toNat_le, UInt8.le_iff_toNat_le]; simp
  simp [this]

theorem mask8_add (x y : UInt8) : mask .w8 (x.toUInt64 + y.toUInt64) = (x + y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [toNat_mask8, UInt8.toNat_toUInt64, UInt64.toNat_add, UInt8.toNat_add]
  omega

theorem mask8_sub (x y : UInt8) : mask .w8 (x.toUInt64 - y.toUInt64) = (x - y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [toNat_mask8, UInt8.toNat_toUInt64, UInt64.toNat_sub, UInt8.toNat_sub]
  omega

attribute [tcpsym] toUInt64_le_iff8 mask8_add mask8_sub

/-! ## `tcp_tick` -/

/-- The retransmission timer of a connection with something outstanding. -/
def tickRtW (w : TW) (ourIp : UInt32) : TW :=
  if w.r.rt_timer ≤ 1 then
    if 8 < w.r.retries + 1 then
      dropW { (emitW w ourIp w.r.rip 7 w.r.rport w.r.snd_nxt w.r.rcv_nxt (4 ||| 16) 0 false 0 0) with
        r := RawTcb.reset } "give-up"
    else rexmitW { w with r := { w.r with retries := w.r.retries + 1, rt_timer := (rtoIter (w.r.retries + 1).toNat 3).toUInt8 } } ourIp
  else { w with r := { w.r with rt_timer := w.r.rt_timer - 1 } }

/-- `tcp_tick`: one tick of the clock. -/
def tickW (w : TW) (ourIp : UInt32) : TW :=
  if w.r.st == 0 then w
  else if w.r.st == 8 then
    if w.r.tw_timer ≤ 1 then { w with r := RawTcb.reset }
    else { w with r := { w.r with tw_timer := w.r.tw_timer - 1 } }
  else if w.r.st == 6 then
    if 60 ≤ w.r.idle + 1 then dropW { w with r := RawTcb.reset } "fin-wait-2-timeout"
    else { w with r := { w.r with idle := w.r.idle + 1 } }
  else if w.r.snd_una != w.r.snd_nxt then tickRtW w ourIp
  else if w.r.st == 2 && w.r.pend_len == 0 then
    if 60 ≤ w.r.idle + 1 then outputW { w with r := { w.r with close_req := true, idle := 0 } } ourIp false
    else { w with r := { w.r with idle := w.r.idle + 1 } }
  else w

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem tcp_tick_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (hs : 40 + w.r.sent.toNat ≤ w.b.size) (hs' : w.r.sent.toNat ≤ 256)
    (hU1 : 40 + (w.r.pend_len - w.r.sent).toNat ≤ w.b.size)
    (hU2 : w.r.sent.toNat + (w.r.pend_len - w.r.sent).toNat ≤ 256) (d : Nat) :
    Sem.call (d + 2000) p (tcpSt st w) "tcp_tick" [] = .ok none (tcpSt st (tickW w ourIp)) := by
  have hwr : ∀ r' : RawTcb, TWok { w with r := r' } := fun r' => ⟨hw.b44, hw.b64, hw.pd⟩
  have h44 : 20 + (tcpOff false).toNat + (UInt16.ofNat 0).toNat ≤ w.b.size := by
    rw [tcpOff_false]; have := hw.b44; simp; omega
  have f_emit : execS (d + 1981) p (tcpSt st w) [("r", u8 (w.r.retries + 1))]
      (.call none "tcp_emit" [.field (.var "t") "rip", .var "ECHO_PORT", .field (.var "t") "rport",
        .field (.var "t") "snd_nxt", .field (.var "t") "rcv_nxt", .bin .bor (.var "F_RST") (.var "F_ACK"),
        .lit 0 (some .w16), .blit false, .lit 0 (some .w16), .lit 0 (some .w16)])
      = .ok (tcpSt st (emitW w ourIp w.r.rip 7 w.r.rport w.r.snd_nxt w.r.rcv_nxt (4 ||| 16) 0 false 0 0))
          [("r", u8 (w.r.retries + 1))] .normal :=
    x_tcp_emit p hP st hB hK ourIp hip w hw _ _ w.r.rip 7 w.r.rport w.r.snd_nxt w.r.rcv_nxt (4 ||| 16)
      (UInt16.ofNat 0) false (UInt16.ofNat 0) (UInt16.ofNat 0) (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) h44 (by simp)
      _ (d + 1680) (by simp)
  have f_rto : execS (d + 1980) p (tcpSt st { w with r := { w.r with retries := w.r.retries + 1 } }) [("r", u8 (w.r.retries + 1))]
      (.call (some (.field (.var "t") "rt_timer")) "rto" [.var "r"])
      = .ok (tcpSt st { w with r := { w.r with retries := w.r.retries + 1, rt_timer := (rtoIter (w.r.retries + 1).toNat 3).toUInt8 } }) [("r", u8 (w.r.retries + 1))] .normal := by
    rw [x_rto p hP.rto _ _ _ _ (w.r.retries + 1) (by tcp_sym_b []) (d + 1679)]
    tcp_sym_b [hP.sTcb, hB]
  have f_rex : execS (d + 1979) p (tcpSt st { w with r := { w.r with retries := w.r.retries + 1, rt_timer := (rtoIter (w.r.retries + 1).toNat 3).toUInt8 } }) [("r", u8 (w.r.retries + 1))]
      (.call none "rexmit" []) = _ :=
    x_rexmit p hP st hB hK ourIp hip { w with r := { w.r with retries := w.r.retries + 1, rt_timer := (rtoIter (w.r.retries + 1).toNat 3).toUInt8 } } (hwr _) hs hs' _ (d + 1268)
  have f_out : execS (d + 1983) p (tcpSt st { w with r := { w.r with close_req := true, idle := 0 } }) [] (.call none "output" [.blit false])
      = _ :=
    x_output p hP st hB hK ourIp hip { w with r := { w.r with close_req := true, idle := 0 } } (hwr _) hU1 hU2 [] (.blit false) false
      (evalE_blit ..) (d + 1182)
  simp only [Sem.call, hP.tcp_tick, tcp_tick, List.map, List.zip, List.zipWith]
  unfold tickW
  by_cases h0 : (w.r.st == 0) = true
  · rw [if_pos h0]
    tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, h0]
  · rw [if_neg h0]
    have h0f : (w.r.st == 0) = false := by simpa using h0
    by_cases h8 : (w.r.st == 8) = true
    · rw [if_pos h8]
      by_cases htw : w.r.tw_timer ≤ 1
      · rw [if_pos htw]
        tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8, htw]
      · rw [if_neg htw]
        tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8, htw]
    · rw [if_neg h8]
      have h8f : (w.r.st == 8) = false := by simpa using h8
      by_cases h6 : (w.r.st == 6) = true
      · rw [if_pos h6]
        by_cases hid : 60 ≤ w.r.idle + 1
        · rw [if_pos hid]
          tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6, hid]
          try (simp only [dropW])
        · rw [if_neg hid]
          tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6, hid]
      · rw [if_neg h6]
        have h6f : (w.r.st == 6) = false := by simpa using h6
        by_cases hout : (w.r.snd_una != w.r.snd_nxt) = true
        · rw [if_pos hout]
          unfold tickRtW
          by_cases hrt : w.r.rt_timer ≤ 1
          · rw [if_pos hrt]
            by_cases hmax : 8 < w.r.retries + 1
            · rw [if_pos hmax]
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, hout, hrt, hmax]
              try (simp only [dropW])
            · rw [if_neg hmax]
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, hout, hrt, hmax]
          · rw [if_neg hrt]
            tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, hout, hrt]
        · rw [if_neg hout]
          have houtf : (w.r.snd_una != w.r.snd_nxt) = false := by simpa using hout
          by_cases hest : (w.r.st == 2 && w.r.pend_len == 0) = true
          · rw [if_pos hest]
            by_cases hid : 60 ≤ w.r.idle + 1
            · rw [if_pos hid]
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, houtf, hest, hid]
            · rw [if_neg hid]
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, houtf, hest, hid]
          · rw [if_neg hest]
            have hestf : (w.r.st == 2 && w.r.pend_len == 0) = false := by simpa using hest
            tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_emit, f_rto, f_rex, f_out, h0f, h8f, h6f, houtf, hestf]

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.tcp_tick_tw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tcp_tick_tw


end Ember.Proof.Refine
