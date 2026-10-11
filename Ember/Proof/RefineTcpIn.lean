import Ember.Proof.RefineTcpOut

/-!
# Ember.Proof.RefineTcpIn — TCP: a segment arrives (plan M5.5)

The receiving half of `Ember/Net/Tcp.lean` as functions on `TW`:
`listen_input`, `ack_input`, and `tcp_segment` — the eight steps of the
state machine — with its two loops (acknowledged bytes leave the echo
buffer, `sh_loop`; data of the segment enters it, `dt_loop`).

`tcp_segment` is long (17 statements, 30 leaves).  Its body is split in
two with `execL_append`: the statements up to the ACK, where every early
exit is, and the tail (data, FIN, output), proved once
(`seg_tail_tw`) for any state that is fit for it (`SegTailOk`).

As in `RefineTcpOut.lean`, `segW` and the others are the code
transcribed; the relation to `Spec.Tcp.input` is the next layer.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-- A list of statements runs as its first part, then the rest (each
statement of the first part takes one unit of fuel). -/
theorem execL_append (p : Prog) (ys : List Stmt) : ∀ (xs : List Stmt) (n : Nat) (st : St) (env : Env),
    execL (n + 1 + xs.length) p st env (xs ++ ys) =
      match execL (n + 1 + xs.length) p st env xs with
      | .ok st' env' .normal => execL (n + 1) p st' env' ys
      | r => r := by
  intro xs
  induction xs with
  | nil =>
    intro n st env
    simp only [List.length_nil, Nat.add_zero, List.nil_append, execL_nil]
  | cons s rest ih =>
    intro n st env
    rw [show n + 1 + (s :: rest).length = (n + 1 + rest.length) + 1 by simp; omega]
    simp only [List.cons_append, execL_cons]
    cases hs : execS (n + 1 + rest.length) p st env s with
    | fuel => rfl
    | trap s' => rfl
    | ok st' env' o =>
      cases o with
      | normal => simp only [ih]
      | brk => rfl
      | ret v => rfl

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

attribute [tcpsym] setG_tcpSt_t setG_tcpSt_sg setG_tcpSt_pend setG_tcpSt_buf setG_tcpSt_ip_id setG_tcpSt_iss

/-- A `drop` line. -/
def dropW (w : TW) (r : String) : TW := { w with evs := w.evs ++ [.drop r] }

/-! ## `listen_input` -/

/-- `listen_input`: a segment in LISTEN, or for a tuple that is not the
connection's. -/
def listenW (w : TW) (ourIp : UInt32) : TW :=
  if w.r.st != 0 then
    if w.sg.flags &&& 4 != 0 then dropW w "rst-no-connection"
    else dropW (resetW w ourIp) "unsupported-second-connection"
  else if w.sg.flags &&& 4 != 0 then dropW w "rst-in-listen"
  else if w.sg.flags &&& 16 != 0 then dropW (resetW w ourIp) "ack-in-listen"
  else if w.sg.flags &&& 2 == 0 then dropW w "no-syn-in-listen"
  else
    let r : RawTcb :=
      { RawTcb.reset with
        st := 1, rip := w.sg.src, rport := w.sg.sport, rcv_nxt := w.sg.seq + 1, snd_una := w.iss,
        snd_nxt := w.iss + 1,
        peer_mss := if w.sg.has_mss then (if w.sg.mss == 0 then 1 else w.sg.mss) else 536,
        rt_timer := 3 }
    sendSegW { w with iss := w.iss + 65536, r := r } ourIp (2 ||| 16) w.iss 0 0 true

set_option maxHeartbeats 4000000 in
theorem listen_input_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (d : Nat) :
    Sem.call (d + 800) p (tcpSt st w) "listen_input" [] = .ok none (tcpSt st (listenW w ourIp)) := by
  have hrs1 : execS (d + 789) p (tcpSt st w) [] (.call none "send_reset" []) = _ :=
    x_send_reset p hP st hB hK ourIp hip w hw [] (d + 438)
  have hrs2 : execS (d + 791) p (tcpSt st w) [] (.call none "send_reset" []) = _ :=
    x_send_reset p hP st hB hK ourIp hip w hw [] (d + 440)
  have hsyn : ∀ (r' : RawTcb) (i' : UInt32) (v : Val),
      execS (d + 782) p (tcpSt st { w with iss := i', r := r' }) [("i0", v)] (.call none "send_syn_ack" [])
      = .ok (tcpSt st (sendSegW { w with iss := i', r := r' } ourIp (2 ||| 16) r'.snd_una 0 0 true)) [("i0", v)]
          .normal :=
    fun r' i' v => x_send_syn_ack p hP st hB hK ourIp hip { w with iss := i', r := r' } ⟨hw.b44, hw.b64, hw.pd⟩
      [("i0", v)] (d + 431)
  simp only [Sem.call, hP.listen_input, listen_input, List.map, List.zip, List.zipWith]
  rcases Bool.eq_false_or_eq_true (w.r.st != 0) with h0 | h0
  · rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 4 != 0) with hr | hr <;>
    (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)
  · rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 4 != 0) with hr | hr
    · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)
    · rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 16 != 0) with ha | ha
      · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)
      · rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 2 == 0) with hs | hs
        · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)
        · rcases Bool.eq_false_or_eq_true w.sg.has_mss with hm | hm
          · rcases Bool.eq_false_or_eq_true (w.sg.mss == 0) with hz | hz <;>
            (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)
          · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, listenW, dropW, RawTcb.reset]; try rfl)

/-! ## `ack_input`: acknowledged bytes leave the echo buffer -/

/-- `x[i] := v` for a global array of bytes. -/
theorem assign_arr (p : Prog) (st : St) (env : Env) (x : String) (b : ByteArray) (i : Expr) (k : UInt16)
    (v : UInt8) (hl : env.lookup x = none) (hb : st.globals.lookup x = some (bufVal b))
    (hi : evalE p st env i = some (u16 k)) (hk : k.toNat < b.size) :
    assign p st env (.index (.var x) i) (u8 v) = some (setG st x (bufVal (Bytes.set b k.toNat v)), env) := by
  have hidx : (u16 k).toNat = k.toNat := by simp [Val.toNat]
  have hget := bufVal_get b k.toNat hk
  simp only [assign, update, hi, hl, hb, bufVal, hidx, hget, bufVal_set b k.toNat v hk, setG]

/-- One step of the shift: byte `i + a` goes to `i`. -/
def shStep (a : Nat) (acc : ByteArray) (i : Nat) : ByteArray := Bytes.set acc i (Bytes.get acc (i + a))

/-- The echo buffer with its first `a` bytes removed: `n` bytes move down. -/
def shiftIn (pd : ByteArray) (a n : Nat) : ByteArray := (List.range' 0 n).foldl (shStep a) pd

theorem shiftIn_spec (pd : ByteArray) (a : Nat) : ∀ n, n + a ≤ pd.size →
    (shiftIn pd a n).size = pd.size ∧ (∀ j, j < n → Bytes.get (shiftIn pd a n) j = Bytes.get pd (j + a)) ∧
      (∀ i, n ≤ i → Bytes.get (shiftIn pd a n) i = Bytes.get pd i) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun i _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨hs, hj, hi⟩ := ih (by omega)
    have hstep : shiftIn pd a (n + 1) = shStep a (shiftIn pd a n) n := by
      simp only [shiftIn, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
        Nat.one_mul]
    rw [hstep]
    simp only [shStep]
    refine ⟨by rw [Bytes.size_set, hs], ?_, ?_⟩
    · intro j hjn
      rw [Bytes.get_set, hs]
      by_cases hjj : j = n
      · subst hjj
        have : j < pd.size := by omega
        simp only [true_and, this, if_true]
        exact hi _ (by omega)
      · have : ¬ (n = j) := by omega
        simp only [this, false_and, if_false]
        exact hj j (by omega)
    · intro i hii
      rw [Bytes.get_set]
      have : ¬ (n = i) := by omega
      simp only [this, false_and, if_false]
      exact hi i (by omega)

@[simp] theorem size_shiftIn (pd : ByteArray) (a n : Nat) : (shiftIn pd a n).size = pd.size := by
  have : ∀ (l : List Nat) (acc : ByteArray), (l.foldl (shStep a) acc).size = acc.size := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x t ih => intro acc; rw [List.foldl_cons, ih]; simp [shStep]
  exact this _ pd

/-- The loop of `ack_input` and its body. -/
def shFor : Stmt :=
  match ack_input.body with
  | [_, _, _, _, _, _, _, .at _ s, _, _, _, _, _, _, _] => s
  | _ => .brk

def shBody : List Stmt :=
  match shFor with
  | .forRange _ _ _ _ body => body
  | _ => []

/-- One iteration of the shift. -/
theorem sh_body (p : Prog) (st : St) (hB : TcpBase st) (a : UInt16) (envL : Env)
    (ha : envL.lookup "acked" = some (u16 a)) (hnp : envL.lookup "pend" = none) (w : TW) (i : Nat)
    (h1 : i + a.toNat < w.pd.size) (h3 : w.pd.size < 65536) (m : Nat) :
    execB (m + 6) p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) shBody
      = .ok (tcpSt st { w with pd := shStep a.toNat w.pd i }) (("i", u16 (UInt16.ofNat i)) :: envL) .normal := by
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have hti := ht i (by omega)
  have ei : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.var "i") = some (u16 (UInt16.ofNat i)) := by
    simp [evalE, lookup, List.lookup]
  have ea : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.var "acked") = some (u16 a) := by
    simp [evalE, lookup, List.lookup, ha]
  have epd : lookup (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) "pend" = some (bufVal w.pd) := by
    simp [lookup, List.lookup, hnp, lookup_tcpSt_pend st hB w]
  have esrc : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.bin .add (.var "i") (.var "acked"))
      = some (u16 (UInt16.ofNat i + a)) := by
    simp only [evalE_bin, ea, ei, Sem.binop, mask16_add]
  have hs : (UInt16.ofNat i + a).toNat = i + a.toNat := by
    simp only [UInt16.toNat_add, hti]; omega
  have hidx : (u16 (UInt16.ofNat i + a)).toNat = i + a.toNat := by
    show (UInt16.ofNat i + a).toUInt64.toNat = _
    rw [UInt16.toNat_toUInt64, hs]
  have ev : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL)
      (.index (.var "pend") (.bin .add (.var "i") (.var "acked"))) = some (u8 (Bytes.get w.pd (i + a.toNat))) := by
    rw [evalE, evalE_var, epd, esrc]
    simp only [bufVal, hidx, bufVal_get w.pd _ h1]
  have eas := assign_arr p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) "pend" w.pd _ (UInt16.ofNat i)
    (Bytes.get w.pd (i + a.toNat)) (by simp [List.lookup, hnp]) (lookup_tcpSt_pend st hB w) ei (by rw [hti]; omega)
  rw [hti, setG_tcpSt_pend] at eas
  simp only [shBody, shFor, ack_input, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, ev, eas, shStep,
    List.length_cons, Nat.sub_self, List.drop_zero]

/-- The shift loop. -/
theorem sh_loop (p : Prog) (st : St) (hB : TcpBase st) (a : UInt16) (envL : Env)
    (ha : envL.lookup "acked" = some (u16 a)) (hnp : envL.lookup "pend" = none) (hi : Nat) :
    ∀ (k cur : Nat) (w : TW) (v0 : Val) (d : Nat), cur + k = hi → hi + a.toNat ≤ w.pd.size → w.pd.size < 65536 →
      ∃ v, forLoop (k + 7 + d) p (tcpSt st w) (("i", v0) :: envL) "i" .w16 cur hi shBody
          = .ok (tcpSt st { w with pd := (List.range' cur k).foldl (shStep a.toNat) w.pd }) (("i", v) :: envL)
              .normal := by
  intro k
  induction k with
  | zero =>
    intro cur w v0 d hk _ _
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 7 + d = (6 + d) + 1 by omega, forLoop_succ]
    simp [this]
  | succ k ih =>
    intro cur w v0 d hk h1 h3
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    have hsz : (shStep a.toNat w.pd cur).size = w.pd.size := by simp [shStep]
    obtain ⟨v, hv⟩ := ih (cur + 1) { w with pd := shStep a.toNat w.pd cur } (u16 (UInt16.ofNat cur)) d (by omega)
      (by show hi + a.toNat ≤ (shStep a.toNat w.pd cur).size; omega)
      (by show (shStep a.toNat w.pd cur).size < 65536; omega)
    refine ⟨v, ?_⟩
    rw [show k + 1 + 7 + d = (k + 7 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 7 + d = (k + 1 + d) + 6 by omega,
      sh_body p st hB a envL ha hnp w cur (by omega) h3 (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 6 = k + 7 + d by omega, hv]
    simp [List.range'_succ]

theorem mask16_u32 (x : UInt32) : mask .w16 x.toUInt64 = x.toUInt16.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask16, UInt32.toNat_toUInt64, UInt16.toNat_toUInt64, UInt32.toNat_toUInt16]

attribute [tcpsym] mask16_u32

/-- `ack_input`: the ACK of a segment in a synchronized state; `false`
when the segment is done with. -/
def ackW (w : TW) (ourIp : UInt32) : Bool × TW :=
  let r := w.r
  let d := w.sg.ack - r.snd_una
  let outn := r.snd_nxt - r.snd_una
  if outn < d then (false, dropW (sendSegW w ourIp 16 r.snd_nxt 0 0 false) "ack-of-unsent")
  else if d == 0 then (true, w)
  else
    let acked : UInt16 := if d < r.sent.toUInt32 then d.toUInt16 else r.sent
    let pd' := shiftIn w.pd acked.toNat (r.pend_len - acked).toNat
    let r1 : RawTcb :=
      { r with pend_len := r.pend_len - acked, sent := r.sent - acked, snd_una := w.sg.ack, retries := 0,
               rt_timer := if w.sg.ack != r.snd_nxt then 3 else 0 }
    if acked.toUInt32 < d then
      if r.st == 5 then (true, { w with pd := pd', r := { r1 with st := 6 } })
      else if r.st == 7 then (true, { w with pd := pd', r := { r1 with st := 8, tw_timer := 20 } })
      else if r.st == 4 then (false, { w with pd := pd', r := RawTcb.reset })
      else (true, { w with pd := pd', r := r1 })
    else (true, { w with pd := pd', r := r1 })

set_option maxHeartbeats 4000000 in
theorem ack_input_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (hi1 : w.r.sent.toNat ≤ w.r.pend_len.toNat) (hi2 : w.r.pend_len.toNat ≤ 256) (d : Nat) :
    Sem.call (d + 800) p (tcpSt st w) "ack_input" []
      = .ok (some (.bool (ackW w ourIp).1)) (tcpSt st (ackW w ourIp).2) := by
  have hfor : ∀ (A : UInt16) (fa : Bool), A.toNat ≤ w.r.pend_len.toNat →
      execS (d + 790) p (tcpSt st w) [("fin_acked", Val.bool fa), ("acked", u16 A), ("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))] shFor
      = .ok (tcpSt st { w with pd := shiftIn w.pd A.toNat (w.r.pend_len - A).toNat }) [("fin_acked", Val.bool fa), ("acked", u16 A), ("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))] .normal := by
    intro A fa hA
    have hsub : (w.r.pend_len - A).toNat = w.r.pend_len.toNat - A.toNat := by
      rw [UInt16.toNat_sub]; have := w.r.pend_len.toNat_lt; have := A.toNat_lt; omega
    obtain ⟨v, hv⟩ := sh_loop p st hB A [("fin_acked", Val.bool fa), ("acked", u16 A), ("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))] (by simp [List.lookup]) (by simp [List.lookup])
      (w.r.pend_len - A).toNat (w.r.pend_len - A).toNat 0 w (.int .w16 (UInt64.ofNat 0))
      (d + 782 - (w.r.pend_len - A).toNat) (by omega) (by rw [hw.pd]; omega) (by rw [hw.pd]; omega)
    rw [show (w.r.pend_len - A).toNat + 7 + (d + 782 - (w.r.pend_len - A).toNat) = d + 789 by omega] at hv
    have t0 : (u16 (UInt16.ofNat 0)).toNat = 0 := rfl
    have tn : (u16 (w.r.pend_len - A)).toNat = (w.r.pend_len - A).toNat := by
      show (w.r.pend_len - A).toUInt64.toNat = _
      rw [UInt16.toNat_toUInt64]
    have ehi : evalE p (tcpSt st w) [("fin_acked", Val.bool fa), ("acked", u16 A), ("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))] (.bin .sub (.field (.var "t") "pend_len") (.var "acked"))
        = some (u16 (w.r.pend_len - A)) := by
      tcp_sym [hP.sTcb, hB]
    simp only [shBody, shFor, ack_input] at hv
    simp only [shFor, ack_input, execS_forRange, evalE_lit16, ehi, Option.getD, t0, tn, hv, List.drop, shiftIn]
  simp only [shFor, ack_input] at hfor
  simp only [Sem.call, hP.ack_input, ack_input, List.map, List.zip, List.zipWith]
  have hsend : execS (d + 791) p (tcpSt st w)
      [("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))]
      (.call none "send_seg" [.var "F_ACK", .field (.var "t") "snd_nxt", .lit 0 (some .w16), .lit 0 (some .w16),
        .blit false])
      = .ok (tcpSt st (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false))
          [("outn", u32 (w.r.snd_nxt - w.r.snd_una)), ("d", u32 (w.sg.ack - w.r.snd_una))] .normal :=
    x_send_seg p hP st hB hK ourIp hip w hw _ _ 16 w.r.snd_nxt (UInt16.ofNat 0) (UInt16.ofNat 0) false
      (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) (by rw [tcpOff_false]; have := hw.b44; simp; omega) (by simp) _
      (d + 450) (by simp)
  have hforS := fun fa => hfor w.r.sent fa hi1
  rcases Classical.em (w.r.snd_nxt - w.r.snd_una < w.sg.ack - w.r.snd_una) with h1 | h1
  · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, ackW, dropW]; try rfl)
  · rcases Bool.eq_false_or_eq_true (w.sg.ack - w.r.snd_una == 0) with h2 | h2
    · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, ackW, dropW]; try rfl)
    · rcases Classical.em (w.sg.ack - w.r.snd_una < w.r.sent.toUInt32) with h3 | h3
      · have hforD := fun fa => hfor (w.sg.ack - w.r.snd_una).toUInt16 fa (by
          have := UInt32.lt_iff_toNat_lt.mp h3
          have hs := w.r.sent.toNat_lt
          simp only [UInt16.toNat_toUInt32, UInt32.toNat_toUInt16] at this ⊢
          omega)
        rcases Classical.em ((w.sg.ack - w.r.snd_una).toUInt16.toUInt32 < w.sg.ack - w.r.snd_una) with h4 | h4 <;>
        rcases Bool.eq_false_or_eq_true (w.sg.ack != w.r.snd_nxt) with h5 | h5 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 5) with h6 | h6 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 7) with h7 | h7 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 4) with h8 | h8 <;>
        (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, ackW, dropW]; try rfl)
      · rcases Classical.em (w.r.sent.toUInt32 < w.sg.ack - w.r.snd_una) with h4 | h4 <;>
        rcases Bool.eq_false_or_eq_true (w.sg.ack != w.r.snd_nxt) with h5 | h5 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 5) with h6 | h6 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 7) with h7 | h7 <;>
        rcases Bool.eq_false_or_eq_true (w.r.st == 4) with h8 | h8 <;>
        (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, ackW, dropW]; try rfl)

/-! ## `tcp_segment`: the data of a segment goes into the echo buffer -/

/-- An element of a global array of bytes. -/
theorem evalE_index_arr (p : Prog) (st : St) (env : Env) (x : String) (b : ByteArray) (i : Expr) (k : UInt16)
    (hb : lookup st env x = some (bufVal b)) (hi : evalE p st env i = some (u16 k)) (hk : k.toNat < b.size) :
    evalE p st env (.index (.var x) i) = some (u8 (Bytes.get b k.toNat)) := by
  have hidx : (u16 k).toNat = k.toNat := by simp [Val.toNat]
  rw [evalE, evalE_var, hb, hi]
  simp only [bufVal, hidx, bufVal_get b k.toNat hk]

/-- Statement 14 of `tcp_segment` (the data), 15 (the FIN), and the copy loop. -/
def segDataIte : Stmt :=
  match tcp_segment.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ s, _, _] => s
  | _ => .brk

def segFinIte : Stmt :=
  match tcp_segment.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ s, _] => s
  | _ => .brk

def dtFor : Stmt :=
  match segDataIte with
  | .ite _ [.at _ (.ite _ [_, _, _, _, _, _, _, .at _ (.ite _ [.at _ s, _] _), _, _, _] _)] _ => s
  | _ => .brk

def dtBody : List Stmt :=
  match dtFor with
  | .forRange _ _ _ _ body => body
  | _ => []

/-- One iteration of the copy into the echo buffer. -/
theorem dt_body (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (skip : UInt32) (envL : Env)
    (hsk : envL.lookup "skip" = some (u32 skip)) (hnp : envL.lookup "pend" = none)
    (hnb : envL.lookup "buf" = none) (hnt : envL.lookup "t" = none) (hns : envL.lookup "sg" = none) (w : TW)
    (i : Nat) (h1 : w.r.pend_len.toNat + i < w.pd.size) (h2 : (w.sg.doff + skip.toUInt16).toNat + i < w.b.size)
    (h3 : w.pd.size < 65536) (h4 : w.b.size < 65536) (m : Nat) :
    execB (m + 6) p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) dtBody
      = .ok (tcpSt st { w with pd := cpStep w.b w.r.pend_len.toNat (w.sg.doff + skip.toUInt16).toNat w.pd i })
          (("i", u16 (UInt16.ofNat i)) :: envL) .normal := by
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have hti := ht i (by omega)
  have ei : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.var "i") = some (u16 (UInt16.ofNat i)) := by
    simp [evalE, lookup, List.lookup]
  have hl1 : List.lookup "t" (("i", u16 (UInt16.ofNat i)) :: envL) = none := by simp [List.lookup, hnt]
  have hl2 : List.lookup "sg" (("i", u16 (UInt16.ofNat i)) :: envL) = none := by simp [List.lookup, hns]
  have esk : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.var "skip") = some (u32 skip) := by
    simp [evalE, lookup, List.lookup, hsk]
  have edst : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL)
      (.bin .add (.field (.var "t") "pend_len") (.var "i")) = some (u16 (w.r.pend_len + UInt16.ofNat i)) := by
    simp only [evalE_bin, getW_t_pend_len p hP.sTcb st hB w _ hl1, ei, Sem.binop, mask16_add]
  have esrc : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL)
      (.bin .add (.bin .add (.field (.var "sg") "doff") (.cast .w16 (.var "skip"))) (.var "i"))
      = some (u16 (w.sg.doff + skip.toUInt16 + UInt16.ofNat i)) := by
    have ec : evalE p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) (.cast .w16 (.var "skip"))
        = some (u16 skip.toUInt16) := by
      rw [evalE_cast, esk]; simp only [mask16_u32]
    simp only [evalE_bin, getW_sg_doff p hP.sSeg st hB w _ hl2, ec, ei, Sem.binop, mask16_add]
  have hd : (w.r.pend_len + UInt16.ofNat i).toNat = w.r.pend_len.toNat + i := by
    simp only [UInt16.toNat_add, hti]; omega
  have hs : (w.sg.doff + skip.toUInt16 + UInt16.ofNat i).toNat = (w.sg.doff + skip.toUInt16).toNat + i := by
    rw [UInt16.toNat_add, hti]; omega
  have ebuf : lookup (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) "buf" = some (bufVal w.b) := by
    simp [lookup, List.lookup, hnb, lookup_tcpSt_buf st hB w]
  have ev := evalE_index_arr p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) "buf" w.b _ _ ebuf esrc
    (by rw [hs]; exact h2)
  rw [hs] at ev
  have eas := assign_arr p (tcpSt st w) (("i", u16 (UInt16.ofNat i)) :: envL) "pend" w.pd _
    (w.r.pend_len + UInt16.ofNat i) (Bytes.get w.b ((w.sg.doff + skip.toUInt16).toNat + i))
    (by simp [List.lookup, hnp]) (lookup_tcpSt_pend st hB w) edst (by rw [hd]; exact h1)
  rw [hd, setG_tcpSt_pend] at eas
  simp only [dtBody, dtFor, segDataIte, tcp_segment, execB_succ, execL_cons, execL_nil, execS_at, execS_assign,
    ev, eas, cpStep, List.length_cons, Nat.sub_self, List.drop_zero]

/-- The echo buffer after bytes `cur … cur+k-1` of the segment's data have been appended. -/
def dtFold (w : TW) (skip : UInt32) (cur k : Nat) : ByteArray :=
  (List.range' cur k).foldl (cpStep w.b w.r.pend_len.toNat (w.sg.doff + skip.toUInt16).toNat) w.pd

/-- The copy loop of the data stage. -/
theorem dt_loop (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (skip : UInt32) (envL : Env)
    (hsk : envL.lookup "skip" = some (u32 skip)) (hnp : envL.lookup "pend" = none)
    (hnb : envL.lookup "buf" = none) (hnt : envL.lookup "t" = none) (hns : envL.lookup "sg" = none) (hi : Nat) :
    ∀ (k cur : Nat) (w : TW) (v0 : Val) (d : Nat), cur + k = hi → w.r.pend_len.toNat + hi ≤ w.pd.size →
      (w.sg.doff + skip.toUInt16).toNat + hi ≤ w.b.size → w.pd.size < 65536 → w.b.size < 65536 →
      ∃ v, forLoop (k + 7 + d) p (tcpSt st w) (("i", v0) :: envL) "i" .w16 cur hi dtBody
          = .ok (tcpSt st { w with pd := dtFold w skip cur k }) (("i", v) :: envL) .normal := by
  intro k
  induction k with
  | zero =>
    intro cur w v0 d hk _ _ _ _
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 7 + d = (6 + d) + 1 by omega, forLoop_succ]
    simp [this, dtFold]
  | succ k ih =>
    intro cur w v0 d hk h1 h2 h3 h4
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    have hsz : (cpStep w.b w.r.pend_len.toNat (w.sg.doff + skip.toUInt16).toNat w.pd cur).size = w.pd.size := by
      simp [cpStep]
    obtain ⟨v, hv⟩ := ih (cur + 1)
      { w with pd := cpStep w.b w.r.pend_len.toNat (w.sg.doff + skip.toUInt16).toNat w.pd cur }
      (u16 (UInt16.ofNat cur)) d (by omega) (by simp only [hsz]; exact h1) h2 (by simp only [hsz]; exact h3) h4
    refine ⟨v, ?_⟩
    rw [show k + 1 + 7 + d = (k + 7 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 7 + d = (k + 1 + d) + 6 by omega,
      dt_body p hP st hB skip envL hsk hnp hnb hnt hns w cur (by omega) (by omega) h3 h4 (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 6 = k + 7 + d by omega, hv]
    simp [dtFold, List.range'_succ]

/-- The echo buffer with `n` bytes of the segment's data appended (those after the ones already received). -/
def dataPd (w : TW) (n : Nat) : ByteArray :=
  cpIn w.pd w.b w.r.pend_len.toNat (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat n

/-- The data stage of `tcp_segment`: in-order bytes that fit the window
are taken (into the echo buffer in ESTABLISHED); the results are the
state, whether an ACK is owed, and whether everything fresh was taken. -/
def segDataW (w : TW) : TW × Bool × Bool :=
  let r := w.r
  if 0 < w.sg.dlen then
    if r.st == 2 || (r.st == 5 || r.st == 6) then
      let skip := r.rcv_nxt - w.sg.seq
      let fresh : UInt16 := if skip < w.sg.dlen.toUInt32 then w.sg.dlen - skip.toUInt16 else 0
      let take : UInt16 := if r.wnd < fresh then r.wnd else fresh
      let w1 : TW :=
        if r.st == 2 then
          { w with pd := dataPd w take.toNat, r := { r with pend_len := r.pend_len + take } }
        else w
      ({ w1 with r := { w1.r with rcv_nxt := r.rcv_nxt + take.toUInt32 } }, true, take == fresh)
    else (w, false, true)
  else (w, false, true)

set_option maxHeartbeats 4000000 in
/-- The data stage as a statement. -/
theorem seg_data_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (hw : TWok w) (fin okv : Bool) (hcap : w.r.pend_len.toNat + w.r.wnd.toNat ≤ 256)
    (hsrc : w.sg.doff.toNat + w.sg.dlen.toNat ≤ w.b.size) (d : Nat) :
    execS (d + 400) p (tcpSt st w)
        [("fin", .bool fin), ("in_order", .bool true), ("ack_now", .bool false), ("ok", .bool okv)] segDataIte
      = .ok (tcpSt st (segDataW w).1)
          [("fin", .bool fin), ("in_order", .bool (segDataW w).2.2), ("ack_now", .bool (segDataW w).2.1),
            ("ok", .bool okv)] .normal := by
  have hb64 := hw.b64
  have t0 : (u16 (UInt16.ofNat 0)).toNat = 0 := rfl
  have hforG : ∀ (T Fr : UInt16), w.r.pend_len.toNat + T.toNat ≤ 256 →
      (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat + T.toNat ≤ w.b.size →
      execS (d + 381) p (tcpSt st w) [("take", u16 T), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] dtFor
      = .ok (tcpSt st { w with pd := dataPd w T.toNat }) [("take", u16 T), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] .normal := by
    intro T Fr h1 h2
    obtain ⟨v, hv⟩ := dt_loop p hP st hB (w.r.rcv_nxt - w.sg.seq) [("take", u16 T), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] (by simp [List.lookup])
      (by simp [List.lookup]) (by simp [List.lookup]) (by simp [List.lookup]) (by simp [List.lookup]) T.toNat T.toNat
      0 w (.int .w16 (UInt64.ofNat 0)) (d + 373 - T.toNat) (by omega) (by rw [hw.pd]; exact h1) h2
      (by rw [hw.pd]; omega) hb64
    rw [show T.toNat + 7 + (d + 373 - T.toNat) = d + 380 by omega] at hv
    have tn : (u16 T).toNat = T.toNat := by
      show T.toUInt64.toNat = _
      rw [UInt16.toNat_toUInt64]
    have ehi : evalE p (tcpSt st w) [("take", u16 T), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] (.var "take") = some (u16 T) := by simp [evalE, lookup, List.lookup]
    simp only [dtBody, dtFor, segDataIte, tcp_segment] at hv
    simp only [dtFor, segDataIte, tcp_segment, execS_forRange, evalE_lit16, ehi, Option.getD, t0, tn, hv, List.drop,
      dtFold, cpIn, dataPd]
  simp only [dtFor, segDataIte, tcp_segment] at hforG
  simp only [segDataIte, tcp_segment]
  have hfor0 : ∀ Fr : UInt16, execS (d + 381) p (tcpSt st w) [("take", u16 0), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] dtFor = .ok (tcpSt st w) [("take", u16 0), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] .normal := by
    intro Fr
    have ehi : evalE p (tcpSt st w) [("take", u16 0), ("w", u16 w.r.wnd), ("fresh", u16 Fr), ("skip", u32 (w.r.rcv_nxt - w.sg.seq)), ("fin", Val.bool fin), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] (.var "take") = some (u16 0) := by simp [evalE, lookup, List.lookup]
    have tz : (u16 0).toNat = 0 := rfl
    simp only [dtFor, segDataIte, tcp_segment, execS_forRange, evalE_lit16, ehi, Option.getD, t0, tz]
    rw [show d + 380 = (d + 379) + 1 by omega, forLoop_succ]
    simp
  simp only [dtFor, segDataIte, tcp_segment] at hfor0
  rcases Classical.em (0 < w.sg.dlen) with h1 | h1
  · rcases Bool.eq_false_or_eq_true (w.r.st == 2) with h5 | h5
    · have hdl := w.sg.dlen.toNat_lt
      rcases Classical.em (w.r.rcv_nxt - w.sg.seq < w.sg.dlen.toUInt32) with h3 | h3
      · have h3n : (w.r.rcv_nxt - w.sg.seq).toNat < w.sg.dlen.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp h3
          simpa using this
        have hsk16 : (w.r.rcv_nxt - w.sg.seq).toUInt16.toNat = (w.r.rcv_nxt - w.sg.seq).toNat := by
          rw [UInt32.toNat_toUInt16]; omega
        have hfr : (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat
            = w.sg.dlen.toNat - (w.r.rcv_nxt - w.sg.seq).toNat := by
          rw [UInt16.toNat_sub, hsk16]; omega
        have hsrcN : (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat
            = w.sg.doff.toNat + (w.r.rcv_nxt - w.sg.seq).toNat := by
          rw [UInt16.toNat_add, hsk16]; omega
        rcases Classical.em (w.r.wnd < w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16) with h4 | h4
        · have h4n := UInt16.lt_iff_toNat_lt.mp h4
          have hf := hforG w.r.wnd (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16) hcap (by omega)
          (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
        · have hf := hforG (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16)
            (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16)
            (by have := mt UInt16.lt_iff_toNat_lt.mpr h4; omega) (by omega)
          (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
      · have h4 : ¬ w.r.wnd < 0 := by
          intro h; have := UInt16.lt_iff_toNat_lt.mp h; simp at this
        have hf0 := hfor0 0
        (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
    · rcases Bool.eq_false_or_eq_true (w.r.st == 5 || w.r.st == 6) with h2 | h2
      · have hdl := w.sg.dlen.toNat_lt
        rcases Classical.em (w.r.rcv_nxt - w.sg.seq < w.sg.dlen.toUInt32) with h3 | h3
        · have h3n : (w.r.rcv_nxt - w.sg.seq).toNat < w.sg.dlen.toNat := by
            have := UInt32.lt_iff_toNat_lt.mp h3
            simpa using this
          have hsk16 : (w.r.rcv_nxt - w.sg.seq).toUInt16.toNat = (w.r.rcv_nxt - w.sg.seq).toNat := by
            rw [UInt32.toNat_toUInt16]; omega
          have hfr : (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat
              = w.sg.dlen.toNat - (w.r.rcv_nxt - w.sg.seq).toNat := by
            rw [UInt16.toNat_sub, hsk16]; omega
          have hsrcN : (w.sg.doff + (w.r.rcv_nxt - w.sg.seq).toUInt16).toNat
              = w.sg.doff.toNat + (w.r.rcv_nxt - w.sg.seq).toNat := by
            rw [UInt16.toNat_add, hsk16]; omega
          rcases Classical.em (w.r.wnd < w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16) with h4 | h4
          · have h4n := UInt16.lt_iff_toNat_lt.mp h4
            have hf := hforG w.r.wnd (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16) hcap (by omega)
            (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
          · have hf := hforG (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16)
              (w.sg.dlen - (w.r.rcv_nxt - w.sg.seq).toUInt16)
              (by have := mt UInt16.lt_iff_toNat_lt.mpr h4; omega) (by omega)
            (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
        · have h4 : ¬ w.r.wnd < 0 := by
            intro h; have := UInt16.lt_iff_toNat_lt.mp h; simp at this
          have hf0 := hfor0 0
          (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
      · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)
  · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segDataW, dataPd, cpIn, List.range', List.foldl]; try rfl)

/-! ## `tcp_segment`: the FIN -/

/-- The FIN stage: an in-order FIN moves the connection on and is
acknowledged. -/
def segFinW (w : TW) (fin inOrder ackNow : Bool) : TW × Bool :=
  let r := w.r
  if fin && (inOrder && (w.sg.seq + w.sg.dlen.toUInt32 == r.rcv_nxt)) then
    if r.st == 2 then ({ w with r := { r with st := 3, rcv_nxt := r.rcv_nxt + 1 } }, true)
    else if r.st == 5 then ({ w with r := { r with st := 7, rcv_nxt := r.rcv_nxt + 1 } }, true)
    else if r.st == 6 then
      ({ w with r := { r with st := 8, tw_timer := 20, rcv_nxt := r.rcv_nxt + 1 } }, true)
    else (w, ackNow)
  else (w, ackNow)

/-- The FIN stage as a statement. -/
theorem seg_fin_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (fin io an okv : Bool) (d : Nat) :
    execS (d + 40) p (tcpSt st w)
        [("fin", .bool fin), ("in_order", .bool io), ("ack_now", .bool an), ("ok", .bool okv)] segFinIte
      = .ok (tcpSt st (segFinW w fin io an).1)
          [("fin", .bool fin), ("in_order", .bool io), ("ack_now", .bool (segFinW w fin io an).2),
            ("ok", .bool okv)] .normal := by
  simp only [segFinIte, tcp_segment]
  rcases Bool.eq_false_or_eq_true (fin && (io && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) with h1 | h1
  · rcases Bool.eq_false_or_eq_true (w.r.st == 2) with h2 | h2
    · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segFinW]; try rfl)
    · rcases Bool.eq_false_or_eq_true (w.r.st == 5) with h3 | h3
      · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segFinW]; try rfl)
      · rcases Bool.eq_false_or_eq_true (w.r.st == 6) with h4 | h4 <;>
        (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segFinW]; try rfl)
  · (tcp_sym_all [hP.toTcpProg, hP.sTcb, hP.sSeg, segFinW]; try rfl)

/-! ## Calls as statements -/

@[tcpsym] theorem x_acceptable (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (w : TW) (env : Env) (dst : Option Expr) (n : Nat) :
    execS (n + 41) p (tcpSt st w) env (.call dst "acceptable" [])
      = storeResult p (tcpSt st w) env dst (some (.bool (accW w))) :=
  execS_call_val p _ env (n + 40) dst "acceptable" [] hP.acceptable (by simp [acceptable]) (by simp [evalArgs])
    (acceptable_tw p hP st hB hK w n)

theorem x_listen_input (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (env : Env) (d : Nat) :
    execS (d + 801) p (tcpSt st w) env (.call none "listen_input" [])
      = .ok (tcpSt st (listenW w ourIp)) env .normal :=
  execS_call_val p _ env _ none "listen_input" [] hP.listen_input (by simp [listen_input]) (by simp [evalArgs])
    (listen_input_tw p hP hR st hB hK ourIp hip w hw d)

theorem x_ack_input (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (hi1 : w.r.sent.toNat ≤ w.r.pend_len.toNat) (hi2 : w.r.pend_len.toNat ≤ 256) (env : Env)
    (dst : Option Expr) (d : Nat) :
    execS (d + 801) p (tcpSt st w) env (.call dst "ack_input" [])
      = storeResult p (tcpSt st (ackW w ourIp).2) env dst (some (.bool (ackW w ourIp).1)) :=
  execS_call_val p _ env _ dst "ack_input" [] hP.ack_input (by simp [ack_input]) (by simp [evalArgs])
    (ack_input_tw p hP hR st hB hK ourIp hip w hw hi1 hi2 d)

theorem x_output (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) (hw : TWok w)
    (hU1 : 40 + (w.r.pend_len - w.r.sent).toNat ≤ w.b.size)
    (hU2 : w.r.sent.toNat + (w.r.pend_len - w.r.sent).toNat ≤ 256) (env : Env) (e : Expr) (an : Bool)
    (he : evalE p (tcpSt st w) env e = some (.bool an)) (d : Nat) :
    execS (d + 801) p (tcpSt st w) env (.call none "output" [e])
      = .ok (tcpSt st (outputW w ourIp an)) env .normal :=
  execS_call_val p _ env _ none "output" [e] hP.output (by simp [output_fn]) (by simp [evalArgs, he])
    (output_tw p hP st hB hK ourIp hip w hw hU1 hU2 an d)

/-- A `note` line. -/
def noteW (w : TW) (s : String) : TW := { w with evs := w.evs ++ [.note s] }

/-- `trace.note(0, 0)`: the connection was reset by the peer. -/
theorem x_note0 (p : Prog) (hR : TcpReasons p) (st : St) (w : TW) (env : Env) (n : Nat) :
    execS (n + 1) p (tcpSt st w) env (.eff none .note [.lit 0 (some .w8), .lit 0 (some .w32)])
      = .ok (tcpSt st (noteW w "connection-reset-by-peer 0")) env .normal := by
  have h8 : (u8 (UInt8.ofNat 0)).toNat = 0 := rfl
  have h32 : (u32 (UInt32.ofNat 0)).toNat = 0 := rfl
  simp only [execS_eff, evalArgs, evalE_lit8, evalE_lit32, Sem.effect, storeResult, List.headD, List.getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD, h8, h32, hR.note0]
  simp only [noteW, tcpSt, setG, foldl_emit_append]
  rfl

/-! ## `tcp_segment` -/

theorem toUInt64_le_iff32 (x y : UInt32) : decide (x.toUInt64 ≤ y.toUInt64) = decide (x ≤ y) := by
  have : x.toUInt64 ≤ y.toUInt64 ↔ x ≤ y := by
    rw [UInt64.le_iff_toNat_le, UInt32.le_iff_toNat_le]; simp
  simp [this]

attribute [tcpsym] toUInt64_le_iff32

/-- Step 5 of `tcp_segment`, the ACK: `.error` when the segment is done
with, `.ok` with the state to go on from. -/
def segAckW (w : TW) (ourIp : UInt32) : Except TW TW :=
  if w.r.st == 1 then
    if w.sg.ack != w.r.snd_nxt then .error (dropW (resetW w ourIp) "bad-ack-in-syn-rcvd")
    else .ok { w with r := { w.r with st := 2, snd_una := w.sg.ack, rt_timer := 0, retries := 0 } }
  else if (ackW w ourIp).1 then .ok (ackW w ourIp).2 else .error (ackW w ourIp).2

/-- Steps 6 to 8: data, FIN, output. -/
def segTailW (w : TW) (ourIp : UInt32) : TW :=
  let fin := w.sg.flags &&& 1 != 0
  if (decide (0 < w.sg.dlen) || fin) && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq) then
    dropW (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false) "out-of-order"
  else
    let dd := segDataW w
    let ff := segFinW dd.1 fin dd.2.2 dd.2.1
    outputW ff.1 ourIp ff.2

/-- A segment that is not acceptable. -/
def segNaW (w : TW) (ourIp : UInt32) : TW :=
  if w.sg.flags &&& 4 != 0 then dropW w "rst-out-of-window"
  else if w.r.st == 1 && (w.sg.flags &&& 2 != 0 && (w.sg.flags &&& 16 == 0 && w.sg.seq + 1 == w.r.rcv_nxt)) then
    dropW (sendSegW w ourIp (2 ||| 16) w.r.snd_una 0 0 true) "duplicate-syn"
  else dropW (sendSegW w ourIp 16 w.r.snd_nxt 0 0 false) "out-of-window"

/-- An acceptable segment: RST, SYN, the ACK, then the tail. -/
def segAccW (w : TW) (ourIp : UInt32) : TW :=
  if w.sg.flags &&& 4 != 0 then noteW { w with r := RawTcb.reset } "connection-reset-by-peer 0"
  else if w.sg.flags &&& 2 != 0 then
    dropW { (emitW w ourIp w.r.rip 7 w.r.rport w.r.snd_nxt 0 4 0 false 0 0) with r := RawTcb.reset } "syn-in-window"
  else if w.sg.flags &&& 16 == 0 then dropW w "no-ack"
  else
    match segAckW w ourIp with
    | .error w' => w'
    | .ok w1 => segTailW w1 ourIp

/-- A segment for the connection (the idle count already cleared). -/
def segConnW (w : TW) (ourIp : UInt32) : TW :=
  if accW w then segAccW w ourIp else segNaW w ourIp

/-- `tcp_segment`: a parsed segment (in `sg`, its data in the packet buffer). -/
def segW (w : TW) (ourIp : UInt32) : TW :=
  if w.sg.dport != 7 then
    dropW (if w.sg.flags &&& 4 == 0 then resetW w ourIp else w) "tcp-port-closed"
  else if w.r.st == 0 || (w.sg.src != w.r.rip || w.sg.sport != w.r.rport) then listenW w ourIp
  else segConnW { w with r := { w.r with idle := 0 } } ourIp

/-- What the tail of `tcp_segment` needs of the state it starts from. -/
structure SegTailOk (w1 : TW) : Prop where
  ok : TWok w1
  cap : w1.r.pend_len.toNat + w1.r.wnd.toNat ≤ 256
  src : w1.sg.doff.toNat + w1.sg.dlen.toNat ≤ w1.b.size
  ok3 : TWok (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1
  u1 : 40 + ((segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.r.pend_len
        - (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.r.sent).toNat
      ≤ (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.b.size
  u2 : (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.r.sent.toNat
      + ((segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.r.pend_len
        - (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1.r.sent).toNat
      ≤ 256


/-- The statements of `tcp_segment` up to the ACK, and those after. -/
def segHeadStmts : List Stmt :=
  match tcp_segment.body with
  | [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, _, _, _, _, _, _, _] => [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  | _ => []

def segTailStmts : List Stmt :=
  match tcp_segment.body with
  | [_, _, _, _, _, _, _, _, _, _, s10, s11, s12, s13, s14, s15, s16] => [s10, s11, s12, s13, s14, s15, s16]
  | _ => []

theorem seg_body_split : tcp_segment.body = segHeadStmts ++ segTailStmts := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The tail of `tcp_segment` (data, FIN, output), from a state that is fit for it. -/
theorem seg_tail_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w1 : TW)
    (h1 : SegTailOk w1) (okv : Bool) (d : Nat) :
    ∃ env' o, execL (d + 2000) p (tcpSt st w1) [("ok", .bool okv)] segTailStmts
        = .ok (tcpSt st (segTailW w1 ourIp)) env' o ∧ (o = .normal ∨ o = .ret none) := by
  have t1 : execS (d + 1991) p (tcpSt st w1) [("fin", Val.bool (w1.sg.flags &&& 1 != 0)), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] (.call none "send_seg" [.var "F_ACK", .field (.var "t") "snd_nxt", .lit 0 (some .w16), .lit 0 (some .w16), .blit false])
      = .ok (tcpSt st (sendSegW w1 ourIp 16 w1.r.snd_nxt 0 0 false)) [("fin", Val.bool (w1.sg.flags &&& 1 != 0)), ("in_order", Val.bool true), ("ack_now", Val.bool false), ("ok", Val.bool okv)] .normal :=
    x_send_seg p hP st hB hK ourIp hip w1 h1.ok _ _ 16 w1.r.snd_nxt (UInt16.ofNat 0) (UInt16.ofNat 0) false
      (by tcp_sym [evalArgs, hP.sTcb, hB, hK])
      (by rw [tcpOff_false]; have := h1.ok.b44; simp; omega) (by simp) _ (d + 1650) (by simp)
  have t2 := seg_data_tw p hP st hB hK w1 h1.ok (w1.sg.flags &&& 1 != 0) okv h1.cap h1.src (d + 1594)
  have f_fin : ∀ (w' : TW) (fin io an : Bool), execS (d + 1993) p (tcpSt st w')
      [("fin", .bool fin), ("in_order", .bool io), ("ack_now", .bool an), ("ok", .bool okv)] segFinIte = _ :=
    fun w' fin io an => seg_fin_tw p hP st hB hK w' fin io an okv (d + 1953)
  have t3 : ∀ an : Bool, execS (d + 1992) p
      (tcpSt st (segFinW (segDataW w1).1 (w1.sg.flags &&& 1 != 0) (segDataW w1).2.2 (segDataW w1).2.1).1)
      [("fin", .bool (w1.sg.flags &&& 1 != 0)), ("in_order", .bool (segDataW w1).2.2), ("ack_now", .bool an),
        ("ok", .bool okv)] (.call none "output" [.var "ack_now"]) = _ :=
    fun an => x_output p hP st hB hK ourIp hip _ h1.ok3 h1.u1 h1.u2 _ _ an (by tcp_sym []) (d + 1191)
  simp only [segFinIte, tcp_segment] at f_fin
  simp only [segDataIte, tcp_segment] at t2
  simp only [segTailStmts, tcp_segment]
  rcases Bool.eq_false_or_eq_true ((decide (0 < w1.sg.dlen) || (w1.sg.flags &&& 1 != 0)) &&
      decide (2147483648 ≤ w1.r.rcv_nxt - w1.sg.seq)) with hooo | hooo
  · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_fin, segTailW, dropW, hooo, t1]
    exact ⟨_, _, rfl, Or.inr rfl⟩
  · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, f_fin, segTailW, dropW, hooo, t2, t3]
    exact ⟨_, _, rfl, Or.inl rfl⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
theorem tcp_segment_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (hi1 : w.r.sent.toNat ≤ w.r.pend_len.toNat) (hi2 : w.r.pend_len.toNat ≤ 256)
    (hT : ∀ w1, segAckW { w with r := { w.r with idle := 0 } } ourIp = .ok w1 → SegTailOk w1) (d : Nat) :
    Sem.call (d + 3000) p (tcpSt st w) "tcp_segment" [] = .ok none (tcpSt st (segW w ourIp)) := by
  have hw0 : TWok { w with r := { w.r with idle := 0 } } := ⟨hw.b44, hw.b64, hw.pd⟩
  have h44 : 20 + (tcpOff false).toNat + (UInt16.ofNat 0).toNat ≤ w.b.size := by
    rw [tcpOff_false]; have := hw.b44; simp; omega
  have f_rst_port : execS (d + 2989) p (tcpSt st w) [] (.call none "send_reset" []) = _ :=
    x_send_reset p hP st hB hK ourIp hip w hw [] (d + 2638)
  have f_listen : execS (d + 2992) p (tcpSt st w) [] (.call none "listen_input" []) = _ :=
    x_listen_input p hP hR st hB hK ourIp hip w hw [] (d + 2191)
  have f_dup : ∀ okv : Bool, execS (d + 2983) p (tcpSt st { w with r := { w.r with idle := 0 } }) [("ok", .bool okv)] (.call none "send_syn_ack" [])
      = .ok (tcpSt st (sendSegW { w with r := { w.r with idle := 0 } } ourIp (2 ||| 16) w.r.snd_una 0 0 true)) [("ok", .bool okv)] .normal :=
    fun okv => x_send_syn_ack p hP st hB hK ourIp hip { w with r := { w.r with idle := 0 } } hw0 _ (d + 2632)
  have f_oow : ∀ okv : Bool, execS (d + 2986) p (tcpSt st { w with r := { w.r with idle := 0 } }) [("ok", .bool okv)]
      (.call none "send_seg" [.var "F_ACK", .field (.var "t") "snd_nxt", .lit 0 (some .w16), .lit 0 (some .w16), .blit false])
      = .ok (tcpSt st (sendSegW { w with r := { w.r with idle := 0 } } ourIp 16 w.r.snd_nxt 0 0 false)) [("ok", .bool okv)] .normal :=
    fun okv => x_send_seg p hP st hB hK ourIp hip { w with r := { w.r with idle := 0 } } hw0 _ _ 16 w.r.snd_nxt (UInt16.ofNat 0) (UInt16.ofNat 0)
      false (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) h44 (by simp) _ (d + 2645) (by simp)
  have f_synw : ∀ okv : Bool, execS (d + 2986) p (tcpSt st { w with r := { w.r with idle := 0 } }) [("ok", .bool okv)]
      (.call none "tcp_emit" [.field (.var "t") "rip", .var "ECHO_PORT", .field (.var "t") "rport",
        .field (.var "t") "snd_nxt", .lit 0 (some .w32), .var "F_RST", .lit 0 (some .w16), .blit false,
        .lit 0 (some .w16), .lit 0 (some .w16)])
      = .ok (tcpSt st (emitW { w with r := { w.r with idle := 0 } } ourIp w.r.rip 7 w.r.rport w.r.snd_nxt 0 4 0 false 0 0)) [("ok", .bool okv)]
          .normal :=
    fun okv => x_tcp_emit p hP st hB hK ourIp hip { w with r := { w.r with idle := 0 } } hw0 _ _ w.r.rip 7 w.r.rport w.r.snd_nxt (UInt32.ofNat 0) 4
      (UInt16.ofNat 0) false (UInt16.ofNat 0) (UInt16.ofNat 0) (by tcp_sym [evalArgs, hP.sTcb, hB, hK]) h44 (by simp)
      _ (d + 2685) (by simp)
  have f_badack : ∀ okv : Bool, execS (d + 2980) p (tcpSt st { w with r := { w.r with idle := 0 } }) [("ok", .bool okv)]
      (.call none "send_reset" []) = .ok (tcpSt st (resetW { w with r := { w.r with idle := 0 } } ourIp)) [("ok", .bool okv)] .normal :=
    fun okv => x_send_reset p hP st hB hK ourIp hip { w with r := { w.r with idle := 0 } } hw0 _ (d + 2629)
  have f_ack : ∀ okv : Bool, execS (d + 2983) p (tcpSt st { w with r := { w.r with idle := 0 } }) [("go", .bool false), ("ok", .bool okv)]
      (.call (some (.var "go")) "ack_input" [])
      = .ok (tcpSt st (ackW { w with r := { w.r with idle := 0 } } ourIp).2) [("go", .bool (ackW { w with r := { w.r with idle := 0 } } ourIp).1), ("ok", .bool okv)] .normal := by
    intro okv
    rw [x_ack_input p hP hR st hB hK ourIp hip { w with r := { w.r with idle := 0 } } hw0 hi1 hi2 _ _ (d + 2182)]
    tcp_sym []
  have hpar : tcp_segment.params = [] := rfl
  simp only [Sem.call, hP.tcp_segment, hpar, List.map, List.zip, List.zipWith, execB_succ]
  have hlen : segHeadStmts.length = 10 := rfl
  rw [seg_body_split, show d + 2999 = (d + 2988) + 1 + segHeadStmts.length from rfl, execL_append, hlen,
    show (d + 2988) + 1 + 10 = d + 2999 from rfl]
  simp only [segHeadStmts, tcp_segment]
  unfold segW
  by_cases hpp : (w.sg.dport != 7) = true
  · have hp := hpp
    rw [if_pos hpp]
    rcases Bool.eq_false_or_eq_true (w.sg.flags &&& 4 == 0) with hr0 | hr0
    · rw [if_pos hr0]
      tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hr0]
      try (simp only [dropW, noteW])
    · rw [if_neg (by rw [hr0]; simp)]
      tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hr0]
      try (simp only [dropW, noteW])
  · have hp : (w.sg.dport != 7) = false := by simpa using hpp
    rw [if_neg hpp]
    by_cases hll : (w.r.st == 0 || (w.sg.src != w.r.rip || w.sg.sport != w.r.rport)) = true
    · have hl := hll
      rw [if_pos hll]
      tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl]
    · have hl : (w.r.st == 0 || (w.sg.src != w.r.rip || w.sg.sport != w.r.rport)) = false := by simpa using hll
      rw [if_neg hll]
      by_cases hacc : accW { w with r := { w.r with idle := 0 } } = true
      · by_cases hr4p : (w.sg.flags &&& 4 != 0) = true
        · have hr4 := hr4p
          rw [segConnW, if_pos hacc, segAccW]
          dsimp only
          rw [if_pos hr4p]
          tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4]
          try (simp only [dropW, noteW])
        · have hr4n := hr4p
          have hr4 : (w.sg.flags &&& 4 != 0) = false := by simpa using hr4p
          by_cases hsynp : (w.sg.flags &&& 2 != 0) = true
          · have hsyn := hsynp
            rw [segConnW, if_pos hacc, segAccW]
            dsimp only
            rw [if_neg hr4n, if_pos hsynp]
            tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn]
            try (simp only [dropW, noteW])
          · have hsynn := hsynp
            have hsyn : (w.sg.flags &&& 2 != 0) = false := by simpa using hsynp
            by_cases hack0p : (w.sg.flags &&& 16 == 0) = true
            · have hack0 := hack0p
              rw [segConnW, if_pos hacc, segAccW]
              dsimp only
              rw [if_neg hr4n, if_neg hsynn, if_pos hack0p]
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn, hack0]
              try (simp only [dropW, noteW])
            · have hack0n := hack0p
              have hack0 : (w.sg.flags &&& 16 == 0) = false := by simpa using hack0p
              rcases Bool.eq_false_or_eq_true (w.r.st == 1) with hs1 | hs1
              · rcases Bool.eq_false_or_eq_true (w.sg.ack != w.r.snd_nxt) with hbad | hbad
                · have hsa : segAckW { w with r := { w.r with idle := 0 } } ourIp = .error (dropW (resetW { w with r := { w.r with idle := 0 } } ourIp) "bad-ack-in-syn-rcvd") := by
                    simp only [segAckW, hs1, hbad, if_true]
                  rw [segConnW, if_pos hacc, segAccW]
                  dsimp only
                  rw [if_neg hr4n, if_neg hsynn, if_neg hack0n, hsa]
                  tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn, hack0, hs1, hbad]
                  try (simp only [dropW, noteW])
                · have hsa : segAckW { w with r := { w.r with idle := 0 } } ourIp = .ok ({ w with r := { w.r with idle := 0, st := 2, snd_una := w.sg.ack, rt_timer := 0, retries := 0 } }) := by
                    simp only [segAckW, hs1, hbad, if_true, Bool.false_eq_true, if_false]
                  obtain ⟨env', o, htl, ho⟩ := seg_tail_tw p hP hR st hB hK ourIp hip ({ w with r := { w.r with idle := 0, st := 2, snd_una := w.sg.ack, rt_timer := 0, retries := 0 } }) (hT _ hsa) true (d + 989)
                  have htl' : execL (d + 2988 + 1) p (tcpSt st ({ w with r := { w.r with idle := 0, st := 2, snd_una := w.sg.ack, rt_timer := 0, retries := 0 } })) [("ok", .bool true)] segTailStmts = _ := htl
                  rw [segConnW, if_pos hacc, segAccW]
                  dsimp only
                  rw [if_neg hr4n, if_neg hsynn, if_neg hack0n, hsa]
                  rcases ho with rfl | rfl <;>
                  · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn, hack0, hs1, hbad, htl']
              · rcases Bool.eq_false_or_eq_true (ackW { w with r := { w.r with idle := 0 } } ourIp).1 with hgo | hgo
                · have hsa : segAckW { w with r := { w.r with idle := 0 } } ourIp = .ok ((ackW { w with r := { w.r with idle := 0 } } ourIp).2) := by
                    simp only [segAckW, hs1, hgo, if_true, Bool.false_eq_true, if_false]
                  obtain ⟨env', o, htl, ho⟩ := seg_tail_tw p hP hR st hB hK ourIp hip ((ackW { w with r := { w.r with idle := 0 } } ourIp).2) (hT _ hsa) true (d + 989)
                  have htl' : execL (d + 2988 + 1) p (tcpSt st ((ackW { w with r := { w.r with idle := 0 } } ourIp).2)) [("ok", .bool true)] segTailStmts = _ := htl
                  rw [segConnW, if_pos hacc, segAccW]
                  dsimp only
                  rw [if_neg hr4n, if_neg hsynn, if_neg hack0n, hsa]
                  rcases ho with rfl | rfl <;>
                  · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn, hack0, hs1, hgo, htl']
                · have hsa : segAckW { w with r := { w.r with idle := 0 } } ourIp = .error (ackW { w with r := { w.r with idle := 0 } } ourIp).2 := by
                    simp only [segAckW, hs1, hgo, Bool.false_eq_true, if_false]
                  rw [segConnW, if_pos hacc, segAccW]
                  dsimp only
                  rw [if_neg hr4n, if_neg hsynn, if_neg hack0n, hsa]
                  tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, hacc, hr4, hsyn, hack0, hs1, hgo]
      · have haccf : accW { w with r := { w.r with idle := 0 } } = false := by simpa using hacc
        rw [segConnW, if_neg hacc, segNaW]
        dsimp only
        by_cases hrp : (w.sg.flags &&& 4 != 0) = true
        · have hr := hrp
          rw [if_pos hrp]
          tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, haccf, hr]
          try (simp only [dropW, noteW])
        · have hr : (w.sg.flags &&& 4 != 0) = false := by simpa using hrp
          rw [if_neg hrp]
          by_cases hdupp : (w.r.st == 1 && (w.sg.flags &&& 2 != 0 &&
              (w.sg.flags &&& 16 == 0 && w.sg.seq + 1 == w.r.rcv_nxt))) = true
          · have hdup := hdupp
            rw [if_pos hdupp]
            tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, haccf, hr, hdup]
            try (simp only [dropW, noteW])
          · have hdup : (w.r.st == 1 && (w.sg.flags &&& 2 != 0 &&
                (w.sg.flags &&& 16 == 0 && w.sg.seq + 1 == w.r.rcv_nxt))) = false := by simpa using hdupp
            rw [if_neg hdupp]
            tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, x_note0 p hR st, f_rst_port, f_listen, f_dup, f_oow, f_synw, f_badack, f_ack, hp, hl, haccf, hr, hdup]
            try (simp only [dropW, noteW])

end Ember.Proof.Refine
