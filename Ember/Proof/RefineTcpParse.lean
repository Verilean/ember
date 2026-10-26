import Ember.Proof.RefineTcpIn

/-!
# Ember.Proof.RefineTcpParse — TCP: the segment is checked and parsed (plan M5.5)

`parse_mss` (the scan of the options, a bounded loop with `break`:
`mss_loop`, by induction over `loopN`) and `tcp_input`, the entry of the
TCP code: length, data offset, checksum, the fields into `sg`, the MSS
option, then `tcp_segment`.

`tcp_input_tw` is the top of the raw layer for a received segment: the
Ember code computes the Lean function `tcpInputW`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## `parse_mss`: the options of a segment -/

/-- One round of the option scan: `none` when the scan stops, else the
next offset and what is known of the MSS option. -/
def mssStep (b : ByteArray) (off : UInt16) (s : UInt16 × Bool × UInt16) : Option (UInt16 × Bool × UInt16) :=
  if off ≤ s.1 then none
  else
    let k := Bytes.get b (20 + s.1).toNat
    if k == 0 then none
    else if k == 1 then some (s.1 + 1, s.2.1, s.2.2)
    else if off ≤ s.1 + 1 then none
    else
      let l := (Bytes.get b (20 + s.1 + 1).toNat).toUInt16
      if l < 2 || off < s.1 + l then none
      else if k == 2 && l == 4 then some (s.1 + l, true, Bytes.get16 b (20 + s.1 + 2).toNat)
      else some (s.1 + l, s.2.1, s.2.2)

/-- At most `n` rounds. -/
def mssIter (b : ByteArray) (off : UInt16) : Nat → UInt16 × Bool × UInt16 → UInt16 × Bool × UInt16
  | 0, s => s
  | n + 1, s =>
    match mssStep b off s with
    | none => s
    | some s' => mssIter b off n s'

/-- The body of the loop of `parse_mss`. -/
def mssBody : List Stmt :=
  match parse_mss.body with
  | [_, _, _, .at _ (.loop _ body)] => body
  | _ => []

theorem loopN_succ (p : Prog) (st : St) (env : Env) (n k : Nat) (body : List Stmt) :
    loopN (n + 1) p st env (k + 1) body =
      match execB n p st env body with
      | .ok st' env' .normal => loopN n p st' env' k body
      | .ok st' env' .brk => .ok st' env' .normal
      | r => r := by
  simp only [loopN]; rfl

theorem loopN_zero (p : Prog) (st : St) (env : Env) (n : Nat) (body : List Stmt) :
    loopN (n + 1) p st env 0 body = .ok st env .normal := by
  simp only [loopN]

theorem toUInt64_le_iff (x y : UInt16) : decide (x.toUInt64 ≤ y.toUInt64) = decide (x ≤ y) := by
  have : x.toUInt64 ≤ y.toUInt64 ↔ x ≤ y := by
    rw [UInt64.le_iff_toNat_le, UInt16.le_iff_toNat_le]; simp
  simp [this]

attribute [tcpsym] toUInt64_le_iff execS_brk

set_option maxHeartbeats 4000000 in
/-- One round of the scan. -/
theorem mss_body (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (off i : UInt16) (hb : 20 + off.toNat ≤ w.b.size) (hb64 : w.b.size < 65536) (m : Nat) :
    execB (m + 40) p (tcpSt st w) [("i", u16 i), ("off", u16 off)] mssBody =
      match mssStep w.b off (i, w.sg.has_mss, w.sg.mss) with
      | none => .ok (tcpSt st w) [("i", u16 i), ("off", u16 off)] .brk
      | some s' =>
        .ok (tcpSt st { w with sg := { w.sg with has_mss := s'.2.1, mss := s'.2.2 } })
          [("i", u16 s'.1), ("off", u16 off)] .normal := by
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  simp only [mssBody, parse_mss]
  rcases Classical.em (off ≤ i) with h1 | h1
  · tcp_sym_b [hP.sTcb, hP.sSeg, hB, hK, h1, mssStep]
  · have h1n : i.toNat < off.toNat := by
      have := mt UInt16.le_iff_toNat_le.mpr h1; omega
    have h20 : (20 + i).toNat = 20 + i.toNat := by
      have t : (20 : UInt16).toNat = 20 := rfl
      rw [UInt16.toNat_add, t]; omega
    have hk : evalE p (tcpSt st w) [("i", u16 i), ("off", u16 off)] (.index (.var "buf") (.bin .add (.lit 20 (some .w16)) (.var "i")))
        = some (u8 (Bytes.get w.b (20 + i).toNat)) :=
      evalE_index_arr p _ _ "buf" w.b _ (20 + i) (by simp [lookup, List.lookup, lookup_tcpSt_buf st hB w])
        (by tcp_sym_b []) (by rw [h20]; omega)
    rcases Bool.eq_false_or_eq_true (Bytes.get w.b (20 + i).toNat == 0) with h2 | h2
    · tcp_sym_b [hP.sTcb, hP.sSeg, hB, hK, h1, h2, hk, mssStep]
    · rcases Bool.eq_false_or_eq_true (Bytes.get w.b (20 + i).toNat == 1) with h3 | h3
      · tcp_sym_b [hP.sTcb, hP.sSeg, hB, hK, h1, h2, h3, hk, mssStep]
        try rfl
      · rcases Classical.em (off ≤ i + 1) with h4 | h4
        · tcp_sym_b [hP.sTcb, hP.sSeg, hB, hK, h1, h2, h3, h4, hk, mssStep]
        · have h4n : i.toNat + 1 < off.toNat := by
            have := mt UInt16.le_iff_toNat_le.mpr h4
            have t : (1 : UInt16).toNat = 1 := rfl
            rw [UInt16.toNat_add, t] at this; omega
          have h21 : (20 + i + 1).toNat = 20 + i.toNat + 1 := by
            have t : (1 : UInt16).toNat = 1 := rfl
            rw [UInt16.toNat_add, h20, t]; omega
          have hl : evalE p (tcpSt st w) [("k", u8 (Bytes.get w.b (20 + i).toNat)), ("i", u16 i), ("off", u16 off)]
              (.cast .w16 (.index (.var "buf") (.bin .add (.bin .add (.lit 20 (some .w16)) (.var "i"))
                (.lit 1 (some .w16))))) = some (u16 (Bytes.get w.b (20 + i + 1).toNat).toUInt16) := by
            rw [evalE_cast, evalE_index_arr p _ _ "buf" w.b _ (20 + i + 1)
              (by simp [lookup, List.lookup, lookup_tcpSt_buf st hB w]) (by tcp_sym_b []) (by rw [h21]; omega)]
            simp only [mask16_u8]
          rcases Bool.eq_false_or_eq_true (decide ((Bytes.get w.b (20 + i + 1).toNat).toUInt16 < 2) ||
              decide (off < i + (Bytes.get w.b (20 + i + 1).toNat).toUInt16)) with h5 | h5
          · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, h1, h2, h3, h4, hk, hl, mssStep, h5]
          · rcases Bool.eq_false_or_eq_true (Bytes.get w.b (20 + i).toNat == 2 &&
                (Bytes.get w.b (20 + i + 1).toNat).toUInt16 == 4) with h6 | h6
            · have hl4 : (Bytes.get w.b (20 + i + 1).toNat).toUInt16 = 4 := by
                have := (Bool.and_eq_true _ _).mp h6
                simpa using this.2
              have h5' : ¬ off < i + 4 := by
                have h5c := h5
                rw [hl4] at h5c
                exact of_decide_eq_false (Bool.or_eq_false_iff.mp h5c).2
              have h22 : (20 + i + 2).toNat = 20 + i.toNat + 2 := by
                have t : (2 : UInt16).toNat = 2 := rfl
                rw [UInt16.toNat_add, h20, t]; omega
              have hi4 : i.toNat + 4 ≤ off.toNat := by
                have := mt UInt16.lt_iff_toNat_lt.mpr h5'
                have t : (4 : UInt16).toNat = 4 := rfl
                rw [UInt16.toNat_add, t] at this; omega
              have hg : ∀ m' : Nat, execS (m' + 7) p
                  (tcpSt st { w with sg := { w.sg with has_mss := true } }) [("l", u16 (Bytes.get w.b (20 + i + 1).toNat).toUInt16), ("k", u8 (Bytes.get w.b (20 + i).toNat)), ("i", u16 i), ("off", u16 off)]
                  (.call (some (.field (.var "sg") "mss")) "get16"
                    [.bin .add (.bin .add (.lit 20 (some .w16)) (.var "i")) (.lit 2 (some .w16))])
                  = storeResult p (tcpSt st { w with sg := { w.sg with has_mss := true } }) [("l", u16 (Bytes.get w.b (20 + i + 1).toNat).toUInt16), ("k", u8 (Bytes.get w.b (20 + i).toNat)), ("i", u16 i), ("off", u16 off)]
                      (some (.field (.var "sg") "mss")) (some (u16 (Bytes.get16 w.b (20 + i + 2).toNat))) :=
                fun m' => execS_get16 p hP.get16 (tcpSt st { w with sg := { w.sg with has_mss := true } }) _ w.b
                  (lookup_tcpSt_buf st hB { w with sg := { w.sg with has_mss := true } }) _ _ (20 + i + 2) m'
                  (by rw [h22]; omega) (by rw [h22]; omega) (by tcp_sym_b [])
              tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, h1, h2, h3, h4, hk, hl, mssStep, h5, h6, hg]
              try rfl
            · tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, h1, h2, h3, h4, hk, hl, mssStep, h5, h6]
              try rfl

/-- The scan: at most `k` rounds. -/
theorem mss_loop (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (off : UInt16)
    (bsz : Nat) (hb : 20 + off.toNat ≤ bsz) (hb64 : bsz < 65536) :
    ∀ (k : Nat) (i : UInt16) (w : TW) (d : Nat), w.b.size = bsz →
      loopN (k + 41 + d) p (tcpSt st w) [("i", u16 i), ("off", u16 off)] k mssBody
        = .ok (tcpSt st { w with sg := { w.sg with
              has_mss := (mssIter w.b off k (i, w.sg.has_mss, w.sg.mss)).2.1,
              mss := (mssIter w.b off k (i, w.sg.has_mss, w.sg.mss)).2.2 } })
            [("i", u16 (mssIter w.b off k (i, w.sg.has_mss, w.sg.mss)).1), ("off", u16 off)] .normal := by
  intro k
  induction k with
  | zero =>
    intro i w d _
    rw [show 0 + 41 + d = (40 + d) + 1 by omega, loopN_zero]
    rfl
  | succ k ih =>
    intro i w d hw
    rw [show k + 1 + 41 + d = (k + 41 + d) + 1 by omega, loopN_succ,
      show k + 41 + d = (k + 1 + d) + 40 by omega,
      mss_body p hP st hB hK w off i (by rw [hw]; exact hb) (by rw [hw]; exact hb64) (k + 1 + d)]
    cases hstep : mssStep w.b off (i, w.sg.has_mss, w.sg.mss) with
    | none =>
      simp only [mssIter, hstep]
    | some s' =>
      simp only []
      rw [show k + 1 + d + 40 = k + 41 + d by omega,
        ih s'.1 { w with sg := { w.sg with has_mss := s'.2.1, mss := s'.2.2 } } d hw]
      simp only [mssIter, hstep]

theorem execS_loop (p : Prog) (st : St) (env : Env) (n k : Nat) (body : List Stmt) :
    execS (n + 1) p st env (.loop k body) = loopN n p st env k body := by
  simp only [execS]

/-- `parse_mss`: the MSS option among the options of the segment at `buf[20, …)`. -/
def parseMssW (w : TW) (off : UInt16) : TW :=
  { w with sg := { w.sg with
      has_mss := (mssIter w.b off 40 (20, false, 0)).2.1,
      mss := (mssIter w.b off 40 (20, false, 0)).2.2 } }

theorem parse_mss_tw (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (off : UInt16) (hb : 20 + off.toNat ≤ w.b.size) (hb64 : w.b.size < 65536) (d : Nat) :
    Sem.call (d + 100) p (tcpSt st w) "parse_mss" [u16 off] = .ok none (tcpSt st (parseMssW w off)) := by
  have hl := mss_loop p hP st hB hK off w.b.size hb hb64 40 20
    { w with sg := { w.sg with has_mss := false, mss := 0 } } (d + 12) rfl
  rw [show 40 + 41 + (d + 12) = d + 93 by omega] at hl
  simp only [mssBody, parse_mss] at hl
  simp only [Sem.call, hP.parse_mss, parse_mss, List.map, List.zip, List.zipWith]
  tcp_sym_b [hP.sSeg, hB, hK, execS_loop, hl]
  try rfl

/-! ## `tcp_input` -/

theorem x_parse_mss (p : Prog) (hP : TcpAll p) (st : St) (hB : TcpBase st) (hK : TcpConsts st) (w : TW)
    (env : Env) (e : Expr) (off : UInt16) (he : evalE p (tcpSt st w) env e = some (u16 off))
    (hb : 20 + off.toNat ≤ w.b.size) (hb64 : w.b.size < 65536) (d : Nat) :
    execS (d + 101) p (tcpSt st w) env (.call none "parse_mss" [e])
      = .ok (tcpSt st (parseMssW w off)) env .normal :=
  execS_call_val p _ env _ none "parse_mss" [e] hP.parse_mss (by simp [parse_mss]) (by simp [evalArgs, he])
    (parse_mss_tw p hP st hB hK w off hb hb64 d)

theorem x_tcp_segment (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (hi1 : w.r.sent.toNat ≤ w.r.pend_len.toNat) (hi2 : w.r.pend_len.toNat ≤ 256)
    (hT : ∀ w1, segAckW { w with r := { w.r with idle := 0 } } ourIp = .ok w1 → SegTailOk w1) (env : Env)
    (d : Nat) :
    execS (d + 3001) p (tcpSt st w) env (.call none "tcp_segment" []) = .ok (tcpSt st (segW w ourIp)) env .normal :=
  execS_call_val p _ env _ none "tcp_segment" [] hP.tcp_segment (by simp [tcp_segment]) (by simp [evalArgs])
    (tcp_segment_tw p hP hR st hB hK ourIp hip w hw hi1 hi2 hT d)

/-- The data offset of the segment at `buf[20, …)`. -/
def tcpDoff (b : ByteArray) : UInt16 := (Bytes.get b 32 >>> 4).toUInt16 * 4

/-- The segment record `tcp_input` fills in (the MSS option apart). -/
def tcpParse (w : TW) (src : UInt32) (n : UInt16) : TW :=
  { w with sg :=
      { w.sg with
        src := src, sport := Bytes.get16 w.b 20, dport := Bytes.get16 w.b 22, seq := Bytes.get32 w.b 24,
        ack := Bytes.get32 w.b 28, flags := Bytes.get w.b 33 &&& 63, doff := 20 + tcpDoff w.b,
        dlen := n - tcpDoff w.b } }

/-- `tcp_input`: the segment at `buf[20, 20+n)` is checked, parsed and handed to `tcp_segment`. -/
def tcpInputW (w : TW) (ourIp src dst : UInt32) (n : UInt16) : TW :=
  if n < 20 then dropW w "short-tcp"
  else if tcpDoff w.b < 20 || n < tcpDoff w.b then dropW w "bad-tcp-header"
  else if !Spec.Checksum.verifies (Spec.Checksum.sum w.b 20 n.toNat (Spec.Checksum.pseudo src dst 6 n.toNat)) then
    dropW w "bad-tcp-checksum"
  else segW (parseMssW (tcpParse w src n) (tcpDoff w.b)) ourIp

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem tcp_input_tw (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (hw : TWok w) (src dst : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ w.b.size)
    (hi1 : w.r.sent.toNat ≤ w.r.pend_len.toNat) (hi2 : w.r.pend_len.toNat ≤ 256)
    (hT : 20 ≤ n.toNat → 20 ≤ (tcpDoff w.b).toNat → (tcpDoff w.b).toNat ≤ n.toNat →
      ∀ w1, segAckW { (parseMssW (tcpParse w src n) (tcpDoff w.b)) with
        r := { (parseMssW (tcpParse w src n) (tcpDoff w.b)).r with idle := 0 } } ourIp = .ok w1 → SegTailOk w1)
    (d : Nat) :
    Sem.call (d + n.toNat + 3100) p (tcpSt st w) "tcp_input" [u32 src, u32 dst, u16 n]
      = .ok none (tcpSt st (tcpInputW w ourIp src dst n)) := by
  have hb64 := hw.b64
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  simp only [Sem.call, hP.tcp_input, tcp_input, List.map, List.zip, List.zipWith]
  unfold tcpInputW
  by_cases h1p : n < 20
  · rw [if_pos h1p]
    tcp_sym_b [hP.sTcb, hP.sSeg, hB, hK, hR, h1p]
    try (simp only [dropW])
  · rw [if_neg h1p]
    have hn20 : 20 ≤ n.toNat := by
      have := mt UInt16.lt_iff_toNat_lt.mpr h1p
      have t : (20 : UInt16).toNat = 20 := rfl
      rw [t] at this; omega
    obtain ⟨off, hoff⟩ : ∃ x : UInt16, x = tcpDoff w.b := ⟨_, rfl⟩
    rw [← hoff]
    have e_off : evalE p (tcpSt st w) [("src", u32 src), ("dst", u32 dst), ("n", u16 n)]
        (.bin .mul (.cast .w16 (.bin .shr (.index (.var "buf") (.lit 32 (some .w16))) (.lit 4 (some .w8))))
          (.lit 4 (some .w16))) = some (u16 off) := by
      have hi : evalE p (tcpSt st w) [("src", u32 src), ("dst", u32 dst), ("n", u16 n)] (.index (.var "buf") (.lit 32 (some .w16)))
          = some (u8 (Bytes.get w.b 32)) := by
        have := evalE_index_arr p (tcpSt st w) [("src", u32 src), ("dst", u32 dst), ("n", u16 n)] "buf" w.b (.lit 32 (some .w16)) (UInt16.ofNat 32)
          (by simp [lookup, List.lookup, lookup_tcpSt_buf st hB w]) (evalE_lit16 ..) (by rw [ht 32 (by omega)]; omega)
        rw [ht 32 (by omega)] at this
        exact this
      simp only [evalE_bin, evalE_cast, hi, evalE_lit8, evalE_lit16, Sem.binop, mask8_shr4, mask16_u8, mask16_mul,
        hoff, tcpDoff]
      rfl
    by_cases h2p : (decide (off < 20) || decide (n < off)) = true
    · rw [if_pos h2p]
      tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, h1p, e_off, h2p]
      try (simp only [dropW])
    · rw [if_neg h2p]
      have h2 : (decide (off < 20) || decide (n < off)) = false := by simpa using h2p
      have hoffn : off.toNat ≤ n.toNat := by
        have := (Bool.or_eq_false_iff.mp h2).2
        have := mt UInt16.lt_iff_toNat_lt.mpr (of_decide_eq_false this)
        omega
      obtain ⟨P, hPd⟩ : ∃ x : UInt16, x = Spec.Checksum.pseudo src dst 6 n.toNat := ⟨_, rfl⟩
      obtain ⟨S, hSd⟩ : ∃ x : UInt16, x = Spec.Checksum.sum w.b 20 n.toNat P := ⟨_, rfl⟩
      rw [← hPd, ← hSd]
      have f_p : ∀ m, execS (m + 41) p (tcpSt st w) (("p", u16 0) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)])
          (.call (some (.var "p")) "pseudo" [.var "src", .var "dst", .lit 6 (some .w8), .var "n"])
          = .ok (tcpSt st w) (("p", u16 P) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)]) .normal := by
        intro m
        rw [execS_pseudo p hP.add16 hP.pseudo _ _ _ _ _ _ _ src dst (UInt8.ofNat 6) n m (by tcp_sym_b [])
          (by tcp_sym_b []) (evalE_lit8 ..) (by tcp_sym_b [])]
        tcp_sym_b [hPd]
      have f_s : execS (d + n.toNat + 3091) p (tcpSt st w) (("s", u16 0) :: ("p", u16 P) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)])
          (.call (some (.var "s")) "csum" [.lit 20 (some .w16), .var "n", .var "p"])
          = .ok (tcpSt st w) (("s", u16 S) :: ("p", u16 P) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)]) .normal := by
        rw [execS_csum p hP.csum hP.get16 hP.add16 _ _ w.b (lookup_tcpSt_buf st hB w) _ _ _ _ (UInt16.ofNat 20) n P
          (by rw [ht 20 (by omega)]; omega) (by omega) (evalE_lit16 ..) (by tcp_sym_b []) (by tcp_sym_b []) _
          (d + n.toNat + 3030 - n.toNat / 2) (by omega)]
        tcp_sym_b [hSd, ht 20 (by omega)]
        rfl
      have f_ok : ∀ m, execS (m + 7) p (tcpSt st w) (("ok", .bool false) :: ("s", u16 S) :: ("p", u16 P) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)])
          (.call (some (.var "ok")) "verifies" [.var "s"])
          = .ok (tcpSt st w) (("ok", .bool (Spec.Checksum.verifies S)) :: ("s", u16 S) :: ("p", u16 P) :: [("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)])
              .normal := by
        intro m
        rw [execS_verifies p hP.verifies _ _ _ _ S m (by tcp_sym_b [])]
        tcp_sym_b []
      rcases Bool.eq_false_or_eq_true (Spec.Checksum.verifies S) with h3 | h3
      · rw [if_neg (by rw [h3]; simp)]
        have hsz : ∀ k : Nat, k + 3 < 40 → k + 3 < w.b.size := by intro k hk; omega
        have g16 : ∀ (k : Nat) (f : String) (sg' : RawSeg) (m : Nat), k + 1 < 40 →
            execS (m + 7) p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)]
              (.call (some (.field (.var "sg") f)) "get16" [.lit k (some .w16)])
            = storeResult p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] (some (.field (.var "sg") f))
                (some (u16 (Bytes.get16 w.b k))) := by
          intro k f sg' m hk
          have := execS_get16 p hP.get16 (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] w.b
            (lookup_tcpSt_buf st hB { w with sg := sg' }) (some (.field (.var "sg") f)) (.lit k (some .w16))
            (UInt16.ofNat k) m (by rw [ht k (by omega)]; omega) (by rw [ht k (by omega)]; omega) (evalE_lit16 ..)
          rw [ht k (by omega)] at this
          exact this
        have g32 : ∀ (k : Nat) (f : String) (sg' : RawSeg) (m : Nat), k + 3 < 40 →
            execS (m + 21) p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)]
              (.call (some (.field (.var "sg") f)) "get32" [.lit k (some .w16)])
            = storeResult p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] (some (.field (.var "sg") f))
                (some (u32 (Bytes.get32 w.b k))) := by
          intro k f sg' m hk
          have := execS_get32 p hP.get32 hP.get16 (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] w.b
            (lookup_tcpSt_buf st hB { w with sg := sg' }) (some (.field (.var "sg") f)) (.lit k (some .w16))
            (UInt16.ofNat k) m (by rw [ht k (by omega)]; omega) (by rw [ht k (by omega)]; omega) (evalE_lit16 ..)
          rw [ht k (by omega)] at this
          exact this
        have c20 := fun sg' m => g16 20 "sport" sg' m (by omega)
        have c22 := fun sg' m => g16 22 "dport" sg' m (by omega)
        have c24 := fun sg' m => g32 24 "seq" sg' m (by omega)
        have c28 := fun sg' m => g32 28 "ack" sg' m (by omega)
        have e33 : ∀ sg' : RawSeg, evalE p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)]
            (.bin .band (.index (.var "buf") (.lit 33 (some .w16))) (.lit 63 (some .w8)))
            = some (u8 (Bytes.get w.b 33 &&& 63)) := by
          intro sg'
          have hi := evalE_index_arr p (tcpSt st { w with sg := sg' }) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] "buf" w.b (.lit 33 (some .w16))
            (UInt16.ofNat 33) (by simp [lookup, List.lookup, lookup_tcpSt_buf st hB { w with sg := sg' }])
            (evalE_lit16 ..) (by rw [ht 33 (by omega)]; omega)
          rw [ht 33 (by omega)] at hi
          simp only [evalE_bin, hi, evalE_lit8, Sem.binop, mask8_and]
          rfl
        rw [← hoff] at hT
        have hoff20 : 20 ≤ off.toNat := by
          have := (Bool.or_eq_false_iff.mp h2).1
          have := mt UInt16.lt_iff_toNat_lt.mpr (of_decide_eq_false this)
          have t : (20 : UInt16).toNat = 20 := rfl
          rw [t] at this; omega
        have hT := hT hn20 hoff20 hoffn
        have hwp : TWok (tcpParse w src n) := ⟨hw.b44, hw.b64, hw.pd⟩
        have fpm := x_parse_mss p hP st hB hK (tcpParse w src n) [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] (.var "off") off (by tcp_sym_b [])
          (by show 20 + off.toNat ≤ w.b.size; omega) hb64 (d + n.toNat + 2978)
        have fseg := x_tcp_segment p hP hR st hB hK ourIp hip (parseMssW (tcpParse w src n) off)
          ⟨hw.b44, hw.b64, hw.pd⟩ hi1 hi2 hT [("ok", Val.bool true), ("s", u16 S), ("p", u16 P), ("off", u16 off), ("src", u32 src), ("dst", u32 dst), ("n", u16 n)] (d + n.toNat + 77)
        rw [show d + n.toNat + 2978 + 101 = d + n.toNat + 3079 by omega] at fpm
        rw [show d + n.toNat + 77 + 3001 = d + n.toNat + 3078 by omega] at fseg
        simp only [tcpParse, ← hoff] at fpm fseg ⊢
        tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, h1p, e_off, h2, f_p, f_s, f_ok, h3, c20, c22, c24, c28, e33, fpm, fseg]
      · rw [if_pos (by rw [h3]; rfl)]
        tcp_sym_b [hP.toTcpProg, hP, hP.sTcb, hP.sSeg, hB, hK, hR, h1p, e_off, h2, f_p, f_s, f_ok, h3]
        try (simp only [dropW])


/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.tcp_input_tw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tcp_input_tw

end Ember.Proof.Refine
