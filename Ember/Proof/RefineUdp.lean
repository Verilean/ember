import Ember.Proof.RefineIcmp

/-!
# Ember.Proof.RefineUdp — the UDP echo (plan M5.5)

`udp_input` against `Spec.Udp.parse` and the echo service of
`Spec.udpInput`: the same four checks with the same drop reasons — too
short, bad length, a non-zero checksum that does not verify, a port other
than 7 — and for port 7 the datagram `Spec.Udp.emit` builds (ports
swapped, checksum recomputed over the pseudo-header, a computed 0 sent as
0xFFFF), in the Spec's IPv4 packet.

The reply is built in place: the code overwrites three header fields of
the received datagram, and `udp_reply_bytes` shows that the result is
byte for byte what `emit` assembles from parts.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## The bytes of a 16-bit field -/

theorem get16_hi (b : ByteArray) (i : Nat) : (Bytes.get16 b i >>> 8).toUInt8 = Bytes.get b i := by
  apply UInt8.toNat_inj.mp
  have h1 := (Bytes.get b i).toNat_lt
  have h2 := (Bytes.get b (i + 1)).toNat_lt
  have t8 : (8 : UInt16).toNat = 8 := rfl
  simp only [Bytes.get16, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_or, UInt16.toNat_shiftLeft,
    UInt8.toNat_toUInt16, t8, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := (Bytes.get b i).toNat * 2 ^ 8) (by omega), Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem get16_lo (b : ByteArray) (i : Nat) : (Bytes.get16 b i).toUInt8 = Bytes.get b (i + 1) := by
  apply UInt8.toNat_inj.mp
  have h1 := (Bytes.get b i).toNat_lt
  have h2 := (Bytes.get b (i + 1)).toNat_lt
  have t8 : (8 : UInt16).toNat = 8 := rfl
  simp only [Bytes.get16, UInt16.toNat_toUInt8, UInt16.toNat_or, UInt16.toNat_shiftLeft,
    UInt8.toNat_toUInt16, t8, Nat.shiftLeft_eq, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := (Bytes.get b i).toNat * 2 ^ 8) (by omega), Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

/-! ## The UDP reply -/

/-- The packet buffer after `udp_input` has swapped the ports and cleared
the checksum field. -/
def udpSwap (b : ByteArray) : ByteArray :=
  Bytes.set16 (Bytes.set16 (Bytes.set16 b 20 (Bytes.get16 b 22)) 22 (Bytes.get16 b 20)) 26 0

@[simp] theorem size_udpSwap (b : ByteArray) : (udpSwap b).size = b.size := by simp [udpSwap]

/-- The reply built in place is the datagram `Spec.Udp.emit` builds:
ports swapped, the same length, the data, the checksum recomputed. -/
theorem udp_reply_bytes (b : ByteArray) (src dst : UInt32) (n : Nat) (ul : UInt16)
    (hul : Bytes.get16 b 24 = ul) (h8 : 8 ≤ ul.toNat) (hn' : ul.toNat ≤ n) (hn : 20 + n ≤ b.size) :
    let c := ~~~ Spec.Checksum.sum (udpSwap b) 20 ul.toNat (Spec.Checksum.pseudo src dst 17 ul.toNat)
    (Bytes.set16 (udpSwap b) 26 (if c == 0 then 0xFFFF else c)).extract 20 (20 + ul.toNat)
      = Spec.Udp.emit src dst (Bytes.get16 b 22) (Bytes.get16 b 20)
          (Bytes.slice (b.extract 20 (20 + n)) 8 (ul.toNat - 8)) := by
  intro c
  have hPs : (b.extract 20 (20 + n)).size = n := by rw [ByteArray.size_extract]; omega
  have hds : (Bytes.slice (b.extract 20 (20 + n)) 8 (ul.toNat - 8)).size = ul.toNat - 8 := by
    rw [Bytes.slice, ByteArray.size_extract, hPs]; omega
  generalize hdata : Bytes.slice (b.extract 20 (20 + n)) 8 (ul.toNat - 8) = data at hds
  have hdget : ∀ k, k < ul.toNat - 8 → Bytes.get data k = Bytes.get b (28 + k) := by
    intro k hk
    rw [← hdata, Bytes.slice, get_extract _ 8 _ k (by omega) (by rw [hPs]; omega),
      get_extract b 20 _ (8 + k) (by omega) hn]
    congr 1; omega
  have hlen : 8 + data.size = ul.toNat := by omega
  let hbL : List UInt8 := Bytes.be16 (Bytes.get16 b 22) ++ Bytes.be16 (Bytes.get16 b 20) ++
    Bytes.be16 (UInt16.ofNat ul.toNat) ++ [0, 0]
  have hL : (Bytes.ofList hbL).size = 8 := by simp [hbL, Bytes.be16]
  have hofNat : UInt16.ofNat ul.toNat = ul := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt ul.toNat_lt
  -- the reply before its checksum, byte by byte
  have key : ∀ j, j < ul.toNat → Bytes.get (udpSwap b) (20 + j) = Bytes.get (Bytes.ofList hbL ++ data) j := by
    intro j hj
    rw [Bytes.get_append, hL]
    by_cases h8' : j < 8
    · rw [if_pos h8', Bytes.get_ofList]
      have g20 : 20 < b.size := by omega
      have g21 : 20 + 1 < b.size := by omega
      have g22 : 22 < b.size := by omega
      have g23 : 22 + 1 < b.size := by omega
      have g26 : 26 < b.size := by omega
      have g27 : 26 + 1 < b.size := by omega
      have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [udpSwap, Bytes.get_set16, hbL, Bytes.be16, g20, g21, g22, g23, g26, g27, hofNat, ← hul, get16_hi,
          get16_lo]
    · rw [if_neg h8', hdget (j - 8) (by omega)]
      simp only [udpSwap]
      rw [Bytes.get_set16_ne (by omega), Bytes.get_set16_ne (by omega), Bytes.get_set16_ne (by omega)]
      congr 1; omega
  have hsum : ∀ ini, Spec.Checksum.sum (udpSwap b) 20 ul.toNat ini
      = Spec.Checksum.sum (Bytes.ofList hbL ++ data) 0 ul.toNat ini := by
    intro ini
    apply Spec.Checksum.sum_congr
    intro i hi
    rw [Nat.zero_add, key i hi]
  have hemit : Spec.Udp.emit src dst (Bytes.get16 b 22) (Bytes.get16 b 20) data
      = Bytes.set16 (Bytes.ofList hbL ++ data) 6 (if c == 0 then 0xFFFF else c) := by
    show Bytes.set16 (Bytes.ofList (Bytes.be16 (Bytes.get16 b 22) ++ Bytes.be16 (Bytes.get16 b 20) ++
        Bytes.be16 (UInt16.ofNat (8 + data.size)) ++ [0, 0]) ++ data) 6 _ = _
    simp only [Spec.Checksum.checksum, hlen, Spec.Ipv4.protoUdp, c, hsum, hbL]
  rw [hemit]
  generalize (if c == 0 then (0xFFFF : UInt16) else c) = v
  have hdd : (Bytes.ofList hbL ++ data).size = ul.toNat := by rw [ByteArray.size_append, hL]; omega
  apply Bytes.ext_get
  · rw [ByteArray.size_extract, Bytes.size_set16, size_udpSwap, Bytes.size_set16, hdd]; omega
  · intro j hj
    have hj' : j < ul.toNat := by
      rw [ByteArray.size_extract, Bytes.size_set16, size_udpSwap] at hj; omega
    rw [get_extract _ 20 _ j (by omega) (by rw [Bytes.size_set16, size_udpSwap]; omega), Bytes.get_set16,
      Bytes.get_set16, size_udpSwap, hdd]
    by_cases h7 : j = 7
    · subst h7
      have : 26 + 1 < b.size := by omega
      have : 6 + 1 < ul.toNat := by omega
      simp [*]
    · by_cases h6 : j = 6
      · subst h6
        have : 26 < b.size := by omega
        have : 6 < ul.toNat := by omega
        simp [*]
      · have e1 : ¬ (26 + 1 = 20 + j) := by omega
        have e2 : ¬ (26 = 20 + j) := by omega
        have e3 : ¬ (6 + 1 = j) := by omega
        have e4 : ¬ (6 = j) := by omega
        simp only [e1, e2, e3, e4, false_and, if_false]
        exact key j hj'

/-- `Spec.Udp.parse`, case by case. -/
theorem parse_eq (src dst : UInt32) (P : ByteArray) :
    Spec.Udp.parse src dst P =
      if P.size < 8 then .error "short-udp"
      else if (Bytes.get16 P 4).toNat < 8 || (Bytes.get16 P 4).toNat > P.size then .error "bad-udp-length"
      else if Bytes.get16 P 6 != 0 && !Spec.Checksum.verifies (Spec.Checksum.sum P 0 (Bytes.get16 P 4).toNat
          (Spec.Checksum.pseudo src dst 17 (Bytes.get16 P 4).toNat)) then .error "bad-udp-checksum"
      else .ok { sport := Bytes.get16 P 0, dport := Bytes.get16 P 2,
                 data := Bytes.slice P 8 ((Bytes.get16 P 4).toNat - 8) } := by
  unfold Spec.Udp.parse
  simp [Spec.Ipv4.protoUdp]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try simp_all) <;> (try rfl)

/-! ## `udp_input` -/

def udp_input : Fn := checked_fn% Net.prog, "udp_input"
#guard (Net.prog.check.toOption.bind (·.fn? "udp_input")) == some udp_input

/-- A program with the functions `udp_input` uses and its drop reasons. -/
structure UdpProg (p : Prog) : Prop extends IcmpProg p where
  pseudo : p.fn? "pseudo" = some pseudo
  udp_input : p.fn? "udp_input" = some udp_input
  r14 : p.dropReasons[14]? = some "short-udp"
  r15 : p.dropReasons[15]? = some "bad-udp-length"
  r16 : p.dropReasons[16]? = some "bad-udp-checksum"
  r17 : p.dropReasons[17]? = some "udp-port-closed"

/-- The constants `udp_input` and `ip_send` read. -/
structure UdpConsts (st : St) (ourIp : UInt32) : Prop where
  ourIp : st.globals.lookup "OUR_IP" = some (u32 ourIp)
  ttl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault)
  echo : st.globals.lookup "ECHO_PORT" = some (u16 7)
  d14 : st.globals.lookup "D_SHORT_UDP" = some (u8 14)
  d15 : st.globals.lookup "D_BAD_UDP_LENGTH" = some (u8 15)
  d16 : st.globals.lookup "D_BAD_UDP_CHECKSUM" = some (u8 16)
  d17 : st.globals.lookup "D_UDP_PORT_CLOSED" = some (u8 17)

theorem toUInt64_ne_iff (x y : UInt16) : (x.toUInt64 != y.toUInt64) = (x != y) := by
  simp only [bne, toUInt64_eq_iff]

theorem execS_pseudo (p : Prog) (h1 : p.fn? "add16" = some add16) (h2 : p.fn? "pseudo" = some pseudo)
    (st : St) (env : Env) (dst' : Option Expr) (e1 e2 e3 e4 : Expr) (src dst : UInt32) (proto : UInt8)
    (len : UInt16) (n : Nat) (he1 : evalE p st env e1 = some (u32 src)) (he2 : evalE p st env e2 = some (u32 dst))
    (he3 : evalE p st env e3 = some (u8 proto)) (he4 : evalE p st env e4 = some (u16 len)) :
    execS (n + 41) p st env (.call dst' "pseudo" [e1, e2, e3, e4]) =
      storeResult p st env dst' (some (u16 (Spec.Checksum.pseudo src dst proto len.toNat))) :=
  execS_call_val p st env (n + 40) dst' "pseudo" [e1, e2, e3, e4] h2 (by simp [pseudo])
    (by simp [evalArgs, he1, he2, he3, he4]) (pseudo_refines p h1 h2 st src dst proto len n)

/-- An `if` whose condition is known: only for a state and variables at
hand (unlike `execS_ite`, which also unfolds under binders). -/
theorem execS_ite_true (p : Prog) (st : St) (env : Env) (n : Nat) (c : Expr) (t e : List Stmt)
    (h : evalE p st env c = some (.bool true)) : execS (n + 1) p st env (.ite c t e) = execB n p st env t := by
  rw [execS_ite, h]; rfl

theorem execS_ite_false (p : Prog) (st : St) (env : Env) (n : Nat) (c : Expr) (t e : List Stmt)
    (h : evalE p st env c = some (.bool false)) : execS (n + 1) p st env (.ite c t e) = execB n p st env e := by
  rw [execS_ite, h]; rfl

/-- The checksum test of `udp_input`. -/
def udpCsIte : Stmt :=
  match udp_input.body with
  | [_, _, _, _, _, _, .at _ s, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => s
  | _ => .brk

/-- The last `if` of `udp_input`: the checksum field is filled in. -/
def udpSendIte : Stmt :=
  match udp_input.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ s, _] => s
  | _ => .brk

/-- **`udp_input` is the Spec's UDP handling** (`Spec.Udp.parse`, then
the echo service of `Spec.udpInput`): for the datagram of `n` bytes at
`buf[20, 20+n)` it writes the drop line the Spec gives — too short, bad
length, bad checksum, port closed — or, for port 7, transmits
`Spec.Udp.emit` with the ports swapped in the Spec's IPv4 packet. -/
theorem udp_input_refines (p : Prog) (hP : UdpProg p) (st : St) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hK : UdpConsts st ourIp) (src dst : UInt32) (n : UInt16)
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat) :
    ∃ st', Sem.call (d + n.toNat + 400) p st "udp_input" [u32 src, u32 dst, u16 n] = .ok none st' ∧
      match Spec.Udp.parse src dst (b.extract 20 (20 + n.toNat)) with
      | .error r => st' = dropSt st r
      | .ok dg =>
        if dg.dport = 7 then
          ∃ B, B.size = b.size ∧ st' = txOut (stIp st B (id + 1)) (st.world.frame ++ Spec.Slip.encode
            (Spec.Ipv4.packet 17 id ourIp src (Spec.Udp.emit ourIp src dg.dport dg.sport dg.data)))
        else st' = dropSt st "udp-port-closed" := by
  have hmsz : (b.extract 20 (20 + n.toNat)).size = n.toNat := by rw [ByteArray.size_extract]; omega
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  rw [parse_eq, hmsz]
  let env0 : Env := [("src", u32 src), ("dst", u32 dst), ("n", u16 n)]
  have evar : ∀ (S : St) (env : Env) (x : String) (v : Val), env.lookup x = some v →
      evalE p S env (.var x) = some v := by
    intro S env x v h; simp [evalE, lookup, h]
  have eglob : ∀ (S : St) (env : Env) (x : String) (v : Val), S.globals.lookup x = some v → env.lookup x = none →
      evalE p S env (.var x) = some v := by
    intro S env x v h h'; simp [evalE, lookup, h, h']
  have econd1 : evalE p st env0 (.bin .lt (.var "n") (.lit 8 (some .w16)))
      = some (.bool (decide (n < UInt16.ofNat 8))) := by
    simp only [evalE_bin, evalE_lit16, evar st env0 "n" (u16 n) (by simp [env0, List.lookup]), Sem.binop,
      toUInt64_lt_iff]
  have hlt8 : ∀ x : UInt16, (x < UInt16.ofNat 8) ↔ x.toNat < 8 := by
    intro x; rw [UInt16.lt_iff_toNat_lt, ht 8 (by omega)]
  simp only [env0] at econd1
  simp only [Sem.call, hP.udp_input, udp_input, execB_succ, execL_cons, execS_at, List.map, List.zip,
    List.zipWith]
  by_cases h8 : n < UInt16.ofNat 8
  · have fd := fun m => execS_drop p st env0 m (.var "D_SHORT_UDP") 14 "short-udp"
      (eglob st env0 _ _ hK.d14 (by simp [env0, List.lookup])) hP.r14
    simp only [env0] at fd
    have c0 := econd1; simp only [h8, decide_true] at c0
    simp only [execS_ite_true, c0, execB_succ, execL_cons, execS_at, fd, execS_ret_none]
    exact ⟨_, rfl, by simp [(hlt8 n).mp h8]⟩
  · have hn8 : 8 ≤ n.toNat := by
      have := mt (hlt8 n).mpr h8; omega
    have hn8' : ¬ n.toNat < 8 := by omega
    have c0 := econd1; simp only [h8, decide_false] at c0
    have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
    have hzb : zeroOf p Ty.bool = .bool false := rfl
    rw [get16_extract b 20 _ 4 (by omega) hn, get16_extract b 20 _ 6 (by omega) hn,
      get16_extract b 20 _ 0 (by omega) hn, get16_extract b 20 _ 2 (by omega) hn]
    simp only [Nat.reduceAdd]
    let ul := Bytes.get16 b 24
    let cs := Bytes.get16 b 26
    let sp := Bytes.get16 b 20
    let dp := Bytes.get16 b 22
    let envU : Env := ("ul", u16 ul) :: env0
    let envC : Env := ("cs", u16 cs) :: envU
    have f_ul : ∀ m, execS (m + 7) p st (("ul", u16 0) :: env0) (.call (some (.var "ul")) "get16"
        [.lit 24 (some .w16)]) = .ok st envU .normal := by
      intro m
      rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 24) m (by rw [ht 24 (by omega)]; omega)
        (by rw [ht 24 (by omega)]; omega) (evalE_lit16 ..)]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 24 (by omega),
        envU, ul]
    have econd_len : evalE p st envU (.bin .lor (.bin .lt (.var "ul") (.lit 8 (some .w16)))
        (.bin .gt (.var "ul") (.var "n"))) = some (.bool (decide (ul < UInt16.ofNat 8) || decide (n < ul))) := by
      simp only [evalE_bin, evalE_lit16, evar st envU "ul" (u16 ul) (by simp [envU, List.lookup]),
        evar st envU "n" (u16 n) (by simp [envU, env0, List.lookup]), Sem.binop, toUInt64_lt_iff]
    have fd15 := fun m => execS_drop p st envU m (.var "D_BAD_UDP_LENGTH") 15 "bad-udp-length"
      (eglob st envU _ _ hK.d15 (by simp [envU, env0, List.lookup])) hP.r15
    simp only [envU, env0, ul] at f_ul econd_len fd15
    have hlenU : ((Bytes.get16 b 24).toNat < 8 ∨ (Bytes.get16 b 24).toNat > n.toNat)
        ↔ (decide (Bytes.get16 b 24 < UInt16.ofNat 8) || decide (n < Bytes.get16 b 24)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, hlt8, UInt16.lt_iff_toNat_lt]
    rcases Bool.eq_false_or_eq_true (decide (Bytes.get16 b 24 < UInt16.ofNat 8) || decide (n < Bytes.get16 b 24))
      with hbad | hbad
    · -- bad length
      have c1 := econd_len; conv at c1 => rhs; rw [hbad]
      simp only [execS_ite_true, execS_ite_false, c0, execB_succ, execL_cons, execL_nil,
        execS_at, execS_decl_none, hz, f_ul, c1, fd15, execS_ret_none, List.length_cons,
        List.length_nil, Nat.sub_self, List.drop_zero]
      refine ⟨_, rfl, ?_⟩
      have := hlenU.mpr hbad
      simp [hn8', this]
    · -- the length is good
      have hlenOk : ¬ ((Bytes.get16 b 24).toNat < 8 ∨ (Bytes.get16 b 24).toNat > n.toNat) := by
        rw [hlenU, hbad]; simp
      have hu8 : 8 ≤ ul.toNat := by
        have : ¬ (Bytes.get16 b 24).toNat < 8 := fun h => hlenOk (Or.inl h)
        simp only [ul]; omega
      have hun : ul.toNat ≤ n.toNat := by
        have : ¬ (Bytes.get16 b 24).toNat > n.toNat := fun h => hlenOk (Or.inr h)
        simp only [ul]; omega
      have c1 := econd_len; conv at c1 => rhs; rw [hbad]
      have f_cs : ∀ m, execS (m + 7) p st (("cs", u16 0) :: envU) (.call (some (.var "cs")) "get16"
          [.lit 26 (some .w16)]) = .ok st envC .normal := by
        intro m
        rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 26) m (by rw [ht 26 (by omega)]; omega)
          (by rw [ht 26 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 26 (by omega),
          envC, cs]
      -- the checksum test
      let P1 := Spec.Checksum.pseudo src dst (UInt8.ofNat 17) ul.toNat
      let S1 := Spec.Checksum.sum b 20 ul.toNat P1
      let V := Spec.Checksum.verifies S1
      have econd_cs : evalE p st envC (.bin .ne (.var "cs") (.lit 0 (some .w16)))
          = some (.bool (cs != UInt16.ofNat 0)) := by
        simp only [evalE_bin, evalE_lit16, evar st envC "cs" (u16 cs) (by simp [envC, List.lookup]), Sem.binop,
          toUInt64_ne_iff]
      let envP : Env := ("p", u16 P1) :: envC
      let envS : Env := ("s", u16 S1) :: envP
      let envK : Env := ("ok", .bool V) :: envS
      have g_p : ∀ m, execS (m + 41) p st (("p", u16 0) :: envC) (.call (some (.var "p")) "pseudo"
          [.var "src", .var "dst", .lit 17 (some .w8), .var "ul"]) = .ok st envP .normal := by
        intro m
        rw [execS_pseudo p hP.add16 hP.pseudo st _ _ _ _ _ _ src dst (UInt8.ofNat 17) ul m
          (evar _ _ "src" _ (by simp [envC, envU, env0, List.lookup]))
          (evar _ _ "dst" _ (by simp [envC, envU, env0, List.lookup])) (evalE_lit8 ..)
          (evar _ _ "ul" _ (by simp [envC, envU, List.lookup]))]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, envP, P1]
      have g_s : execS (d + n.toNat + 384) p st (("s", u16 0) :: envP) (.call (some (.var "s")) "csum"
          [.lit 20 (some .w16), .var "ul", .var "p"]) = .ok st envS .normal := by
        rw [execS_csum p hP.csum hP.get16 hP.add16 st _ b hb _ _ _ _ (UInt16.ofNat 20) ul P1
          (by rw [ht 20 (by omega)]; omega) (by omega) (evalE_lit16 ..)
          (evar _ _ "ul" _ (by simp [envP, envC, envU, List.lookup])) (evar _ _ "p" _ (by simp [envP, List.lookup]))
          _ (d + (n.toNat - ul.toNat / 2) + 323) (by omega)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 20 (by omega),
          envS, S1]
      have g_ok : ∀ m, execS (m + 7) p st (("ok", .bool false) :: envS)
          (.call (some (.var "ok")) "verifies" [.var "s"]) = .ok st envK .normal := by
        intro m
        rw [execS_verifies p hP.verifies st _ _ _ S1 m (evar _ _ "s" _ (by simp [envS, List.lookup]))]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, envK, V]
      have g_cond : evalE p st envK (.un .lnot (.var "ok")) = some (.bool (!V)) := by
        simp only [evalE, lookup, List.lookup, beq_self_eq_true, envK]
      have g_drop := fun m => execS_drop p st envK m (.var "D_BAD_UDP_CHECKSUM") 16 "bad-udp-checksum"
        (eglob st envK _ _ hK.d16 (by simp [envK, envS, envP, envC, envU, env0, List.lookup])) hP.r16
      have f6ok : (cs = UInt16.ofNat 0 ∨ V = true) →
          execS (d + n.toNat + 391) p st envC udpCsIte = .ok st envC .normal := by
        intro h
        simp only [udpCsIte, udp_input, execS_ite, econd_cs, Val.toBool]
        by_cases hc0 : cs = UInt16.ofNat 0
        · simp [hc0, execB_succ, execL_nil]
        · have hV : V = true := by rcases h with h | h; exact absurd h hc0; exact h
          have hne : (cs != UInt16.ofNat 0) = true := bne_iff_ne.mpr hc0
          have gc := g_cond; conv at gc => rhs; rw [hV]
          simp only [hne, if_true, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_decl_none, hz, hzb,
            g_p, g_s, g_ok, gc, Val.toBool, Bool.not_true, Bool.false_eq_true, if_false]
          have hd : ∀ k : Nat, k + 1 + 1 + 1 - k = 3 := by intro k; omega
          simp [envK, envS, envP, hd]
      have f6bad : cs ≠ UInt16.ofNat 0 → V = false →
          execS (d + n.toNat + 391) p st envC udpCsIte = .ok (dropSt st "bad-udp-checksum") envC (.ret none) := by
        intro hc0 hV
        have hne : (cs != UInt16.ofNat 0) = true := bne_iff_ne.mpr hc0
        have gc := g_cond; conv at gc => rhs; rw [hV]
        have hd : ∀ k : Nat, k + 1 + 1 + 1 - k = 3 := by intro k; omega
        simp only [udpCsIte, udp_input, execS_ite, econd_cs, Val.toBool, hne, if_true, execB_succ, execL_cons,
          execL_nil, execS_at, execS_decl_none, hz, hzb, g_p, g_s, g_ok, gc, g_drop, execS_ret_none, Bool.not_false]
        simp [envK, envS, envP, hd]
      simp only [udpCsIte, udp_input] at f6ok f6bad
      -- the ports
      let envSp : Env := ("sport", u16 sp) :: envC
      let envDp : Env := ("dport", u16 dp) :: envSp
      have f_sp : ∀ m, execS (m + 7) p st (("sport", u16 0) :: envC) (.call (some (.var "sport")) "get16"
          [.lit 20 (some .w16)]) = .ok st envSp .normal := by
        intro m
        rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 20) m (by rw [ht 20 (by omega)]; omega)
          (by rw [ht 20 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 20 (by omega),
          envSp, sp]
      have f_dp : ∀ m, execS (m + 7) p st (("dport", u16 0) :: envSp) (.call (some (.var "dport")) "get16"
          [.lit 22 (some .w16)]) = .ok st envDp .normal := by
        intro m
        rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 22) m (by rw [ht 22 (by omega)]; omega)
          (by rw [ht 22 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 22 (by omega),
          envDp, dp]
      have econd_port : evalE p st envDp (.bin .ne (.var "dport") (.var "ECHO_PORT"))
          = some (.bool (dp != 7)) := by
        simp only [evalE_bin, evar st envDp "dport" (u16 dp) (by simp [envDp, List.lookup]),
          eglob st envDp "ECHO_PORT" _ hK.echo (by simp [envDp, envSp, envC, envU, env0, List.lookup]),
          Sem.binop, toUInt64_ne_iff]
      have fd17 := fun m => execS_drop p st envDp m (.var "D_UDP_PORT_CLOSED") 17 "udp-port-closed"
        (eglob st envDp _ _ hK.d17 (by simp [envDp, envSp, envC, envU, env0, List.lookup])) hP.r17
      -- the reply
      let b1 := Bytes.set16 b 20 dp
      let b2 := Bytes.set16 b1 22 sp
      let b3 := Bytes.set16 b2 26 (UInt16.ofNat 0)
      let st1 := withBuf st b1
      let st2 := withBuf st1 b2
      let st3 := withBuf st2 b3
      have hb1 : st1.globals.lookup "buf" = some (bufVal b1) := lookup_withBuf st b b1 hb
      have hb2 : st2.globals.lookup "buf" = some (bufVal b2) := lookup_withBuf st1 b1 b2 hb1
      have hb3 : st3.globals.lookup "buf" = some (bufVal b3) := lookup_withBuf st2 b2 b3 hb2
      have sb1 : b1.size = b.size := by simp [b1]
      have sb2 : b2.size = b.size := by simp [b2, sb1]
      have sb3 : b3.size = b.size := by simp [b3, sb2]
      have f_s1 : ∀ m, execS (m + 9) p st envDp (.call none "set16" [.lit 20 (some .w16), .var "dport"])
          = .ok st1 envDp .normal := by
        intro m
        rw [execS_set16 p hP.set16 st envDp b hb _ _ (UInt16.ofNat 20) dp m (by rw [ht 20 (by omega)]; omega)
          (by rw [ht 20 (by omega)]; omega) (evalE_lit16 ..) (evar _ _ "dport" _ (by simp [envDp, List.lookup])),
          ht 20 (by omega)]
      have f_s2 : ∀ m, execS (m + 9) p st1 envDp (.call none "set16" [.lit 22 (some .w16), .var "sport"])
          = .ok st2 envDp .normal := by
        intro m
        rw [execS_set16 p hP.set16 st1 envDp b1 hb1 _ _ (UInt16.ofNat 22) sp m (by rw [ht 22 (by omega)]; omega)
          (by rw [ht 22 (by omega)]; omega) (evalE_lit16 ..)
          (evar _ _ "sport" _ (by simp [envDp, envSp, List.lookup])), ht 22 (by omega)]
      have f_s3 : ∀ m, execS (m + 9) p st2 envDp (.call none "set16" [.lit 26 (some .w16), .lit 0 (some .w16)])
          = .ok st3 envDp .normal := by
        intro m
        rw [execS_set16 p hP.set16 st2 envDp b2 hb2 _ _ (UInt16.ofNat 26) (UInt16.ofNat 0) m
          (by rw [ht 26 (by omega)]; omega) (by rw [ht 26 (by omega)]; omega) (evalE_lit16 ..) (evalE_lit16 ..),
          ht 26 (by omega)]
      have l3 : ∀ x : String, x ≠ "buf" → st3.globals.lookup x = st.globals.lookup x := by
        intro x hx
        simp only [st3, st2, st1, withBuf_eq]
        rw [lookup_setG_ne _ _ _ _ (Ne.symm hx), lookup_setG_ne _ _ _ _ (Ne.symm hx),
          lookup_setG_ne _ _ _ _ (Ne.symm hx)]
      let P2 := Spec.Checksum.pseudo ourIp src (UInt8.ofNat 17) ul.toNat
      let S2 := Spec.Checksum.sum b3 20 ul.toNat P2
      let envP2 : Env := ("p2", u16 P2) :: envDp
      let envS2 : Env := ("s2", u16 S2) :: envP2
      let envCc : Env := ("c", u16 (~~~ S2)) :: envS2
      have f_p2 : ∀ m, execS (m + 41) p st3 (("p2", u16 0) :: envDp) (.call (some (.var "p2")) "pseudo"
          [.var "OUR_IP", .var "src", .lit 17 (some .w8), .var "ul"]) = .ok st3 envP2 .normal := by
        intro m
        rw [execS_pseudo p hP.add16 hP.pseudo st3 _ _ _ _ _ _ ourIp src (UInt8.ofNat 17) ul m
          (eglob _ _ "OUR_IP" _ (by rw [l3 _ (by decide)]; exact hK.ourIp)
            (by simp [envDp, envSp, envC, envU, env0, List.lookup]))
          (evar _ _ "src" _ (by simp [envDp, envSp, envC, envU, env0, List.lookup])) (evalE_lit8 ..)
          (evar _ _ "ul" _ (by simp [envDp, envSp, envC, envU, List.lookup]))]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, envP2, P2]
      have f_sum2 : execS (d + n.toNat + 379) p st3 (("s2", u16 0) :: envP2) (.call (some (.var "s2")) "csum"
          [.lit 20 (some .w16), .var "ul", .var "p2"]) = .ok st3 envS2 .normal := by
        rw [execS_csum p hP.csum hP.get16 hP.add16 st3 _ b3 hb3 _ _ _ _ (UInt16.ofNat 20) ul P2
          (by rw [ht 20 (by omega)]; omega) (by omega) (evalE_lit16 ..)
          (evar _ _ "ul" _ (by simp [envP2, envDp, envSp, envC, envU, List.lookup]))
          (evar _ _ "p2" _ (by simp [envP2, List.lookup])) _ (d + (n.toNat - ul.toNat / 2) + 318) (by omega)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 20 (by omega),
          envS2, S2]
      have e_c : evalE p st3 envS2 (.un .bnot (.var "s2")) = some (u16 (~~~ S2)) := by
        simp only [evalE, lookup, List.lookup, beq_self_eq_true, mask16_not, envS2]
      let v := if (~~~ S2 == UInt16.ofNat 0) then UInt16.ofNat 65535 else ~~~ S2
      let b4 := Bytes.set16 b3 26 v
      let st4 := withBuf st3 b4
      have hb4 : st4.globals.lookup "buf" = some (bufVal b4) := lookup_withBuf st3 b3 b4 hb3
      have f_ite : ∀ m, execS (m + 14) p st3 envCc udpSendIte = .ok st4 envCc .normal := by
        intro m
        have ec0 : evalE p st3 envCc (.bin .eq (.var "c") (.lit 0 (some .w16)))
            = some (.bool (~~~ S2 == UInt16.ofNat 0)) := by
          simp only [evalE_bin, evalE_lit16, evar st3 envCc "c" (u16 (~~~ S2)) (by simp [envCc, List.lookup]),
            Sem.binop, toUInt64_eq_iff]
        have k1 := execS_set16 p hP.set16 st3 envCc b3 hb3 (.lit 26 (some .w16)) (.lit 65535 (some .w16))
          (UInt16.ofNat 26) (UInt16.ofNat 65535) (m + 1) (by rw [ht 26 (by omega)]; omega)
          (by rw [ht 26 (by omega)]; omega) (evalE_lit16 ..) (evalE_lit16 ..)
        have k2 := execS_set16 p hP.set16 st3 envCc b3 hb3 (.lit 26 (some .w16)) (.var "c")
          (UInt16.ofNat 26) (~~~ S2) (m + 1) (by rw [ht 26 (by omega)]; omega)
          (by rw [ht 26 (by omega)]; omega) (evalE_lit16 ..) (evar _ _ "c" _ (by simp [envCc, List.lookup]))
        rw [ht 26 (by omega)] at k1 k2
        simp only [udpSendIte, udp_input, execS_ite, ec0, Val.toBool, execB_succ, execL_cons, execL_nil, execS_at]
        cases hc : (~~~ S2 == UInt16.ofNat 0) with
        | true =>
          simp only [if_true, k1, st4, b4, v, hc]
          simp
        | false =>
          simp only [Bool.false_eq_true, if_false, k2, st4, b4, v, hc]
          simp
      simp only [udpSendIte, udp_input] at f_ite
      have l4 : ∀ x : String, x ≠ "buf" → st4.globals.lookup x = st.globals.lookup x := by
        intro x hx
        simp only [st4, withBuf_eq]
        rw [lookup_setG_ne _ _ _ _ (Ne.symm hx), l3 x hx]
      have f_ip : execS (d + n.toNat + 376) p st4 envCc
          (.call none "ip_send" [.lit 17 (some .w8), .var "src", .var "ul"])
          = .ok (txOut (stIp st4 (ipHeader b4 (UInt8.ofNat 17) id ourIp src ul Spec.ttlDefault) (id + 1))
              (st4.world.frame ++ Spec.Slip.encode
                (Spec.Ipv4.packet (UInt8.ofNat 17) id ourIp src (b4.extract 20 (20 + ul.toNat))))) envCc .normal :=
        execS_ip_send p hP.toIpProg st4 envCc b4 id hb4
          (by rw [l4 _ (by decide)]; exact hid) ourIp (by rw [l4 _ (by decide)]; exact hK.ourIp)
          (by rw [l4 _ (by decide)]; exact hK.ttl) _ _ _ _ src ul (evalE_lit8 ..)
          (evar _ _ "src" _ (by simp [envCc, envS2, envP2, envDp, envSp, envC, envU, env0, List.lookup]))
          (evar _ _ "ul" _ (by simp [envCc, envS2, envP2, envDp, envSp, envC, envU, env0, List.lookup]))
          (by simp only [b4, Bytes.size_set16, sb3]; omega) (by simp only [b4, Bytes.size_set16, sb3]; omega) _
          (d + (n.toNat - ul.toNat) + 225) (by omega)
      have hsumP : Spec.Checksum.sum (b.extract 20 (20 + n.toNat)) 0 (Bytes.get16 b 24).toNat
            (Spec.Checksum.pseudo src dst 17 (Bytes.get16 b 24).toNat)
          = Spec.Checksum.sum b 20 (Bytes.get16 b 24).toNat
              (Spec.Checksum.pseudo src dst 17 (Bytes.get16 b 24).toNat) := by
        apply Spec.Checksum.sum_congr
        intro i hi
        rw [Nat.zero_add, get_extract b 20 _ i (by simp only [ul] at hun; omega) hn]
      have hr : b4.extract 20 (20 + ul.toNat)
          = Spec.Udp.emit ourIp src dp sp (Bytes.slice (b.extract 20 (20 + n.toNat)) 8 (ul.toNat - 8)) :=
        udp_reply_bytes b ourIp src n.toNat ul rfl hu8 hun hn
      have hu8' : ¬ (Bytes.get16 b 24).toNat < 8 := by simp only [ul] at hu8; omega
      have hun' : ¬ (Bytes.get16 b 24).toNat > n.toNat := by simp only [ul] at hun; omega
      rw [hsumP]
      by_cases hck : cs ≠ UInt16.ofNat 0 ∧ V = false
      · -- bad checksum
        have f6 := f6bad hck.1 hck.2
        have cport := econd_port
        have hVf : Spec.Checksum.verifies (Spec.Checksum.sum b 20 (Bytes.get16 b 24).toNat
            (Spec.Checksum.pseudo src dst 17 (Bytes.get16 b 24).toNat)) = false := hck.2
        have hcs : ¬ Bytes.get16 b 26 = 0 := hck.1
        simp only [ul, cs, sp, dp, envU, envC, P1, S1, V, envP, envS, envK, envSp, envDp, b1, b2, b3, st1, st2, st3, P2, S2, envP2, envS2, envCc, v, b4, st4, env0] at f_cs f6 f_sp f_dp cport fd17 f_s1 f_s2 f_s3 f_p2 f_sum2 e_c f_ite f_ip
        simp only [execS_ite_true, execS_ite_false, c0, execB_succ, execL_cons, execL_nil,
          execS_at, execS_decl_none, execS_decl_some, hz, hzb, f_ul, c1, f_cs, f6, f_sp, f_dp, cport, fd17,
          f_s1, f_s2, f_s3, f_p2, f_sum2, e_c, f_ite, f_ip, execS_ret_none, List.length_cons,
          List.length_nil, Nat.sub_self, List.drop_zero]
        refine ⟨_, rfl, ?_⟩
        simp [hn8', hu8', hun', hVf, hcs]
      · have hok : cs = UInt16.ofNat 0 ∨ V = true := by
          by_cases h0 : cs = UInt16.ofNat 0
          · exact Or.inl h0
          · right
            cases hV : V with
            | true => rfl
            | false => exact absurd ⟨h0, hV⟩ hck
        have f6 := f6ok hok
        have hckS : (Bytes.get16 b 26 != 0 && !Spec.Checksum.verifies (Spec.Checksum.sum b 20 (Bytes.get16 b 24).toNat
            (Spec.Checksum.pseudo src dst 17 (Bytes.get16 b 24).toNat))) = false := by
          rcases hok with h | h
          · have : Bytes.get16 b 26 = 0 := h
            simp [this]
          · have : Spec.Checksum.verifies (Spec.Checksum.sum b 20 (Bytes.get16 b 24).toNat
                (Spec.Checksum.pseudo src dst 17 (Bytes.get16 b 24).toNat)) = true := h
            simp [this]
        rcases Bool.eq_false_or_eq_true (dp != 7) with hport | hport
        · -- port closed
          have cport := econd_port; conv at cport => rhs; rw [hport]
          have hp7 : ¬ Bytes.get16 b 22 = 7 := by simpa [dp] using hport
          simp only [ul, cs, sp, dp, envU, envC, P1, S1, V, envP, envS, envK, envSp, envDp, b1, b2, b3, st1, st2, st3, P2, S2, envP2, envS2, envCc, v, b4, st4, env0] at f_cs f6 f_sp f_dp cport fd17 f_s1 f_s2 f_s3 f_p2 f_sum2 e_c f_ite f_ip
          simp only [execS_ite_true, execS_ite_false, c0, execB_succ, execL_cons, execL_nil,
          execS_at, execS_decl_none, execS_decl_some, hz, hzb, f_ul, c1, f_cs, f6, f_sp, f_dp, cport, fd17,
          f_s1, f_s2, f_s3, f_p2, f_sum2, e_c, f_ite, f_ip, execS_ret_none, List.length_cons,
          List.length_nil, Nat.sub_self, List.drop_zero]
          refine ⟨_, rfl, ?_⟩
          simp [hn8', hu8', hun', hckS, hp7]
        · -- the echo
          have cport := econd_port; conv at cport => rhs; rw [hport]
          have hp7 : Bytes.get16 b 22 = 7 := by simpa [dp] using hport
          simp only [ul, cs, sp, dp, envU, envC, P1, S1, V, envP, envS, envK, envSp, envDp, b1, b2, b3, st1, st2, st3, P2, S2, envP2, envS2, envCc, v, b4, st4, env0] at f_cs f6 f_sp f_dp cport fd17 f_s1 f_s2 f_s3 f_p2 f_sum2 e_c f_ite f_ip hr
          simp only [execS_ite_true, execS_ite_false, c0, execB_succ, execL_cons, execL_nil,
          execS_at, execS_decl_none, execS_decl_some, hz, hzb, f_ul, c1, f_cs, f6, f_sp, f_dp, cport, fd17,
          f_s1, f_s2, f_s3, f_p2, f_sum2, e_c, f_ite, f_ip, execS_ret_none, List.length_cons,
          List.length_nil, Nat.sub_self, List.drop_zero]
          refine ⟨_, rfl, ?_⟩
          simp only [hn8', hu8', hun', hckS, if_false, Bool.or_self, decide_false, Bool.false_eq_true]
          rw [if_pos hp7, hr]
          simp only [withBuf_eq, stIp_setG_buf]
          exact ⟨_, by simp, rfl⟩

/-- The stack's initial globals have the constants `udp_input` reads. -/
theorem net_consts_udp (inputs : Array Trace.Input) :
    UdpConsts (Sem.initial Net.prog inputs) Spec.ourIpDefault :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- the checked stack is a `UdpProg` (with the `#guard`s at the functions)
#guard (Net.prog.check.toOption.map fun q =>
    (q.dropReasons[14]?, q.dropReasons[15]?, q.dropReasons[16]?, q.dropReasons[17]?))
  == some (some "short-udp", some "bad-udp-length", some "bad-udp-checksum", some "udp-port-closed")

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.udp_input_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms udp_input_refines

end Ember.Proof.Refine
