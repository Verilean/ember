import Ember.Proof.RefineUdp

/-!
# Ember.Proof.RefineIpInput — IPv4 validation and dispatch (plan M5.5)

`ip_input` against `Spec.Ipv4.validate` and the dispatch of
`Spec.ipInput`: the eight checks in the Spec's order with the Spec's drop
reasons, then — for a packet that is not TCP — what the Spec does with
the payload: `broadcast`, the ICMP echo, the UDP echo, or
`unsupported-protocol`.

The Spec cuts the payload out of the packet (`Bytes.slice p ihl …`); the
code leaves it in the packet buffer and, when the header has options,
moves it up to offset 20 with a loop (`sq_loop`, `squeeze_spec`).
`hpay` in the proof is the equality of the two.

TCP is not covered: the theorem assumes that the protocol field of a
packet of 20 bytes or more is not 6.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-! ## More values -/

theorem mask8_and (x y : UInt8) : mask .w8 (x.toUInt64 &&& y.toUInt64) = (x &&& y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hlt : x.toNat &&& y.toNat < 2 ^ 8 := Nat.lt_of_le_of_lt Nat.and_le_left hx
  simp only [toNat_mask8, UInt8.toNat_toUInt64, UInt64.toNat_and, UInt8.toNat_and]
  omega

theorem mask8_shr4 (x : UInt8) :
    mask .w8 (if (UInt8.ofNat 4).toUInt64.toNat ≥ Width.bits .w8 then 0
              else x.toUInt64 >>> (UInt8.ofNat 4).toUInt64) = (x >>> 4).toUInt64 := by
  have h4 : ¬ ((UInt8.ofNat 4).toUInt64.toNat ≥ Width.bits .w8) := by decide
  have hk : (UInt8.ofNat 4).toUInt64 = 4 := rfl
  have hx := x.toNat_lt
  have h1 : UInt64.toNat 4 = 4 := rfl
  have h2 : UInt8.toNat 4 = 4 := rfl
  simp only [h4, if_false]
  apply UInt64.toNat_inj.mp
  simp only [hk, toNat_mask8, UInt64.toNat_shiftRight, UInt8.toNat_toUInt64, UInt8.toNat_shiftRight, h1, h2,
    Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  omega

theorem mask16_u8 (x : UInt8) : mask .w16 x.toUInt64 = x.toUInt16.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [toNat_mask16, UInt8.toNat_toUInt64, UInt16.toNat_toUInt64, UInt8.toNat_toUInt16]
  omega

theorem mask32_ofNat (k : Nat) : mask .w32 (UInt64.ofNat k) = (UInt32.ofNat k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask32, UInt32.toNat_toUInt64, UInt64.toNat_ofNat', UInt32.toNat_ofNat']
  omega

theorem toUInt64_eq_iff32 (x y : UInt32) : (x.toUInt64 == y.toUInt64) = (x == y) := by
  have h : x.toUInt64 = y.toUInt64 ↔ x = y := by
    constructor
    · intro h
      apply UInt32.toNat_inj.mp
      have := congrArg UInt64.toNat h
      simpa using this
    · intro h; rw [h]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : x.toUInt64 ≠ y.toUInt64 := fun e => hxy (h.mp e)
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hxy]

theorem toUInt64_ne_iff32 (x y : UInt32) : (x.toUInt64 != y.toUInt64) = (x != y) := by
  simp only [bne, toUInt64_eq_iff32]

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

def ip_input_fn : Fn := checked_fn% Net.prog, "ip_input"
#guard (Net.prog.check.toOption.bind (·.fn? "ip_input")) == some ip_input_fn

/-! ## `Spec.Ipv4.validate`, case by case -/

theorem validate_eq (p : ByteArray) (ourIp : UInt32) :
    Spec.Ipv4.validate p ourIp =
      if p.size < 20 then .error "short-packet"
      else if Bytes.get p 0 >>> 4 != 4 then .error "bad-version"
      else if (Bytes.get p 0 &&& 0x0F).toNat * 4 < 20 || (Bytes.get p 0 &&& 0x0F).toNat * 4 > p.size then
        .error "bad-ihl"
      else if !Spec.Checksum.verifies (Spec.Checksum.sum p 0 ((Bytes.get p 0 &&& 0x0F).toNat * 4)) then
        .error "bad-ip-checksum"
      else if (Bytes.get16 p 2).toNat < (Bytes.get p 0 &&& 0x0F).toNat * 4 || (Bytes.get16 p 2).toNat > p.size then
        .error "bad-length"
      else if Bytes.get16 p 6 &&& 0x3FFF != 0 then .error "fragment"
      else if Bytes.get p 8 == 0 then .error "ttl-zero"
      else if Bytes.get32 p 16 != ourIp && Bytes.get32 p 16 != Spec.Ipv4.broadcast then .error "not-for-us"
      else .ok ({ ihl := (Bytes.get p 0 &&& 0x0F).toNat * 4, totalLen := (Bytes.get16 p 2).toNat,
                  id := Bytes.get16 p 4, ttl := Bytes.get p 8, proto := Bytes.get p 9,
                  src := Bytes.get32 p 12, dst := Bytes.get32 p 16 },
                Bytes.slice p ((Bytes.get p 0 &&& 0x0F).toNat * 4)
                  ((Bytes.get16 p 2).toNat - (Bytes.get p 0 &&& 0x0F).toNat * 4)) := by
  unfold Spec.Ipv4.validate
  by_cases h1 : p.size < 20
  · simp [h1]; rfl
  · by_cases h2 : Bytes.get p 0 >>> 4 != 4
    · simp [h1, h2]; rfl
    · by_cases h3 : (Bytes.get p 0 &&& 0x0F).toNat * 4 < 20 || (Bytes.get p 0 &&& 0x0F).toNat * 4 > p.size
      · simp [h1, h2, h3]; rfl
      · by_cases h4 : !Spec.Checksum.verifies (Spec.Checksum.sum p 0 ((Bytes.get p 0 &&& 0x0F).toNat * 4))
        · simp [h1, h2, h3, h4]; rfl
        · by_cases h5 : (Bytes.get16 p 2).toNat < (Bytes.get p 0 &&& 0x0F).toNat * 4
              || (Bytes.get16 p 2).toNat > p.size
          · simp [h1, h2, h3, h4, h5]; rfl
          · by_cases h6 : Bytes.get16 p 6 &&& 0x3FFF != 0
            · simp [h1, h2, h3, h4, h5, h6]; rfl
            · by_cases h7 : Bytes.get p 8 == 0
              · simp [h1, h2, h3, h4, h5, h6, h7]; rfl
              · by_cases h8 : Bytes.get32 p 16 != ourIp && Bytes.get32 p 16 != Spec.Ipv4.broadcast
                · simp [h1, h2, h3, h4, h5, h6, h7, h8]; rfl
                · simp [h1, h2, h3, h4, h5, h6, h7, h8]; rfl

/-! ## Skipping IP options: the payload moves up to offset 20 -/

/-- One step of the copy: byte `ihl + i` goes to `20 + i`. -/
def sqStep (ihl : Nat) (acc : ByteArray) (i : Nat) : ByteArray :=
  Bytes.set acc (20 + i) (Bytes.get acc (ihl + i))

/-- The buffer after `n` bytes have been moved from offset `ihl` to offset 20. -/
def squeeze (b : ByteArray) (ihl n : Nat) : ByteArray := (List.range' 0 n).foldl (sqStep ihl) b

theorem squeeze_spec (b : ByteArray) (ihl : Nat) (h20 : 20 ≤ ihl) : ∀ n, ihl + n ≤ b.size →
    (squeeze b ihl n).size = b.size ∧ (∀ j, j < n → Bytes.get (squeeze b ihl n) (20 + j) = Bytes.get b (ihl + j)) ∧
      (∀ i, i < 20 ∨ 20 + n ≤ i → Bytes.get (squeeze b ihl n) i = Bytes.get b i) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun i _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨hs, hj, hi⟩ := ih (by omega)
    have hstep : squeeze b ihl (n + 1) = sqStep ihl (squeeze b ihl n) n := by
      simp only [squeeze, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
        Nat.one_mul]
    rw [hstep]
    simp only [sqStep]
    refine ⟨by rw [Bytes.size_set, hs], ?_, ?_⟩
    · intro j hjn
      rw [Bytes.get_set, hs]
      by_cases hjj : j = n
      · subst hjj
        have : 20 + j < b.size := by omega
        simp only [true_and, this, if_true]
        exact hi _ (Or.inr (by omega))
      · have : ¬ (20 + n = 20 + j) := by omega
        simp only [this, false_and, if_false]
        exact hj j (by omega)
    · intro i hii
      rw [Bytes.get_set]
      have : ¬ (20 + n = i) := by omega
      simp only [this, false_and, if_false]
      exact hi i (by omega)

/-- The body of the loop of `ip_input`. -/
def sqBody : List Stmt :=
  match ip_input_fn.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ (.ite _ [.at _ (.forRange _ _ _ _ body)] _), _, _, _] => body
  | _ => []

/-- One iteration of the copy. -/
theorem sq_body (p : Prog) (ihl : UInt16) (envL : Env) (hih : envL.lookup "ihl" = some (u16 ihl))
    (hnb : envL.lookup "buf" = none) (st : St) (B : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal B)) (i : Nat) (h1 : ihl.toNat + i < B.size)
    (h2 : 20 + i < B.size) (h3 : B.size < 65536) (m : Nat) :
    execB (m + 6) p st (("i", u16 (UInt16.ofNat i)) :: envL) sqBody
      = .ok (setG st "buf" (bufVal (sqStep ihl.toNat B i))) (("i", u16 (UInt16.ofNat i)) :: envL) .normal := by
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have ei : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.var "i") = some (u16 (UInt16.ofNat i)) := by
    simp [evalE, lookup, List.lookup]
  have eih : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.var "ihl") = some (u16 ihl) := by
    simp [evalE, lookup, List.lookup, hih]
  have ebuf : lookup st (("i", u16 (UInt16.ofNat i)) :: envL) "buf" = some (bufVal B) := by
    simp [lookup, List.lookup, hnb, hb]
  have esrc : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.bin .add (.var "ihl") (.var "i"))
      = some (u16 (ihl + UInt16.ofNat i)) := by
    simp only [evalE_bin, eih, ei, Sem.binop, mask16_add]
  have edst : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL) (.bin .add (.lit 20 (some .w16)) (.var "i"))
      = some (u16 (UInt16.ofNat 20 + UInt16.ofNat i)) := by
    simp only [evalE_bin, evalE_lit16, ei, Sem.binop, mask16_add]
  have hs : (ihl + UInt16.ofNat i).toNat = ihl.toNat + i := by
    simp only [UInt16.toNat_add, ht i (by omega)]; omega
  have hd : (UInt16.ofNat 20 + UInt16.ofNat i).toNat = 20 + i := by
    simp only [UInt16.toNat_add, ht i (by omega), ht 20 (by omega)]; omega
  have hidx : (u16 (ihl + UInt16.ofNat i)).toNat = ihl.toNat + i := by
    show (ihl + UInt16.ofNat i).toUInt64.toNat = _
    rw [UInt16.toNat_toUInt64, hs]
  have ev : evalE p st (("i", u16 (UInt16.ofNat i)) :: envL)
      (.index (.var "buf") (.bin .add (.var "ihl") (.var "i"))) = some (u8 (Bytes.get B (ihl.toNat + i))) := by
    rw [evalE, evalE_var, ebuf, esrc]
    simp only [bufVal, hidx, bufVal_get B _ h1]
  have ea := assign_buf p st (("i", u16 (UInt16.ofNat i)) :: envL) B _ (UInt16.ofNat 20 + UInt16.ofNat i)
    (Bytes.get B (ihl.toNat + i)) (by simp [List.lookup, hnb]) hb edst (by rw [hd]; exact h2)
  rw [hd, withBuf_eq] at ea
  simp only [sqBody, ip_input_fn, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, ev, ea, sqStep,
    List.length_cons, Nat.sub_self, List.drop_zero]

/-- The loop of `ip_input`: bytes `cur … cur+k-1` of the payload move up. -/
theorem sq_loop (p : Prog) (ihl : UInt16) (envL : Env) (hih : envL.lookup "ihl" = some (u16 ihl))
    (hnb : envL.lookup "buf" = none) (hi : Nat) :
    ∀ (k cur : Nat) (st : St) (B : ByteArray) (v0 : Val) (d : Nat),
      st.globals.lookup "buf" = some (bufVal B) → cur + k = hi → ihl.toNat + hi ≤ B.size → 20 + hi ≤ B.size →
      B.size < 65536 →
      ∃ v, forLoop (k + 7 + d) p st (("i", v0) :: envL) "i" .w16 cur hi sqBody
          = .ok (setG st "buf" (bufVal ((List.range' cur k).foldl (sqStep ihl.toNat) B))) (("i", v) :: envL)
              .normal := by
  intro k
  induction k with
  | zero =>
    intro cur st B v0 d hb hk _ _ _
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 7 + d = (6 + d) + 1 by omega, forLoop_succ]
    simp [this, setG_same st _ _ hb]
  | succ k ih =>
    intro cur st B v0 d hb hk h1 h2 h3
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    have hsz : (sqStep ihl.toNat B cur).size = B.size := by simp [sqStep]
    obtain ⟨v, hv⟩ := ih (cur + 1) (setG st "buf" (bufVal (sqStep ihl.toNat B cur))) (sqStep ihl.toNat B cur)
      (u16 (UInt16.ofNat cur)) d (lookup_setG st _ _ _ hb) (by omega) (by omega) (by omega) (by omega)
    refine ⟨v, ?_⟩
    rw [show k + 1 + 7 + d = (k + 7 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 7 + d = (k + 1 + d) + 6 by omega,
      sq_body p ihl envL hih hnb st B hb cur (by omega) (by omega) h3 (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 6 = k + 7 + d by omega, hv, setG_setG]
    simp [List.range'_succ]

/-! ## `ip_input` -/

theorem get32_extract (b : ByteArray) (s e j : Nat) (h : s + j + 3 < e) (he : e ≤ b.size) :
    Bytes.get32 (b.extract s e) j = Bytes.get32 b (s + j) := by
  simp only [Bytes.get32]
  rw [get_extract b s e j (by omega) he, get_extract b s e (j + 1) (by omega) he,
    get_extract b s e (j + 2) (by omega) he, get_extract b s e (j + 3) (by omega) he]
  rfl

/-- A program with the functions `ip_input` uses (TCP apart) and its drop reasons. -/
structure InProg (p : Prog) : Prop extends UdpProg p where
  get32 : p.fn? "get32" = some get32
  ip_input : p.fn? "ip_input" = some ip_input_fn
  r1 : p.dropReasons[1]? = some "short-packet"
  r2 : p.dropReasons[2]? = some "bad-version"
  r3 : p.dropReasons[3]? = some "bad-ihl"
  r4 : p.dropReasons[4]? = some "bad-ip-checksum"
  r5 : p.dropReasons[5]? = some "bad-length"
  r6 : p.dropReasons[6]? = some "fragment"
  r7 : p.dropReasons[7]? = some "ttl-zero"
  r8 : p.dropReasons[8]? = some "not-for-us"
  r9 : p.dropReasons[9]? = some "broadcast"
  r10 : p.dropReasons[10]? = some "unsupported-protocol"

/-- The constants the receive path reads. -/
structure InConsts (st : St) (ourIp : UInt32) : Prop where
  icmp : IcmpConsts st ourIp
  udp : UdpConsts st ourIp
  d1 : st.globals.lookup "D_SHORT_PACKET" = some (u8 1)
  d2 : st.globals.lookup "D_BAD_VERSION" = some (u8 2)
  d3 : st.globals.lookup "D_BAD_IHL" = some (u8 3)
  d4 : st.globals.lookup "D_BAD_IP_CHECKSUM" = some (u8 4)
  d5 : st.globals.lookup "D_BAD_LENGTH" = some (u8 5)
  d6 : st.globals.lookup "D_FRAGMENT" = some (u8 6)
  d7 : st.globals.lookup "D_TTL_ZERO" = some (u8 7)
  d8 : st.globals.lookup "D_NOT_FOR_US" = some (u8 8)
  d9 : st.globals.lookup "D_BROADCAST" = some (u8 9)
  d10 : st.globals.lookup "D_UNSUPPORTED_PROTOCOL" = some (u8 10)

/-- The `if` around the copy loop of `ip_input`. -/
def sqIte : Stmt :=
  match ip_input_fn.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ s, _, _, _] => s
  | _ => .brk

/-- The dispatch on the protocol at the end of `ip_input`. -/
def dispatchIte : Stmt :=
  match ip_input_fn.body with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .at _ s] => s
  | _ => .brk

theorem icmpConsts_setG_buf (st : St) (ourIp : UInt32) (v : Val) (h : IcmpConsts st ourIp) :
    IcmpConsts (setG st "buf" v) ourIp :=
  ⟨by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.ourIp, by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.ttl,
   by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d11, by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d12,
   by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d13⟩

theorem udpConsts_setG_buf (st : St) (ourIp : UInt32) (v : Val) (h : UdpConsts st ourIp) :
    UdpConsts (setG st "buf" v) ourIp :=
  ⟨by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.ourIp, by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.ttl,
   by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.echo, by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d14,
   by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d15, by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d16,
   by rw [lookup_setG_ne _ _ _ _ (by decide)]; exact h.d17⟩

/-- A call of `icmp_input` as a statement. -/
theorem execS_icmp_input (p : Prog) (hP : IcmpProg p) (st : St) (env : Env) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hK : IcmpConsts st ourIp) (e1 e2 : Expr) (src : UInt32) (n : UInt16)
    (he1 : evalE p st env e1 = some (u32 src)) (he2 : evalE p st env e2 = some (u16 n))
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (m d : Nat) (hm : m = d + n.toNat + 251) :
    ∃ st', execS m p st env (.call none "icmp_input" [e1, e2]) = .ok st' env .normal ∧
      match Spec.Icmp.reply (b.extract 20 (20 + n.toNat)) with
      | .error r => st' = dropSt st r
      | .ok msg => ∃ B, B.size = b.size ∧ st' = txOut (stIp st B (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 1 id ourIp src msg)) := by
  subst hm
  obtain ⟨st', hc, hres⟩ := icmp_input_refines p hP st b id hb hid ourIp hK src n hn hsz d
  exact ⟨st', execS_call_val p st env _ none "icmp_input" [e1, e2] hP.icmp_input (by simp [icmp_input])
    (by simp [evalArgs, he1, he2]) hc, hres⟩

/-- A call of `udp_input` as a statement. -/
theorem execS_udp_input (p : Prog) (hP : UdpProg p) (st : St) (env : Env) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hK : UdpConsts st ourIp) (e1 e2 e3 : Expr) (src dst : UInt32) (n : UInt16)
    (he1 : evalE p st env e1 = some (u32 src)) (he2 : evalE p st env e2 = some (u32 dst))
    (he3 : evalE p st env e3 = some (u16 n))
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (m d : Nat) (hm : m = d + n.toNat + 401) :
    ∃ st', execS m p st env (.call none "udp_input" [e1, e2, e3]) = .ok st' env .normal ∧
      match Spec.Udp.parse src dst (b.extract 20 (20 + n.toNat)) with
      | .error r => st' = dropSt st r
      | .ok dg =>
        if dg.dport = 7 then
          ∃ B, B.size = b.size ∧ st' = txOut (stIp st B (id + 1)) (st.world.frame ++ Spec.Slip.encode
            (Spec.Ipv4.packet 17 id ourIp src (Spec.Udp.emit ourIp src dg.dport dg.sport dg.data)))
        else st' = dropSt st "udp-port-closed" := by
  subst hm
  obtain ⟨st', hc, hres⟩ := udp_input_refines p hP st b id hb hid ourIp hK src dst n hn hsz d
  exact ⟨st', execS_call_val p st env _ none "udp_input" [e1, e2, e3] hP.udp_input (by simp [udp_input])
    (by simp [evalArgs, he1, he2, he3]) hc, hres⟩

/-- What `ip_input` does with a packet the Spec accepts.  (`b` is the
packet buffer before: the buffer after has the same size.) -/
def ipOutcomeT (TcpR : ByteArray → UInt32 → UInt32 → UInt16 → St → Prop) (st st' : St) (b : ByteArray)
    (id : UInt16) (ourIp : UInt32) (h : Spec.Ipv4.Hdr) (payload : ByteArray) : Prop :=
  ∃ B : ByteArray, B.size = b.size ∧
    if h.dst == Spec.Ipv4.broadcast && h.proto != 17 then st' = dropSt (setG st "buf" (bufVal B)) "broadcast"
    else if h.proto = 1 then
      match Spec.Icmp.reply payload with
      | .error r => st' = dropSt (setG st "buf" (bufVal B)) r
      | .ok m => ∃ B', B'.size = b.size ∧ st' = txOut (stIp st B' (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 1 id ourIp h.src m))
    else if h.proto = 17 then
      match Spec.Udp.parse h.src h.dst payload with
      | .error r => st' = dropSt (setG st "buf" (bufVal B)) r
      | .ok dg =>
        if dg.dport = 7 then
          ∃ B', B'.size = b.size ∧ st' = txOut (stIp st B' (id + 1)) (st.world.frame ++ Spec.Slip.encode
            (Spec.Ipv4.packet 17 id ourIp h.src (Spec.Udp.emit ourIp h.src dg.dport dg.sport dg.data)))
        else st' = dropSt (setG st "buf" (bufVal B)) "udp-port-closed"
    else if h.proto = 6 then
      ∃ n : UInt16, payload = B.extract 20 (20 + n.toNat) ∧ 20 + n.toNat ≤ B.size ∧ TcpR B h.src h.dst n st'
    else st' = dropSt (setG st "buf" (bufVal B)) "unsupported-protocol"

/-- The same when the packet is known not to be TCP. -/
def ipOutcome (st st' : St) (b : ByteArray) (id : UInt16) (ourIp : UInt32) (h : Spec.Ipv4.Hdr)
    (payload : ByteArray) : Prop :=
  ∃ B : ByteArray, B.size = b.size ∧
    if h.dst == Spec.Ipv4.broadcast && h.proto != 17 then st' = dropSt (setG st "buf" (bufVal B)) "broadcast"
    else if h.proto = 1 then
      match Spec.Icmp.reply payload with
      | .error r => st' = dropSt (setG st "buf" (bufVal B)) r
      | .ok m => ∃ B', B'.size = b.size ∧ st' = txOut (stIp st B' (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 1 id ourIp h.src m))
    else if h.proto = 17 then
      match Spec.Udp.parse h.src h.dst payload with
      | .error r => st' = dropSt (setG st "buf" (bufVal B)) r
      | .ok dg =>
        if dg.dport = 7 then
          ∃ B', B'.size = b.size ∧ st' = txOut (stIp st B' (id + 1)) (st.world.frame ++ Spec.Slip.encode
            (Spec.Ipv4.packet 17 id ourIp h.src (Spec.Udp.emit ourIp h.src dg.dport dg.sport dg.data)))
        else st' = dropSt (setG st "buf" (bufVal B)) "udp-port-closed"
    else st' = dropSt (setG st "buf" (bufVal B)) "unsupported-protocol"

theorem ipOutcome_of (st st' : St) (b : ByteArray) (id : UInt16) (ourIp : UInt32) (h : Spec.Ipv4.Hdr)
    (payload : ByteArray) (ho : ipOutcomeT (fun _ _ _ _ _ => False) st st' b id ourIp h payload) :
    ipOutcome st st' b id ourIp h payload := by
  obtain ⟨B, hB, ho⟩ := ho
  refine ⟨B, hB, ?_⟩
  by_cases c1 : (h.dst == Spec.Ipv4.broadcast && h.proto != 17) = true
  · rw [if_pos c1] at ho ⊢; exact ho
  rw [if_neg c1] at ho ⊢
  by_cases c2 : h.proto = 1
  · rw [if_pos c2] at ho ⊢; exact ho
  rw [if_neg c2] at ho ⊢
  by_cases c3 : h.proto = 17
  · rw [if_pos c3] at ho ⊢; exact ho
  rw [if_neg c3] at ho ⊢
  by_cases c4 : h.proto = 6
  · rw [if_pos c4] at ho; obtain ⟨_, _, _, f⟩ := ho; exact f.elim
  rw [if_neg c4] at ho; exact ho

set_option maxHeartbeats 2000000 in
/-- **`ip_input` is `Spec.Ipv4.validate` and the dispatch of
`Spec.ipInput`**, for the packet `buf[0, len)`: either the drop line the
Spec gives for the first check that fails, or what the Spec does with
the payload (`ipOutcomeT`).  For a TCP packet that is whatever the call
`tcp_input(src, dst, n)` does on the segment at offset 20 (`hTcp`, with
its result `TcpR`). -/
theorem ip_input_refines_tcp (p : Prog) (hP : InProg p) (st : St) (b : ByteArray) (L id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hlen : st.globals.lookup "len" = some (u16 L))
    (hid : st.globals.lookup "ip_id" = some (u16 id)) (ourIp : UInt32) (hK : InConsts st ourIp)
    (hL : L.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat)
    (TcpR : ByteArray → UInt32 → UInt32 → UInt16 → St → Prop)
    (hTcp : 20 ≤ L.toNat → Bytes.get b 9 = 6 → ∀ (B : ByteArray) (env : Env) (src dst : UInt32) (n : UInt16),
      B.size = b.size → 20 + n.toNat ≤ B.size → n.toNat ≤ L.toNat →
      evalE p (setG st "buf" (bufVal B)) env (.var "src") = some (u32 src) →
      evalE p (setG st "buf" (bufVal B)) env (.var "dst") = some (u32 dst) →
      evalE p (setG st "buf" (bufVal B)) env (.var "n") = some (u16 n) →
      ∃ st', execS (d + L.toNat + 460) p (setG st "buf" (bufVal B)) env
          (.call none "tcp_input" [.var "src", .var "dst", .var "n"]) = .ok st' env .normal ∧
        TcpR B src dst n st') :
    ∃ st', Sem.call (d + L.toNat + 500) p st "ip_input" [] = .ok none st' ∧
      match Spec.Ipv4.validate (b.extract 0 L.toNat) ourIp with
      | .error r => st' = dropSt st r
      | .ok (h, payload) => ipOutcomeT TcpR st st' b id ourIp h payload := by
  have hpsz : (b.extract 0 L.toNat).size = L.toNat := by rw [ByteArray.size_extract]; omega
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have hz32 : zeroOf p (Ty.int .w32) = u32 0 := rfl
  have hzb : zeroOf p Ty.bool = .bool false := rfl
  have evar : ∀ (S : St) (env : Env) (x : String) (v : Val), env.lookup x = some v →
      evalE p S env (.var x) = some v := by
    intro S env x v h; simp [evalE, lookup, h]
  have eglob : ∀ (S : St) (env : Env) (x : String) (v : Val), S.globals.lookup x = some v → env.lookup x = none →
      evalE p S env (.var x) = some v := by
    intro S env x v h h'; simp [evalE, lookup, h, h']
  have ebyte : ∀ (env : Env) (k : Nat), env.lookup "buf" = none → k < b.size →
      evalE p st env (.index (.var "buf") (.lit k (some .w16))) = some (u8 (Bytes.get b k)) := by
    intro env k hnb hk
    have hidx : (u16 (UInt16.ofNat k)).toNat = k := by
      show (UInt16.ofNat k).toUInt64.toNat = _
      rw [UInt16.toNat_toUInt64, ht k (by omega)]
    rw [evalE, eglob st env "buf" _ hb hnb, evalE_lit16]
    simp only [bufVal, hidx, bufVal_get b k hk]
  have hlt : ∀ (x : UInt16) (k : Nat), k < 65536 → ((x < UInt16.ofNat k) ↔ x.toNat < k) := by
    intro x k hk; rw [UInt16.lt_iff_toNat_lt, ht k hk]
  rw [validate_eq, hpsz]
  simp only [Sem.call, hP.ip_input, ip_input_fn, execB_succ, execL_cons, execS_at, List.map, List.zip,
    List.zipWith]
  -- 1. the length
  have econd0 : evalE p st [] (.bin .lt (.var "len") (.lit 20 (some .w16)))
      = some (.bool (decide (L < UInt16.ofNat 20))) := by
    simp only [evalE_bin, evalE_lit16, eglob st [] "len" _ hlen rfl, Sem.binop, toUInt64_lt_iff]
  have fd1 := fun m => execS_drop p st [] m (.var "D_SHORT_PACKET") 1 "short-packet"
    (eglob st [] _ _ hK.d1 rfl) hP.r1
  by_cases h0 : L < UInt16.ofNat 20
  · have c0 := econd0; simp only [h0, decide_true] at c0
    simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1]
    exact ⟨_, rfl, by simp [(hlt L 20 (by omega)).mp h0]⟩
  · have c0 := econd0; simp only [h0, decide_false] at c0
    have hL20 : 20 ≤ L.toNat := by
      have := mt (hlt L 20 (by omega)).mpr h0; omega
    have hL20' : ¬ L.toNat < 20 := by omega
    -- the fields of the packet are the fields of the buffer
    rw [get_extract b 0 _ 0 (by omega) hL, get_extract b 0 _ 8 (by omega) hL, get_extract b 0 _ 9 (by omega) hL,
      get16_extract b 0 _ 2 (by omega) hL, get16_extract b 0 _ 4 (by omega) hL,
      get16_extract b 0 _ 6 (by omega) hL, get32_extract b 0 _ 12 (by omega) hL,
      get32_extract b 0 _ 16 (by omega) hL]
    simp only [Nat.zero_add]
    -- 2. the version
    have econd1 : evalE p st [] (.bin .ne (.bin .shr (.index (.var "buf") (.lit 0 (some .w16))) (.lit 4 (some .w8)))
        (.lit 4 (some .w8))) = some (.bool (Bytes.get b 0 >>> 4 != UInt8.ofNat 4)) := by
      simp only [evalE_bin, ebyte [] 0 rfl (by omega), evalE_lit8, Sem.binop, mask8_shr4, toUInt64_ne_iff8]
    have fd2 := fun m => execS_drop p st [] m (.var "D_BAD_VERSION") 2 "bad-version"
      (eglob st [] _ _ hK.d2 rfl) hP.r2
    rcases Bool.eq_false_or_eq_true (Bytes.get b 0 >>> 4 != UInt8.ofNat 4) with h1 | h1
    · have c1 := econd1; conv at c1 => rhs; rw [h1]
      simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2]
      refine ⟨_, rfl, ?_⟩
      have h1' : (Bytes.get b 0 >>> 4 != 4) = true := h1
      simp [hL20', h1']
    · have c1 := econd1; conv at c1 => rhs; rw [h1]
      have h1' : (Bytes.get b 0 >>> 4 != 4) = false := h1
      -- 3. the header length
      have eb : evalE p st [] (.bin .band (.index (.var "buf") (.lit 0 (some .w16))) (.lit 15 (some .w8)))
          = some (u8 (Bytes.get b 0 &&& UInt8.ofNat 15)) := by
        simp only [evalE_bin, ebyte [] 0 rfl (by omega), evalE_lit8, Sem.binop, mask8_and]
      have ec : evalE p st [] (.cast .w16 (.bin .band (.index (.var "buf") (.lit 0 (some .w16)))
          (.lit 15 (some .w8)))) = some (u16 (Bytes.get b 0 &&& UInt8.ofNat 15).toUInt16) := by
        rw [evalE, eb]; simp only [mask16_u8]
      obtain ⟨ihl, hihl_def⟩ : ∃ x : UInt16, x = (Bytes.get b 0 &&& UInt8.ofNat 15).toUInt16 * UInt16.ofNat 4 :=
        ⟨_, rfl⟩
      have e_ihl : evalE p st [] (.bin .mul (.cast .w16 (.bin .band (.index (.var "buf") (.lit 0 (some .w16)))
          (.lit 15 (some .w8)))) (.lit 4 (some .w16))) = some (u16 ihl) := by
        simp only [evalE_bin, ec, evalE_lit16, Sem.binop, mask16_mul, hihl_def]
      have hihl : ihl.toNat = (Bytes.get b 0 &&& 0x0F).toNat * 4 := by
        have h15 : (Bytes.get b 0 &&& 0x0F).toNat < 256 := UInt8.toNat_lt _
        have t4 : (UInt16.ofNat 4).toNat = 4 := ht 4 (by omega)
        rw [hihl_def, UInt16.toNat_mul, UInt8.toNat_toUInt16, t4]
        show (Bytes.get b 0 &&& 0x0F).toNat * 4 % 2 ^ 16 = _
        omega
      rw [← hihl]
      have econd2 : evalE p st [("ihl", u16 ihl)] (.bin .lor (.bin .lt (.var "ihl") (.lit 20 (some .w16)))
          (.bin .gt (.var "ihl") (.var "len"))) = some (.bool (decide (ihl < UInt16.ofNat 20) || decide (L < ihl))) := by
        simp only [evalE_bin, evalE_lit16, evar st [("ihl", u16 ihl)] "ihl" (u16 ihl) (by simp [List.lookup]),
          eglob st [("ihl", u16 ihl)] "len" _ hlen (by simp [List.lookup]), Sem.binop, toUInt64_lt_iff]
      have fd3 := fun m => execS_drop p st [("ihl", u16 ihl)] m (.var "D_BAD_IHL") 3 "bad-ihl"
        (eglob st [("ihl", u16 ihl)] _ _ hK.d3 (by simp [List.lookup])) hP.r3
      have hk2 : (decide (ihl < UInt16.ofNat 20) || decide (L < ihl)) = true ↔ (ihl.toNat < 20 ∨ ihl.toNat > L.toNat) := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, hlt ihl 20 (by omega), UInt16.lt_iff_toNat_lt]
      rcases Bool.eq_false_or_eq_true (decide (ihl < UInt16.ofNat 20) || decide (L < ihl)) with h2 | h2
      · have c2 := econd2; conv at c2 => rhs; rw [h2]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3]
        refine ⟨_, rfl, ?_⟩
        have := hk2.mp h2
        simp [hL20', h1', this]
      have c2 := econd2; conv at c2 => rhs; rw [h2]
      have h2' : ¬ (ihl.toNat < 20 ∨ ihl.toNat > L.toNat) := by rw [← hk2, h2]; simp
      have hi20 : 20 ≤ ihl.toNat := by
        have : ¬ ihl.toNat < 20 := fun h => h2' (Or.inl h)
        omega
      have hiL : ihl.toNat ≤ L.toNat := by
        have : ¬ ihl.toNat > L.toNat := fun h => h2' (Or.inr h)
        omega
      -- 4. the header checksum
      have hsumP : Spec.Checksum.sum (b.extract 0 L.toNat) 0 ihl.toNat 0 = Spec.Checksum.sum b 0 ihl.toNat 0 := by
        apply Spec.Checksum.sum_congr
        intro i hi
        rw [get_extract b 0 _ (0 + i) (by omega) hL, Nat.zero_add]
      rw [hsumP]
      obtain ⟨hs, hhs⟩ : ∃ x : UInt16, x = Spec.Checksum.sum b 0 ihl.toNat 0 := ⟨_, rfl⟩
      obtain ⟨hok, hhok⟩ : ∃ x : Bool, x = Spec.Checksum.verifies hs := ⟨_, rfl⟩
      rw [← hhs, ← hhok]
      have f_hs : execS (d + L.toNat + 492) p st [("hs", u16 0), ("ihl", u16 ihl)]
          (.call (some (.var "hs")) "csum" [.lit 0 (some .w16), .var "ihl", .lit 0 (some .w16)])
          = .ok st [("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        rw [execS_csum p hP.csum hP.get16 hP.add16 st _ b hb _ _ _ _ (UInt16.ofNat 0) ihl (UInt16.ofNat 0)
          (by rw [ht 0 (by omega)]; omega) (by omega) (evalE_lit16 ..)
          (evar _ _ "ihl" _ (by simp [List.lookup])) (evalE_lit16 ..) _ (d + (L.toNat - ihl.toNat / 2) + 431) (by omega)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 0 (by omega), hhs]
        rfl
      have f_hok : ∀ m, execS (m + 7) p st [("hok", Val.bool false), ("hs", u16 hs), ("ihl", u16 ihl)]
          (.call (some (.var "hok")) "verifies" [.var "hs"]) = .ok st [("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        intro m
        rw [execS_verifies p hP.verifies st _ _ _ hs m (evar _ _ "hs" _ (by simp [List.lookup]))]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, hhok]
      have econd3 : evalE p st [("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.un .lnot (.var "hok")) = some (.bool (!hok)) := by
        simp only [evalE, lookup, List.lookup, beq_self_eq_true]
      have fd4 := fun m => execS_drop p st [("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_BAD_IP_CHECKSUM") 4 "bad-ip-checksum"
        (eglob st [("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ hK.d4 (by simp [List.lookup])) hP.r4
      rcases (Bool.eq_false_or_eq_true hok).symm with h3 | h3
      · have c3 := econd3; conv at c3 => rhs; rw [h3]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false]
        refine ⟨_, rfl, ?_⟩
        simp [hL20', h1', h2', h3]
      have c3 := econd3; conv at c3 => rhs; rw [h3]
      -- 5. the total length
      obtain ⟨tl, htl⟩ : ∃ x : UInt16, x = Bytes.get16 b 2 := ⟨_, rfl⟩
      rw [← htl]
      have f_tl : ∀ m, execS (m + 7) p st (("tl", u16 0) :: [("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)])
          (.call (some (.var "tl")) "get16" [.lit 2 (some .w16)]) = .ok st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        intro m
        rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 2) m (by rw [ht 2 (by omega)]; omega)
          (by rw [ht 2 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 2 (by omega), htl]
      have econd4 : evalE p st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .lor (.bin .lt (.var "tl") (.var "ihl"))
          (.bin .gt (.var "tl") (.var "len"))) = some (.bool (decide (tl < ihl) || decide (L < tl))) := by
        simp only [evalE_bin, evar st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "tl" (u16 tl) (by simp [List.lookup]), evar st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "ihl" (u16 ihl) (by simp [List.lookup]),
          eglob st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "len" _ hlen (by simp [List.lookup]), Sem.binop, toUInt64_lt_iff]
      have fd5 := fun m => execS_drop p st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_BAD_LENGTH") 5 "bad-length"
        (eglob st [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ hK.d5 (by simp [List.lookup])) hP.r5
      have hk4 : (decide (tl < ihl) || decide (L < tl)) = true ↔ (tl.toNat < ihl.toNat ∨ tl.toNat > L.toNat) := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, UInt16.lt_iff_toNat_lt]
      rcases Bool.eq_false_or_eq_true (decide (tl < ihl) || decide (L < tl)) with h4 | h4
      · have c4 := econd4; conv at c4 => rhs; rw [h4]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5]
        refine ⟨_, rfl, ?_⟩
        have := hk4.mp h4
        simp [hL20', h1', h2', h3, this]
      have c4 := econd4; conv at c4 => rhs; rw [h4]
      have h4' : ¬ (tl.toNat < ihl.toNat ∨ tl.toNat > L.toNat) := by rw [← hk4, h4]; simp
      have hti : ihl.toNat ≤ tl.toNat := by
        have : ¬ tl.toNat < ihl.toNat := fun h => h4' (Or.inl h)
        omega
      have htL : tl.toNat ≤ L.toNat := by
        have : ¬ tl.toNat > L.toNat := fun h => h4' (Or.inr h)
        omega
      -- 6. fragments
      obtain ⟨ff, hff⟩ : ∃ x : UInt16, x = Bytes.get16 b 6 := ⟨_, rfl⟩
      rw [← hff]
      have f_ff : ∀ m, execS (m + 7) p st (("ff", u16 0) :: [("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)])
          (.call (some (.var "ff")) "get16" [.lit 6 (some .w16)]) = .ok st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        intro m
        rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 6) m (by rw [ht 6 (by omega)]; omega)
          (by rw [ht 6 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 6 (by omega), hff]
      have econd5 : evalE p st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .ne (.bin .band (.var "ff") (.lit 16383 (some .w16)))
          (.lit 0 (some .w16))) = some (.bool (ff &&& UInt16.ofNat 16383 != UInt16.ofNat 0)) := by
        simp only [evalE_bin, evar st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "ff" (u16 ff) (by simp [List.lookup]), evalE_lit16, Sem.binop, mask16_and, toUInt64_ne_iff]
      have fd6 := fun m => execS_drop p st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_FRAGMENT") 6 "fragment"
        (eglob st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ hK.d6 (by simp [List.lookup])) hP.r6
      rcases Bool.eq_false_or_eq_true (ff &&& UInt16.ofNat 16383 != UInt16.ofNat 0) with h5 | h5
      · have c5 := econd5; conv at c5 => rhs; rw [h5]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6]
        refine ⟨_, rfl, ?_⟩
        have h5' : (ff &&& 0x3FFF != 0) = true := h5
        simp [hL20', h1', h2', h3, h4', h5']
      have c5 := econd5; conv at c5 => rhs; rw [h5]
      have h5' : (ff &&& 0x3FFF != 0) = false := h5
      -- 7. the TTL
      have econd6 : evalE p st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .eq (.index (.var "buf") (.lit 8 (some .w16))) (.lit 0 (some .w8)))
          = some (.bool (Bytes.get b 8 == UInt8.ofNat 0)) := by
        simp only [evalE_bin, ebyte [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] 8 (by simp [List.lookup]) (by omega), evalE_lit8, Sem.binop, toUInt64_eq_iff8]
      have fd7 := fun m => execS_drop p st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_TTL_ZERO") 7 "ttl-zero"
        (eglob st [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ hK.d7 (by simp [List.lookup])) hP.r7
      rcases Bool.eq_false_or_eq_true (Bytes.get b 8 == UInt8.ofNat 0) with h6 | h6
      · have c6 := econd6; conv at c6 => rhs; rw [h6]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7]
        refine ⟨_, rfl, ?_⟩
        have h6' : (Bytes.get b 8 == 0) = true := h6
        simp [hL20', h1', h2', h3, h4', h5', h6']
      have c6 := econd6; conv at c6 => rhs; rw [h6]
      have h6' : (Bytes.get b 8 == 0) = false := h6
      -- 8. the destination
      obtain ⟨dst, hdst⟩ : ∃ x : UInt32, x = Bytes.get32 b 16 := ⟨_, rfl⟩
      rw [← hdst]
      have f_dst : ∀ m, execS (m + 21) p st (("dst", u32 0) :: [("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)])
          (.call (some (.var "dst")) "get32" [.lit 16 (some .w16)]) = .ok st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        intro m
        rw [execS_get32 p hP.get32 hP.get16 st _ b hb _ _ (UInt16.ofNat 16) m (by rw [ht 16 (by omega)]; omega)
          (by rw [ht 16 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 16 (by omega), hdst]
      have econd7 : evalE p st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .land (.bin .ne (.var "dst") (.var "OUR_IP"))
          (.bin .ne (.var "dst") (.lit 4294967295 (some .w32))))
          = some (.bool (dst != ourIp && dst != UInt32.ofNat 4294967295)) := by
        simp only [evalE_bin, evar st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "dst" (u32 dst) (by simp [List.lookup]), eglob st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "OUR_IP" _ hK.icmp.ourIp (by simp [List.lookup]),
          evalE_lit, mask32_ofNat, Sem.binop, toUInt64_ne_iff32]
      have fd8 := fun m => execS_drop p st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_NOT_FOR_US") 8 "not-for-us"
        (eglob st [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ hK.d8 (by simp [List.lookup])) hP.r8
      rcases Bool.eq_false_or_eq_true (dst != ourIp && dst != UInt32.ofNat 4294967295) with h7 | h7
      · have c7 := econd7; conv at c7 => rhs; rw [h7]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8]
        refine ⟨_, rfl, ?_⟩
        have h7' : (dst != ourIp && dst != Spec.Ipv4.broadcast) = true := h7
        simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, if_true, Bool.not_true, Bool.false_eq_true,
          Bool.or_eq_true, decide_eq_true_eq]
      have c7 := econd7; conv at c7 => rhs; rw [h7]
      have h7' : (dst != ourIp && dst != Spec.Ipv4.broadcast) = false := h7
      -- the remaining fields
      obtain ⟨src, hsrc⟩ : ∃ x : UInt32, x = Bytes.get32 b 12 := ⟨_, rfl⟩
      obtain ⟨proto, hproto⟩ : ∃ x : UInt8, x = Bytes.get b 9 := ⟨_, rfl⟩
      rw [← hsrc, ← hproto]
      have f_src : ∀ m, execS (m + 21) p st (("src", u32 0) :: [("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)])
          (.call (some (.var "src")) "get32" [.lit 12 (some .w16)]) = .ok st [("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        intro m
        rw [execS_get32 p hP.get32 hP.get16 st _ b hb _ _ (UInt16.ofNat 12) m (by rw [ht 12 (by omega)]; omega)
          (by rw [ht 12 (by omega)]; omega) (evalE_lit16 ..)]
        simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 12 (by omega), hsrc]
      have e_proto : evalE p st [("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.index (.var "buf") (.lit 9 (some .w16))) = some (u8 proto) := by
        rw [ebyte [("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] 9 (by simp [List.lookup]) (by omega), hproto]
      -- options: the payload moves up to offset 20
      obtain ⟨n, hn⟩ : ∃ x : UInt16, x = tl - ihl := ⟨_, rfl⟩
      have hnN : n.toNat = tl.toNat - ihl.toNat := by
        rw [hn, UInt16.toNat_sub]
        have := tl.toNat_lt
        have := ihl.toNat_lt
        omega
      have econd8 : evalE p st [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .gt (.var "ihl") (.lit 20 (some .w16)))
          = some (.bool (decide (UInt16.ofNat 20 < ihl))) := by
        simp only [evalE_bin, evar st [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "ihl" (u16 ihl) (by simp [List.lookup]), evalE_lit16, Sem.binop, toUInt64_lt_iff]
      have e_sub : ∀ (S : St) (env : Env), env.lookup "tl" = some (u16 tl) → env.lookup "ihl" = some (u16 ihl) →
          evalE p S env (.bin .sub (.var "tl") (.var "ihl")) = some (u16 n) := by
        intro S env h1 h2
        simp only [evalE_bin, evar S env "tl" _ h1, evar S env "ihl" _ h2, Sem.binop, mask16_sub, hn]
      obtain ⟨b2, hb2def⟩ : ∃ x : ByteArray, x = if 20 < ihl.toNat then squeeze b ihl.toNat n.toNat else b :=
        ⟨_, rfl⟩
      have hsq := squeeze_spec b ihl.toNat hi20 n.toNat (by omega)
      have sb2 : b2.size = b.size := by
        rw [hb2def]; split
        · exact hsq.1
        · rfl
      have hb2get : ∀ j, j < n.toNat → Bytes.get b2 (20 + j) = Bytes.get b (ihl.toNat + j) := by
        intro j hj
        rw [hb2def]; split
        · exact hsq.2.1 j hj
        · have : ihl.toNat = 20 := by omega
          rw [this]
      have f_sq : execS (d + L.toNat + 475) p st [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] sqIte = .ok (setG st "buf" (bufVal b2)) [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] .normal := by
        simp only [sqIte, ip_input_fn]
        rcases Bool.eq_false_or_eq_true (decide (UInt16.ofNat 20 < ihl)) with h8 | h8
        · have c8 := econd8; conv at c8 => rhs; rw [h8]
          have h20 : 20 < ihl.toNat := by
            have := of_decide_eq_true h8
            rw [UInt16.lt_iff_toNat_lt, ht 20 (by omega)] at this
            exact this
          obtain ⟨v, hv⟩ := sq_loop p ihl [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (by simp [List.lookup]) (by simp [List.lookup]) n.toNat n.toNat 0 st b
            (.int .w16 (UInt64.ofNat 0)) (d + (L.toNat - n.toNat) + 463) hb (by omega)
            (by omega) (by omega) hsz
          rw [show n.toNat + 7 + (d + (L.toNat - n.toNat) + 463) = d + L.toNat + 470 by omega] at hv
          have t0 : (u16 (UInt16.ofNat 0)).toNat = 0 := rfl
          have tn : (u16 n).toNat = n.toNat := by
            show n.toUInt64.toNat = _
            rw [UInt16.toNat_toUInt64]
          simp only [sqBody, ip_input_fn] at hv
          simp only [execS_ite_true, c8, execB_succ, execL_cons, execL_nil, execS_at, execS_forRange, evalE_lit16,
            e_sub st [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (by simp [List.lookup]) (by simp [List.lookup]), Option.getD, t0, tn, hv, List.drop, List.length_cons, List.length_nil,
            Nat.sub_self]
          rw [hb2def, if_pos h20]
          rfl
        · have c8 := econd8; conv at c8 => rhs; rw [h8]
          have h20 : ¬ 20 < ihl.toNat := by
            have := of_decide_eq_false h8
            rw [UInt16.lt_iff_toNat_lt, ht 20 (by omega)] at this
            exact this
          simp only [execS_ite_false, c8, execB_succ, execL_nil, List.length_cons, List.length_nil, Nat.sub_self,
            List.drop_zero]
          rw [hb2def, if_neg h20, setG_same st _ _ hb]
      simp only [sqIte, ip_input_fn] at f_sq
      obtain ⟨st2, hst2⟩ : ∃ x : St, x = setG st "buf" (bufVal b2) := ⟨_, rfl⟩
      rw [← hst2] at f_sq
      have hb2 : st2.globals.lookup "buf" = some (bufVal b2) := by rw [hst2]; exact lookup_setG st _ _ _ hb
      have l2 : ∀ x : String, x ≠ "buf" → st2.globals.lookup x = st.globals.lookup x := by
        intro x hx; rw [hst2, lookup_setG_ne _ _ _ _ (Ne.symm hx)]
      have e_n := e_sub st2 [("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (by simp [List.lookup]) (by simp [List.lookup])
      -- the payload the Spec hands on is what now lies at offset 20
      have hpay : Bytes.slice (b.extract 0 L.toNat) ihl.toNat (tl.toNat - ihl.toNat)
          = b2.extract 20 (20 + n.toNat) := by
        have hs1 : (Bytes.slice (b.extract 0 L.toNat) ihl.toNat (tl.toNat - ihl.toNat)).size = n.toNat := by
          rw [Bytes.slice, ByteArray.size_extract, hpsz]; omega
        apply Bytes.ext_get
        · rw [hs1, ByteArray.size_extract, sb2]; omega
        · intro j hj
          rw [hs1] at hj
          rw [Bytes.slice, get_extract _ ihl.toNat _ j (by omega) (by rw [hpsz]; omega),
            get_extract b 0 _ (ihl.toNat + j) (by omega) hL, Nat.zero_add,
            get_extract b2 20 _ j (by omega) (by rw [sb2]; omega), hb2get j hj]
      rw [hpay]
      -- 9. broadcast is for UDP only
      have econd9 : evalE p st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .land (.bin .eq (.var "dst") (.lit 4294967295 (some .w32)))
          (.bin .ne (.var "proto") (.lit 17 (some .w8))))
          = some (.bool (dst == UInt32.ofNat 4294967295 && proto != UInt8.ofNat 17)) := by
        simp only [evalE_bin, evar st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "dst" (u32 dst) (by simp [List.lookup]), evar st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "proto" (u8 proto) (by simp [List.lookup]),
          evalE_lit, mask32_ofNat, mask8_ofNat, Sem.binop, toUInt64_eq_iff32, toUInt64_ne_iff8]
      have fd9 := fun m => execS_drop p st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_BROADCAST") 9 "broadcast"
        (eglob st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ (by rw [l2 _ (by decide)]; exact hK.d9) (by simp [List.lookup])) hP.r9
      rcases Bool.eq_false_or_eq_true (dst == UInt32.ofNat 4294967295 && proto != UInt8.ofNat 17) with h9 | h9
      · have c9 := econd9; conv at c9 => rhs; rw [h9]
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8, f_src, e_proto, f_sq, e_n, c9, fd9]
        refine ⟨_, rfl, ?_⟩
        have h9' : (dst == Spec.Ipv4.broadcast && proto != 17) = true := h9
        simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, Bool.not_true, Bool.false_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨b2, sb2, by rw [if_pos h9', hst2]⟩
      have c9 := econd9; conv at c9 => rhs; rw [h9]
      have h9' : (dst == Spec.Ipv4.broadcast && proto != 17) = false := h9
      -- 10. the protocol
      have eeq : ∀ k : Nat, evalE p st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] (.bin .eq (.var "proto") (.lit k (some .w8)))
          = some (.bool (proto == UInt8.ofNat k)) := by
        intro k
        simp only [evalE_bin, evar st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] "proto" (u8 proto) (by simp [List.lookup]), evalE_lit8, Sem.binop, toUInt64_eq_iff8]
      have hn20 : 20 + n.toNat ≤ b2.size := by rw [sb2]; omega
      have hsz2 : b2.size < 65536 := by rw [sb2]; exact hsz
      have hid2 : st2.globals.lookup "ip_id" = some (u16 id) := by rw [l2 _ (by decide)]; exact hid
      have hKi : IcmpConsts st2 ourIp := by rw [hst2]; exact icmpConsts_setG_buf st ourIp _ hK.icmp
      have hKu : UdpConsts st2 ourIp := by rw [hst2]; exact udpConsts_setG_buf st ourIp _ hK.udp
      have hw2 : st2.world = st.world := by rw [hst2]; rfl
      have hstip : ∀ (B : ByteArray) (I : UInt16), stIp st2 B I = stIp st B I := by
        intro B I; rw [hst2, stIp_setG_buf]
      rcases Bool.eq_false_or_eq_true (proto == UInt8.ofNat 1) with h10 | h10
      · -- ICMP
        have c10 := eeq 1; conv at c10 => rhs; rw [h10]
        have hp1 : proto = 1 := by simpa using h10
        obtain ⟨st', hs', hres⟩ := execS_icmp_input p hP.toIcmpProg st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] b2 id hb2 hid2 ourIp hKi
          (.var "src") (.var "n") src n (evar _ _ "src" _ (by simp [List.lookup])) (evar _ _ "n" _ (by simp [List.lookup])) hn20 hsz2
          (d + L.toNat + 468) (d + (L.toNat - n.toNat) + 217) (by omega)
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8, f_src, e_proto, f_sq, e_n, c9, fd9, c10, hs']
        refine ⟨st', rfl, ?_⟩
        simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, Bool.not_true, Bool.false_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨b2, sb2, ?_⟩
        simp only [h9', Bool.false_eq_true, if_false]
        simp only [hst2, stIp_setG_buf, world_setG, sb2] at hres
        rw [if_pos hp1]
        exact hres
      have c10 := eeq 1; conv at c10 => rhs; rw [h10]
      have hp1 : ¬ proto = 1 := by simpa using h10
      rcases Bool.eq_false_or_eq_true (proto == UInt8.ofNat 17) with h11 | h11
      · -- UDP
        have c11 := eeq 17; conv at c11 => rhs; rw [h11]
        have hp17 : proto = 17 := by simpa using h11
        obtain ⟨st', hs', hres⟩ := execS_udp_input p hP.toUdpProg st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] b2 id hb2 hid2 ourIp hKu
          (.var "src") (.var "dst") (.var "n") src dst n (evar _ _ "src" _ (by simp [List.lookup])) (evar _ _ "dst" _ (by simp [List.lookup]))
          (evar _ _ "n" _ (by simp [List.lookup])) hn20 hsz2 (d + L.toNat + 464) (d + (L.toNat - n.toNat) + 63) (by omega)
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8, f_src, e_proto, f_sq, e_n, c9, fd9, c10, c11, hs']
        refine ⟨st', rfl, ?_⟩
        simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, Bool.not_true, Bool.false_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨b2, sb2, ?_⟩
        simp only [h9', Bool.false_eq_true, if_false]
        simp only [hst2, stIp_setG_buf, world_setG, sb2] at hres
        rw [if_neg hp1, if_pos hp17]
        exact hres
      have c11 := eeq 17; conv at c11 => rhs; rw [h11]
      have hp17 : ¬ proto = 17 := by simpa using h11
      rcases Bool.eq_false_or_eq_true (proto == UInt8.ofNat 6) with h12 | h12
      · -- TCP
        have c12 := eeq 6; conv at c12 => rhs; rw [h12]
        have hp6 : proto = 6 := by simpa using h12
        obtain ⟨st', hs', hres⟩ := hTcp hL20 (by rw [← hproto]; exact hp6) b2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] src dst n sb2 hn20 (by omega)
          (by rw [← hst2]; exact evar _ _ "src" _ (by simp [List.lookup]))
          (by rw [← hst2]; exact evar _ _ "dst" _ (by simp [List.lookup]))
          (by rw [← hst2]; exact evar _ _ "n" _ (by simp [List.lookup]))
        rw [← hst2] at hs'
        simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8, f_src, e_proto, f_sq, e_n, c9, fd9, c10, c11, c12, hs']
        refine ⟨st', rfl, ?_⟩
        simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, Bool.not_true, Bool.false_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨b2, sb2, ?_⟩
        simp only [h9', Bool.false_eq_true, if_false]
        rw [if_neg hp1, if_neg hp17, if_pos hp6]
        exact ⟨n, rfl, hn20, hres⟩
      -- none of them: unsupported
      have h12 : (proto == UInt8.ofNat 6) = false := h12
      have hp6 : ¬ proto = 6 := by simpa using h12
      have c12 := eeq 6; conv at c12 => rhs; rw [h12]
      have fd10 := fun m => execS_drop p st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] m (.var "D_UNSUPPORTED_PROTOCOL") 10 "unsupported-protocol"
        (eglob st2 [("n", u16 n), ("proto", u8 proto), ("src", u32 src), ("dst", u32 dst), ("ff", u16 ff), ("tl", u16 tl), ("hok", Val.bool hok), ("hs", u16 hs), ("ihl", u16 ihl)] _ _ (by rw [l2 _ (by decide)]; exact hK.d10) (by simp [List.lookup])) hP.r10
      simp only [execS_ite_true, execS_ite_false, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, execS_decl_some, hz, hzb, hz32, execS_ret_none, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, c0, fd1, c1, fd2, e_ihl, c2, fd3, f_hs, f_hok, c3, fd4, Bool.not_true, Bool.not_false, f_tl, c4, fd5, f_ff, c5, fd6, c6, fd7, f_dst, c7, fd8, f_src, e_proto, f_sq, e_n, c9, fd9, c10, c11, c12, fd10]
      refine ⟨_, rfl, ?_⟩
      simp only [hL20', h1', h2', h3, h4', h5', h6', h7', if_false, Bool.not_true, Bool.false_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      refine ⟨b2, sb2, ?_⟩
      simp only [h9', Bool.false_eq_true, if_false]
      rw [if_neg hp1, if_neg hp17, if_neg hp6, hst2]

/-- **`ip_input` for a packet that is not TCP** (the statement M5.6 uses
so far): the drop line of the first check that fails, or `ipOutcome`. -/
theorem ip_input_refines (p : Prog) (hP : InProg p) (st : St) (b : ByteArray) (L id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hlen : st.globals.lookup "len" = some (u16 L))
    (hid : st.globals.lookup "ip_id" = some (u16 id)) (ourIp : UInt32) (hK : InConsts st ourIp)
    (hL : L.toNat ≤ b.size) (hsz : b.size < 65536) (hntcp : 20 ≤ L.toNat → Bytes.get b 9 ≠ 6) (d : Nat) :
    ∃ st', Sem.call (d + L.toNat + 500) p st "ip_input" [] = .ok none st' ∧
      match Spec.Ipv4.validate (b.extract 0 L.toNat) ourIp with
      | .error r => st' = dropSt st r
      | .ok (h, payload) => ipOutcome st st' b id ourIp h payload := by
  obtain ⟨st', hc, hres⟩ := ip_input_refines_tcp p hP st b L id hb hlen hid ourIp hK hL hsz d
    (fun _ _ _ _ _ => False) (fun h20 h6 => absurd h6 (hntcp h20))
  refine ⟨st', hc, ?_⟩
  cases hv : Spec.Ipv4.validate (b.extract 0 L.toNat) ourIp with
  | error r => rw [hv] at hres; exact hres
  | ok hp =>
    obtain ⟨h, payload⟩ := hp
    rw [hv] at hres
    exact ipOutcome_of st st' b id ourIp h payload hres


/-- The stack's initial globals have the constants the receive path reads. -/
theorem net_consts_in (inputs : Array Trace.Input) : InConsts (Sem.initial Net.prog inputs) Spec.ourIpDefault :=
  ⟨net_consts inputs, net_consts_udp inputs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- the checked stack is an `InProg` (with the `#guard`s at the functions)
#guard (Net.prog.check.toOption.map fun q => (List.range 11).map fun i => q.dropReasons[i]?)
  == some [some "oversize-frame", some "short-packet", some "bad-version", some "bad-ihl", some "bad-ip-checksum",
    some "bad-length", some "fragment", some "ttl-zero", some "not-for-us", some "broadcast",
    some "unsupported-protocol"]

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.ip_input_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ip_input_refines

/-- info: 'Ember.Proof.Refine.ip_input_refines_tcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ip_input_refines_tcp

end Ember.Proof.Refine
