import Ember.Proof.RefineSlip
import Ember.Proof.Headers

/-!
# Ember.Proof.RefineIp — sending an IP packet (plan M5.5)

`ip_send` writes a 20-byte header in front of the payload that is
already in the packet buffer, computes the header checksum and hands the
packet to `slip_send`.  Two theorems:

* `ip_send_spec` — what the call does to the state, with the buffer
  written out as the function's own sequence of writes (`ipHeader`);
* `ipHeader_extract` — those bytes are `Spec.Ipv4.header` followed by
  the payload, byte for byte, the checksum included.

Together (`ip_send_refines`): the frame transmitted is the SLIP encoding
of `Spec.Ipv4.packet`, which is what `Spec.sendIp` transmits.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-! ## More about globals -/

theorem setFirst_comm (l : Env) (x y : String) (v w : Val) (h : x ≠ y) :
    setFirst (setFirst l x v) y w = setFirst (setFirst l y w) x v := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, u⟩ := hd
    by_cases hx : k = x
    · subst hx
      have hy : (k == y) = false := by simp [h]
      simp [setFirst, hy]
    · have hx' : (k == x) = false := by simp [hx]
      by_cases hy : k = y
      · subst hy; simp [setFirst, hx']
      · have hy' : (k == y) = false := by simp [hy]
        simp [setFirst, hx', hy', ih]

theorem setG_comm (st : St) (x y : String) (v w : Val) (h : x ≠ y) :
    setG (setG st x v) y w = setG (setG st y w) x v := by
  simp only [setG, setFirst_comm _ x y v w h]

theorem setG_setG (st : St) (x : String) (v w : Val) : setG (setG st x v) x w = setG st x w := by
  simp [setG, setFirst_setFirst]

theorem setFirst_same (l : Env) (x : String) (v : Val) (h : l.lookup x = some v) : setFirst l x v = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, u⟩ := hd
    by_cases hk : k = x
    · subst hk
      simp [List.lookup] at h
      simp [setFirst, h]
    · have hk' : (k == x) = false := by simp [hk]
      have hk'' : (x == k) = false := by simp [Ne.symm hk]
      simp only [List.lookup, hk''] at h
      simp [setFirst, hk', ih h]

theorem setG_same (st : St) (x : String) (v : Val) (h : st.globals.lookup x = some v) : setG st x v = st := by
  simp [setG, setFirst_same _ _ _ h]

/-- `buf[k] := x` for a literal index. -/
theorem assign_buf_lit (p : Prog) (st : St) (env : Env) (b : ByteArray) (k : Nat) (x : UInt8)
    (hl : env.lookup "buf" = none) (hb : st.globals.lookup "buf" = some (bufVal b))
    (hk : k < b.size) (hk' : k < 65536) :
    assign p st env (.index (.var "buf") (.lit k (some .w16))) (u8 x)
      = some (setG st "buf" (bufVal (Bytes.set b k x)), env) := by
  have ht : (UInt16.ofNat k).toNat = k := by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk'
  have := assign_buf p st env b (.lit k (some .w16)) (UInt16.ofNat k) x hl hb
    (by rw [evalE_lit, mask16_ofNat]) (by omega)
  rw [ht] at this
  exact this

/-- A 16-bit literal. -/
theorem evalE_lit16 (p : Prog) (st : St) (env : Env) (k : Nat) :
    evalE p st env (.lit k (some .w16)) = some (u16 (UInt16.ofNat k)) := by
  rw [evalE_lit, mask16_ofNat]

theorem mask8_ofNat (k : Nat) : mask .w8 (UInt64.ofNat k) = (UInt8.ofNat k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask8, UInt8.toNat_toUInt64, UInt64.toNat_ofNat', UInt8.toNat_ofNat']
  omega

/-- An 8-bit literal. -/
theorem evalE_lit8 (p : Prog) (st : St) (env : Env) (k : Nat) :
    evalE p st env (.lit k (some .w8)) = some (u8 (UInt8.ofNat k)) := by
  rw [evalE_lit, mask8_ofNat]

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## Calls as statements -/

/-- A call of `set32` as a statement. -/
theorem execS_set32 (p : Prog) (hp : p.fn? "set32" = some set32) (hs : p.fn? "set16" = some set16)
    (st : St) (env : Env) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) (eo ev : Expr)
    (o : UInt16) (v : UInt32) (n : Nat) (ho : o.toNat + 3 < b.size) (ho' : o.toNat + 3 < 65536)
    (he : evalE p st env eo = some (u16 o)) (hv : evalE p st env ev = some (u32 v)) :
    execS (n + 21) p st env (.call none "set32" [eo, ev]) =
      .ok (withBuf st (Bytes.set32 b o.toNat v)) env .normal :=
  execS_call_val p st env (n + 20) none "set32" [eo, ev] hp (by simp [set32]) (by simp [evalArgs, he, hv])
    (set32_refines p hp hs st b hb o v ho ho' n)

/-- A call of `csum` as a statement. -/
theorem execS_csum (p : Prog) (hc : p.fn? "csum" = some csum) (hg : p.fn? "get16" = some get16)
    (ha : p.fn? "add16" = some add16) (st : St) (env : Env) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (dst : Option Expr) (eo en ei : Expr) (o n ini : UInt16)
    (hr : o.toNat + n.toNat ≤ b.size) (hsz : b.size ≤ 65536)
    (heo : evalE p st env eo = some (u16 o)) (hen : evalE p st env en = some (u16 n))
    (hei : evalE p st env ei = some (u16 ini)) (m d : Nat) (hm : m = d + n.toNat / 2 + 61) :
    execS m p st env (.call dst "csum" [eo, en, ei]) =
      storeResult p st env dst (some (u16 (Spec.Checksum.sum b o.toNat n.toNat ini))) := by
  subst hm
  exact execS_call_val p st env _ dst "csum" [eo, en, ei] hc (by simp [csum]) (by simp [evalArgs, heo, hen, hei])
    (csum_refines p hc hg ha st b hb o n ini hr hsz d)

/-- A call of `slip_send` as a statement. -/
theorem execS_slip_send (p : Prog) (hp : p.fn? "slip_send" = some slip_send) (st : St) (env : Env)
    (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) (en : Expr) (n : UInt16)
    (hn : n.toNat ≤ b.size) (he : evalE p st env en = some (u16 n)) (m d : Nat) (hm : m = d + n.toNat + 41) :
    execS m p st env (.call none "slip_send" [en]) =
      .ok (txOut st (st.world.frame ++ Spec.Slip.encode (b.extract 0 n.toNat))) env .normal := by
  subst hm
  exact execS_call_val p st env _ none "slip_send" [en] hp (by simp [slip_send]) (by simp [evalArgs, he])
    (slip_send_refines p hp st b hb n hn d)

/-! ## `ip_send` -/

def ip_send : Fn := checked_fn% Net.prog, "ip_send"
#guard (Net.prog.check.toOption.bind (·.fn? "ip_send")) == some ip_send

/-- A program with the functions `ip_send` uses. -/
structure IpProg (p : Prog) : Prop where
  add16 : p.fn? "add16" = some add16
  get16 : p.fn? "get16" = some get16
  set16 : p.fn? "set16" = some set16
  set32 : p.fn? "set32" = some set32
  csum : p.fn? "csum" = some csum
  slip_send : p.fn? "slip_send" = some slip_send
  ip_send : p.fn? "ip_send" = some ip_send

/-- The buffer after `ip_send` has written the header in front of the
payload: the writes of the function, in its order. -/
def ipHeader (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8) :
    ByteArray :=
  let b := Bytes.set b 0 0x45
  let b := Bytes.set b 1 0
  let b := Bytes.set16 b 2 (20 + n)
  let b := Bytes.set16 b 4 id
  let b := Bytes.set b 6 (if proto == 1 then 0 else 0x40)
  let b := Bytes.set b 7 0
  let b := Bytes.set b 8 ttl
  let b := Bytes.set b 9 proto
  let b := Bytes.set16 b 10 0
  let b := Bytes.set32 b 12 src
  let b := Bytes.set32 b 16 dst
  Bytes.set16 b 10 (~~~ Spec.Checksum.sum b 0 20 0)

@[simp] theorem size_set32 (b : ByteArray) (i : Nat) (v : UInt32) : (Bytes.set32 b i v).size = b.size := by
  simp [Bytes.set32]

/-- The globals `ip_send` writes, set. -/
def stIp (st : St) (b : ByteArray) (id : UInt16) : St := setG (setG st "ip_id" (u16 id)) "buf" (bufVal b)

/-- The `if` of `ip_send`. -/
def ipSendIte : Stmt :=
  match ip_send.body with
  | [_, _, _, _, _, .at _ s, _, _, _, _, _, _, _, _, _, _] => s
  | _ => .brk

/-- `ip_send` from a state whose `buf` and `ip_id` are set. -/
theorem ip_send_core (p : Prog) (hP : IpProg p) (st : St) (vb vi : Val)
    (hb0 : st.globals.lookup "buf" = some vb) (hi0 : st.globals.lookup "ip_id" = some vi)
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (ttl : UInt8) (httl : st.globals.lookup "TTL" = some (u8 ttl))
    (b : ByteArray) (id : UInt16) (proto : UInt8) (dst : UInt32) (n : UInt16)
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat) :
    Sem.call (d + n.toNat + 150) p (stIp st b id) "ip_send" [u8 proto, u32 dst, u16 n]
      = .ok none (txOut (stIp st (ipHeader b proto id ourIp dst n ttl) (id + 1))
          (st.world.frame ++ Spec.Slip.encode ((ipHeader b proto id ourIp dst n ttl).extract 0 (20 + n.toNat)))) := by
  -- the state
  have lbuf : ∀ (B : ByteArray) (I : UInt16), (stIp st B I).globals.lookup "buf" = some (bufVal B) := by
    intro B I; simp [stIp, lookup_setG_self, lookup_setG_ne, hb0]
  have lid : ∀ (B : ByteArray) (I : UInt16), (stIp st B I).globals.lookup "ip_id" = some (u16 I) := by
    intro B I; simp [stIp, lookup_setG_self, lookup_setG_ne, hi0]
  have lip : ∀ (B : ByteArray) (I : UInt16), (stIp st B I).globals.lookup "OUR_IP" = some (u32 ourIp) := by
    intro B I; simp [stIp, lookup_setG_ne, hip]
  have lttl : ∀ (B : ByteArray) (I : UInt16), (stIp st B I).globals.lookup "TTL" = some (u8 ttl) := by
    intro B I; simp [stIp, lookup_setG_ne, httl]
  have wS : ∀ (B : ByteArray) (I : UInt16) (B' : ByteArray), withBuf (stIp st B I) B' = stIp st B' I := by
    intro B I B'; simp [stIp, withBuf_eq, setG_setG]
  have iS : ∀ (B : ByteArray) (I I' : UInt16), setG (stIp st B I) "ip_id" (u16 I') = stIp st B I' := by
    intro B I I'
    simp only [stIp]
    rw [setG_comm _ "buf" "ip_id" _ _ (by decide), setG_setG]
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have h20n : (UInt16.ofNat 20 + n).toNat = 20 + n.toNat := by
    have := ht 20 (by omega)
    simp only [UInt16.toNat_add, this]; omega
  -- the buffer after each call
  let env0 : Env := [("proto", u8 proto), ("dst", u32 dst), ("n", u16 n)]
  let B2 := Bytes.set (Bytes.set b 0 (UInt8.ofNat 69)) 1 (UInt8.ofNat 0)
  let B3 := Bytes.set16 B2 2 (UInt16.ofNat 20 + n)
  let B4 := Bytes.set16 B3 4 id
  let B5 := Bytes.set B4 6 (if proto == UInt8.ofNat 1 then UInt8.ofNat 0 else UInt8.ofNat 64)
  let B8 := Bytes.set (Bytes.set (Bytes.set B5 7 (UInt8.ofNat 0)) 8 ttl) 9 proto
  let B9 := Bytes.set16 B8 10 (UInt16.ofNat 0)
  let B10 := Bytes.set32 B9 12 ourIp
  let B11 := Bytes.set32 B10 16 dst
  let C := Spec.Checksum.sum B11 0 20 0
  let B12 := Bytes.set16 B11 10 (~~~ C)
  let I1 := id + UInt16.ofNat 1
  -- expressions
  have evar : ∀ (S : St) (env : Env) (x : String) (v : Val), env.lookup x = some v →
      evalE p S env (.var x) = some v := by
    intro S env x v h; simp [evalE, lookup, h]
  have e20n : ∀ (S : St) (env : Env), env.lookup "n" = some (u16 n) →
      evalE p S env (.bin .add (.lit 20 (some .w16)) (.var "n")) = some (u16 (UInt16.ofNat 20 + n)) := by
    intro S env h
    simp only [evalE_bin, evalE_lit16, evar S env "n" _ h, Sem.binop, mask16_add]
  have eglob : ∀ (S : St) (x : String) (v : Val), S.globals.lookup x = some v → env0.lookup x = none →
      evalE p S env0 (.var x) = some v := by
    intro S x v h h'; simp [evalE, lookup, h, h']
  -- statements
  have A : ∀ (B : ByteArray) (I : UInt16) (k : Nat) (x : UInt8), k < B.size → k < 65536 →
      assign p (stIp st B I) env0 (.index (.var "buf") (.lit k (some .w16))) (u8 x)
        = some (stIp st (Bytes.set B k x) I, env0) := by
    intro B I k x hk hk'
    rw [assign_buf_lit p _ env0 B k x (by simp [env0, List.lookup]) (lbuf B I) hk hk', ← withBuf_eq, wS]
  have sB2 : B2.size = b.size := by simp [B2]
  have sB3 : B3.size = b.size := by simp [B3, sB2]
  have sB4 : B4.size = b.size := by simp [B4, sB3]
  have sB5 : B5.size = b.size := by simp [B5, sB4]
  have sB8 : B8.size = b.size := by simp [B8, sB5]
  have sB9 : B9.size = b.size := by simp [B9, sB8]
  have sB10 : B10.size = b.size := by simp [B10, sB9]
  have sB11 : B11.size = b.size := by simp [B11, sB10]
  have sB12 : B12.size = b.size := by simp [B12, sB11]
  have c1 : ∀ m, execS (m + 9) p (stIp st B2 id) env0
      (.call none "set16" [.lit 2 (some .w16), .bin .add (.lit 20 (some .w16)) (.var "n")])
      = .ok (stIp st B3 id) env0 .normal := by
    intro m
    rw [execS_set16 p hP.set16 _ env0 B2 (lbuf _ _) _ _ (UInt16.ofNat 2) (UInt16.ofNat 20 + n) m
      (by rw [ht 2 (by omega)]; omega) (by rw [ht 2 (by omega)]; omega) (evalE_lit16 ..)
      (e20n _ _ (by simp [env0, List.lookup])), wS, ht 2 (by omega)]
  have c2 : ∀ m, execS (m + 9) p (stIp st B3 id) env0 (.call none "set16" [.lit 4 (some .w16), .var "ip_id"])
      = .ok (stIp st B4 id) env0 .normal := by
    intro m
    rw [execS_set16 p hP.set16 _ env0 B3 (lbuf _ _) _ _ (UInt16.ofNat 4) id m
      (by rw [ht 4 (by omega)]; omega) (by rw [ht 4 (by omega)]; omega) (evalE_lit16 ..)
      (eglob _ _ _ (lid _ _) (by simp [env0, List.lookup])), wS, ht 4 (by omega)]
  have c3 : assign p (stIp st B4 id) env0 (.var "ip_id") (u16 I1) = some (stIp st B4 I1, env0) := by
    rw [assign_var]
    simp [env0, List.lookup, lid, iS]
  have eid1 : evalE p (stIp st B4 id) env0 (.bin .add (.var "ip_id") (.lit 1 (some .w16))) = some (u16 I1) := by
    simp only [evalE_bin, evalE_lit16, eglob _ _ _ (lid _ _) (by simp [env0, List.lookup] : env0.lookup "ip_id" = none),
      Sem.binop, mask16_add, I1]
  have c4 : ∀ m, execS (m + 5) p (stIp st B4 I1) env0 ipSendIte = .ok (stIp st B5 I1) env0 .normal := by
    intro m
    have ep : evalE p (stIp st B4 I1) env0 (.bin .eq (.var "proto") (.lit 1 (some .w8)))
        = some (.bool (proto == UInt8.ofNat 1)) := by
      simp only [evalE_bin, evalE_lit8, evar _ env0 "proto" (u8 proto) (by simp [env0, List.lookup]), Sem.binop,
        toUInt64_eq_iff8]
    simp only [ipSendIte, ip_send, execS_ite, ep, Val.toBool, execB_succ, execL_cons, execL_nil, execS_at,
      execS_assign, evalE_lit8]
    cases hp1 : proto == UInt8.ofNat 1 with
    | true =>
      simp only [if_true, A B4 I1 6 (UInt8.ofNat 0) (by omega) (by omega), B5, hp1]
      rfl
    | false =>
      simp only [Bool.false_eq_true, if_false, A B4 I1 6 (UInt8.ofNat 64) (by omega) (by omega), B5, hp1]
      rfl
  simp only [ipSendIte, ip_send] at c4
  have c5 : ∀ m, execS (m + 9) p (stIp st B8 I1) env0
      (.call none "set16" [.lit 10 (some .w16), .lit 0 (some .w16)]) = .ok (stIp st B9 I1) env0 .normal := by
    intro m
    rw [execS_set16 p hP.set16 _ env0 B8 (lbuf _ _) _ _ (UInt16.ofNat 10) (UInt16.ofNat 0) m
      (by rw [ht 10 (by omega)]; omega) (by rw [ht 10 (by omega)]; omega) (evalE_lit16 ..) (evalE_lit16 ..),
      wS, ht 10 (by omega)]
  have c6 : ∀ m, execS (m + 21) p (stIp st B9 I1) env0
      (.call none "set32" [.lit 12 (some .w16), .var "OUR_IP"]) = .ok (stIp st B10 I1) env0 .normal := by
    intro m
    rw [execS_set32 p hP.set32 hP.set16 _ env0 B9 (lbuf _ _) _ _ (UInt16.ofNat 12) ourIp m
      (by rw [ht 12 (by omega)]; omega) (by rw [ht 12 (by omega)]; omega) (evalE_lit16 ..)
      (eglob _ _ _ (lip _ _) (by simp [env0, List.lookup])), wS, ht 12 (by omega)]
  have c7 : ∀ m, execS (m + 21) p (stIp st B10 I1) env0
      (.call none "set32" [.lit 16 (some .w16), .var "dst"]) = .ok (stIp st B11 I1) env0 .normal := by
    intro m
    rw [execS_set32 p hP.set32 hP.set16 _ env0 B10 (lbuf _ _) _ _ (UInt16.ofNat 16) dst m
      (by rw [ht 16 (by omega)]; omega) (by rw [ht 16 (by omega)]; omega) (evalE_lit16 ..)
      (evar _ env0 "dst" _ (by simp [env0, List.lookup])), wS, ht 16 (by omega)]
  have c8 : ∀ m, execS (m + 71) p (stIp st B11 I1) (("c", u16 0) :: env0)
      (.call (some (.var "c")) "csum" [.lit 0 (some .w16), .lit 20 (some .w16), .lit 0 (some .w16)])
      = .ok (stIp st B11 I1) (("c", u16 C) :: env0) .normal := by
    intro m
    rw [execS_csum p hP.csum hP.get16 hP.add16 _ _ B11 (lbuf _ _) _ _ _ _ (UInt16.ofNat 0) (UInt16.ofNat 20)
      (UInt16.ofNat 0) (by rw [ht 0 (by omega), ht 20 (by omega)]; omega) (by omega) (evalE_lit16 ..)
      (evalE_lit16 ..) (evalE_lit16 ..) (m + 71) m (by rw [ht 20 (by omega)])]
    simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 0 (by omega),
      ht 20 (by omega), C]
    rfl
  have c9 : ∀ m, execS (m + 9) p (stIp st B11 I1) (("c", u16 C) :: env0)
      (.call none "set16" [.lit 10 (some .w16), .un .bnot (.var "c")])
      = .ok (stIp st B12 I1) (("c", u16 C) :: env0) .normal := by
    intro m
    have ec : evalE p (stIp st B11 I1) (("c", u16 C) :: env0) (.un .bnot (.var "c")) = some (u16 (~~~ C)) := by
      simp only [evalE, lookup, List.lookup, beq_self_eq_true, mask16_not]
    rw [execS_set16 p hP.set16 _ _ B11 (lbuf _ _) _ _ (UInt16.ofNat 10) (~~~ C) m
      (by rw [ht 10 (by omega)]; omega) (by rw [ht 10 (by omega)]; omega) (evalE_lit16 ..) ec, wS,
      ht 10 (by omega)]
  have c10 : execS (d + n.toNat + 132) p (stIp st B12 I1) (("c", u16 C) :: env0)
      (.call none "slip_send" [.bin .add (.lit 20 (some .w16)) (.var "n")])
      = .ok (txOut (stIp st B12 I1) (st.world.frame ++ Spec.Slip.encode (B12.extract 0 (20 + n.toNat))))
          (("c", u16 C) :: env0) .normal := by
    rw [execS_slip_send p hP.slip_send _ _ B12 (lbuf _ _) _ (UInt16.ofNat 20 + n) (by rw [h20n]; omega)
      (e20n _ _ (by simp [env0, List.lookup])) _ (d + 71) (by rw [h20n]; omega), h20n]
    rfl
  have e_ttl : ∀ (B : ByteArray) (I : UInt16), evalE p (stIp st B I) env0 (.var "TTL") = some (u8 ttl) :=
    fun B I => eglob _ _ _ (lttl B I) (by simp [env0, List.lookup])
  have e_proto : ∀ S : St, evalE p S env0 (.var "proto") = some (u8 proto) :=
    fun S => evar S env0 "proto" _ (by simp [env0, List.lookup])
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  simp only [B2, B3, B4, B5, B8, B9, B10, B11, B12, C, I1, env0] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 eid1 e_ttl e_proto A
  simp (disch := first | omega | (simp only [Bytes.size_set, Bytes.size_set16, size_set32]; omega)) only
    [Sem.call, hP.ip_send, ip_send, execB_succ, execL_cons, execL_nil, execS_at, List.map, List.zip, List.zipWith,
     execS_assign, execS_decl_none, hz, evalE_lit8, A, c1, c2, eid1, c3, c4, e_ttl, e_proto, c5, c6, c7, c8, c9, c10]
  rfl

/-- **`ip_send`**: from a state with the packet buffer `b` (the payload
at offset 20) and identification `id`, the call writes the header in
front, takes the next identification and transmits the `20 + n` bytes as
one SLIP frame. -/
theorem ip_send_spec (p : Prog) (hP : IpProg p) (st : St) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (ttl : UInt8) (httl : st.globals.lookup "TTL" = some (u8 ttl))
    (proto : UInt8) (dst : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat) :
    Sem.call (d + n.toNat + 150) p st "ip_send" [u8 proto, u32 dst, u16 n]
      = .ok none (txOut (stIp st (ipHeader b proto id ourIp dst n ttl) (id + 1))
          (st.world.frame ++ Spec.Slip.encode ((ipHeader b proto id ourIp dst n ttl).extract 0 (20 + n.toNat)))) := by
  have h0 : stIp st b id = st := by
    have e1 : setG st "ip_id" (u16 id) = st := setG_same st _ _ hid
    simp only [stIp, e1, setG_same st _ _ hb]
  have := ip_send_core p hP st _ _ hb hid ourIp hip ttl httl b id proto dst n hn hsz d
  rwa [h0] at this

/-! ## The packet `ip_send` transmits is the Spec's -/

theorem get_set_ne (b : ByteArray) (i j : Nat) (v : UInt8) (h : i ≠ j) : Bytes.get (Bytes.set b i v) j = Bytes.get b j := by
  simp [Bytes.get_set, h]

theorem get_set32_ne (b : ByteArray) (i j : Nat) (v : UInt32) (h : j < i ∨ i + 3 < j) :
    Bytes.get (Bytes.set32 b i v) j = Bytes.get b j := by
  simp only [Bytes.set32]
  rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega),
    get_set_ne _ _ _ _ (by omega)]

theorem get_extract (b : ByteArray) (s e j : Nat) (h : s + j < e) (he : e ≤ b.size) :
    Bytes.get (b.extract s e) j = Bytes.get b (s + j) := by
  have h1 : j < (b.extract s e).size := by simp [ByteArray.size_extract]; omega
  have h2 : s + j < b.size := by omega
  have h3 : j < min e b.size - s := by omega
  simp [Bytes.get, h1, h2, h3, ByteArray.getElem_eq_getElem_data]
  rfl

/-- The buffer `ip_send` leaves, before the checksum is filled in. -/
def ipHeader0 (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8) :
    ByteArray :=
  let b := Bytes.set b 0 0x45
  let b := Bytes.set b 1 0
  let b := Bytes.set16 b 2 (20 + n)
  let b := Bytes.set16 b 4 id
  let b := Bytes.set b 6 (if proto == 1 then 0 else 0x40)
  let b := Bytes.set b 7 0
  let b := Bytes.set b 8 ttl
  let b := Bytes.set b 9 proto
  let b := Bytes.set16 b 10 0
  let b := Bytes.set32 b 12 src
  Bytes.set32 b 16 dst

theorem ipHeader_eq (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8) :
    ipHeader b proto id src dst n ttl
      = Bytes.set16 (ipHeader0 b proto id src dst n ttl) 10
          (~~~ Spec.Checksum.sum (ipHeader0 b proto id src dst n ttl) 0 20 0) := rfl

theorem ipHeader0_tail (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8)
    (i : Nat) (hi : 20 ≤ i) : Bytes.get (ipHeader0 b proto id src dst n ttl) i = Bytes.get b i := by
  simp (disch := omega) only [ipHeader0, get_set_ne, Bytes.get_set16_ne, get_set32_ne]

theorem ipHeader0_head (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8)
    (hb : 20 ≤ b.size) (i : Nat) (hi : i < 20) :
    Bytes.get (ipHeader0 b proto id src dst n ttl) i
      = (Spec.Ipv4.headerBytes proto id src dst n.toNat ttl).getD i 0 := by
  have hlen : UInt16.ofNat (20 + n.toNat) = 20 + n := by
    apply UInt16.toNat_inj.mp
    have t : (20 : UInt16).toNat = 20 := rfl
    simp only [UInt16.toNat_ofNat', UInt16.toNat_add, t]
  have g0 : 0 < b.size := by omega
  have g1 : 1 < b.size := by omega
  have g2 : 2 < b.size := by omega
  have g3 : 3 < b.size := by omega
  have g4 : 4 < b.size := by omega
  have g5 : 5 < b.size := by omega
  have g6 : 6 < b.size := by omega
  have g7 : 7 < b.size := by omega
  have g8 : 8 < b.size := by omega
  have g9 : 9 < b.size := by omega
  have g10 : 10 < b.size := by omega
  have g11 : 11 < b.size := by omega
  have g12 : 12 < b.size := by omega
  have g13 : 13 < b.size := by omega
  have g14 : 14 < b.size := by omega
  have g15 : 15 < b.size := by omega
  have g16 : 16 < b.size := by omega
  have g17 : 17 < b.size := by omega
  have g18 : 18 < b.size := by omega
  have g19 : 19 < b.size := by omega
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ipHeader0, Bytes.get_set, Bytes.get_set16, Bytes.set32, Spec.Ipv4.headerBytes, Spec.Ipv4.dfFor, Spec.Ipv4.protoIcmp, hlen, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19]

@[simp] theorem size_ipHeader0 (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16)
    (ttl : UInt8) : (ipHeader0 b proto id src dst n ttl).size = b.size := by
  simp [ipHeader0]

@[simp] theorem size_ipHeader (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16)
    (ttl : UInt8) : (ipHeader b proto id src dst n ttl).size = b.size := by
  rw [ipHeader_eq, Bytes.size_set16, size_ipHeader0]

/-- **The bytes `ip_send` transmits are the Spec's packet**
(`Spec.Ipv4.header` in front of the payload): the same header fields,
the same checksum. -/
theorem ipHeader_extract (b : ByteArray) (proto : UInt8) (id : UInt16) (src dst : UInt32) (n : UInt16) (ttl : UInt8)
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) :
    (ipHeader b proto id src dst n ttl).extract 0 (20 + n.toNat)
      = Spec.Ipv4.header proto id src dst n.toNat ttl ++ b.extract 20 (20 + n.toNat) := by
  have hs0 : (ipHeader0 b proto id src dst n ttl).size = b.size := size_ipHeader0 ..
  have hhead : ∀ i, i < 20 → Bytes.get (ipHeader0 b proto id src dst n ttl) i
      = (Spec.Ipv4.headerBytes proto id src dst n.toNat ttl).getD i 0 :=
    fun i hi => ipHeader0_head b proto id src dst n ttl (by omega) i hi
  have htail : ∀ i, 20 ≤ i → Bytes.get (ipHeader0 b proto id src dst n ttl) i = Bytes.get b i :=
    fun i hi => ipHeader0_tail b proto id src dst n ttl i hi
  rw [ipHeader_eq, Spec.Ipv4.header_eq]
  generalize ipHeader0 b proto id src dst n ttl = B0 at *
  generalize hH : Spec.Ipv4.headerBytes proto id src dst n.toNat ttl = H at *
  have hHlen : H.length = 20 := by rw [← hH]; rfl
  have hsum : Spec.Checksum.sum B0 0 20 0 = Spec.Checksum.sum (Bytes.ofList H) 0 20 0 := by
    apply Spec.Checksum.sum_congr
    intro i hi
    rw [Nat.zero_add, hhead i hi, Bytes.get_ofList]
  simp only [Spec.Checksum.checksum, hsum]
  generalize (~~~ Spec.Checksum.sum (Bytes.ofList H) 0 20 0) = c
  have hpl : (b.extract 20 (20 + n.toNat)).size = n.toNat := by rw [ByteArray.size_extract]; omega
  have hsz1 : ((Bytes.set16 B0 10 c).extract 0 (20 + n.toNat)).size = 20 + n.toNat := by
    rw [ByteArray.size_extract, Bytes.size_set16, hs0]; omega
  have hsz2 : (Bytes.set16 (Bytes.ofList H) 10 c).size = 20 := by rw [Bytes.size_set16, Bytes.size_ofList, hHlen]
  apply Bytes.ext_get
  · rw [hsz1, ByteArray.size_append, hsz2, hpl]
  · intro i hi
    have hi' : i < 20 + n.toNat := by rw [hsz1] at hi; exact hi
    rw [get_extract _ 0 _ i (by omega) (by rw [Bytes.size_set16, hs0]; omega), Nat.zero_add, Bytes.get_append, hsz2]
    by_cases h20 : i < 20
    · rw [if_pos h20, Bytes.get_set16, Bytes.get_set16, hs0, Bytes.size_ofList, hHlen]
      by_cases h11 : 10 + 1 = i
      · have : 10 + 1 < b.size := by omega
        subst h11; simp [this]
      · by_cases h10 : 10 = i
        · have : 10 < b.size := by omega
          subst h10; simp [this]
        · simp only [h11, h10, false_and, if_false]
          rw [hhead i h20, Bytes.get_ofList]
    · rw [if_neg h20, Bytes.get_set16_ne (by omega), htail _ (by omega),
        get_extract _ 20 _ (i - 20) (by omega) (by omega)]
      congr 1; omega

/-- **`ip_send` sends the Spec's packet** (what `Spec.sendIp` puts on a
SLIP link): `Spec.Ipv4.packet` for this protocol, the current
identification, our address, the destination and the payload found at
`buf[20, 20+n)`, SLIP-encoded, as one frame; and the identification
counter moves on. -/
theorem ip_send_refines (p : Prog) (hP : IpProg p) (st : St) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (httl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault))
    (proto : UInt8) (dst : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat) :
    Sem.call (d + n.toNat + 150) p st "ip_send" [u8 proto, u32 dst, u16 n]
      = .ok none (txOut (stIp st (ipHeader b proto id ourIp dst n Spec.ttlDefault) (id + 1))
          (st.world.frame ++
            Spec.Slip.encode (Spec.Ipv4.packet proto id ourIp dst (b.extract 20 (20 + n.toNat))))) := by
  have hpl : (b.extract 20 (20 + n.toNat)).size = n.toNat := by rw [ByteArray.size_extract]; omega
  rw [ip_send_spec p hP st b id hb hid ourIp hip _ httl proto dst n hn hsz d, ipHeader_extract _ _ _ _ _ _ _ hn hsz,
    Spec.Ipv4.packet, hpl]

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.ip_send_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ip_send_refines

end Ember.Proof.Refine
