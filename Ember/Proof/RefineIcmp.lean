import Ember.Proof.RefineIp
import Ember.Proof.Icmp

/-!
# Ember.Proof.RefineIcmp — the ICMP echo reply (plan M5.5)

`icmp_input` against `Spec.Icmp.reply` followed by `Spec.sendIp`: the
same three checks with the same drop reasons, and for an echo request the
same reply — built in place in the packet buffer by changing one byte and
updating the checksum (RFC 1624) — in the same IPv4 packet.

`Ember.Proof.Icmp.reply_verifies` (M5.1) says that this reply's checksum
verifies; here the Ember code is shown to produce exactly that reply.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-- The state after a `drop` line has gone to the trace. -/
def dropSt (st : St) (r : String) : St := { st with world := st.world.emit (.drop r) }

@[simp] theorem globals_dropSt (st : St) (r : String) : (dropSt st r).globals = st.globals := rfl

/-- `trace.drop(e)`. -/
theorem execS_drop (p : Prog) (st : St) (env : Env) (n : Nat) (e : Expr) (k : UInt8) (r : String)
    (he : evalE p st env e = some (u8 k)) (hr : p.dropReasons[k.toNat]? = some r) :
    execS (n + 1) p st env (.eff none .drop [e]) = .ok (dropSt st r) env .normal := by
  have hk : (u8 k).toNat = k.toNat := by simp [Val.toNat]
  simp [execS_eff, evalArgs, he, Sem.effect, storeResult, dropSt, hk, List.getD, hr]

theorem stIp_setG_buf (st : St) (v : Val) (B : ByteArray) (I : UInt16) :
    Ember.Proof.Refine.stIp (setG st "buf" v) B I = Ember.Proof.Refine.stIp st B I := by
  simp only [Ember.Proof.Refine.stIp]
  rw [setG_comm _ "buf" "ip_id" _ _ (by decide), setG_setG]

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## Calls as statements -/

theorem execS_verifies (p : Prog) (hp : p.fn? "verifies" = some verifies) (st : St) (env : Env)
    (dst : Option Expr) (e : Expr) (s : UInt16) (n : Nat) (he : evalE p st env e = some (u16 s)) :
    execS (n + 7) p st env (.call dst "verifies" [e]) =
      storeResult p st env dst (some (.bool (Spec.Checksum.verifies s))) :=
  execS_call_val p st env (n + 6) dst "verifies" [e] hp (by simp [verifies]) (by simp [evalArgs, he])
    (verifies_refines p hp st s n)

theorem execS_csum_update (p : Prog) (h1 : p.fn? "add16" = some add16)
    (h2 : p.fn? "csum_update" = some csum_update) (st : St) (env : Env) (dst : Option Expr)
    (e1 e2 e3 : Expr) (hc old new : UInt16) (n : Nat) (he1 : evalE p st env e1 = some (u16 hc))
    (he2 : evalE p st env e2 = some (u16 old)) (he3 : evalE p st env e3 = some (u16 new)) :
    execS (n + 31) p st env (.call dst "csum_update" [e1, e2, e3]) =
      storeResult p st env dst (some (u16 (Spec.Checksum.incremental hc old new))) :=
  execS_call_val p st env (n + 30) dst "csum_update" [e1, e2, e3] h2 (by simp [csum_update])
    (by simp [evalArgs, he1, he2, he3]) (csum_update_refines p h1 h2 st hc old new n)

theorem execS_ip_send (p : Prog) (hP : IpProg p) (st : St) (env : Env) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp))
    (httl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault))
    (e1 e2 e3 : Expr) (proto : UInt8) (dst : UInt32) (n : UInt16)
    (he1 : evalE p st env e1 = some (u8 proto)) (he2 : evalE p st env e2 = some (u32 dst))
    (he3 : evalE p st env e3 = some (u16 n))
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (m d : Nat) (hm : m = d + n.toNat + 151) :
    execS m p st env (.call none "ip_send" [e1, e2, e3]) =
      .ok (txOut (stIp st (ipHeader b proto id ourIp dst n Spec.ttlDefault) (id + 1))
          (st.world.frame ++
            Spec.Slip.encode (Spec.Ipv4.packet proto id ourIp dst (b.extract 20 (20 + n.toNat))))) env .normal := by
  subst hm
  exact execS_call_val p st env _ none "ip_send" [e1, e2, e3] hP.ip_send (by simp [ip_send])
    (by simp [evalArgs, he1, he2, he3]) (ip_send_refines p hP st b id hb hid ourIp hip httl proto dst n hn hsz d)

/-! ## The ICMP message -/

theorem low_byte (hi lo : UInt8) : ((hi.toUInt16 <<< 8 ||| lo.toUInt16) &&& 255).toUInt8 = lo := by
  apply UInt8.toNat_inj.mp
  have h1 := hi.toNat_lt
  have h2 := lo.toNat_lt
  have t : (255 : UInt16).toNat = 2 ^ 8 - 1 := rfl
  have t8 : (8 : UInt16).toNat = 8 := rfl
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_and, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    t, t8, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := hi.toNat * 2 ^ 8) (by omega), Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem high_byte_zero (x : UInt16) : ((x &&& 255) >>> 8).toUInt8 = 0 := by
  apply UInt8.toNat_inj.mp
  have t : (255 : UInt16).toNat = 2 ^ 8 - 1 := rfl
  have t8 : (8 : UInt16).toNat = 8 := rfl
  have t0 : (0 : UInt8).toNat = 0 := rfl
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_and, UInt16.toNat_shiftRight, t, t8, t0,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  omega

/-- `Spec.Icmp.reply`, case by case. -/
theorem reply_eq (msg : ByteArray) :
    Spec.Icmp.reply msg =
      if msg.size < 8 then .error "short-icmp"
      else if !Spec.Checksum.verifies (Spec.Checksum.sum msg 0 msg.size) then .error "bad-icmp-checksum"
      else if Bytes.get msg 0 != 8 then .error "unsupported-icmp-type"
      else .ok (Bytes.set16 (Bytes.set16 msg 0 (Bytes.get16 msg 0 &&& 255)) 2
        (Spec.Checksum.incremental (Bytes.get16 msg 2) (Bytes.get16 msg 0) (Bytes.get16 msg 0 &&& 255))) := by
  unfold Spec.Icmp.reply
  simp [Spec.Icmp.typeEchoRequest, Spec.Icmp.typeEchoReply]
  split <;> (try split) <;> (try split) <;> rfl

theorem get16_extract (b : ByteArray) (s e j : Nat) (h : s + j + 1 < e) (he : e ≤ b.size) :
    Bytes.get16 (b.extract s e) j = Bytes.get16 b (s + j) := by
  simp only [Bytes.get16]
  rw [get_extract b s e j (by omega) he, get_extract b s e (j + 1) (by omega) he]
  rfl

/-- The reply built in place in the packet buffer is the Spec's reply to
the message that was there. -/
theorem icmp_reply_bytes (b : ByteArray) (n : Nat) (hn8 : 8 ≤ n) (hn : 20 + n ≤ b.size) :
    (Bytes.set16 (Bytes.set b 20 0) 22
        (Spec.Checksum.incremental (Bytes.get16 b 22) (Bytes.get16 b 20) (Bytes.get16 b 20 &&& 255))).extract
        20 (20 + n)
      = Bytes.set16 (Bytes.set16 (b.extract 20 (20 + n)) 0 (Bytes.get16 (b.extract 20 (20 + n)) 0 &&& 255)) 2
          (Spec.Checksum.incremental (Bytes.get16 (b.extract 20 (20 + n)) 2) (Bytes.get16 (b.extract 20 (20 + n)) 0)
            (Bytes.get16 (b.extract 20 (20 + n)) 0 &&& 255)) := by
  have hsz : (b.extract 20 (20 + n)).size = n := by rw [ByteArray.size_extract]; omega
  rw [get16_extract b 20 _ 0 (by omega) hn, get16_extract b 20 _ 2 (by omega) hn]
  generalize Spec.Checksum.incremental (Bytes.get16 b (20 + 2)) (Bytes.get16 b (20 + 0))
    (Bytes.get16 b (20 + 0) &&& 255) = c
  have hlo : (Bytes.get16 b (20 + 0) &&& 255).toUInt8 = Bytes.get b 21 := low_byte _ _
  have hhi : ((Bytes.get16 b (20 + 0) &&& 255) >>> 8).toUInt8 = 0 := high_byte_zero _
  apply Bytes.ext_get
  · rw [ByteArray.size_extract, Bytes.size_set16, Bytes.size_set, Bytes.size_set16, Bytes.size_set16, hsz]; omega
  · intro j hj
    have hj' : j < n := by
      rw [ByteArray.size_extract, Bytes.size_set16, Bytes.size_set] at hj; omega
    rw [get_extract _ 20 _ j (by omega) (by rw [Bytes.size_set16, Bytes.size_set]; omega)]
    simp only [Bytes.get_set16, Bytes.get_set, Bytes.size_set, Bytes.size_set16, hsz, hlo, hhi]
    by_cases h3 : j = 3
    · subst h3
      have : 22 + 1 < b.size := by omega
      have : 2 + 1 < n := by omega
      simp [*]
    · by_cases h2 : j = 2
      · subst h2
        have : 22 < b.size := by omega
        have : 2 < n := by omega
        simp [*]
      · by_cases h1 : j = 1
        · subst h1
          have : 0 + 1 < n := by omega
          simp [*]
        · by_cases h0 : j = 0
          · subst h0
            have : 20 < b.size := by omega
            have : 0 < n := by omega
            simp [*]
          · have e1 : ¬ (22 + 1 = 20 + j) := by omega
            have e2 : ¬ (22 = 20 + j) := by omega
            have e3 : ¬ (20 = 20 + j) := by omega
            have e4 : ¬ (2 + 1 = j) := by omega
            have e5 : ¬ (2 = j) := by omega
            have e6 : ¬ (0 + 1 = j) := by omega
            have e7 : ¬ (0 = j) := by omega
            simp only [e1, e2, e3, e4, e5, e6, e7, false_and, if_false]
            rw [get_extract b 20 _ j (by omega) hn]

/-! ## `icmp_input` -/

def icmp_input : Fn := checked_fn% Net.prog, "icmp_input"
#guard (Net.prog.check.toOption.bind (·.fn? "icmp_input")) == some icmp_input

/-- A program with the functions `icmp_input` uses and its drop reasons. -/
structure IcmpProg (p : Prog) : Prop extends IpProg p where
  verifies : p.fn? "verifies" = some verifies
  csum_update : p.fn? "csum_update" = some csum_update
  icmp_input : p.fn? "icmp_input" = some icmp_input
  r11 : p.dropReasons[11]? = some "short-icmp"
  r12 : p.dropReasons[12]? = some "bad-icmp-checksum"
  r13 : p.dropReasons[13]? = some "unsupported-icmp-type"

/-- The constants `icmp_input` and `ip_send` read. -/
structure IcmpConsts (st : St) (ourIp : UInt32) : Prop where
  ourIp : st.globals.lookup "OUR_IP" = some (u32 ourIp)
  ttl : st.globals.lookup "TTL" = some (u8 Spec.ttlDefault)
  d11 : st.globals.lookup "D_SHORT_ICMP" = some (u8 11)
  d12 : st.globals.lookup "D_BAD_ICMP_CHECKSUM" = some (u8 12)
  d13 : st.globals.lookup "D_UNSUPPORTED_ICMP_TYPE" = some (u8 13)

theorem toUInt64_ne_iff8 (x y : UInt8) : (x.toUInt64 != y.toUInt64) = (x != y) := by
  simp only [bne, toUInt64_eq_iff8]

/-- **`icmp_input` is the Spec's ICMP handling** (`Spec.Icmp.reply`, then
`Spec.sendIp`): for the message of `n` bytes at `buf[20, 20+n)` it either
writes the drop line the Spec gives — too short, bad checksum, not an
echo request — or transmits the Spec's reply in the Spec's IPv4 packet,
SLIP-encoded, and takes the next identification. -/
theorem icmp_input_refines (p : Prog) (hP : IcmpProg p) (st : St) (b : ByteArray) (id : UInt16)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (hid : st.globals.lookup "ip_id" = some (u16 id))
    (ourIp : UInt32) (hK : IcmpConsts st ourIp) (src : UInt32) (n : UInt16)
    (hn : 20 + n.toNat ≤ b.size) (hsz : b.size < 65536) (d : Nat) :
    ∃ st', Sem.call (d + n.toNat + 250) p st "icmp_input" [u32 src, u16 n] = .ok none st' ∧
      match Spec.Icmp.reply (b.extract 20 (20 + n.toNat)) with
      | .error r => st' = dropSt st r
      | .ok m => ∃ B, B.size = b.size ∧ st' = txOut (stIp st B (id + 1))
          (st.world.frame ++ Spec.Slip.encode (Spec.Ipv4.packet 1 id ourIp src m)) := by
  have hmsz : (b.extract 20 (20 + n.toNat)).size = n.toNat := by rw [ByteArray.size_extract]; omega
  have ht : ∀ k : Nat, k < 65536 → (UInt16.ofNat k).toNat = k := by
    intro k hk; rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  have hsum : Spec.Checksum.sum (b.extract 20 (20 + n.toNat)) 0 n.toNat 0 = Spec.Checksum.sum b 20 n.toNat 0 := by
    apply Spec.Checksum.sum_congr
    intro i hi
    rw [Nat.zero_add, get_extract b 20 _ i (by omega) hn]
  rw [reply_eq, hmsz, hsum]
  let env0 : Env := [("src", u32 src), ("n", u16 n)]
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
  have hlt8 : (n < UInt16.ofNat 8) ↔ n.toNat < 8 := by rw [UInt16.lt_iff_toNat_lt, ht 8 (by omega)]
  simp only [env0] at econd1
  simp only [Sem.call, hP.icmp_input, icmp_input, execB_succ, execL_cons, execS_at, List.map, List.zip,
    List.zipWith, execS_ite, econd1, Val.toBool]
  by_cases h8 : n < UInt16.ofNat 8
  · have fd1 := fun m => execS_drop p st env0 m (.var "D_SHORT_ICMP") 11 "short-icmp"
      (eglob st env0 _ _ hK.d11 (by simp [env0, List.lookup])) hP.r11
    simp only [env0] at fd1
    simp only [h8, decide_true, if_true, execB_succ, execL_cons, execS_at, fd1, execS_ret_none]
    exact ⟨_, rfl, by simp [hlt8.mp h8]⟩
  · have hn8 : 8 ≤ n.toNat := by
      have := mt hlt8.mpr h8; omega
    have hg0 : Bytes.get (b.extract 20 (20 + n.toNat)) 0 = Bytes.get b 20 :=
      get_extract b 20 _ 0 (by omega) hn
    rw [hg0]
    have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
    have hzb : zeroOf p Ty.bool = .bool false := rfl
    let S := Spec.Checksum.sum b 20 n.toNat 0
    let V := Spec.Checksum.verifies S
    let env2 : Env := ("ok", .bool V) :: ("s", u16 S) :: env0
    let old := Bytes.get16 b 20
    let new := old &&& UInt16.ofNat 255
    let env4 : Env := ("new", u16 new) :: ("old", u16 old) :: env2
    let b1 := Bytes.set b 20 (UInt8.ofNat 0)
    let st1 := setG st "buf" (bufVal b1)
    let hc := Bytes.get16 b1 22
    let c := Spec.Checksum.incremental hc old new
    let env6 : Env := ("c", u16 c) :: ("hc", u16 hc) :: env4
    let b2 := Bytes.set16 b1 22 c
    let st2 := withBuf st1 b2
    have hb1 : st1.globals.lookup "buf" = some (bufVal b1) := lookup_setG st _ _ _ hb
    have sb1 : b1.size = b.size := by simp [b1]
    have sb2 : b2.size = b.size := by simp [b2, sb1]
    have f_s : execS (d + n.toNat + 245) p st (("s", u16 0) :: env0)
        (.call (some (.var "s")) "csum" [.lit 20 (some .w16), .var "n", .lit 0 (some .w16)])
        = .ok st (("s", u16 S) :: env0) .normal := by
      rw [execS_csum p hP.csum hP.get16 hP.add16 st _ b hb _ _ _ _ (UInt16.ofNat 20) n (UInt16.ofNat 0)
        (by rw [ht 20 (by omega)]; omega) (by omega) (evalE_lit16 ..)
        (evar _ _ "n" _ (by simp [env0, List.lookup])) (evalE_lit16 ..) _ (d + (n.toNat - n.toNat / 2) + 184)
        (by omega)]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 20 (by omega), S]
      rfl
    have f_ok : ∀ m, execS (m + 7) p st (("ok", .bool false) :: ("s", u16 S) :: env0)
        (.call (some (.var "ok")) "verifies" [.var "s"]) = .ok st env2 .normal := by
      intro m
      rw [execS_verifies p hP.verifies st _ _ _ S m (evar _ _ "s" _ (by simp [List.lookup]))]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, env2, V]
    have econd2 : evalE p st env2 (.un .lnot (.var "ok")) = some (.bool (!V)) := by
      simp only [evalE, lookup, List.lookup, beq_self_eq_true, env2]
    have econd3 : ∀ S' : St, S'.globals.lookup "buf" = some (bufVal b) →
        evalE p S' env2 (.bin .ne (.index (.var "buf") (.lit 20 (some .w16))) (.lit 8 (some .w8)))
        = some (.bool (Bytes.get b 20 != UInt8.ofNat 8)) := by
      intro S' hS'
      have e1 : evalE p S' env2 (.var "buf") = some (bufVal b) :=
        eglob _ _ _ _ hS' (by simp [env2, env0, List.lookup])
      have hidx : (u16 (UInt16.ofNat 20)).toNat = 20 := by simp [Val.toNat]
      have hget := bufVal_get b 20 (by omega)
      have ei : evalE p S' env2 (.index (.var "buf") (.lit 20 (some .w16))) = some (u8 (Bytes.get b 20)) := by
        rw [evalE, e1, evalE_lit16]
        simp only [bufVal, hidx, hget]
      rw [evalE_bin, ei, evalE_lit8]
      simp only [Sem.binop, toUInt64_ne_iff8]
    have econd3' := econd3 st hb
    have fd2 := fun m => execS_drop p st env2 m (.var "D_BAD_ICMP_CHECKSUM") 12 "bad-icmp-checksum"
      (eglob st env2 _ _ hK.d12 (by simp [env2, env0, List.lookup])) hP.r12
    have fd3 := fun m => execS_drop p st env2 m (.var "D_UNSUPPORTED_ICMP_TYPE") 13 "unsupported-icmp-type"
      (eglob st env2 _ _ hK.d13 (by simp [env2, env0, List.lookup])) hP.r13
    have f_old : ∀ m, execS (m + 7) p st (("old", u16 0) :: env2) (.call (some (.var "old")) "get16"
        [.lit 20 (some .w16)]) = .ok st (("old", u16 old) :: env2) .normal := by
      intro m
      rw [execS_get16 p hP.get16 st _ b hb _ _ (UInt16.ofNat 20) m (by rw [ht 20 (by omega)]; omega)
        (by rw [ht 20 (by omega)]; omega) (evalE_lit16 ..)]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 20 (by omega), old]
    have e_new : evalE p st (("old", u16 old) :: env2) (.bin .band (.var "old") (.lit 255 (some .w16)))
        = some (u16 new) := by
      simp only [evalE_bin, evalE_lit16, evar st (("old", u16 old) :: env2) "old" (u16 old) (by simp only [List.lookup, beq_self_eq_true]), Sem.binop, mask16_and,
        new]
    have a20 : assign p st env4 (.index (.var "buf") (.lit 20 (some .w16))) (u8 (UInt8.ofNat 0))
        = some (st1, env4) :=
      assign_buf_lit p st env4 b 20 _ (by simp [env4, env2, env0, List.lookup]) hb (by omega) (by omega)
    have f_hc : ∀ m, execS (m + 7) p st1 (("hc", u16 0) :: env4) (.call (some (.var "hc")) "get16"
        [.lit 22 (some .w16)]) = .ok st1 (("hc", u16 hc) :: env4) .normal := by
      intro m
      rw [execS_get16 p hP.get16 st1 _ b1 hb1 _ _ (UInt16.ofNat 22) m (by rw [ht 22 (by omega)]; omega)
        (by rw [ht 22 (by omega)]; omega) (evalE_lit16 ..)]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, ht 22 (by omega), hc]
    have f_c : ∀ m, execS (m + 31) p st1 (("c", u16 0) :: ("hc", u16 hc) :: env4)
        (.call (some (.var "c")) "csum_update" [.var "hc", .var "old", .var "new"]) = .ok st1 env6 .normal := by
      intro m
      rw [execS_csum_update p hP.add16 hP.csum_update st1 _ _ _ _ _ hc old new m
        (evar _ _ "hc" _ (by simp [List.lookup])) (evar _ _ "old" _ (by simp [env4, List.lookup]))
        (evar _ _ "new" _ (by simp [env4, List.lookup]))]
      simp only [storeResult, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true, env6, c]
    have f_set : ∀ m, execS (m + 9) p st1 env6 (.call none "set16" [.lit 22 (some .w16), .var "c"])
        = .ok st2 env6 .normal := by
      intro m
      rw [execS_set16 p hP.set16 st1 env6 b1 hb1 _ _ (UInt16.ofNat 22) c m (by rw [ht 22 (by omega)]; omega)
        (by rw [ht 22 (by omega)]; omega) (evalE_lit16 ..) (evar _ _ "c" _ (by simp [env6, List.lookup])),
        ht 22 (by omega)]
    have l2 : ∀ x : String, x ≠ "buf" → st2.globals.lookup x = st.globals.lookup x := by
      intro x hx
      simp only [st2, st1, withBuf_eq]
      rw [lookup_setG_ne _ _ _ _ (Ne.symm hx), lookup_setG_ne _ _ _ _ (Ne.symm hx)]
    have f_ip : execS (d + n.toNat + 231) p st2 env6 (.call none "ip_send" [.lit 1 (some .w8), .var "src", .var "n"])
        = .ok (txOut (stIp st2 (ipHeader b2 (UInt8.ofNat 1) id ourIp src n Spec.ttlDefault) (id + 1))
            (st2.world.frame ++ Spec.Slip.encode
              (Spec.Ipv4.packet (UInt8.ofNat 1) id ourIp src (b2.extract 20 (20 + n.toNat))))) env6 .normal :=
      execS_ip_send p hP.toIpProg st2 env6 b2 id (lookup_withBuf st1 b1 b2 hb1)
        (by rw [l2 _ (by decide)]; exact hid) ourIp (by rw [l2 _ (by decide)]; exact hK.ourIp)
        (by rw [l2 _ (by decide)]; exact hK.ttl) _ _ _ _ src n (evalE_lit8 ..)
        (evar _ _ "src" _ (by simp [env6, env4, env2, env0, List.lookup]))
        (evar _ _ "n" _ (by simp [env6, env4, env2, env0, List.lookup])) (by omega) (by omega) _ (d + 80)
        (by omega)
    simp only [S, V, env2, old, new, env4, b1, st1, hc, c, env6, b2, st2, env0] at f_s f_ok econd2 econd3' fd2 fd3 f_old e_new a20 f_hc f_c f_set f_ip
    have hn8' : ¬ n.toNat < 8 := by omega
    rcases Bool.eq_false_or_eq_true (Spec.Checksum.verifies (Spec.Checksum.sum b 20 n.toNat 0)) with hv | hv
    · rcases Bool.eq_false_or_eq_true (Bytes.get b 20 != UInt8.ofNat 8) with ht8 | ht8
      · -- not an echo request
        have c2 := econd2; conv at c2 => rhs; rw [hv]
        have c3 := econd3'; rw [ht8] at c3
        simp (disch := omega) only [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_decl_none,
        execS_decl_some, execS_assign, execS_ret_none, evalE_lit8, hz, hzb, f_s, f_ok, c2, c3, fd2, fd3,
        f_old, e_new, a20, f_hc, f_c, f_set, f_ip, Val.toBool, Bool.not_true, Bool.not_false, Bool.false_eq_true, h8, decide_false,
        if_true, if_false, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
        refine ⟨_, rfl, ?_⟩
        have ht8' : (Bytes.get b 20 != 8) = true := ht8
        simp [hn8', hv, ht8']
      · -- the reply
        have c2 := econd2; conv at c2 => rhs; rw [hv]
        have c3 := econd3'; rw [ht8] at c3
        simp (disch := omega) only [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_decl_none,
        execS_decl_some, execS_assign, execS_ret_none, evalE_lit8, hz, hzb, f_s, f_ok, c2, c3, fd2, fd3,
        f_old, e_new, a20, f_hc, f_c, f_set, f_ip, Val.toBool, Bool.not_true, Bool.not_false, Bool.false_eq_true, h8, decide_false,
        if_true, if_false, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
        refine ⟨_, rfl, ?_⟩
        have ht8' : (Bytes.get b 20 != 8) = false := ht8
        simp only [hn8', hv, ht8', if_false, Bool.not_true, Bool.false_eq_true]
        have e0 : UInt8.ofNat 0 = 0 := rfl
        have e1 : UInt8.ofNat 1 = 1 := rfl
        have e255 : UInt16.ofNat 255 = 255 := rfl
        have h22 : Bytes.get16 (Bytes.set b 20 0) 22 = Bytes.get16 b 22 := by
          simp only [Bytes.get16]
          rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega)]
        rw [e0, e1, e255, h22, icmp_reply_bytes b n.toNat hn8 hn, withBuf_eq, stIp_setG_buf, stIp_setG_buf]
        exact ⟨_, by simp, rfl⟩
    · -- bad checksum
      have c2 := econd2; conv at c2 => rhs; rw [hv]
      have c3 := econd3'
      simp (disch := omega) only [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_decl_none,
        execS_decl_some, execS_assign, execS_ret_none, evalE_lit8, hz, hzb, f_s, f_ok, c2, c3, fd2, fd3,
        f_old, e_new, a20, f_hc, f_c, f_set, f_ip, Val.toBool, Bool.not_true, Bool.not_false, Bool.false_eq_true, h8, decide_false,
        if_true, if_false, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
      refine ⟨_, rfl, ?_⟩
      simp [hn8', hv]

/-- The stack's initial globals have the constants `icmp_input` reads. -/
theorem net_consts (inputs : Array Trace.Input) : IcmpConsts (Sem.initial Net.prog inputs) Spec.ourIpDefault :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- the checked stack is an `IcmpProg` (with the `#guard`s at the functions)
#guard (Net.prog.check.toOption.map fun q => (q.dropReasons[11]?, q.dropReasons[12]?, q.dropReasons[13]?))
  == some (some "short-icmp", some "bad-icmp-checksum", some "unsupported-icmp-type")
#guard (Net.prog.check.toOption.map (·.globals.map (·.name))) == some (Net.prog.globals.map (·.name))

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.icmp_input_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms icmp_input_refines

end Ember.Proof.Refine
