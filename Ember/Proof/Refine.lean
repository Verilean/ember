import Ember.Proof.Symex
import Ember.Lang.Checked
import Ember.Net.Main
import Ember.Proof.Checksum

/-!
# Ember.Proof.Refine — Ember functions refine the Spec (plan M5.4, M5.5)

"P2" of the design: the stack written in Ember computes what
`Ember.Spec` specifies, function by function.  The statements are about
`Ember.Lang.Sem.call`, the total semantics, applied to the checked AST of
the function.
-/

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-- `add16` of the stack, type-checked. -/
def add16 : Fn := checked_fn% Net.prog, "add16"

#guard (Net.prog.check.toOption.bind (·.fn? "add16")) == some add16

/-! ## Values -/

/-- The arithmetic of `add16`: add modulo 2^16, and one more when the sum
came out smaller than an operand (it wrapped). -/
theorem add16_value (a b : UInt16) :
    (if mask .w16 (a.toUInt64 + b.toUInt64) < a.toUInt64
      then mask .w16 (mask .w16 (a.toUInt64 + b.toUInt64) + mask .w16 1)
      else mask .w16 (a.toUInt64 + b.toUInt64)) = (Spec.Checksum.add a b).toUInt64 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hadd := Spec.Checksum.toNat_add a b
  have h1 : UInt64.toNat 1 = 1 := rfl
  apply UInt64.toNat_inj.mp
  split
  next h =>
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [toNat_mask16, UInt64.toNat_add, UInt16.toNat_toUInt64, h1] at h ⊢
    rw [hadd]
    split <;> omega
  next h =>
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [toNat_mask16, UInt64.toNat_add, UInt16.toNat_toUInt64] at h ⊢
    rw [hadd]
    split <;> omega

/-! ## Functions -/

/-- **`add16` is one's-complement addition** (`Spec.Checksum.add`): in
any program that has this `add16`, from any state, with any fuel from 12
on, the call returns the Spec's sum and leaves the state as it was. -/
theorem add16_refines (p : Prog) (hp : p.fn? "add16" = some add16) (st : St) (a b : UInt16) (n : Nat) :
    Sem.call (n + 12) p st "add16" [.int .w16 a.toUInt64, .int .w16 b.toUInt64]
      = .ok (some (.int .w16 (Spec.Checksum.add a b).toUInt64)) st := by
  have hv := add16_value a b
  simp only [Sem.call, hp, add16, Sem.execB, Sem.execL, Sem.execS, Sem.evalE, Sem.binop, Sem.lookup,
    List.lookup, List.map, List.zip, List.zipWith]
  by_cases h : mask Width.w16 (a.toUInt64 + b.toUInt64) < a.toUInt64
  · simp [h, Val.toBool, List.lookup] at hv ⊢
    exact hv
  · simp [h, Val.toBool, List.lookup] at hv ⊢
    exact hv

/-- A call of `add16` as a statement: the sum of the two argument values
is stored.  (How the proofs of its callers use `add16_refines`.) -/
theorem execS_add16 (p : Prog) (hp : p.fn? "add16" = some add16) (st : St) (env : Env) (dst : Option Expr)
    (ea eb : Expr) (a b : UInt16) (n : Nat)
    (ha : evalE p st env ea = some (u16 a)) (hb : evalE p st env eb = some (u16 b)) :
    execS (n + 13) p st env (.call dst "add16" [ea, eb]) =
      storeResult p st env dst (some (u16 (Spec.Checksum.add a b))) :=
  execS_call_val p st env (n + 12) dst "add16" [ea, eb] hp (by simp [add16]) (by simp [evalArgs, ha, hb])
    (add16_refines p hp st a b n)

def verifies : Fn := checked_fn% Net.prog, "verifies"
#guard (Net.prog.check.toOption.bind (·.fn? "verifies")) == some verifies

/-- **`verifies`**: is the sum `0xFFFF` or `0`? -/
theorem verifies_refines (p : Prog) (hp : p.fn? "verifies" = some verifies) (st : St) (s : UInt16) (n : Nat) :
    Sem.call (n + 6) p st "verifies" [u16 s] = .ok (some (.bool (Spec.Checksum.verifies s))) st := by
  have h1 : mask .w16 65535 = (0xFFFF : UInt16).toUInt64 := rfl
  have h0 : mask .w16 0 = (0 : UInt16).toUInt64 := rfl
  simp [Sem.call, hp, verifies, execB_succ, execL_cons, execS_at, execS_ret_some, evalE, Sem.binop,
    lookup, List.lookup, h1, h0, Spec.Checksum.verifies]
  have e1 : (65535 : UInt64) = (65535 : UInt16).toUInt64 := rfl
  have e0 : (0 : UInt64) = (0 : UInt16).toUInt64 := rfl
  rw [e1, e0, toUInt64_eq_iff, toUInt64_eq_iff]

def csum_update : Fn := checked_fn% Net.prog, "csum_update"
#guard (Net.prog.check.toOption.bind (·.fn? "csum_update")) == some csum_update

/-- **`csum_update` is RFC 1624's incremental update**
(`Spec.Checksum.incremental`, which `Ember.Proof.Checksum` relates to
recomputing the checksum). -/
theorem csum_update_refines (p : Prog) (h1 : p.fn? "add16" = some add16)
    (h2 : p.fn? "csum_update" = some csum_update) (st : St) (hc old new : UInt16) (n : Nat) :
    Sem.call (n + 30) p st "csum_update" [u16 hc, u16 old, u16 new]
      = .ok (some (u16 (Spec.Checksum.incremental hc old new))) st := by
  simp only [Sem.call, h2, csum_update, execB_succ, execL_cons, execS_at, execS_decl_none, List.map, List.zip,
    List.zipWith]
  rw [execS_add16 p h1 (a := ~~~hc) (b := ~~~old) (ha := by simp [evalE, lookup, List.lookup, mask16_not])
    (hb := by simp [evalE, lookup, List.lookup, mask16_not])]
  simp only [storeResult, assign, update, setFirst, List.lookup, zeroOf, beq_self_eq_true, ite_true]
  rw [execS_add16 p h1 (a := Spec.Checksum.add (~~~hc) (~~~old)) (b := new)
    (ha := by simp [evalE, lookup, List.lookup]) (hb := by simp [evalE, lookup, List.lookup])]
  simp [storeResult, assign, update, setFirst, List.lookup, execS_ret_some, evalE, lookup, mask16_not,
    Spec.Checksum.incremental]

def pseudo : Fn := checked_fn% Net.prog, "pseudo"
#guard (Net.prog.check.toOption.bind (·.fn? "pseudo")) == some pseudo

/-- **`pseudo` is the pseudo-header sum** of UDP and TCP
(`Spec.Checksum.pseudo`): source and destination address by halves, the
protocol, the length. -/
theorem pseudo_refines (p : Prog) (h1 : p.fn? "add16" = some add16) (h2 : p.fn? "pseudo" = some pseudo)
    (st : St) (src dst : UInt32) (proto : UInt8) (len : UInt16) (n : Nat) :
    Sem.call (n + 40) p st "pseudo" [u32 src, u32 dst, u8 proto, u16 len]
      = .ok (some (u16 (Spec.Checksum.pseudo src dst proto len.toNat))) st := by
  -- the running sum after each of the five additions
  let s1 := Spec.Checksum.add (src >>> 16).toUInt16 src.toUInt16
  let s2 := Spec.Checksum.add s1 (dst >>> 16).toUInt16
  let s3 := Spec.Checksum.add s2 dst.toUInt16
  let s4 := Spec.Checksum.add s3 proto.toUInt16
  simp only [Sem.call, h2, pseudo, execB_succ, execL_cons, execS_at, execS_decl_none, List.map, List.zip,
    List.zipWith]
  rw [execS_add16 p h1 (a := (src >>> 16).toUInt16) (b := src.toUInt16)
    (ha := evalE_hi16 p st _ "src" src (by simp [lookup, List.lookup]))
    (hb := evalE_lo16 p st _ "src" src (by simp [lookup, List.lookup]))]
  simp only [storeResult, assign, update, setFirst, List.lookup, zeroOf, beq_self_eq_true, ite_true]
  rw [execS_add16 p h1 (a := s1) (b := (dst >>> 16).toUInt16) (ha := by simp [evalE, lookup, List.lookup, s1])
    (hb := evalE_hi16 p st _ "dst" dst (by simp [lookup, List.lookup]))]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true]
  rw [execS_add16 p h1 (a := s2) (b := dst.toUInt16) (ha := by simp [evalE, lookup, List.lookup, s2, s1])
    (hb := evalE_lo16 p st _ "dst" dst (by simp [lookup, List.lookup]))]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true]
  rw [execS_add16 p h1 (a := s3) (b := proto.toUInt16) (ha := by simp [evalE, lookup, List.lookup, s3, s2, s1])
    (hb := evalE_u8_16 p st _ "proto" proto (by simp [lookup, List.lookup]))]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true]
  rw [execS_add16 p h1 (a := s4) (b := len) (ha := by simp [evalE, lookup, List.lookup, s4, s3, s2, s1])
    (hb := by simp [evalE, lookup, List.lookup])]
  simp [storeResult, assign, update, setFirst, List.lookup, execS_ret_some, evalE, lookup, Spec.Checksum.pseudo,
    s4, s3, s2, s1]

/-! ## Reading the packet buffer

`buf` is a global array of bytes; `bufVal b` is the value it has when it
holds the bytes of `b`. -/

def get16 : Fn := checked_fn% Net.prog, "get16"
#guard (Net.prog.check.toOption.bind (·.fn? "get16")) == some get16

/-- **`get16` reads a big-endian word** (`Bytes.get16`) when both bytes
are inside the buffer. -/
theorem get16_refines (p : Prog) (hp : p.fn? "get16" = some get16) (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (o : UInt16)
    (ho : o.toNat + 1 < b.size) (ho' : o.toNat + 1 < 65536) (n : Nat) :
    Sem.call (n + 6) p st "get16" [u16 o] = .ok (some (u16 (Bytes.get16 b o.toNat))) st := by
  have hbuf : lookup st [("o", u16 o)] "buf" = some (bufVal b) := by simp [lookup, List.lookup, hb]
  have e0 : evalE p st [("o", u16 o)] (.var "o") = some (u16 o) := by simp [evalE, lookup, List.lookup]
  have h1 : mask .w16 (UInt64.ofNat 1) = (1 : UInt16).toUInt64 := rfl
  have e1 : evalE p st [("o", u16 o)] (.bin .add (.var "o") (.lit 1 (some .w16))) = some (u16 (o + 1)) := by
    rw [evalE, e0, evalE]
    simp only [Sem.binop, h1, mask16_add]
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    have : (1 : UInt16).toNat = 1 := rfl
    simp only [UInt16.toNat_add, this]; omega
  have b0 := evalE_buf16 p st _ b (.var "o") o hbuf e0 (by omega)
  have b1 := evalE_buf16 p st _ b _ (o + 1) hbuf e1 (by omega)
  rw [ho1] at b1
  simp only [Sem.call, hp, get16, execB_succ, execL_cons, execL_nil, execS_at, execS_ret_some, List.map, List.zip,
    List.zipWith]
  have hv : evalE p st [("o", u16 o)]
      (.bin .bor (.bin .shl (.cast .w16 (.index (.var "buf") (.var "o"))) (.lit 8 (some .w8)))
        (.cast .w16 (.index (.var "buf") (.bin .add (.var "o") (.lit 1 (some .w16))))))
      = some (u16 (Bytes.get16 b o.toNat)) := by
    have h8 : ¬ ((mask .w8 (UInt64.ofNat 8)).toNat ≥ Width.bits .w16) := by decide
    rw [evalE, evalE, b0, b1]
    simp only [evalE, Sem.binop, h8, if_false, word_value, Bytes.get16]
  rw [hv]

/-- A call of `get16` as a statement. -/
theorem execS_get16 (p : Prog) (hp : p.fn? "get16" = some get16) (st : St) (env : Env) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (dst : Option Expr) (eo : Expr) (o : UInt16) (n : Nat)
    (ho : o.toNat + 1 < b.size) (ho' : o.toNat + 1 < 65536) (he : evalE p st env eo = some (u16 o)) :
    execS (n + 7) p st env (.call dst "get16" [eo]) =
      storeResult p st env dst (some (u16 (Bytes.get16 b o.toNat))) :=
  execS_call_val p st env (n + 6) dst "get16" [eo] hp (by simp [get16]) (by simp [evalArgs, he])
    (get16_refines p hp st b hb o ho ho' n)

/-! ## The checksum of a range of the buffer -/

def csum : Fn := checked_fn% Net.prog, "csum"
#guard (Net.prog.check.toOption.bind (·.fn? "csum")) == some csum

/-- The body of the loop of `csum`. -/
def csumBody : List Stmt :=
  match csum.body with
  | [_, .at _ (.forRange _ _ _ _ body), _, _] => body
  | _ => []

/-- One iteration: the word at `o + 2·i` is added to `s`. -/
theorem csum_body (p : Prog) (hg : p.fn? "get16" = some get16) (ha : p.fn? "add16" = some add16)
    (st : St) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b))
    (o nn ini s : UInt16) (i : Nat) (hi : o.toNat + 2 * i + 1 < b.size) (hi' : o.toNat + 2 * i + 1 < 65536) (m : Nat) :
    execB (m + 30) p st [("i", u16 (UInt16.ofNat i)), ("s", u16 s), ("o", u16 o), ("n", u16 nn), ("init", u16 ini)]
        csumBody
      = .ok st [("i", u16 (UInt16.ofNat i)), ("s", u16 (Spec.Checksum.add s (Bytes.get16 b (o.toNat + 2 * i)))),
                ("o", u16 o), ("n", u16 nn), ("init", u16 ini)] .normal := by
  have h2 : mask .w16 (UInt64.ofNat 2) = (2 : UInt16).toUInt64 := rfl
  have haddr : (o + 2 * UInt16.ofNat i).toNat = o.toNat + 2 * i := by
    have : (2 : UInt16).toNat = 2 := rfl
    simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_ofNat', this]
    omega
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  simp only [csumBody, csum, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, hz]
  have he : evalE p st [("w", u16 0), ("i", u16 (UInt16.ofNat i)), ("s", u16 s), ("o", u16 o), ("n", u16 nn),
        ("init", u16 ini)]
      (.bin .add (.var "o") (.bin .mul (.lit 2 (some .w16)) (.var "i"))) = some (u16 (o + 2 * UInt16.ofNat i)) := by
    have eo : evalE p st [("w", u16 0), ("i", u16 (UInt16.ofNat i)), ("s", u16 s), ("o", u16 o), ("n", u16 nn),
        ("init", u16 ini)] (.var "o") = some (u16 o) := by simp [evalE, lookup, List.lookup]
    have ei : evalE p st [("w", u16 0), ("i", u16 (UInt16.ofNat i)), ("s", u16 s), ("o", u16 o), ("n", u16 nn),
        ("init", u16 ini)] (.var "i") = some (u16 (UInt16.ofNat i)) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, eo, ei, Sem.binop, h2, mask16_mul, mask16_add]
  rw [execS_get16 p hg st _ b hb (o := o + 2 * UInt16.ofNat i) (ho := by omega) (ho' := by omega) (he := he)]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true, haddr]
  rw [execS_add16 p ha (a := s) (b := Bytes.get16 b (o.toNat + 2 * i))
    (ha := by simp [evalE, lookup, List.lookup]) (hb := by simp [evalE, lookup, List.lookup])]
  simp [storeResult, assign, update, setFirst, List.lookup]

/-- The loop of `csum`: `k` more words from index `cur` on are added to `s`. -/
theorem csum_loop (p : Prog) (hg : p.fn? "get16" = some get16) (ha : p.fn? "add16" = some add16)
    (st : St) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b))
    (o nn ini : UInt16) (hi : Nat) (hsz : o.toNat + 2 * hi ≤ b.size) (hsz' : o.toNat + 2 * hi ≤ 65536) :
    ∀ (k cur : Nat) (s : UInt16) (v0 : Val) (d : Nat), cur + k = hi →
      ∃ v, forLoop (k + 31 + d) p st [("i", v0), ("s", u16 s), ("o", u16 o), ("n", u16 nn), ("init", u16 ini)]
            "i" .w16 cur hi csumBody
          = .ok st [("i", v), ("s", u16 (((List.range' cur k).map fun j => Bytes.get16 b (o.toNat + 2 * j)).foldl
                      Spec.Checksum.add s)), ("o", u16 o), ("n", u16 nn), ("init", u16 ini)] .normal := by
  intro k
  induction k with
  | zero =>
    intro cur s v0 d hk
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 31 + d = (30 + d) + 1 by omega, forLoop_succ]
    simp [this]
  | succ k ih =>
    intro cur s v0 d hk
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    obtain ⟨v, hv⟩ := ih (cur + 1) (Spec.Checksum.add s (Bytes.get16 b (o.toNat + 2 * cur)))
      (u16 (UInt16.ofNat cur)) d (by omega)
    refine ⟨v, ?_⟩
    rw [show k + 1 + 31 + d = (k + 31 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 31 + d = (k + 1 + d) + 30 by omega,
      csum_body p hg ha st b hb o nn ini s cur (by omega) (by omega) (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 30 = k + 31 + d by omega, hv]
    simp [List.range'_succ]

/-- **`csum` is the Internet checksum's sum** (`Spec.Checksum.sum`) over
`buf[o, o+n)`, for every buffer content, offset, length and start value
with the range inside the buffer.  The fuel needed grows with the number
of words (one unit per loop iteration).

With `Ember.Proof.Checksum` this connects the Ember code to the algebra
of M5.1: the sum the stack computes is the left fold of one's-complement
addition over the big-endian words of the range. -/
theorem csum_refines (p : Prog) (hc : p.fn? "csum" = some csum) (hg : p.fn? "get16" = some get16)
    (ha : p.fn? "add16" = some add16) (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (o n ini : UInt16)
    (hr : o.toNat + n.toNat ≤ b.size) (hsz : b.size ≤ 65536) (d : Nat) :
    Sem.call (d + n.toNat / 2 + 60) p st "csum" [u16 o, u16 n, u16 ini]
      = .ok (some (u16 (Spec.Checksum.sum b o.toNat n.toNat ini))) st := by
  have e_init : evalE p st [("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.var "init") = some (u16 ini) := by
    simp [evalE, lookup, List.lookup]
  have e_lo : evalE p st [("s", u16 ini), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.lit 0 (some .w16))
      = some (u16 0) := by rw [evalE_lit]; rfl
  have e_hi : evalE p st [("s", u16 ini), ("o", u16 o), ("n", u16 n), ("init", u16 ini)]
      (.bin .div (.var "n") (.lit 2 (some .w16))) = some (u16 (n / 2)) := by
    have en : evalE p st [("s", u16 ini), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.var "n")
        = some (u16 n) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, en, Sem.binop, div2_value]
  have t0 : (u16 (0 : UInt16)).toNat = 0 := rfl
  have thi : (u16 (n / 2)).toNat = n.toNat / 2 := by
    have t2' : UInt16.toNat 2 = 2 := rfl
    simp [Val.toNat]
  obtain ⟨v, hv⟩ := csum_loop p hg ha st b hb o n ini (n.toNat / 2) (by omega) (by omega) (n.toNat / 2) 0 ini
    (.int .w16 (UInt64.ofNat 0)) (d + 24) (by omega)
  simp only [csumBody, csum] at hv
  simp only [Sem.call, hc, csum, execB_succ, execL_cons, execS_at, execS_decl_some, execS_forRange, List.map,
    List.zip, List.zipWith, e_init, e_lo, e_hi, t0, thi, Option.getD]
  rw [show d + n.toNat / 2 + 55 = n.toNat / 2 + 31 + (d + 24) by omega, hv]
  rw [show n.toNat / 2 + 31 + (d + 24) = d + n.toNat / 2 + 55 by omega]
  -- the sum of the whole words
  generalize hS : List.foldl Spec.Checksum.add ini
      (List.map (fun j => Bytes.get16 b (o.toNat + 2 * j)) (List.range' 0 (n.toNat / 2))) = S
  have h1 : mask .w16 (UInt64.ofNat 1) = (1 : UInt16).toUInt64 := rfl
  have e_n : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.var "n") = some (u16 n) := by
    simp [evalE, lookup, List.lookup]
  have e_o : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.var "o") = some (u16 o) := by
    simp [evalE, lookup, List.lookup]
  have e_s : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] (.var "s") = some (u16 S) := by
    simp [evalE, lookup, List.lookup]
  have e_c : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)]
      (.bin .eq (.bin .band (.var "n") (.lit 1 (some .w16))) (.lit 1 (some .w16)))
      = some (.bool (decide (n.toNat % 2 = 1))) := by
    simp only [evalE_bin, evalE_lit, e_n, Sem.binop, h1, mask16_and, toUInt64_eq_iff, and_one_eq]
  simp only [List.drop, execS_ite, e_c, Val.toBool]
  have hbuf : lookup st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)] "buf" = some (bufVal b) := by
    simp [lookup, List.lookup, hb]
  by_cases hodd : n.toNat % 2 = 1
  · -- an odd byte at the end
    have hidx : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)]
        (.bin .sub (.bin .add (.var "o") (.var "n")) (.lit 1 (some .w16))) = some (u16 (o + n - 1)) := by
      simp only [evalE_bin, evalE_lit, e_o, e_n, Sem.binop, h1, mask16_add, mask16_sub]
    have hK : (o + n - 1).toNat = o.toNat + (n.toNat - 1) := by
      have t1 : UInt16.toNat 1 = 1 := rfl
      have := o.toNat_lt
      have := n.toNat_lt
      simp only [UInt16.toNat_sub, UInt16.toNat_add, t1]
      omega
    have hbyte := evalE_buf16 p st _ b _ (o + n - 1) hbuf hidx (by omega)
    rw [hK] at hbyte
    have harg : evalE p st [("s", u16 S), ("o", u16 o), ("n", u16 n), ("init", u16 ini)]
        (.bin .shl (.cast .w16 (.index (.var "buf")
          (.bin .sub (.bin .add (.var "o") (.var "n")) (.lit 1 (some .w16))))) (.lit 8 (some .w8)))
        = some (u16 ((Bytes.get b (o.toNat + (n.toNat - 1))).toUInt16 <<< 8)) := by
      rw [evalE_bin, hbyte, evalE_lit]
      simp only [Sem.binop, shl8_value]
    simp only [hodd, decide_true, if_true, execB_succ, execL_cons, execL_nil, execS_at]
    rw [execS_add16 p ha (a := S) (b := (Bytes.get b (o.toNat + (n.toNat - 1))).toUInt16 <<< 8)
      (ha := e_s) (hb := harg)]
    simp [storeResult, assign, update, setFirst, List.lookup, execS_ret_some, evalE, lookup,
      Spec.Checksum.sum_eq_foldl, Spec.Checksum.words, hodd, List.foldl_append, List.range_eq_range', hS]
  · -- no odd byte
    simp [hodd, execB_succ, execL_nil, execS_ret_some, evalE, lookup, List.lookup,
      Spec.Checksum.sum_eq_foldl, Spec.Checksum.words, List.range_eq_range', hS]

/-! ## Writing the packet buffer -/

def set16 : Fn := checked_fn% Net.prog, "set16"
#guard (Net.prog.check.toOption.bind (·.fn? "set16")) == some set16

/-- **`set16` writes a big-endian word** (`Bytes.set16`): the state after
the call is the state before with `buf` holding the updated bytes. -/
theorem set16_refines (p : Prog) (hp : p.fn? "set16" = some set16) (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (o v : UInt16)
    (ho : o.toNat + 1 < b.size) (ho' : o.toNat + 1 < 65536) (n : Nat) :
    Sem.call (n + 8) p st "set16" [u16 o, u16 v] = .ok none (withBuf st (Bytes.set16 b o.toNat v)) := by
  have h1 : mask .w16 (UInt64.ofNat 1) = (1 : UInt16).toUInt64 := rfl
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    have : (1 : UInt16).toNat = 1 := rfl
    simp only [UInt16.toNat_add, this]; omega
  -- the first byte
  have ev1 := evalE_hi8 p st [("o", u16 o), ("v", u16 v)] "v" v (by simp [lookup, List.lookup])
  have eo : evalE p st [("o", u16 o), ("v", u16 v)] (.var "o") = some (u16 o) := by simp [evalE, lookup, List.lookup]
  have a1 := assign_buf p st [("o", u16 o), ("v", u16 v)] b (.var "o") o (v >>> 8).toUInt8
    (by simp [List.lookup]) hb eo (by omega)
  -- the second, in the state after the first
  let b1 := Bytes.set b o.toNat (v >>> 8).toUInt8
  have hb1 : (withBuf st b1).globals.lookup "buf" = some (bufVal b1) := lookup_withBuf st b b1 hb
  have hsz1 : b1.size = b.size := by simp [b1, Bytes.set]; split <;> simp
  have ev2 := evalE_lo8 p (withBuf st b1) [("o", u16 o), ("v", u16 v)] "v" v (by simp [lookup, List.lookup])
  have eo1 : evalE p (withBuf st b1) [("o", u16 o), ("v", u16 v)] (.bin .add (.var "o") (.lit 1 (some .w16)))
      = some (u16 (o + 1)) := by
    have eo' : evalE p (withBuf st b1) [("o", u16 o), ("v", u16 v)] (.var "o") = some (u16 o) := by
      simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, eo', Sem.binop, h1, mask16_add]
  have a2 := assign_buf p (withBuf st b1) [("o", u16 o), ("v", u16 v)] b1 _ (o + 1) v.toUInt8
    (by simp [List.lookup]) hb1 eo1 (by omega)
  rw [ho1, withBuf_withBuf] at a2
  simp only [Sem.call, hp, set16, execB_succ, execL_cons, execL_nil, execS_at, execS_assign, List.map, List.zip,
    List.zipWith, ev1, a1, ev2, a2, b1]
  rfl

end Ember.Proof.Refine
