import Ember.Proof.Refine
import Ember.Proof.Slip
import Ember.Net.Loop

/-!
# Ember.Proof.RefineSlip — 32-bit fields, and the SLIP code with its effects (plan M5.5)

`Refine.lean` has the functions that compute a value.  Here are the
first that change several globals and that write to the wire:

* `get32`/`set32`, through `get16`/`set16`;
* `slip_store` is `Spec.Slip.Dec.store`;
* `slip_send` transmits `Spec.Slip.encode` of the buffer's first bytes
  (a loop of `out.byte`, then `out.end`);
* `loop_rx` and `main` of the SLIP loopback (`Ember.Net.Loop`): one call
  of `main` is one step of `Spec.Slip.Dec.feed`, and a completed frame
  goes out encoded.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Lang.Sem

/-! ## Globals -/

/-- The state with global `x` set to `v`. -/
def setG (st : St) (x : String) (v : Val) : St := { st with globals := setFirst st.globals x v }

theorem lookup_setFirst_ne (l : Env) (x y : String) (v : Val) (h : x ≠ y) :
    (setFirst l x v).lookup y = l.lookup y := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, u⟩ := hd
    by_cases hk : k = x
    · subst hk
      have : (y == k) = false := by simp [Ne.symm h]
      simp [setFirst, List.lookup, this]
    · have hk' : (k == x) = false := by simp [hk]
      simp only [setFirst, hk', Bool.false_eq_true, if_false, List.lookup]
      split <;> simp_all

theorem lookup_setG_ne (st : St) (x y : String) (v : Val) (h : x ≠ y) :
    (setG st x v).globals.lookup y = st.globals.lookup y := lookup_setFirst_ne _ _ _ _ h

theorem lookup_setG (st : St) (x : String) (v w : Val) (h : st.globals.lookup x = some w) :
    (setG st x v).globals.lookup x = some v := lookup_setFirst _ _ _ _ h

@[simp] theorem world_setG (st : St) (x : String) (v : Val) : (setG st x v).world = st.world := rfl

theorem withBuf_eq (st : St) (b : ByteArray) : withBuf st b = setG st "buf" (bufVal b) := rfl

/-- `x := v` for a global that no local variable hides. -/
theorem assign_global (p : Prog) (st : St) (env : Env) (x : String) (v old : Val)
    (hl : env.lookup x = none) (hg : st.globals.lookup x = some old) :
    assign p st env (.var x) v = some (setG st x v, env) := by
  simp only [assign, update, hl, hg, setG]

theorem lookup_setG_self (st : St) (x : String) (v : Val) :
    (setG st x v).globals.lookup x = if (st.globals.lookup x).isSome then some v else none := by
  cases h : st.globals.lookup x with
  | none =>
    have : ∀ l : Env, l.lookup x = none → (setFirst l x v).lookup x = none := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons hd tl ih =>
        obtain ⟨k, u⟩ := hd
        by_cases hk : k = x
        · subst hk; simp [List.lookup]
        · have hk' : (k == x) = false := by simp [hk]
          have hk'' : (x == k) = false := by simp [Ne.symm hk]
          simp only [setFirst, hk', Bool.false_eq_true, if_false, List.lookup, hk'']
          exact ih
    show (setFirst st.globals x v).lookup x = _
    rw [this _ h]; rfl
  | some w => simpa using lookup_setG st x v w h

/-- `x := v`: the innermost local `x`, or else the global. -/
theorem assign_var (p : Prog) (st : St) (env : Env) (x : String) (v : Val) :
    assign p st env (.var x) v =
      match env.lookup x with
      | some _ => some (st, setFirst env x v)
      | none => if (st.globals.lookup x).isSome then some (setG st x v, env) else none := by
  simp only [assign, update, setG]
  cases env.lookup x with
  | some w => rfl
  | none => cases st.globals.lookup x <;> rfl

theorem mask16_zero : mask .w16 0 = 0 := rfl
theorem mask16_one : mask .w16 1 = 1 := rfl
theorem mask16_add_one (x : UInt16) : mask .w16 (x.toUInt64 + 1) = (x + 1).toUInt64 := mask16_add x 1

theorem setG_fold (st : St) (x : String) (v : Val) :
    ({ st with globals := setFirst st.globals x v } : St) = setG st x v := rfl

theorem toUInt64_lt_iff (x y : UInt16) : decide (x.toUInt64 < y.toUInt64) = decide (x < y) := by
  have : x.toUInt64 < y.toUInt64 ↔ x < y := by
    rw [UInt64.lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]; simp
  simp [this]

/-! ## Bytes to the wire -/

/-- The state with bytes appended to the frame being transmitted. -/
def pushOut (st : St) (l : List UInt8) : St :=
  { st with world := { st.world with frame := l.foldl ByteArray.push st.world.frame } }

@[simp] theorem globals_pushOut (st : St) (l : List UInt8) : (pushOut st l).globals = st.globals := rfl

theorem pushOut_pushOut (st : St) (a c : List UInt8) : pushOut (pushOut st a) c = pushOut st (a ++ c) := by
  simp [pushOut, List.foldl_append]

theorem u8_toUInt8 (c : UInt8) : (u8 c).toNat.toUInt8 = c := by
  apply UInt8.toNat_inj.mp
  have := c.toNat_lt
  simp [Val.toNat]

/-- `out.byte(e)`. -/
theorem execS_out (p : Prog) (st : St) (env : Env) (n : Nat) (e : Expr) (c : UInt8)
    (he : evalE p st env e = some (u8 c)) :
    execS (n + 1) p st env (.eff none .outByte [e]) = .ok (pushOut st [c]) env .normal := by
  have := u8_toUInt8 c
  simp only [execS_eff, evalArgs, he, effect, storeResult, pushOut, List.headD, this, List.foldl]

theorem toUInt64_eq_iff8 (x y : UInt8) : (x.toUInt64 == y.toUInt64) = (x == y) := by
  have h : x.toUInt64 = y.toUInt64 ↔ x = y := by
    constructor
    · intro h
      apply UInt8.toNat_inj.mp
      have := congrArg UInt64.toNat h
      simpa using this
    · intro h; rw [h]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : x.toUInt64 ≠ y.toUInt64 := fun e => hxy (h.mp e)
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hxy]

end Ember.Lang.Sem

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## 32-bit fields -/

private theorem mul_two_pow_or (k : Nat) {y : Nat} (h : y < 2 ^ k) (x : Nat) :
    x * 2 ^ k ||| y = x * 2 ^ k + y := by
  rw [Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt h]

/-- A 32-bit field is its two 16-bit halves. -/
theorem get32_eq_halves (b : ByteArray) (i : Nat) :
    Bytes.get32 b i = ((Bytes.get16 b i).toUInt32 <<< 16) ||| (Bytes.get16 b (i + 2)).toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [Bytes.get32, Bytes.get16, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt16.toNat_toUInt32, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
  have h0 := (Bytes.get b i).toNat_lt
  have h1 := (Bytes.get b (i + 1)).toNat_lt
  have h2 := (Bytes.get b (i + 2)).toNat_lt
  have h3 := (Bytes.get b (i + 2 + 1)).toNat_lt
  generalize (Bytes.get b i).toNat = x0 at *
  generalize (Bytes.get b (i + 1)).toNat = x1 at *
  generalize (Bytes.get b (i + 2)).toNat = x2 at *
  generalize (Bytes.get b (i + 2 + 1)).toNat = x3 at *
  simp only [Nat.shiftLeft_eq, UInt32.reduceToNat, UInt16.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := x0 * 2 ^ 24) (by omega), Nat.mod_eq_of_lt (a := x1 * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := x2 * 2 ^ 8) (by omega), Nat.mod_eq_of_lt (a := x0 * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := x2 * 2 ^ 8) (by omega)]
  rw [mul_two_pow_or 8 h1, mul_two_pow_or 8 h3, Nat.mod_eq_of_lt (a := (x0 * 2 ^ 8 + x1) * 2 ^ 16) (by omega),
    mul_two_pow_or 16 (by omega), mul_two_pow_or 24 (by omega)]
  rw [show x0 * 2 ^ 24 + x1 * 2 ^ 16 = (x0 * 2 ^ 8 + x1) * 2 ^ 16 by omega, mul_two_pow_or 16 (by omega)]
  rw [show (x0 * 2 ^ 8 + x1) * 2 ^ 16 + x2 * 2 ^ 8 = ((x0 * 2 ^ 8 + x1) * 2 ^ 8 + x2) * 2 ^ 8 by omega,
    mul_two_pow_or 8 h3]
  omega

def get32 : Fn := checked_fn% Net.prog, "get32"
#guard (Net.prog.check.toOption.bind (·.fn? "get32")) == some get32

/-- `((hi : u32) <<< 16) ||| (lo : u32)`, the way the semantics computes it. -/
theorem halves_value (hi lo : UInt16) :
    mask .w32 (mask .w32 (mask .w32 hi.toUInt64 <<< mask .w8 (UInt64.ofNat 16)) ||| mask .w32 lo.toUInt64)
      = (hi.toUInt32 <<< 16 ||| lo.toUInt32).toUInt64 := by
  have hk : mask .w8 (UInt64.ofNat 16) = 16 := rfl
  have hh := hi.toNat_lt
  have hl := lo.toNat_lt
  have h1 : UInt64.toNat 16 = 16 := rfl
  have h2 : UInt32.toNat 16 = 16 := rfl
  apply UInt64.toNat_inj.mp
  simp only [hk, toNat_mask32, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt16.toNat_toUInt64,
    UInt32.toNat_toUInt64, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32, h1, h2, Nat.reduceMod]
  have hs : (hi.toNat % 4294967296) <<< 16 = hi.toNat * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]; simp [Nat.shiftLeft_eq]
  have hs' : hi.toNat <<< 16 = hi.toNat * 65536 := by simp [Nat.shiftLeft_eq]
  rw [hs, hs']
  have e1 : hi.toNat * 65536 % 2 ^ 64 % 4294967296 = hi.toNat * 65536 := by omega
  have e2 : hi.toNat * 65536 % 2 ^ 32 = hi.toNat * 65536 := by omega
  have e3 : lo.toNat % 4294967296 = lo.toNat := by omega
  rw [e1, e2, e3]
  have hlt : hi.toNat * 65536 ||| lo.toNat < 2 ^ 32 := Nat.or_lt_two_pow (by omega) (by omega)
  omega

/-- **`get32` reads a big-endian 32-bit field** (`Bytes.get32`). -/
theorem get32_refines (p : Prog) (hp : p.fn? "get32" = some get32) (hg : p.fn? "get16" = some get16)
    (st : St) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) (o : UInt16)
    (ho : o.toNat + 3 < b.size) (ho' : o.toNat + 3 < 65536) (n : Nat) :
    Sem.call (n + 20) p st "get32" [u16 o] = .ok (some (u32 (Bytes.get32 b o.toNat))) st := by
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have h2 : mask .w16 (UInt64.ofNat 2) = (2 : UInt16).toUInt64 := rfl
  have ho2 : (o + 2).toNat = o.toNat + 2 := by
    have : (2 : UInt16).toNat = 2 := rfl
    simp only [UInt16.toNat_add, this]; omega
  simp only [Sem.call, hp, get32, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, hz, List.map,
    List.zip, List.zipWith]
  rw [execS_get16 p hg st _ b hb (o := o) (ho := by omega) (ho' := by omega)
    (he := by simp [evalE, lookup, List.lookup])]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true]
  have e2 : evalE p st [("lo", u16 0), ("hi", u16 (Bytes.get16 b o.toNat)), ("o", u16 o)]
      (.bin .add (.var "o") (.lit 2 (some .w16))) = some (u16 (o + 2)) := by
    have eo : evalE p st [("lo", u16 0), ("hi", u16 (Bytes.get16 b o.toNat)), ("o", u16 o)] (.var "o")
        = some (u16 o) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, eo, Sem.binop, h2, mask16_add]
  rw [execS_get16 p hg st _ b hb (o := o + 2) (ho := by omega) (ho' := by omega) (he := e2)]
  simp only [storeResult, assign, update, setFirst, List.lookup, beq_self_eq_true, ite_true, ho2]
  have h16 : ¬ ((mask .w8 (UInt64.ofNat 16)).toNat ≥ Width.bits .w32) := by decide
  have hv : evalE p st [("lo", u16 (Bytes.get16 b (o.toNat + 2))), ("hi", u16 (Bytes.get16 b o.toNat)),
        ("o", u16 o)]
      (.bin .bor (.bin .shl (.cast .w32 (.var "hi")) (.lit 16 (some .w8))) (.cast .w32 (.var "lo")))
      = some (u32 (Bytes.get32 b o.toNat)) := by
    have ehi : lookup st [("lo", u16 (Bytes.get16 b (o.toNat + 2))), ("hi", u16 (Bytes.get16 b o.toNat)),
        ("o", u16 o)] "hi" = some (u16 (Bytes.get16 b o.toNat)) := by simp [lookup, List.lookup]
    have elo : lookup st [("lo", u16 (Bytes.get16 b (o.toNat + 2))), ("hi", u16 (Bytes.get16 b o.toNat)),
        ("o", u16 o)] "lo" = some (u16 (Bytes.get16 b (o.toNat + 2))) := by simp [lookup, List.lookup]
    simp only [evalE, ehi, elo, Sem.binop, h16, if_false, halves_value, get32_eq_halves]
  simp only [execS_ret_some, hv]

/-- A call of `get32` as a statement. -/
theorem execS_get32 (p : Prog) (hp : p.fn? "get32" = some get32) (hg : p.fn? "get16" = some get16)
    (st : St) (env : Env) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) (dst : Option Expr)
    (eo : Expr) (o : UInt16) (n : Nat) (ho : o.toNat + 3 < b.size) (ho' : o.toNat + 3 < 65536)
    (he : evalE p st env eo = some (u16 o)) :
    execS (n + 21) p st env (.call dst "get32" [eo]) =
      storeResult p st env dst (some (u32 (Bytes.get32 b o.toNat))) :=
  execS_call_val p st env (n + 20) dst "get32" [eo] hp (by simp [get32]) (by simp [evalArgs, he])
    (get32_refines p hp hg st b hb o ho ho' n)

/-- A call of `set16` as a statement. -/
theorem execS_set16 (p : Prog) (hp : p.fn? "set16" = some set16) (st : St) (env : Env) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (eo ev : Expr) (o v : UInt16) (n : Nat)
    (ho : o.toNat + 1 < b.size) (ho' : o.toNat + 1 < 65536)
    (he : evalE p st env eo = some (u16 o)) (hv : evalE p st env ev = some (u16 v)) :
    execS (n + 9) p st env (.call none "set16" [eo, ev]) =
      .ok (withBuf st (Bytes.set16 b o.toNat v)) env .normal :=
  execS_call_val p st env (n + 8) none "set16" [eo, ev] hp (by simp [set16]) (by simp [evalArgs, he, hv])
    (set16_refines p hp st b hb o v ho ho' n)

/-- Writing a 32-bit field is writing its halves. -/
theorem set32_eq_halves (b : ByteArray) (i : Nat) (v : UInt32) :
    Bytes.set16 (Bytes.set16 b i (v >>> 16).toUInt16) (i + 2) v.toUInt16 = Bytes.set32 b i v := by
  have e1 : ((v >>> 16).toUInt16 >>> 8).toUInt8 = (v >>> 24).toUInt8 := by
    apply UInt8.toNat_inj.mp
    have := v.toNat_lt
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt32.toNat_toUInt16, UInt32.toNat_shiftRight,
      UInt32.toNat_toUInt8, UInt32.reduceToNat, UInt16.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : (v >>> 16).toUInt16.toUInt8 = (v >>> 16).toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt32.toNat_toUInt16, UInt32.toNat_toUInt8]
    omega
  have e3 : (v.toUInt16 >>> 8).toUInt8 = (v >>> 8).toUInt8 := by
    apply UInt8.toNat_inj.mp
    have := v.toNat_lt
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt32.toNat_toUInt16, UInt32.toNat_shiftRight,
      UInt32.toNat_toUInt8, UInt32.reduceToNat, UInt16.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    omega
  have e4 : v.toUInt16.toUInt8 = v.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt32.toNat_toUInt16, UInt32.toNat_toUInt8]
    omega
  simp only [Bytes.set16, Bytes.set32, e1, e2, e3, e4]

def set32 : Fn := checked_fn% Net.prog, "set32"
#guard (Net.prog.check.toOption.bind (·.fn? "set32")) == some set32

/-- **`set32` writes a big-endian 32-bit field** (`Bytes.set32`). -/
theorem set32_refines (p : Prog) (hp : p.fn? "set32" = some set32) (hs : p.fn? "set16" = some set16)
    (st : St) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) (o : UInt16) (v : UInt32)
    (ho : o.toNat + 3 < b.size) (ho' : o.toNat + 3 < 65536) (n : Nat) :
    Sem.call (n + 20) p st "set32" [u16 o, u32 v] = .ok none (withBuf st (Bytes.set32 b o.toNat v)) := by
  have h2 : mask .w16 (UInt64.ofNat 2) = (2 : UInt16).toUInt64 := rfl
  have ho2 : (o + 2).toNat = o.toNat + 2 := by
    have : (2 : UInt16).toNat = 2 := rfl
    simp only [UInt16.toNat_add, this]; omega
  let b1 := Bytes.set16 b o.toNat (v >>> 16).toUInt16
  have hb1 : (withBuf st b1).globals.lookup "buf" = some (bufVal b1) := lookup_withBuf st b b1 hb
  have hsz1 : b1.size = b.size := by simp [b1]
  simp only [Sem.call, hp, set32, execB_succ, execL_cons, execL_nil, execS_at, List.map, List.zip, List.zipWith]
  rw [execS_set16 p hs st _ b hb (o := o) (v := (v >>> 16).toUInt16) (ho := by omega) (ho' := by omega)
    (he := by simp [evalE, lookup, List.lookup])
    (hv := evalE_hi16 p st _ "v" v (by simp [lookup, List.lookup]))]
  have e2 : evalE p (withBuf st b1) [("o", u16 o), ("v", u32 v)] (.bin .add (.var "o") (.lit 2 (some .w16)))
      = some (u16 (o + 2)) := by
    have eo : evalE p (withBuf st b1) [("o", u16 o), ("v", u32 v)] (.var "o") = some (u16 o) := by
      simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, eo, Sem.binop, h2, mask16_add]
  simp only []
  rw [execS_set16 p hs (withBuf st b1) _ b1 hb1 (o := o + 2) (v := v.toUInt16) (ho := by omega) (ho' := by omega)
    (he := e2) (hv := evalE_lo16 p _ _ "v" v (by simp [lookup, List.lookup]))]
  simp only [ho2, withBuf_withBuf, b1, set32_eq_halves]

/-! ## The SLIP receiver -/

def slip_store : Fn := checked_fn% Net.prog, "slip_store"
#guard (Net.prog.check.toOption.bind (·.fn? "slip_store")) == some slip_store
#guard (Net.Loop.prog.check.toOption.bind (·.fn? "slip_store")) == some slip_store

/-- `slip_store(c)` on the receiver's globals, as they are. -/
theorem slip_store_spec (p : Prog) (hp : p.fn? "slip_store" = some slip_store) (st : St) (b : ByteArray)
    (len mtu : UInt16) (esc over : Bool)
    (hbuf : st.globals.lookup "buf" = some (bufVal b)) (hlen : st.globals.lookup "len" = some (u16 len))
    (hesc : st.globals.lookup "esc" = some (.bool esc)) (hover : st.globals.lookup "over" = some (.bool over))
    (hmtu : st.globals.lookup "MTU" = some (u16 mtu)) (hsz : mtu.toNat ≤ b.size) (c : UInt8) (n : Nat) :
    Sem.call (n + 12) p st "slip_store" [u8 c] = .ok none
      (if over then setG st "esc" (.bool false)
       else if len < mtu then
         setG (setG (setG st "buf" (bufVal (Bytes.set b len.toNat c))) "len" (u16 (len + 1))) "esc" (.bool false)
       else setG (setG (setG st "over" (.bool true)) "len" (u16 0)) "esc" (.bool false)) := by
  by_cases ho : over
  · subst ho
    simp [Sem.call, hp, slip_store, execB_succ, execL_cons, execS_at, execS_ite, execS_assign,
      execS_ret_none, evalE, lookup, List.lookup, hover, hesc, assign_var, Val.toBool]
  · have ho' : over = false := by simpa using ho
    subst ho'
    have h1 : mask .w16 (UInt64.ofNat 1) = (1 : UInt16).toUInt64 := rfl
    by_cases hl : len < mtu
    · have hk : len.toNat < b.size := by
        have := UInt16.lt_iff_toNat_lt.mp hl
        omega
      have a1 := assign_buf p st [("c", u8 c)] b (.var "len") len c (by simp [List.lookup]) hbuf
        (by simp [evalE, lookup, List.lookup, hlen]) hk
      rw [withBuf_eq] at a1
      simp [Sem.call, hp, slip_store, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign,
        execS_ret_none, evalE, lookup, List.lookup, hover, hesc, hlen, hmtu, hbuf, assign_var, a1,
        Val.toBool, Sem.binop, toUInt64_lt_iff, hl, lookup_setG_ne, lookup_setG_self, mask16_zero, mask16_one, mask16_add_one]
      have e : (len.toUInt64 + 1) % 65536 = (len + 1).toUInt64 := by
        apply UInt64.toNat_inj.mp
        have t1 : UInt64.toNat 1 = 1 := rfl
        have t2 : UInt64.toNat 65536 = 65536 := rfl
        have t3 : UInt16.toNat 1 = 1 := rfl
        have := len.toNat_lt
        simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt16.toNat_toUInt64, UInt16.toNat_add, t1, t2, t3]
        omega
      rw [e]
    · simp [Sem.call, hp, slip_store, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign,
        execS_ret_none, evalE, lookup, List.lookup, hover, hesc, hlen, hmtu, hbuf, assign_var,
        Val.toBool, Sem.binop, toUInt64_lt_iff, hl, lookup_setG_ne, lookup_setG_self, mask16_zero, mask16_add_one]
      rfl

/-! ## The SLIP transmitter -/

def slip_send : Fn := checked_fn% Net.prog, "slip_send"
#guard (Net.prog.check.toOption.bind (·.fn? "slip_send")) == some slip_send
#guard (Net.Loop.prog.check.toOption.bind (·.fn? "slip_send")) == some slip_send

/-- The body of the loop of `slip_send`. -/
def sendBody : List Stmt :=
  match slip_send.body with
  | [_, .at _ (.forRange _ _ _ _ body), _, _] => body
  | _ => []

/-- One iteration: byte `i` of the buffer goes out escaped. -/
theorem send_body (p : Prog) (st : St) (b : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b))
    (nn : UInt16) (i : Nat) (hi : i < b.size) (hi' : i < 65536) (m : Nat) :
    execB (m + 20) p st [("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] sendBody
      = .ok (pushOut st (Spec.Slip.encodeByte (Bytes.get b i))) [("i", u16 (UInt16.ofNat i)), ("n", u16 nn)]
          .normal := by
  have hidx : (u16 (UInt16.ofNat i)).toNat = i := by
    simp [Val.toNat]; omega
  have hget := bufVal_get b i hi
  have ec : evalE p st [("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] (.index (.var "buf") (.var "i"))
      = some (u8 (Bytes.get b i)) := by
    have e1 : lookup st [("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] "buf" = some (bufVal b) := by
      simp [lookup, List.lookup, hb]
    have e2 : lookup st [("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] "i" = some (u16 (UInt16.ofNat i)) := by
      simp [lookup, List.lookup]
    simp only [evalE, e1, e2, bufVal, hidx, hget]
  generalize Bytes.get b i = c at ec
  have k192 : mask .w8 (UInt64.ofNat 192) = (192 : UInt8).toUInt64 := rfl
  have k219 : mask .w8 (UInt64.ofNat 219) = (219 : UInt8).toUInt64 := rfl
  have k220 : mask .w8 (UInt64.ofNat 220) = (220 : UInt8).toUInt64 := rfl
  have k221 : mask .w8 (UInt64.ofNat 221) = (221 : UInt8).toUInt64 := rfl
  simp only [sendBody, slip_send, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_some, ec, execS_ite]
  have ecv : ∀ k : Nat, ∀ kv : UInt8, mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
      evalE p st [("c", u8 c), ("i", u16 (UInt16.ofNat i)), ("n", u16 nn)]
        (.bin .eq (.var "c") (.lit k (some .w8))) = some (.bool (c == kv)) := by
    intro k kv hk
    have e1 : evalE p st [("c", u8 c), ("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] (.var "c") = some (u8 c) := by
      simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, e1, Sem.binop, hk, toUInt64_eq_iff8]
  have elit : ∀ k : Nat, ∀ kv : UInt8, mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
      ∀ st' : St, evalE p st' [("c", u8 c), ("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] (.lit k (some .w8))
        = some (u8 kv) := by
    intro k kv hk st'
    rw [evalE_lit, hk]
  rw [ecv 192 192 k192]
  by_cases h1 : c = 192
  · subst h1
    simp only [Val.toBool, beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at]
    rw [execS_out p _ _ _ _ 219 (elit 219 219 k219 _)]
    simp only []
    rw [execS_out p _ _ _ _ 220 (elit 220 220 k220 _)]
    simp only [pushOut_pushOut]
    rfl
  · have h1' : (c == 192) = false := by simp [h1]
    simp only [Val.toBool, h1', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at,
      execS_ite]
    rw [ecv 219 219 k219]
    by_cases h2 : c = 219
    · subst h2
      simp only [Val.toBool, beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at]
      rw [execS_out p _ _ _ _ 219 (elit 219 219 k219 _)]
      simp only []
      rw [execS_out p _ _ _ _ 221 (elit 221 221 k221 _)]
      simp only [pushOut_pushOut]
      rfl
    · have h2' : (c == 219) = false := by simp [h2]
      have e1 : evalE p st [("c", u8 c), ("i", u16 (UInt16.ofNat i)), ("n", u16 nn)] (.var "c") = some (u8 c) := by
        simp [evalE, lookup, List.lookup]
      simp only [Val.toBool, h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at]
      rw [execS_out p _ _ _ _ c e1]
      have : Spec.Slip.encodeByte c = [c] := by
        simp [Spec.Slip.encodeByte, Spec.Slip.END, Spec.Slip.ESC, h1, h2]
      rw [this]
      rfl

/-- The loop of `slip_send`: `k` more bytes from index `cur` on go out. -/
theorem send_loop (p : Prog) (b : ByteArray) (nn : UInt16) (hi : Nat) (hsz : hi ≤ b.size) (hsz' : hi ≤ 65536) :
    ∀ (k cur : Nat) (st : St) (v0 : Val) (d : Nat), st.globals.lookup "buf" = some (bufVal b) → cur + k = hi →
      ∃ v, forLoop (k + 21 + d) p st [("i", v0), ("n", u16 nn)] "i" .w16 cur hi sendBody
          = .ok (pushOut st ((List.range' cur k).flatMap fun j => Spec.Slip.encodeByte (Bytes.get b j)))
              [("i", v), ("n", u16 nn)] .normal := by
  intro k
  induction k with
  | zero =>
    intro cur st v0 d _ hk
    have : ¬ cur < hi := by omega
    refine ⟨v0, ?_⟩
    rw [show 0 + 21 + d = (20 + d) + 1 by omega, forLoop_succ]
    simp [this, pushOut]
  | succ k ih =>
    intro cur st v0 d hb hk
    have hlt : cur < hi := by omega
    have hcur : cur < 65536 := by omega
    obtain ⟨v, hv⟩ := ih (cur + 1) (pushOut st (Spec.Slip.encodeByte (Bytes.get b cur)))
      (u16 (UInt16.ofNat cur)) d hb (by omega)
    refine ⟨v, ?_⟩
    rw [show k + 1 + 21 + d = (k + 21 + d) + 1 by omega, forLoop_succ]
    simp only [hlt, if_true, setFirst, beq_self_eq_true, ofNat_u16 cur hcur]
    rw [show k + 21 + d = (k + 1 + d) + 20 by omega,
      send_body p st b hb nn cur (by omega) hcur (k + 1 + d)]
    simp only []
    rw [show k + 1 + d + 20 = k + 21 + d by omega, hv]
    simp [List.range'_succ, pushOut_pushOut]

/-- A byte array is its list of bytes. -/
theorem eq_of_toList_eq {a c : ByteArray} (h : a.toList = c.toList) : a = c := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← Spec.Slip.toList_eq, ← Spec.Slip.toList_eq, h]

theorem toList_extract (b : ByteArray) (n : Nat) (h : n ≤ b.size) :
    (b.extract 0 n).toList = (List.range' 0 n).map fun j => Bytes.get b j := by
  rw [Spec.Slip.toList_eq]
  apply List.ext_getElem
  · have : (b.extract 0 n).size = n := by simp [ByteArray.size_extract]; omega
    simpa using this
  · intro i h1 h2
    simp at h2
    have : i < b.size := by omega
    simp [Bytes.get, this, ByteArray.getElem_eq_getElem_data]

/-- The state after a frame has gone out. -/
def txOut (st : St) (f : ByteArray) : St :=
  { st with world := { (st.world.emit (.tx f)) with frame := .empty } }

@[simp] theorem globals_txOut (st : St) (f : ByteArray) : (txOut st f).globals = st.globals := rfl

/-- **`slip_send` transmits `Spec.Slip.encode`** of the first `n` bytes
of the buffer, as one frame; nothing else changes.  (Bytes already in
the frame — there are none when the stack calls it — stay in front.) -/
theorem slip_send_refines (p : Prog) (hp : p.fn? "slip_send" = some slip_send) (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (n : UInt16) (hn : n.toNat ≤ b.size) (d : Nat) :
    Sem.call (d + n.toNat + 40) p st "slip_send" [u16 n]
      = .ok none (txOut st (st.world.frame ++ Spec.Slip.encode (b.extract 0 n.toNat))) := by
  have k192 : mask .w8 (UInt64.ofNat 192) = (192 : UInt8).toUInt64 := rfl
  have e192 : ∀ (st' : St) (env : Env), evalE p st' env (.lit 192 (some .w8)) = some (u8 192) := by
    intro st' env; rw [evalE_lit, k192]
  have e_lo : ∀ st' : St, evalE p st' [("n", u16 n)] (.lit 0 (some .w16)) = some (u16 0) := by
    intro st'; rw [evalE_lit]; rfl
  have e_hi : ∀ st' : St, evalE p st' [("n", u16 n)] (.var "n") = some (u16 n) := by
    intro st'; simp [evalE, lookup, List.lookup]
  have t0 : (u16 (0 : UInt16)).toNat = 0 := rfl
  have thi : (u16 n).toNat = n.toNat := by simp [Val.toNat]
  obtain ⟨v, hv⟩ := send_loop p b n n.toNat hn (by have := n.toNat_lt; omega) n.toNat 0 (pushOut st [192])
    (.int .w16 (UInt64.ofNat 0)) (d + 14) hb (by omega)
  simp only [sendBody, slip_send] at hv
  simp only [Sem.call, hp, slip_send, execB_succ, execL_cons, execL_nil, execS_at, List.map, List.zip,
    List.zipWith]
  rw [execS_out p _ _ _ _ 192 (e192 _ _)]
  simp only [execS_forRange, e_lo, e_hi, t0, thi, Option.getD]
  rw [show d + n.toNat + 35 = n.toNat + 21 + (d + 14) by omega, hv]
  simp only [List.drop]
  rw [show n.toNat + 21 + (d + 14) = (d + n.toNat + 34) + 1 by omega, execS_out p _ _ _ _ 192 (e192 _ _)]
  simp only [pushOut_pushOut, execS_eff, evalArgs, Sem.effect, storeResult]
  have F : List.foldl ByteArray.push st.world.frame
      ([192] ++ List.flatMap (fun j => Spec.Slip.encodeByte (Bytes.get b j)) (List.range' 0 n.toNat) ++ [192])
      = st.world.frame ++ Spec.Slip.encode (b.extract 0 n.toNat) := by
    apply eq_of_toList_eq
    rw [Spec.Slip.toList_foldl_push, Spec.Slip.toList_append, Spec.Slip.toList_encode, toList_extract b _ hn]
    simp [Spec.Slip.END, List.flatMap_map]
  simp only [txOut, pushOut, World.emit, F]

/-! ## The receiver's globals and the decoder state -/

/-- Global `x` has the same value in both states. -/
def SameG (st st' : St) (x : String) : Prop := st'.globals.lookup x = st.globals.lookup x

/-- The receiver's globals hold the decoder state `d`: `len` bytes of
`buf` are the frame so far. -/
def SlipRel (st : St) (d : Spec.Slip.Dec) (mtu : UInt16) : Prop :=
  ∃ b : ByteArray, st.globals.lookup "buf" = some (bufVal b) ∧ mtu.toNat ≤ b.size ∧ d.buf.size ≤ mtu.toNat ∧
    st.globals.lookup "len" = some (u16 (UInt16.ofNat d.buf.size)) ∧
    st.globals.lookup "esc" = some (.bool d.esc) ∧ st.globals.lookup "over" = some (.bool d.over) ∧
    st.globals.lookup "MTU" = some (u16 mtu) ∧ b.extract 0 d.buf.size = d.buf

/-- The packet buffer has `N` bytes. -/
def BufSize (st : St) (N : Nat) : Prop := ∃ b : ByteArray, st.globals.lookup "buf" = some (bufVal b) ∧ b.size = N

theorem bufVal_size_eq {a b : ByteArray} (h : bufVal a = bufVal b) : a.size = b.size := by
  have h' := congrArg (fun v => match v with | Val.arr xs => xs.size | _ => 0) h
  simp only [bufVal, Array.size_map] at h'
  exact h'

theorem extract_set_push (b : ByteArray) (k : Nat) (c : UInt8) (hk : k < b.size) :
    (Bytes.set b k c).extract 0 (k + 1) = (b.extract 0 k).push c := by
  apply eq_of_toList_eq
  rw [toList_extract _ _ (by simp; omega), Spec.Slip.toList_push, toList_extract _ _ (by omega),
    List.range'_concat]
  simp only [List.map_append, List.map_cons, List.map_nil, Nat.zero_add]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have : j < k := by simpa using hj
    rw [Bytes.get_set]
    simp; omega
  · rw [Bytes.get_set]; simp [hk]

/-- **`slip_store` is `Spec.Slip.Dec.store`**: on globals that hold the
decoder state `d`, the call leaves globals that hold `d.store c mtu`.
No event, and no other global changes. -/
theorem slip_store_refines (p : Prog) (hp : p.fn? "slip_store" = some slip_store) (st : St)
    (d : Spec.Slip.Dec) (mtu : UInt16) (hrel : SlipRel st d mtu) (c : UInt8) (n : Nat) :
    ∃ st', Sem.call (n + 12) p st "slip_store" [u8 c] = .ok none st' ∧ SlipRel st' (d.store c mtu.toNat) mtu ∧
      st'.world = st.world ∧ (∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → SameG st st' x) ∧
      ∀ N, BufSize st N → BufSize st' N := by
  obtain ⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre⟩ := hrel
  have hm := mtu.toNat_lt
  have hbs : ∀ (b0 : ByteArray), st.globals.lookup "buf" = some (bufVal b0) → b0.size = b.size := by
    intro b0 h0
    exact bufVal_size_eq (Option.some.inj (h0.symm.trans hbuf))
  rw [slip_store_spec p hp st b _ mtu _ _ hbuf hlen hesc hover hmtu hsz c n]
  have hlt : (UInt16.ofNat d.buf.size < mtu) ↔ d.buf.size < mtu.toNat := by
    rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_ofNat']
    have : d.buf.size % 2 ^ 16 = d.buf.size := Nat.mod_eq_of_lt (by omega)
    rw [this]
  cases hov : d.over with
  | true =>
    refine ⟨_, rfl, ⟨b, ?_⟩, rfl, ?_, ?_⟩
    · simp [Spec.Slip.Dec.store, hov, lookup_setG_ne, lookup_setG_self, hbuf, hsz, hle, hlen, hesc, hover, hmtu,
        hpre]
    · intro x _ _ h3 _
      exact lookup_setG_ne _ _ _ _ (Ne.symm h3)
    · intro N ⟨b0, h0, hN⟩
      exact ⟨b0, (lookup_setG_ne st "esc" "buf" _ (by decide)).trans h0, hN⟩
  | false =>
    simp only [Bool.false_eq_true, if_false]
    by_cases hl : d.buf.size < mtu.toNat
    · have hl' := hlt.mpr hl
      rw [if_pos hl']
      have hk : (UInt16.ofNat d.buf.size).toNat = d.buf.size := by
        rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hinc : UInt16.ofNat d.buf.size + 1 = UInt16.ofNat (d.buf.size + 1) := by
        apply UInt16.toNat_inj.mp
        have t1 : UInt16.toNat 1 = 1 := rfl
        simp only [UInt16.toNat_add, UInt16.toNat_ofNat', t1]
        omega
      refine ⟨_, rfl, ⟨Bytes.set b d.buf.size c, ?_⟩, rfl, ?_, ?_⟩
      rotate_left 2
      · intro N ⟨b0, h0, hN⟩
        refine ⟨Bytes.set b (UInt16.ofNat d.buf.size).toNat c, ?_, ?_⟩
        · simp [lookup_setG_ne, lookup_setG_self, hbuf]
        · rw [Bytes.size_set, ← hbs b0 h0, hN]
      · have hp' := extract_set_push b d.buf.size c (by omega)
        rw [hpre] at hp'
        rw [hk, hinc]
        simp [Spec.Slip.Dec.store, hov, hl, lookup_setG_ne, lookup_setG_self, hbuf, hsz, hlen, hesc,
          hover, hmtu, hp', ByteArray.size_push]
        omega
      · intro x h1 h2 h3 _
        simp only [SameG]
        rw [lookup_setG_ne _ _ _ _ (Ne.symm h3), lookup_setG_ne _ _ _ _ (Ne.symm h2),
          lookup_setG_ne _ _ _ _ (Ne.symm h1)]
    · have hl' : ¬ (UInt16.ofNat d.buf.size < mtu) := fun h => hl (hlt.mp h)
      rw [if_neg hl']
      refine ⟨_, rfl, ⟨b, ?_⟩, rfl, ?_, ?_⟩
      · simp [Spec.Slip.Dec.store, hov, hl, hl', lookup_setG_ne, lookup_setG_self, hbuf, hsz, hlen, hesc,
          hover, hmtu]
      · intro x _ h2 h3 h4
        simp only [SameG]
        rw [lookup_setG_ne _ _ _ _ (Ne.symm h3), lookup_setG_ne _ _ _ _ (Ne.symm h2),
          lookup_setG_ne _ _ _ _ (Ne.symm h4)]
      · intro N ⟨b0, h0, hN⟩
        exact ⟨b0, by simp [lookup_setG_ne, h0], hN⟩

/-- A call of `slip_store` as a statement. -/
theorem execS_slip_store (p : Prog) (hp : p.fn? "slip_store" = some slip_store) (st : St) (env : Env)
    (d : Spec.Slip.Dec) (mtu : UInt16) (hrel : SlipRel st d mtu) (e : Expr) (c : UInt8)
    (he : evalE p st env e = some (u8 c)) (m n : Nat) (hm : m = n + 13) :
    ∃ st', execS m p st env (.call none "slip_store" [e]) = .ok st' env .normal ∧
      SlipRel st' (d.store c mtu.toNat) mtu ∧ st'.world = st.world ∧
      (∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → SameG st st' x) ∧
      ∀ N, BufSize st N → BufSize st' N := by
  subst hm
  obtain ⟨st', hc, h2, h3, h4⟩ := slip_store_refines p hp st d mtu hrel c n
  refine ⟨st', ?_, h2, h3, h4⟩
  exact execS_call_val p st env (n + 12) none "slip_store" [e] hp (by simp [slip_store])
    (by simp [evalArgs, he]) hc

/-! ## The SLIP loopback (`Ember.Net.Loop`) -/

def loop_rx : Fn := checked_fn% Net.Loop.prog, "loop_rx"
#guard (Net.Loop.prog.check.toOption.bind (·.fn? "loop_rx")) == some loop_rx

def loop_main : Fn := checked_fn% Net.Loop.prog, "main"
#guard (Net.Loop.prog.check.toOption.bind (·.fn? "main")) == some loop_main

/-- A program with the loopback's functions. -/
structure LoopProg (p : Prog) : Prop where
  store : p.fn? "slip_store" = some slip_store
  send : p.fn? "slip_send" = some slip_send
  rx : p.fn? "loop_rx" = some loop_rx
  main : p.fn? "main" = some loop_main
  reason : p.dropReasons[0]? = some "oversize-frame"

/-- What the loopback puts into the trace for a decoder result. -/
def loopOut (w : World) : Spec.Slip.Result → World
  | .none => w
  | .drop r => w.emit (.drop r)
  | .frame f => w.emit (.tx (Spec.Slip.encode f))

/-- The loopback's state between two calls: the globals hold the decoder
state, no frame is half transmitted. -/
def LoopInv (st : St) (d : Spec.Slip.Dec) (mtu : UInt16) : Prop :=
  SlipRel st d mtu ∧ st.world.frame = .empty ∧ st.globals.lookup "D_OVERSIZE" = some (u8 0)

theorem toUInt64_gt_zero (x : UInt16) : decide (x.toUInt64 > 0) = decide (0 < x.toNat) := by
  have : x.toUInt64 > 0 ↔ 0 < x.toNat := by
    show (0 : UInt64) < x.toUInt64 ↔ _
    rw [UInt64.lt_iff_toNat_lt]; simp
  simp [this]

/-- After `END`: the receiver is reset. -/
theorem inv_reset (st : St) (b : ByteArray) (mtu : UInt16) (vl ve vo : Val)
    (hbuf : st.globals.lookup "buf" = some (bufVal b)) (hsz : mtu.toNat ≤ b.size)
    (hlen : st.globals.lookup "len" = some vl) (hesc : st.globals.lookup "esc" = some ve)
    (hover : st.globals.lookup "over" = some vo) (hmtu : st.globals.lookup "MTU" = some (u16 mtu))
    (hfr : st.world.frame = .empty) (hdo : st.globals.lookup "D_OVERSIZE" = some (u8 0)) :
    LoopInv (setG (setG (setG st "len" (.int .w16 0)) "esc" (.bool false)) "over" (.bool false)) {} mtu := by
  refine ⟨⟨b, ?_⟩, hfr, ?_⟩
  · simp [lookup_setG_ne, lookup_setG_self, hbuf, hsz, hlen, hesc, hover, hmtu]
  · simp [lookup_setG_ne, hdo]

/-- **`loop_rx` is one step of the decoder** (`Spec.Slip.Dec.feed`): the
globals go from holding `d` to holding the next decoder state, and what
the step yields appears in the trace — nothing, the drop of an oversize
frame, or the completed frame transmitted SLIP-encoded. -/
theorem loop_rx_refines (p : Prog) (hP : LoopProg p) (st : St) (d : Spec.Slip.Dec) (mtu : UInt16)
    (hinv : LoopInv st d mtu) (c : UInt8) (n : Nat) :
    ∃ st', Sem.call (n + mtu.toNat + 60) p st "loop_rx" [u8 c] = .ok none st' ∧
      LoopInv st' (d.feed c mtu.toNat).1 mtu ∧ st'.world = loopOut st.world (d.feed c mtu.toNat).2 := by
  have hrel := hinv.1
  obtain ⟨⟨b, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre⟩, hfr, hdo⟩ := hinv
  have hm := mtu.toNat_lt
  have k192 : mask .w8 (UInt64.ofNat 192) = (192 : UInt8).toUInt64 := rfl
  have k219 : mask .w8 (UInt64.ofNat 219) = (219 : UInt8).toUInt64 := rfl
  have k220 : mask .w8 (UInt64.ofNat 220) = (220 : UInt8).toUInt64 := rfl
  have k221 : mask .w8 (UInt64.ofNat 221) = (221 : UInt8).toUInt64 := rfl
  have ecv : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
      evalE p st' [("c", u8 c)] (.bin .eq (.var "c") (.lit k (some .w8))) = some (.bool (c == kv)) := by
    intro st' k kv hk
    have e1 : evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, e1, Sem.binop, hk, toUInt64_eq_iff8]
  have hk : (UInt16.ofNat d.buf.size).toNat = d.buf.size := by
    rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Sem.call, hP.rx, loop_rx, execB_succ, execL_cons, execS_at, execS_ite, List.map, List.zip,
    List.zipWith, ecv st 192 192 k192]
  by_cases h1 : c = 192
  · subst h1
    have hfeed : Spec.Slip.Dec.feed d 192 mtu.toNat = (({} : Spec.Slip.Dec),
        if d.over then Spec.Slip.Result.drop "oversize-frame"
        else if d.buf.size == 0 then Spec.Slip.Result.none else Spec.Slip.Result.frame d.buf) := rfl
    rw [hfeed]
    cases hov : d.over with
    | true =>
      rw [hov] at hover
      simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
        evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
        Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, hP.reason]
      exact ⟨inv_reset _ b mtu _ _ _ hbuf hsz hlen hesc hover hmtu hfr hdo, rfl⟩
    | false =>
      rw [hov] at hover
      by_cases h0 : d.buf.size = 0
      · have hlen0 : st.globals.lookup "len" = some (u16 0) := by rw [hlen, h0]; rfl
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen0, hdo, assign_var,
          Val.toBool, Val.toNat, lookup_setG_ne, lookup_setG_self, mask16_zero, hP.reason, Sem.binop, h0]
        exact ⟨inv_reset _ b mtu _ _ _ hbuf hsz hlen hesc hover hmtu hfr hdo, rfl⟩
      · have hpos : decide (0 < (UInt16.ofNat d.buf.size).toNat) = true := by simp [hk]; omega
        have hpos' : 0 < d.buf.size := by omega
        have hmod : d.buf.size % 65536 = d.buf.size := Nat.mod_eq_of_lt (by omega)
        have hsend : execS (n + mtu.toNat + 45) p st [("c", u8 192)] (.call none "slip_send" [.var "len"])
            = .ok (txOut st (st.world.frame ++ Spec.Slip.encode (b.extract 0 (UInt16.ofNat d.buf.size).toNat)))
                [("c", u8 192)] .normal := by
          have hc := slip_send_refines p hP.send st b hbuf (UInt16.ofNat d.buf.size) (by omega)
            (n + (mtu.toNat - d.buf.size) + 4)
          rw [show n + (mtu.toNat - d.buf.size) + 4 + (UInt16.ofNat d.buf.size).toNat + 40
            = n + mtu.toNat + 44 by omega] at hc
          exact execS_call_val p st _ (n + mtu.toNat + 44) none "slip_send" [.var "len"] hP.send
            (by simp [slip_send]) (by simp [evalArgs, evalE, lookup, List.lookup, hlen]) hc
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_ite, execS_assign, execS_ret_none, execS_eff,
          evalArgs, Sem.effect, storeResult, evalE, lookup, List.lookup, hover, hesc, hlen, hdo, assign_var,
          Val.toBool, lookup_setG_ne, lookup_setG_self, mask16_zero, hP.reason, Sem.binop,
          toUInt64_gt_zero, hpos, h0, hmod, hsend, hpos']
        refine ⟨inv_reset (txOut st _) b mtu _ _ _ hbuf hsz hlen hesc hover hmtu rfl hdo, ?_⟩
        simp [txOut, loopOut, hk, hpre, hfr, World.emit]
  · have h1' : (c == 192) = false := by simp [h1]
    have hEND : (c == Spec.Slip.END) = false := h1'
    have evc : ∀ st' : St, evalE p st' [("c", u8 c)] (.var "c") = some (u8 c) := by
      intro st'; simp [evalE, lookup, List.lookup]
    have elit : ∀ (st' : St) (k : Nat) (kv : UInt8), mask .w8 (UInt64.ofNat k) = kv.toUInt64 →
        evalE p st' [("c", u8 c)] (.lit k (some .w8)) = some (u8 kv) := by
      intro st' k kv hk; rw [evalE_lit, hk]
    have eesc : evalE p st [("c", u8 c)] (.var "esc") = some (.bool d.esc) := by
      simp [evalE, lookup, List.lookup, hesc]
    -- every case that stores a byte ends the same way
    have fin : ∀ (st' : St) (v : UInt8), SlipRel st' (d.store v mtu.toNat) mtu → st'.world = st.world →
        (∀ x, x ≠ "buf" → x ≠ "len" → x ≠ "esc" → x ≠ "over" → SameG st st' x) →
        Spec.Slip.Dec.feed d c mtu.toNat = (d.store v mtu.toNat, .none) →
        LoopInv st' (d.feed c mtu.toNat).1 mtu ∧ st'.world = loopOut st.world (d.feed c mtu.toNat).2 := by
      intro st' v hr hw hs hf
      rw [hf]
      refine ⟨⟨hr, by rw [hw]; exact hfr, ?_⟩, by rw [hw]; rfl⟩
      rw [hs "D_OVERSIZE" (by decide) (by decide) (by decide) (by decide)]; exact hdo
    simp only [Val.toBool, h1', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at,
      execS_ite, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero, eesc]
    cases hde : d.esc with
    | true =>
      simp only [if_true, execB_succ, execL_cons, execL_nil, execS_at, execS_ite, ecv st 220 220 k220, Val.toBool]
      by_cases h2 : c = 220
      · subst h2
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.store st [("c", u8 220)] d mtu hrel _ 192
          (elit st 192 192 k192) (n + mtu.toNat + 48) (n + mtu.toNat + 35) (by omega)
        simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
        exact ⟨st', rfl, fin st' 192 hr hw hsm.1 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, hde])⟩
      · have h2' : (c == 220) = false := by simp [h2]
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
          ecv st 221 221 k221, Val.toBool]
        by_cases h3 : c = 221
        · subst h3
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.store st [("c", u8 221)] d mtu hrel _ 219
            (elit st 219 219 k219) (n + mtu.toNat + 44) (n + mtu.toNat + 31) (by omega)
          simp only [beq_self_eq_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs, execS_ret_none]
          exact ⟨st', rfl, fin st' 219 hr hw hsm.1 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde])⟩
        · have h3' : (c == 221) = false := by simp [h3]
          obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.store st [("c", u8 c)] d mtu hrel _ c
            (evc st) (n + mtu.toNat + 44) (n + mtu.toNat + 31) (by omega)
          simp only [h3', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs,
            execS_ret_none]
          exact ⟨st', rfl, fin st' c hr hw hsm.1 (by
            simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, Spec.Slip.ESC_END, Spec.Slip.ESC_ESC, hde,
              h1, h2, h3])⟩
    | false =>
      simp only [Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, execS_ite,
        ecv st 219 219 k219, Val.toBool]
      by_cases h2 : c = 219
      · subst h2
        rw [hde] at hesc
        have hf : Spec.Slip.Dec.feed d 219 mtu.toNat = ({ d with esc := true }, .none) := by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde]
        rw [hf]
        simp [execB_succ, execL_cons, execL_nil, execS_at, execS_assign, evalE, assign_var, List.lookup, hesc]
        refine ⟨⟨⟨b, ?_⟩, hfr, ?_⟩, rfl⟩
        · simp [lookup_setG_ne, lookup_setG_self, hbuf, hsz, hle, hlen, hesc, hover, hmtu, hpre]
        · simp [lookup_setG_ne, hdo]
      · have h2' : (c == 219) = false := by simp [h2]
        obtain ⟨st', hs, hr, hw, hsm⟩ := execS_slip_store p hP.store st [("c", u8 c)] d mtu hrel _ c
          (evc st) (n + mtu.toNat + 51) (n + mtu.toNat + 38) (by omega)
        simp only [h2', Bool.false_eq_true, if_false, execB_succ, execL_cons, execL_nil, execS_at, hs]
        exact ⟨st', rfl, fin st' c hr hw hsm.1 (by
          simp [Spec.Slip.Dec.feed, Spec.Slip.END, Spec.Slip.ESC, hde, h1, h2])⟩

/-! ## One call of the loopback's `main` -/

/-- Skipping exhausted chunks moves the read position only. -/
theorem normalize_eq (w : World) : ∃ pos off, w.normalize = { w with pos := pos, off := off } := by
  fun_induction World.normalize w with
  | case1 w h => exact ⟨w.pos, w.off, rfl⟩
  | case2 w h hlt b hb hge ih =>
    obtain ⟨p', o', e⟩ := ih
    exact ⟨p', o', by rw [e]⟩
  | case3 w h hlt b hb hge => exact ⟨w.pos, w.off, rfl⟩
  | case4 w h hlt hb => exact ⟨w.pos, w.off, rfl⟩
  | case5 w h hlt => exact ⟨w.pos, w.off, rfl⟩

/-- Reading an input item changes the read position (and which item is
current), nothing else: the trace so far and the frame being built stay. -/
theorem next_eq (w : World) : ∃ pos off cur, w.next.2 = { w with pos := pos, off := off, cur := cur } := by
  obtain ⟨p0, o0, e0⟩ := normalize_eq w
  unfold World.next
  simp only [e0]
  split
  · split
    · obtain ⟨p1, o1, e1⟩ := normalize_eq { w with cur := p0, pos := p0 + 1, off := 0 }
      exact ⟨p1, o1, p0, e1⟩
    · obtain ⟨p1, o1, e1⟩ := normalize_eq { w with pos := p0, cur := p0, off := o0 + 1 }
      exact ⟨p1, o1, p0, e1⟩
  · exact ⟨p0, o0, w.cur, rfl⟩

theorem next_frame (w : World) : w.next.2.frame = w.frame := by
  obtain ⟨_, _, _, e⟩ := next_eq w; rw [e]

theorem next_events (w : World) : w.next.2.events = w.events := by
  obtain ⟨_, _, _, e⟩ := next_eq w; rw [e]

/-- A call of `loop_rx` as a statement. -/
theorem execS_loop_rx (p : Prog) (hP : LoopProg p) (st : St) (env : Env) (d : Spec.Slip.Dec) (mtu : UInt16)
    (hinv : LoopInv st d mtu) (e : Expr) (c : UInt8) (he : evalE p st env e = some (u8 c)) (m n : Nat)
    (hm : m = n + mtu.toNat + 60 + 1) :
    ∃ st', execS m p st env (.call none "loop_rx" [e]) = .ok st' env .normal ∧
      LoopInv st' (d.feed c mtu.toNat).1 mtu ∧ st'.world = loopOut st.world (d.feed c mtu.toNat).2 := by
  subst hm
  obtain ⟨st', hc, h2, h3⟩ := loop_rx_refines p hP st d mtu hinv c n
  exact ⟨st', execS_call_val p st env _ none "loop_rx" [e] hP.rx (by simp [loop_rx]) (by simp [evalArgs, he]) hc,
    h2, h3⟩

/-- **One call of `main` of the SLIP loopback is one step of the Spec's
decoder.**  The call reads one input item `k` (`World.next`).  If it is a
byte, the globals go from holding the decoder state `d` to holding
`(d.feed k).1`, and the trace gets what the step yields: nothing, the
drop of an oversize frame, or the completed frame, SLIP-encoded, as a
transmission.  If it is a tick or the end of the input, nothing changes. -/
theorem loop_main_refines (p : Prog) (hP : LoopProg p) (st : St) (d : Spec.Slip.Dec) (mtu : UInt16)
    (hinv : LoopInv st d mtu) (n : Nat) :
    ∃ st', Sem.call (n + mtu.toNat + 70) p st "main" [] = .ok none st' ∧
      if st.world.next.1 < 256 then
        LoopInv st' (d.feed st.world.next.1.toUInt8 mtu.toNat).1 mtu ∧
          st'.world = loopOut st.world.next.2 (d.feed st.world.next.1.toUInt8 mtu.toNat).2
      else LoopInv st' d mtu ∧ st'.world = st.world.next.2 := by
  generalize hr : st.world.next = r
  have hfr : r.2.frame = .empty := by rw [← hr, next_frame]; exact hinv.2.1
  have hinv1 : LoopInv { st with world := r.2 } d mtu := ⟨hinv.1, hfr, hinv.2.2⟩
  have h256 : mask .w16 (UInt64.ofNat 256) = (256 : UInt16).toUInt64 := rfl
  have hz : zeroOf p (Ty.int .w16) = u16 0 := rfl
  have ek : ∀ st' : St, evalE p st' [("k", u16 r.1)] (.bin .lt (.var "k") (.lit 256 (some .w16)))
      = some (.bool (decide (r.1 < 256))) := by
    intro st'
    have e1 : evalE p st' [("k", u16 r.1)] (.var "k") = some (u16 r.1) := by simp [evalE, lookup, List.lookup]
    simp only [evalE_bin, evalE_lit, e1, Sem.binop, h256, toUInt64_lt_iff]
  simp only [Sem.call, hP.main, loop_main, execB_succ, execL_cons, execL_nil, execS_at, execS_decl_none, hz,
    execS_eff, evalArgs, Sem.effect, storeResult, hr, assign_var, List.lookup, beq_self_eq_true, setFirst, ite_true,
    List.map, List.zip, List.zipWith, execS_ite, ek, Val.toBool]
  by_cases hlt : r.1 < 256
  · obtain ⟨st', hs, hi, hw⟩ := execS_loop_rx p hP { st with world := r.2 } [("k", u16 r.1)] d mtu hinv1 _
      r.1.toUInt8 (evalE_lo8 p _ _ "k" r.1 (by simp [lookup, List.lookup])) (n + mtu.toNat + 61) n (by omega)
    simp only [hlt, decide_true, if_true, execB_succ, execL_cons, execL_nil, execS_at, hs]
    exact ⟨st', rfl, hi, hw⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, execB_succ, execL_nil]
    exact ⟨_, rfl, hinv1, rfl⟩

/-- **The loopback starts in the decoder's initial state**: the globals
of `Ember.Net.Loop.prog` as the semantics sets them up hold `{}`, with
the MTU the program declares. -/
theorem loop_initial (inputs : Array Trace.Input) : LoopInv (Sem.initial Net.Loop.prog inputs) {} 296 := by
  refine ⟨⟨⟨Array.replicate 296 0⟩, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩, rfl, rfl⟩
  · have hz : mask .w8 (UInt64.ofNat 0) = (0 : UInt8).toUInt64 := rfl
    have : List.lookup "buf" (Sem.initial Net.Loop.prog inputs).globals
        = some (.arr ((Array.range 296).map fun _ => Val.int .w8 (mask .w8 (UInt64.ofNat 0)))) := rfl
    rw [this, hz, bufVal]
    congr 2
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  · simp [ByteArray.size]
  · show 0 ≤ 296
    omega
  · show (ByteArray.mk (Array.replicate 296 0)).extract 0 0 = ByteArray.empty
    apply eq_of_toList_eq
    rw [toList_extract _ _ (Nat.zero_le _)]
    simp [ByteArray.toList_empty]

/-- `k` calls of the entry function, one after the other; `none` if one
traps or runs out of fuel. -/
def callN (fuel : Nat) (p : Prog) (f : String) : Nat → St → Option St
  | 0, st => some st
  | k + 1, st =>
    match Sem.call fuel p st f [] with
    | .ok _ st' => callN fuel p f k st'
    | _ => none

/-- **The loopback never traps.**  From a state that holds a decoder
state, any number of calls of `main` — on any input — run to the end with
`mtu + 70` units of fuel each: no index is out of range, and the state
after still holds a decoder state. -/
theorem loop_safe (p : Prog) (hP : LoopProg p) (mtu : UInt16) (n : Nat) :
    ∀ (k : Nat) (st : St) (d : Spec.Slip.Dec), LoopInv st d mtu →
      ∃ st' d', callN (n + mtu.toNat + 70) p "main" k st = some st' ∧ LoopInv st' d' mtu := by
  intro k
  induction k with
  | zero => intro st d h; exact ⟨st, d, rfl, h⟩
  | succ k ih =>
    intro st d h
    obtain ⟨st1, hc, hcase⟩ := loop_main_refines p hP st d mtu h n
    simp only [callN, hc]
    split at hcase
    · exact ih st1 _ hcase.1
    · exact ih st1 _ hcase.1

-- the checked program is a `LoopProg` (with the `#guard`s at the four functions), and
-- checking leaves the globals as they are
#guard (Net.Loop.prog.check.toOption.map (·.dropReasons[0]?)) == some (some "oversize-frame")
#guard (Net.Loop.prog.check.toOption.map (·.globals.map (·.name))) == some (Net.Loop.prog.globals.map (·.name))

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.loop_main_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_main_refines

/-- info: 'Ember.Proof.Refine.set32_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms set32_refines

/-- info: 'Ember.Proof.Refine.get32_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get32_refines

/-- info: 'Ember.Proof.Refine.loop_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_initial

/-- info: 'Ember.Proof.Refine.loop_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_safe

end Ember.Proof.Refine
