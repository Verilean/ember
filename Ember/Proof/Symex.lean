import Ember.Lang.Sem
import Ember.Util.Bytes

/-!
# Ember.Proof.Symex — executing Ember code symbolically (plan M5.4)

`Ember.Lang.Sem` unfolds one construct at a time through the lemmas
here — one per statement form, each an equation of `execS` at fuel
`n + 1` — so a proof steps through a function's checked AST with
`simp only [symex…]`.  A call is *not* unfolded into the callee's body:
it is rewritten with the callee's own theorem (`execS_call_val`), which
is how the proofs compose.

The fuel in a statement is written `n + k`: whatever the caller has left
(`n`) plus what the function needs (`k`, a number found by trying).
-/

namespace Ember.Lang.Sem

variable (p : Prog) (st : St) (env : Env) (n : Nat)

theorem execB_succ (ss : List Stmt) :
    execB (n + 1) p st env ss =
      match execL n p st env ss with
      | .ok st' env' o => .ok st' (env'.drop (env'.length - env.length)) o
      | r => r := by
  simp only [execB]; rfl

theorem execL_nil : execL (n + 1) p st env [] = .ok st env .normal := by
  simp only [execL]

theorem execL_cons (s : Stmt) (rest : List Stmt) :
    execL (n + 1) p st env (s :: rest) =
      match execS n p st env s with
      | .ok st' env' .normal => execL n p st' env' rest
      | r => r := by
  simp only [execL]; rfl

theorem execS_at (sp : Span) (s : Stmt) : execS (n + 1) p st env (.at sp s) = execS n p st env s := by
  simp only [execS]

theorem execS_decl_some (x : String) (ty : Ty) (e : Expr) :
    execS (n + 1) p st env (.decl x ty (some e)) =
      match evalE p st env e with
      | some v => .ok st ((x, v) :: env) .normal
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_decl_none (x : String) (ty : Ty) :
    execS (n + 1) p st env (.decl x ty none) = .ok st ((x, zeroOf p ty) :: env) .normal := by
  simp only [execS]

theorem execS_assign (l r : Expr) :
    execS (n + 1) p st env (.assign l r) =
      match evalE p st env r with
      | some v =>
        match assign p st env l v with
        | some (st', env') => .ok st' env' .normal
        | none => .trap st
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_ite (c : Expr) (t e : List Stmt) :
    execS (n + 1) p st env (.ite c t e) =
      match evalE p st env c with
      | some cv => if cv.toBool then execB n p st env t else execB n p st env e
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_brk : execS (n + 1) p st env .brk = .ok st env .brk := by
  simp only [execS]

theorem execS_ret_none : execS (n + 1) p st env (.ret none) = .ok st env (.ret none) := by
  simp only [execS]

theorem execS_ret_some (e : Expr) :
    execS (n + 1) p st env (.ret (some e)) =
      match evalE p st env e with
      | some v => .ok st env (.ret (some v))
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_call (dst : Option Expr) (f : String) (args : List Expr) :
    execS (n + 1) p st env (.call dst f args) =
      match p.fn? f with
      | some fd =>
        match evalArgs p st env args with
        | some vs =>
          match execB n p st ((fd.params.map (·.name)).zip vs) fd.body with
          | .ok st' cenv o =>
            match copyBack p cenv fd.params args st' env with
            | some (st'', env'') =>
              storeResult p st'' env'' dst (match o with | .ret v => v | _ => none)
            | none => .trap st'
          | r => r
        | none => .trap st
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_eff (dst : Option Expr) (e : Effect) (args : List Expr) :
    execS (n + 1) p st env (.eff dst e args) =
      match evalArgs p st env args with
      | some vs => storeResult p (effect p st e vs).2 env dst (effect p st e vs).1
      | none => .trap st := by
  simp only [execS]; rfl

theorem execS_forRange (x : String) (w : Option Width) (lo hi : Expr) (body : List Stmt) :
    execS (n + 1) p st env (.forRange x w lo hi body) =
      match evalE p st env lo, evalE p st env hi with
      | some a, some b =>
        match forLoop n p st ((x, .int (w.getD .w32) (UInt64.ofNat a.toNat)) :: env) x (w.getD .w32)
                a.toNat b.toNat body with
        | .ok st' env' o => .ok st' (env'.drop 1) o
        | r => r
      | _, _ => .trap st := by
  simp only [execS]; rfl

theorem forLoop_succ (x : String) (w : Width) (cur hi : Nat) (body : List Stmt) :
    forLoop (n + 1) p st env x w cur hi body =
      if cur < hi then
        match execB n p st (setFirst env x (.int w (UInt64.ofNat cur))) body with
        | .ok st' env' .normal => forLoop n p st' env' x w (cur + 1) hi body
        | .ok st' env' .brk => .ok st' env' .normal
        | r => r
      else .ok st env .normal := by
  simp only [forLoop]; rfl

/-- Nothing is copied back when no parameter is by reference. -/
theorem copyBack_val (cenv : Env) (ps : List Param) (as : List Expr)
    (h : ∀ prm ∈ ps, prm.byRef = false) : copyBack p cenv ps as st env = some (st, env) := by
  induction ps generalizing as with
  | nil => cases as <;> simp [copyBack]
  | cons prm ps ih =>
    cases as with
    | nil => simp [copyBack]
    | cons a as =>
      have h1 : prm.byRef = false := h prm (by simp)
      simp only [copyBack, h1, Bool.false_eq_true, if_false]
      exact ih as fun q hq => h q (by simp [hq])

/-- **A call statement, through the callee's theorem**: when the callee
(all parameters by value) is known to return `v` leaving the state `st'`,
the statement stores `v`. -/
theorem execS_call_val {fd : Fn} {vs : List Val} {v : Option Val} {st' : St}
    (dst : Option Expr) (f : String) (args : List Expr)
    (hf : p.fn? f = some fd) (hval : ∀ prm ∈ fd.params, prm.byRef = false)
    (ha : evalArgs p st env args = some vs) (hc : call n p st f vs = .ok v st') :
    execS (n + 1) p st env (.call dst f args) = storeResult p st' env dst v := by
  rw [execS_call, hf]
  simp only [ha]
  unfold call at hc
  rw [hf] at hc
  simp only at hc
  generalize hb : execB n p st ((fd.params.map (·.name)).zip vs) fd.body = r at hc ⊢
  cases r with
  | fuel => simp at hc
  | trap s => simp at hc
  | ok s cenv o =>
    simp only [copyBack_val p s env cenv fd.params args hval]
    cases o with
    | normal => simp only [CallRes.ok.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; rfl
    | brk => simp only [CallRes.ok.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; rfl
    | ret w => simp only [CallRes.ok.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; rfl

/-! ## Expressions, one constructor at a time -/

theorem evalE_lit (v : Nat) (w : Width) :
    evalE p st env (.lit v (some w)) = some (.int w (mask w (UInt64.ofNat v))) := by
  rw [evalE]

theorem evalE_var (x : String) : evalE p st env (.var x) = lookup st env x := by
  rw [evalE]

theorem evalE_bin (op : BinOp) (a b : Expr) :
    evalE p st env (.bin op a b) =
      match evalE p st env a, evalE p st env b with
      | some x, some y => binop op x y
      | _, _ => none := by
  rw [evalE]; rfl

/-! ## 16-bit values

A `u16` in the semantics is `Val.int .w16 x` with `x : UInt64` below
2^16; the Spec's functions are on `UInt16`.  These lemmas keep values in
the form `(x : UInt16).toUInt64` through the operations. -/

/-- The value of a `u16`. -/
abbrev u16 (x : UInt16) : Val := .int .w16 x.toUInt64

theorem toNat_mask16 (v : UInt64) : (mask .w16 v).toNat = v.toNat % 65536 := by
  have h : (Width.w16 == Width.w64) = false := rfl
  have h2 : ((1 : UInt64) <<< (16 : UInt64) - 1).toNat = 2 ^ 16 - 1 := rfl
  simp only [mask, h, Width.bits, Bool.false_eq_true, if_false, UInt64.toNat_and]
  show v.toNat &&& ((1 : UInt64) <<< (16 : UInt64) - 1).toNat = _
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]

theorem mask16_toUInt64 (x : UInt16) : mask .w16 x.toUInt64 = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [toNat_mask16, UInt16.toNat_toUInt64]
  omega

theorem mask16_not (x : UInt16) : mask .w16 (~~~ x.toUInt64) = (~~~ x).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have h64 : UInt64.size = 18446744073709551616 := rfl
  have h16 : UInt16.size = 65536 := rfl
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_not, UInt16.toNat_not, h64, h16]
  omega

theorem mask16_add (x y : UInt16) : mask .w16 (x.toUInt64 + y.toUInt64) = (x + y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_add, UInt16.toNat_add]
  omega

theorem mask16_ofNat (k : Nat) : mask .w16 (UInt64.ofNat k) = (UInt16.ofNat k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_ofNat', UInt16.toNat_ofNat']
  omega

theorem toUInt64_eq_iff (x y : UInt16) : (x.toUInt64 == y.toUInt64) = (x == y) := by
  have h : x.toUInt64 = y.toUInt64 ↔ x = y := by
    constructor
    · intro h
      apply UInt16.toNat_inj.mp
      have := congrArg UInt64.toNat h
      simpa using this
    · intro h; rw [h]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : x.toUInt64 ≠ y.toUInt64 := fun e => hxy (h.mp e)
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hxy]

theorem ofNat_u16 (k : Nat) (h : k < 65536) : UInt64.ofNat k = (UInt16.ofNat k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt16.toNat_toUInt64, UInt16.toNat_ofNat']
  omega

theorem mask16_mul (x y : UInt16) : mask .w16 (x.toUInt64 * y.toUInt64) = (x * y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have : x.toNat * y.toNat < 2 ^ 64 := by
    calc x.toNat * y.toNat < 2 ^ 16 * 2 ^ 16 := Nat.mul_lt_mul'' hx hy
      _ ≤ 2 ^ 64 := by decide
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_mul, UInt16.toNat_mul]
  omega

theorem mask16_and (x y : UInt16) : mask .w16 (x.toUInt64 &&& y.toUInt64) = (x &&& y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hlt : x.toNat &&& y.toNat < 2 ^ 16 := Nat.lt_of_le_of_lt Nat.and_le_left hx
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_and, UInt16.toNat_and]
  omega

theorem mask16_sub (x y : UInt16) : mask .w16 (x.toUInt64 - y.toUInt64) = (x - y).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [toNat_mask16, UInt16.toNat_toUInt64, UInt64.toNat_sub, UInt16.toNat_sub]
  omega

/-- `a <<< 8` on a `u16` value, the way the semantics computes it. -/
theorem shl8_value (a : UInt16) :
    mask .w16 (if (mask .w8 (UInt64.ofNat 8)).toNat ≥ Width.bits .w16 then 0
               else a.toUInt64 <<< mask .w8 (UInt64.ofNat 8)) = (a <<< 8).toUInt64 := by
  have h8 : ¬ ((mask .w8 (UInt64.ofNat 8)).toNat ≥ Width.bits .w16) := by decide
  have hk : mask .w8 (UInt64.ofNat 8) = 8 := rfl
  have ha := a.toNat_lt
  have h1 : UInt64.toNat 8 = 8 := rfl
  have h2 : UInt16.toNat 8 = 8 := rfl
  simp only [h8, if_false]
  apply UInt64.toNat_inj.mp
  simp only [hk, toNat_mask16, UInt64.toNat_shiftLeft, UInt16.toNat_toUInt64, UInt16.toNat_shiftLeft, h1, h2,
    Nat.reduceMod]
  have hs : a.toNat <<< 8 = a.toNat * 256 := by simp [Nat.shiftLeft_eq]
  rw [hs]
  omega

/-- `n &&& 1 == 1` is "`n` is odd". -/
theorem and_one_eq (n : UInt16) : (n &&& 1 == 1) = decide (n.toNat % 2 = 1) := by
  have t1 : UInt16.toNat 1 = 1 := rfl
  have h : (n &&& 1 = 1) ↔ n.toNat % 2 = 1 := by
    rw [← UInt16.toNat_inj, UInt16.toNat_and, t1, Nat.and_one_is_mod]
  by_cases hodd : n.toNat % 2 = 1
  · simp [hodd, h.mpr hodd]
  · have : ¬ (n &&& 1 = 1) := fun e => hodd (h.mp e)
    simp [hodd, this]

theorem div2_value (x : UInt16) :
    mask .w16 (if (mask .w16 (UInt64.ofNat 2) == 0) = true then 0 else x.toUInt64 / mask .w16 (UInt64.ofNat 2))
      = (x / 2).toUInt64 := by
  have h2 : mask .w16 (UInt64.ofNat 2) = 2 := rfl
  have hne : ((2 : UInt64) == 0) = false := rfl
  have t2 : UInt64.toNat 2 = 2 := rfl
  have t2' : UInt16.toNat 2 = 2 := rfl
  have := x.toNat_lt
  rw [h2, hne]
  simp only [Bool.false_eq_true, if_false]
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask16, UInt64.toNat_div, UInt16.toNat_toUInt64, UInt16.toNat_div, t2, t2']
  omega

/-! ## 32- and 8-bit values, and the casts between -/

/-- The value of a `u32`, of a `u8`. -/
abbrev u32 (x : UInt32) : Val := .int .w32 x.toUInt64
abbrev u8 (x : UInt8) : Val := .int .w8 x.toUInt64

theorem toNat_mask32 (v : UInt64) : (mask .w32 v).toNat = v.toNat % 4294967296 := by
  have h : (Width.w32 == Width.w64) = false := rfl
  have h2 : ((1 : UInt64) <<< (32 : UInt64) - 1).toNat = 2 ^ 32 - 1 := rfl
  simp only [mask, h, Width.bits, Bool.false_eq_true, if_false, UInt64.toNat_and]
  show v.toNat &&& ((1 : UInt64) <<< (32 : UInt64) - 1).toNat = _
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]

/-- `(v : u16)` of a `u32` variable: its low half. -/
theorem evalE_lo16 (v : String) (x : UInt32) (h : lookup st env v = some (u32 x)) :
    evalE p st env (.cast .w16 (.var v)) = some (u16 x.toUInt16) := by
  simp only [evalE, h]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask16, UInt32.toNat_toUInt64, UInt16.toNat_toUInt64, UInt32.toNat_toUInt16]

/-- `(v >>> 16 : u16)` of a `u32` variable: its high half. -/
theorem evalE_hi16 (v : String) (x : UInt32) (h : lookup st env v = some (u32 x)) :
    evalE p st env (.cast .w16 (.bin .shr (.var v) (.lit 16 (some .w8)))) = some (u16 (x >>> 16).toUInt16) := by
  have hk : mask .w8 (UInt64.ofNat 16) = 16 := rfl
  have h16 : ¬ (UInt64.toNat 16 ≥ Width.bits .w32) := by decide
  simp only [evalE, h, Sem.binop, hk, h16, if_false]
  congr 2
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have h1 : UInt64.toNat 16 = 16 := rfl
  have h2 : UInt32.toNat 16 = 16 := rfl
  simp only [toNat_mask16, toNat_mask32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt16.toNat_toUInt64,
    UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, h1, h2, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
  omega

/-- `(v : u16)` of a `u8` variable. -/
theorem evalE_u8_16 (v : String) (x : UInt8) (h : lookup st env v = some (u8 x)) :
    evalE p st env (.cast .w16 (.var v)) = some (u16 x.toUInt16) := by
  simp only [evalE, h]
  congr 2
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [toNat_mask16, UInt8.toNat_toUInt64, UInt16.toNat_toUInt64, UInt8.toNat_toUInt16]
  omega

theorem toNat_mask8 (v : UInt64) : (mask .w8 v).toNat = v.toNat % 256 := by
  have h : (Width.w8 == Width.w64) = false := rfl
  have h2 : ((1 : UInt64) <<< (8 : UInt64) - 1).toNat = 2 ^ 8 - 1 := rfl
  simp only [mask, h, Width.bits, Bool.false_eq_true, if_false, UInt64.toNat_and]
  show v.toNat &&& ((1 : UInt64) <<< (8 : UInt64) - 1).toNat = _
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]

/-- `(a <<< 8) ||| c` on `u16` values, the way the semantics computes it. -/
theorem word_value (a c : UInt16) :
    mask .w16 (mask .w16 (a.toUInt64 <<< mask .w8 (UInt64.ofNat 8)) ||| c.toUInt64) = (a <<< 8 ||| c).toUInt64 := by
  have hk : mask .w8 (UInt64.ofNat 8) = 8 := rfl
  have ha := a.toNat_lt
  have hc := c.toNat_lt
  have h1 : UInt64.toNat 8 = 8 := rfl
  have h2 : UInt16.toNat 8 = 8 := rfl
  apply UInt64.toNat_inj.mp
  simp only [hk, toNat_mask16, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt16.toNat_toUInt64,
    UInt16.toNat_or, UInt16.toNat_shiftLeft, h1, h2, Nat.reduceMod]
  have hs : a.toNat <<< 8 = a.toNat * 256 := by simp [Nat.shiftLeft_eq]
  have h3 : a.toNat * 256 % 2 ^ 64 % 65536 = a.toNat * 256 % 2 ^ 16 := by omega
  rw [hs, h3]
  have hlt : a.toNat * 256 % 2 ^ 16 ||| c.toNat < 2 ^ 16 := Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) hc
  omega

/-! ## The packet buffer -/

/-- The packet buffer as a value: an array of `u8`. -/
def bufVal (b : ByteArray) : Val := .arr (b.data.map fun x => u8 x)

theorem bufVal_get (b : ByteArray) (i : Nat) (h : i < b.size) :
    (b.data.map fun x => u8 x)[i]? = some (u8 (Bytes.get b i)) := by
  have h' : i < b.data.size := h
  simp [Bytes.get, h, ByteArray.getElem_eq_getElem_data]
  rfl

/-- `(buf[i] : u16)` for an index in range. -/
theorem evalE_buf16 (b : ByteArray) (i : Expr) (k : UInt16)
    (hb : lookup st env "buf" = some (bufVal b)) (hi : evalE p st env i = some (u16 k)) (hk : k.toNat < b.size) :
    evalE p st env (.cast .w16 (.index (.var "buf") i)) = some (u16 (Bytes.get b k.toNat).toUInt16) := by
  have hidx : (u16 k).toNat = k.toNat := by simp [Val.toNat]
  simp only [evalE, hb, hi, bufVal, hidx, bufVal_get b k.toNat hk]
  congr 2
  apply UInt64.toNat_inj.mp
  have := (Bytes.get b k.toNat).toNat_lt
  simp only [toNat_mask16, UInt8.toNat_toUInt64, UInt16.toNat_toUInt64, UInt8.toNat_toUInt16]
  omega

/-! ## Writing the packet buffer -/

theorem bufVal_set (b : ByteArray) (k : Nat) (x : UInt8) (h : k < b.size) :
    (b.data.map fun y => u8 y).set! k (u8 x) = (Bytes.set b k x).data.map fun y => u8 y := by
  simp [Bytes.set, h, ByteArray.set!]

theorem lookup_setFirst (l : Env) (x : String) (v w : Val) (h : l.lookup x = some w) :
    (setFirst l x v).lookup x = some v := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨y, u⟩ := hd
    by_cases hy : y = x
    · subst hy; simp [setFirst]
    · have hy' : (y == x) = false := by simp [hy]
      have hxy : (x == y) = false := by simp [Ne.symm hy]
      simp only [setFirst, hy', Bool.false_eq_true, if_false, List.lookup, hxy] at h ⊢
      exact ih h

theorem setFirst_setFirst (l : Env) (x : String) (v w : Val) : setFirst (setFirst l x v) x w = setFirst l x w := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨y, u⟩ := hd
    by_cases hy : y = x
    · subst hy; simp [setFirst]
    · have hy' : (y == x) = false := by simp [hy]
      simp [setFirst, hy', ih]

/-- The state with `buf` holding the bytes of `b`. -/
def withBuf (st : St) (b : ByteArray) : St := { st with globals := setFirst st.globals "buf" (bufVal b) }

/-- `buf[i] := x` for an index in range: the buffer with that byte set. -/
theorem assign_buf (b : ByteArray) (i : Expr) (k : UInt16) (x : UInt8)
    (hl : env.lookup "buf" = none) (hb : st.globals.lookup "buf" = some (bufVal b))
    (hi : evalE p st env i = some (u16 k)) (hk : k.toNat < b.size) :
    assign p st env (.index (.var "buf") i) (u8 x) = some (withBuf st (Bytes.set b k.toNat x), env) := by
  have hidx : (u16 k).toNat = k.toNat := by simp [Val.toNat]
  have hget := bufVal_get b k.toNat hk
  simp only [assign, update, hi, hl, hb, bufVal, hidx, hget, bufVal_set b k.toNat x hk, withBuf]

theorem lookup_withBuf (b b' : ByteArray) (hb : st.globals.lookup "buf" = some (bufVal b)) :
    (withBuf st b').globals.lookup "buf" = some (bufVal b') :=
  lookup_setFirst st.globals "buf" _ _ hb

theorem withBuf_withBuf (b b' : ByteArray) : withBuf (withBuf st b) b' = withBuf st b' := by
  simp [withBuf, setFirst_setFirst]

/-- `(v : u8)` of a `u16` variable: its low byte. -/
theorem evalE_lo8 (v : String) (x : UInt16) (h : lookup st env v = some (u16 x)) :
    evalE p st env (.cast .w8 (.var v)) = some (u8 x.toUInt8) := by
  simp only [evalE, h]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [toNat_mask8, UInt16.toNat_toUInt64, UInt8.toNat_toUInt64, UInt16.toNat_toUInt8]

/-- `(v >>> 8 : u8)` of a `u16` variable: its high byte. -/
theorem evalE_hi8 (v : String) (x : UInt16) (h : lookup st env v = some (u16 x)) :
    evalE p st env (.cast .w8 (.bin .shr (.var v) (.lit 8 (some .w8)))) = some (u8 (x >>> 8).toUInt8) := by
  have hk : mask .w8 (UInt64.ofNat 8) = 8 := rfl
  have h8 : ¬ (UInt64.toNat 8 ≥ Width.bits .w16) := by decide
  simp only [evalE, h, Sem.binop, hk, h8, if_false]
  congr 2
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  have h1 : UInt64.toNat 8 = 8 := rfl
  have h2 : UInt16.toNat 8 = 8 := rfl
  simp only [toNat_mask8, toNat_mask16, UInt64.toNat_shiftRight, UInt16.toNat_toUInt64, UInt8.toNat_toUInt64,
    UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, h1, h2, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
  omega

end Ember.Lang.Sem
