import Ember.Proof.IRExpr

/-!
# Ember.Proof.IRJump — conditions as jumps (plan M7.1)

* `noTrap`: an expression without an index that is not a literal has a
  value (so `&&` and `||` may skip it);
* `condJump_ok`: the code for a condition jumps to the target exactly
  when the condition's value is the sense asked for, and falls through
  otherwise — or traps when the condition has no value.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK closed_evalE natCmp
  binop_cmp)

/-- **An expression that cannot trap has a value.** -/
theorem noTrap {c : Ctx} {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}
    (L : LayOK E.prog c) (hrel : SRel c E cur lst env ist) : ∀ (e : Expr) (ty : Ty), WT E e → E.tyOf e = .ok ty →
    canTrap e = false → ∃ v, Lang.Sem.evalE E.prog lst env e = some v
  | .lit v (some w), _, _, _, _ => ⟨_, rfl⟩
  | .lit _ none, _, hw, _, _ => absurd hw (by simp [WT])
  | .blit _, _, _, _, _ => ⟨_, rfl⟩
  | .var x, ty, _, hty, _ => by
    simp only [Env.tyOf] at hty
    cases hi : E.varInfo x with
    | error m => simp [hi] at hty
    | ok info =>
      obtain ⟨_, v, _, hl, _⟩ := hrel.var L hi
      exact ⟨v, by simpa [Lang.Sem.evalE] using hl⟩
  | .field b fld, ty, hw, hty, hc => by
    simp only [canTrap] at hc
    simp only [Env.tyOf] at hty
    cases htb : E.tyOf b with
    | error m => simp [htb] at hty
    | ok tb =>
      obtain ⟨bv, hev⟩ := noTrap L hrel b tb hw htb hc
      have hv := evalE_hasTy E lst env (hrel.typed L) b bv tb hw hev htb
      cases tb with
      | int _ => simp [htb, Env.err] at hty
      | bool => simp [htb, Env.err] at hty
      | arr _ _ => simp [htb, Env.err] at hty
      | record rn =>
        obtain ⟨fs, sd, rfl, hsd, hsz, _⟩ := hasTy_record hv
        simp only [htb, fieldOff, hsd, Option.map_some, Option.getD_some] at hty
        cases hi : sd.fields.findIdx? (·.1 == fld) with
        | none => rw [fieldOffIn_none _ _ _ _ hi] at hty; simp [Env.err] at hty
        | some i =>
          obtain ⟨hlt, _⟩ := fieldOffIn_of_findIdx E.prog sd.fields fld 0 i hi
          exact ⟨fs[i]'(by omega), by
            simp only [Lang.Sem.evalE, hev, Lang.Sem.fieldIndex, hsd, hi]
            exact Array.getElem?_eq_getElem (by omega)⟩
  | .index b i, ty, hw, hty, hc => by
    obtain ⟨hwb, hwi, _, _, hlit⟩ := hw
    simp only [canTrap, Bool.or_eq_false_iff] at hc
    simp only [Env.tyOf] at hty
    cases htb : E.tyOf b with
    | error m => simp [htb] at hty
    | ok tb =>
      obtain ⟨bv, hev⟩ := noTrap L hrel b tb hwb htb hc.2
      have hv := evalE_hasTy E lst env (hrel.typed L) b bv tb hwb hev htb
      cases tb with
      | int _ => simp [htb, Env.err] at hty
      | bool => simp [htb, Env.err] at hty
      | record _ => simp [htb, Env.err] at hty
      | arr el n =>
        obtain ⟨xs, rfl, hxs, _⟩ := hasTy_arr hv
        cases i with
        | lit v w =>
          have hvn := hlit v w el n rfl htb
          cases w with
          | none => exact absurd hwi (by simp [WT])
          | some w =>
            have hvw : v < 2 ^ w.bits := hwi
            have h64 : v < 2 ^ 64 := Nat.lt_of_lt_of_le hvw (Nat.pow_le_pow_right (by decide) (Ember.Proof.CSim.bits_le w))
            have hn : (mask w (UInt64.ofNat v)).toNat = v := by
              rw [Ember.Proof.CSim.mask_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hvw]
            exact ⟨xs[v]'(by omega), by
              simp only [Lang.Sem.evalE, hev, Val.toNat, hn]
              exact Array.getElem?_eq_getElem (by omega)⟩
        | _ => simp at hc
  | .bin op a b, ty, hw, hty, hc => by
    simp only [canTrap, Bool.or_eq_false_iff] at hc
    obtain ⟨ta, tb, hta, htb, _, _, hcond, _⟩ := bin_types hw
    obtain ⟨x, hx⟩ := noTrap L hrel a ta hw.1 hta hc.1
    obtain ⟨y, hy⟩ := noTrap L hrel b tb hw.2.1 htb hc.2
    obtain ⟨v, hv⟩ := binop_some E.prog op x y ta tb
      (evalE_hasTy E lst env (hrel.typed L) a x ta hw.1 hx hta)
      (evalE_hasTy E lst env (hrel.typed L) b y tb hw.2.1 hy htb) hcond
    exact ⟨v, by simp only [Lang.Sem.evalE, hx, hy, hv]⟩
  | .un op a, ty, hw, hty, hc => by
    simp only [canTrap] at hc
    have hta : E.tyOf a = .ok ty := by simpa only [Env.tyOf] using hty
    obtain ⟨x, hx⟩ := noTrap L hrel a ty hw.1 hta hc
    have hvx := evalE_hasTy E lst env (hrel.typed L) a x ty hw.1 hx hta
    have hw2 := hw.2
    rw [evalE_un, hx]
    cases op with
    | lnot =>
      simp only [if_true, hta, Except.ok.injEq] at hw2
      subst hw2
      obtain ⟨b, rfl⟩ := hasTy_bool hvx
      exact ⟨_, rfl⟩
    | bnot =>
      simp only [reduceCtorEq, if_false, hta, Except.ok.injEq] at hw2
      obtain ⟨w, rfl⟩ := hw2
      obtain ⟨xv, rfl, _⟩ := hasTy_int hvx
      exact ⟨_, rfl⟩
    | neg =>
      simp only [reduceCtorEq, if_false, hta, Except.ok.injEq] at hw2
      obtain ⟨w, rfl⟩ := hw2
      obtain ⟨xv, rfl, _⟩ := hasTy_int hvx
      exact ⟨_, rfl⟩
  | .cast w a, ty, hw, hty, hc => by
    simp only [canTrap] at hc
    obtain ⟨hwa, ta, hta, hsa⟩ := hw
    obtain ⟨x, hx⟩ := noTrap L hrel a ta hwa hta hc
    obtain ⟨cv, hcv, _, _⟩ := cast_val E.prog w (evalE_hasTy E lst env (hrel.typed L) a x ta hwa hx hta) hsa
    exact ⟨cv, by rw [evalE_cast, hx]; exact hcv⟩
  | .cond cnd a b, ty, hw, hty, hc => by
    simp only [canTrap, Bool.or_eq_false_iff] at hc
    obtain ⟨hwc, hwa, hwb, htc, t0, hta, htb, _⟩ := hw
    obtain ⟨cv, hcv⟩ := noTrap L hrel cnd .bool hwc htc hc.1.1
    obtain ⟨x, hx⟩ := noTrap L hrel a t0 hwa hta hc.1.2
    obtain ⟨y, hy⟩ := noTrap L hrel b t0 hwb htb hc.2
    exact ⟨if cv.toBool then x else y, by simp only [Lang.Sem.evalE, hcv, hx, hy]⟩

/-! ## Jumps -/

/-- From `a`: when `taken`, to wherever the label `target` is; otherwise on to `e`. -/
def Jumps (c : Ctx) (f : IR.Fn) (ist : St) (a e target : Nat) (tmps : Array Nat) (taken : Bool) : Prop :=
  if taken = true then
    ∀ i : Nat, f.body[i]? = some (Instr.label target) →
      ∃ tmps', Reach c f a tmps ist i tmps' ist ∧ tmps'.size = tmps.size
  else ∃ tmps', Reach c f a tmps ist e tmps' ist ∧ tmps'.size = tmps.size

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

theorem Jumps.prefix {ist : St} {a m e target : Nat} {tmps t1 : Array Nat} {taken : Bool}
    (r : Reach c f a tmps ist m t1 ist) (hsz : t1.size = tmps.size) (h : Jumps c f ist m e target t1 taken) :
    Jumps c f ist a e target tmps taken := by
  unfold Jumps at h ⊢
  cases taken with
  | true =>
    simp only [if_true] at h ⊢
    intro i hi
    obtain ⟨t', r', s'⟩ := h i hi
    exact ⟨t', r.trans r', by rw [s', hsz]⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨t', r', s'⟩ := h
    exact ⟨t', r.trans r', by rw [s', hsz]⟩

/-- Nothing emitted, no jump. -/
theorem Jumps.none {ist : St} {a target : Nat} {tmps : Array Nat} : Jumps c f ist a a target tmps false := by
  unfold Jumps
  simp only [Bool.false_eq_true, if_false]
  exact ⟨tmps, Reach.refl, rfl⟩

/-- One instruction that jumps to `target` or goes on. -/
theorem Jumps.one (F : Final c fn f sF) {ist : St} {a target : Nat} {tmps : Array Nat} {ins : Instr}
    {taken : Bool} (hb : f.body[a]? = some ins)
    (hs : step c ist tmps ins = if taken = true then .goto target else .next ist tmps) :
    Jumps c f ist a (a + 1) target tmps taken := by
  unfold Jumps
  cases taken with
  | true =>
    simp only [if_true] at hs ⊢
    exact fun i hi => ⟨tmps, Reach.goto hb hs (F.label hi), rfl⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at hs ⊢
    exact ⟨tmps, Reach.next hb hs, rfl⟩

/-- Two jumps to one target, one after the other. -/
theorem Jumps.or {ist : St} {a m e target : Nat} {tmps : Array Nat} {ta tb : Bool}
    (hA : Jumps c f ist a m target tmps ta)
    (hB : ∀ t1 : Array Nat, t1.size = tmps.size → Jumps c f ist m e target t1 tb) :
    Jumps c f ist a e target tmps (ta || tb) := by
  cases ta with
  | true =>
    unfold Jumps at hA ⊢
    simpa using hA
  | false =>
    have hA' := hA
    unfold Jumps at hA'
    simp only [Bool.false_eq_true, if_false] at hA'
    obtain ⟨t1, r1, s1⟩ := hA'
    simpa using Jumps.prefix r1 s1 (hB t1 s1)

/-- A jump past the second one (to `skip`, which is at `lpos`), then a jump to `target`. -/
theorem Jumps.skip {ist : St} {a m lpos target skip : Nat} {tmps : Array Nat} {ta tb : Bool}
    (hA : Jumps c f ist a m skip tmps ta)
    (hB : ∀ t1 : Array Nat, t1.size = tmps.size → Jumps c f ist m lpos target t1 tb)
    (hl : f.body[lpos]? = some (Instr.label skip)) :
    Jumps c f ist a (lpos + 1) target tmps (!ta && tb) := by
  have hlab : ∀ t : Array Nat, Reach c f lpos t ist (lpos + 1) t ist := fun t => Reach.next hl (step_label c ist t skip)
  cases ta with
  | true =>
    unfold Jumps at hA ⊢
    simp only [if_true] at hA
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    obtain ⟨t1, r1, s1⟩ := hA lpos hl
    exact ⟨t1, r1.trans (hlab t1), s1⟩
  | false =>
    have hA' := hA
    unfold Jumps at hA'
    simp only [Bool.false_eq_true, if_false] at hA'
    obtain ⟨t1, r1, s1⟩ := hA'
    have hB' := hB t1 s1
    simp only [Bool.not_false, Bool.true_and]
    refine Jumps.prefix r1 s1 ?_
    cases tb with
    | true => exact (by unfold Jumps at hB' ⊢; simpa using hB')
    | false =>
      unfold Jumps at hB' ⊢
      simp only [Bool.false_eq_true, if_false] at hB' ⊢
      obtain ⟨t2, r2, s2⟩ := hB'
      exact ⟨t2, r2.trans (hlab t2), s2⟩

/-- The code between `s` and `s'` jumps to `target` when `e` is `sense`. -/
def JSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (e : Expr) (sense : Bool) (target : Nat) (s s' : LS) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env e with
    | some v => Jumps c f ist s.out.size s'.out.size target tmps (v.toBool == sense)
    | none => Ends c f s.out.size tmps ist (.trap ist)

/-- What `condJump` promises. -/
def JPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (e : Expr) (sense : Bool) (target : Nat) (s : LS) (_ : Unit)
    (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ JSem c f sF E e sense target s s'

theorem cmpOp_negate (k : Cmp) (a b : Nat) : cmpOp k.negate a b = !cmpOp k a b := by
  cases k
  · rfl
  · simp [cmpOp, Cmp.negate, bne]
  · by_cases h : a < b <;> simp [cmpOp, Cmp.negate, h] <;> omega
  · by_cases h : a < b <;> simp [cmpOp, Cmp.negate, h] <;> omega

theorem cmpOf_spec (c : Ctx) (ist : St) (tmps : Array Nat) (op : BinOp) (hc : op.isCompare = true) (m : Nat)
    (oa ob : Opd) :
    cmpOp (cmpOf op oa ob).1 (opd c ist tmps m (cmpOf op oa ob).2.1) (opd c ist tmps m (cmpOf op oa ob).2.2) =
      natCmp op (opd c ist tmps m oa) (opd c ist tmps m ob) := by
  cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;> simp [cmpOf, cmpOp, natCmp]

theorem cmpZero_spec (c : Ctx) (ist : St) (tmps : Array Nat) (m : Nat) (r : Cmp × Opd × Opd) :
    cmpOp (cmpZero r).1 (opd c ist tmps m (cmpZero r).2.1) (opd c ist tmps m (cmpZero r).2.2) =
      cmpOp r.1 (opd c ist tmps m r.2.1) (opd c ist tmps m r.2.2) := by
  obtain ⟨k, x, y⟩ := r
  unfold cmpZero
  split
  · rename_i h1 h2
    simp only at h1 h2
    subst h1 h2
    simp only [cmpOp, opd_const, modN, Nat.zero_mod]
    generalize opd c ist tmps m y = n
    cases n <;> simp
  · rename_i h1 h2
    simp only at h1 h2
    subst h1 h2
    simp only [cmpOp, opd_const, modN, Nat.zero_mod]
    generalize opd c ist tmps m y = n
    cases n <;> simp
  · rfl

/-- The branch of a comparison is taken exactly when the comparison is `sense`. -/
theorem cmpBr_step (c : Ctx) (ist : St) (tmps : Array Nat) (op : BinOp) (hc : op.isCompare = true) (sense : Bool)
    (m : Nat) (oa ob : Opd) (target : Nat) :
    step c ist tmps (cmpBr op sense m oa ob target) =
      if (natCmp op (opd c ist tmps m oa) (opd c ist tmps m ob) == sense) = true then .goto target
      else .next ist tmps := by
  unfold cmpBr
  rw [step_br]
  have h := cmpZero_spec c ist tmps m (cmpOf op oa ob)
  rw [cmpOf_spec c ist tmps op hc m oa ob] at h
  cases sense with
  | true => simp only [if_true, h, beq_true]
  | false =>
    simp only [Bool.false_eq_true, if_false, cmpOp_negate, h, beq_false]

/-- The value of a comparison. -/
theorem cmp_val (p : Prog) (op : BinOp) (hc : op.isCompare = true) (x y v : Val) (ta tb : Ty)
    (hx : HasTy p ta x) (hy : HasTy p tb y)
    (hw : if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true else ∃ w, ta = .int w ∧ tb = .int w)
    (hb : Lang.Sem.binop op x y = some v) : v = .bool (natCmp op x.toNat y.toNat) := by
  have hint : ∀ w w' (a b : UInt64), x = .int w a → y = .int w' b → v = .bool (natCmp op x.toNat y.toNat) := by
    intro w w' a b hx' hy'
    subst hx' hy'
    rw [binop_cmp op hc] at hb
    exact (Option.some.inj hb).symm
  by_cases he : op = .eq ∨ op = .ne
  · rw [if_pos he] at hw
    obtain ⟨rfl, hs⟩ := hw
    cases ta with
    | int w =>
      obtain ⟨a, rfl, _⟩ := hasTy_int hx
      obtain ⟨b, rfl, _⟩ := hasTy_int hy
      exact hint _ _ _ _ rfl rfl
    | bool =>
      obtain ⟨a, rfl⟩ := hasTy_bool hx
      obtain ⟨b, rfl⟩ := hasTy_bool hy
      rcases he with rfl | rfl <;> simp only [Lang.Sem.binop, Option.some.injEq] at hb <;> subst hb <;>
        cases a <;> cases b <;> rfl
    | arr _ _ => simp [Ty.isScalar] at hs
    | record _ => simp [Ty.isScalar] at hs
  · rw [if_neg he] at hw
    obtain ⟨w, rfl, rfl⟩ := hw
    obtain ⟨a, rfl, _⟩ := hasTy_int hx
    obtain ⟨b, rfl, _⟩ := hasTy_int hy
    exact hint _ _ _ _ rfl rfl

/-- A `bool` expression as a jump: its value against zero. -/
theorem boolJump_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (e : Expr) (s : LS)
    (sense : Bool) (target : Nat) (hw : WT E e) (hty : E.tyOf e = .ok .bool) :
    wp (boolJump e sense target) E (JPost c f sF E e sense target s) s := by
  unfold boolJump
  simp only [wp_bind]
  refine wp_mono (expr_ok F e E s .bool L hE hw hty rfl) ?_
  intro o s1 ⟨hx1, hc1, ho1, hs1⟩
  rw [wp_emit]
  refine ⟨hx1.trans (Ext.emit _ _), hc1, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hp := hs1 cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
  simp only [Array.size_push]
  cases hev : Lang.Sem.evalE E.prog lst env e with
  | none => simp only [hev] at hp ⊢; exact hp
  | some v =>
    simp only [hev] at hp ⊢
    obtain ⟨b, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) e v .bool hw hev hty)
    obtain ⟨t1, r1, sz1, ag1, ho⟩ := hp
    refine Jumps.prefix r1 sz1 (Jumps.one F (F.emitted hxF rfl) ?_)
    have ho' : opd c ist t1 1 o = (Val.bool b).toNat := ho
    rw [step_br, ho']
    cases b <;> cases sense <;> rfl

/-- A closed condition: a jump or nothing. -/
theorem closedJ_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (e : Expr) (s : LS) (sense : Bool)
    (target : Nat) {k : Nat} (hw : WT E e) (hty : E.tyOf e = .ok .bool) (hc : closed? e = some k) :
    wp (if ((k != 0) == sense) = true then emit (.jmp target) else pure ()) E
      (JPost c f sF E e sense target s) s := by
  obtain ⟨_, val, hv, hall⟩ := closed_val hw hty rfl hc
  have hb : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St), SRel c E cur lst env ist →
      ∃ b : Bool, val = .bool b ∧ (k != 0) = b := by
    intro cur lst env ist hrel
    obtain ⟨b, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) e val .bool hw (hall lst env) hty)
    refine ⟨b, rfl, ?_⟩
    rw [← hv]
    cases b <;> rfl
  by_cases hj : ((k != 0) == sense) = true
  · rw [if_pos hj, wp_emit]
    refine ⟨Ext.emit _ _, rfl, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    obtain ⟨b, rfl, hkb⟩ := hb cur lst env ist hrel
    rw [hall lst env]
    simp only [Array.size_push]
    rw [hkb] at hj
    refine Jumps.one F (F.emitted hxF rfl) ?_
    rw [step_jmp]
    simp only [Val.toBool, hj, if_true]
  · rw [if_neg hj, wp_pure]
    refine ⟨Ext.refl s, rfl, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    obtain ⟨b, rfl, hkb⟩ := hb cur lst env ist hrel
    rw [hall lst env]
    rw [hkb] at hj
    have : ((Val.bool b).toBool == sense) = false := by simpa [Val.toBool] using hj
    simp only [this]
    exact Jumps.none

/-- The value of `&&` and `||`. -/
def lres (op : BinOp) (x y : Bool) : Bool := if op == .land then x && y else x || y

theorem logic_val (op : BinOp) (hl : op.isLogic = true) (x y : Bool) :
    Lang.Sem.binop op (.bool x) (.bool y) = some (.bool (lres op x y)) := by
  cases op <;> simp [BinOp.isLogic] at hl <;> rfl

/-- `a && b` when false, `a || b` when true: either operand decides. -/
theorem logic_or_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (op : BinOp) (a b : Expr) (s : LS)
    (sense : Bool) (target : Nat) (hl : op.isLogic = true) (hw : WT E (.bin op a b))
    (hta : E.tyOf a = .ok .bool) (htb : E.tyOf b = .ok .bool) (hnt : canTrap b = false)
    (hid : ∀ x y, (lres op x y == sense) = ((x == sense) || (y == sense)))
    (iha : ∀ s1, wp (condJump a sense target) E (JPost c f sF E a sense target s1) s1)
    (ihb : ∀ s1, wp (condJump b sense target) E (JPost c f sF E b sense target s1) s1) :
    wp (do condJump a sense target; condJump b sense target) E (JPost c f sF E (.bin op a b) sense target s) s := by
  simp only [wp_bind]
  refine wp_mono (iha s) ?_
  intro _ s1 ⟨hx1, hc1, hs1⟩
  refine wp_mono (ihb s1) ?_
  intro _ s2 ⟨hx2, hc2, hs2⟩
  refine ⟨hx1.trans hx2, by rw [hc2, hc1], ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hA := hs1 cur lst env ist tmps (hx2.trans hxF) hrel hsz
  obtain ⟨y, hy⟩ := noTrap L hrel b .bool hw.2.1 htb hnt
  simp only [Lang.Sem.evalE, hy]
  cases hx : Lang.Sem.evalE E.prog lst env a with
  | none => simp only [hx] at hA ⊢; exact hA
  | some x =>
    simp only [hx] at hA ⊢
    obtain ⟨xa, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) a x .bool hw.1 hx hta)
    obtain ⟨yb, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) b y .bool hw.2.1 hy htb)
    rw [logic_val op hl]
    simp only [Val.toBool] at hA ⊢
    rw [hid]
    refine Jumps.or hA (fun t1 ht1 => ?_)
    have hB := hs2 cur lst env ist t1 hxF hrel (by rw [ht1]; exact hsz)
    simp only [hy, Val.toBool] at hB
    exact hB

/-- `a && b` when true, `a || b` when false: the first operand may skip the second. -/
theorem logic_skip_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (op : BinOp) (a b : Expr) (s : LS)
    (sense : Bool) (target : Nat) (hl : op.isLogic = true) (hw : WT E (.bin op a b))
    (hta : E.tyOf a = .ok .bool) (htb : E.tyOf b = .ok .bool) (hnt : canTrap b = false)
    (hid : ∀ x y, (lres op x y == sense) = (!(x == !sense) && (y == sense)))
    (iha : ∀ s1 l, wp (condJump a (!sense) l) E (JPost c f sF E a (!sense) l s1) s1)
    (ihb : ∀ s1, wp (condJump b sense target) E (JPost c f sF E b sense target s1) s1) :
    wp (do let skip ← newLabel; condJump a (!sense) skip; condJump b sense target; emit (.label skip)) E
      (JPost c f sF E (.bin op a b) sense target s) s := by
  simp only [wp_bind, wp_newLabel]
  refine wp_mono (iha _ s.labels) ?_
  intro _ s1 ⟨hx1, hc1, hs1⟩
  refine wp_mono (ihb s1) ?_
  intro _ s2 ⟨hx2, hc2, hs2⟩
  rw [wp_emit]
  refine ⟨(Ext.newLabel s).trans (hx1.trans (hx2.trans (Ext.emit _ _))), by rw [← hc1, ← hc2], ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
  have hA := hs1 cur lst env ist tmps (hx2.trans hxF2) hrel hsz
  obtain ⟨y, hy⟩ := noTrap L hrel b .bool hw.2.1 htb hnt
  simp only [Lang.Sem.evalE, hy, Array.size_push]
  cases hx : Lang.Sem.evalE E.prog lst env a with
  | none => simp only [hx] at hA ⊢; exact hA
  | some x =>
    simp only [hx] at hA ⊢
    obtain ⟨xa, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) a x .bool hw.1 hx hta)
    obtain ⟨yb, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) b y .bool hw.2.1 hy htb)
    rw [logic_val op hl]
    simp only [Val.toBool] at hA ⊢
    rw [hid]
    refine Jumps.skip hA (fun t1 ht1 => ?_) (F.emitted hxF rfl)
    have hB := hs2 cur lst env ist t1 hxF2 hrel (by rw [ht1]; exact hsz)
    simp only [hy, Val.toBool] at hB
    exact hB

/-- A comparison as a jump. -/
theorem cmpJump_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (op : BinOp) (a b : Expr)
    (s : LS) (sense : Bool) (target : Nat) (hc : op.isCompare = true) (hw : WT E (.bin op a b)) :
    wp (do
      let m ← size (← tyOf a)
      let ob ← expr b
      let oa ← expr a
      emit (cmpBr op sense m oa ob target)) E (JPost c f sF E (.bin op a b) sense target s) s := by
  obtain ⟨ta, tb, hta, htb, hsa, hsb, hcond, _⟩ := bin_types hw
  have hl : op.isLogic = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  have hsh : op.isShift = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  simp only [hl, hsh, Bool.false_eq_true, if_false] at hcond
  have htt : tb = ta := by
    by_cases he : op = .eq ∨ op = .ne
    · rw [if_pos he] at hcond; exact hcond.1.symm
    · rw [if_neg he] at hcond
      obtain ⟨w, rfl, rfl⟩ := hcond
      rfl
  subst htt
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t ht
  rw [hta] at ht
  cases ht
  refine wp_mono (expr_ok F b E s tb L hE hw.2.1 htb hsb) ?_
  intro ob s1 ⟨hx1, hc1, ho1, hs1⟩
  refine wp_mono (expr_ok F a E s1 tb L hE hw.1 hta hsa) ?_
  intro oa s2 ⟨hx2, hc2, ho2, hs2⟩
  rw [wp_emit]
  refine ⟨(hx1.trans hx2).trans (Ext.emit _ _), by rw [← hc1, ← hc2], ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
  have hpb := hs1 cur lst env ist tmps (hx2.trans hxF2) hrel hsz
  simp only [Lang.Sem.evalE, Array.size_push]
  cases hevb : Lang.Sem.evalE E.prog lst env b with
  | none =>
    simp only [hevb] at hpb
    cases Lang.Sem.evalE E.prog lst env a <;> exact hpb
  | some y =>
    simp only [hevb] at hpb
    cases heva : Lang.Sem.evalE E.prog lst env a with
    | none =>
      refine hpb.ends (fun t1 hts _ _ => ?_)
      have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [hts]; exact hsz)
      simp only [heva] at h2
      exact h2
    | some x =>
      have hvx := evalE_hasTy E lst env (hrel.typed L) a x tb hw.1 heva hta
      have hvy := evalE_hasTy E lst env (hrel.typed L) b y tb hw.2.1 hevb htb
      obtain ⟨v, hv⟩ := binop_some E.prog op x y tb tb hvx hvy (by rw [if_neg (by rw [hl]; decide), if_neg (by rw [hsh]; decide)]; exact hcond)
      have hvb := cmp_val E.prog op hc x y v tb tb hvx hvy hcond hv
      subst hvb
      simp only [hv]
      obtain ⟨t1, r1, sz1, ag1, hob⟩ := hpb
      have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [sz1]; exact hsz)
      simp only [heva] at h2
      obtain ⟨t2, r2, sz2, ag2, hoa⟩ := h2
      have hob2 : opd c ist t2 (sizeOf E.prog tb) ob = y.toNat := by
        rw [opd_agree c ist _ (fun t ht => (ho1.1 t ht).2) ag2]
        exact hob
      refine Jumps.prefix (r1.trans r2) (by rw [sz2, sz1]) (Jumps.one F (F.emitted hxF rfl) ?_)
      rw [cmpBr_step c ist t2 op hc, hoa, hob2]
      rfl

/-- **A condition as a jump.** -/
theorem condJump_ok (F : Final c fn f sF) : ∀ (e : Expr) (E : Env) (s : LS) (sense : Bool) (target : Nat),
    LayOK E.prog c → EnvOK E → WT E e → E.tyOf e = .ok .bool →
    wp (condJump e sense target) E (JPost c f sF E e sense target s) s
  | .un op a, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.un op a) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none =>
      cases op with
      | lnot =>
        have hta : E.tyOf a = .ok .bool := by simpa only [Env.tyOf] using hty
        refine wp_mono (condJump_ok F a E s (!sense) target L hE hw.1 hta) ?_
        intro _ s1 ⟨hx1, hc1, hs1⟩
        refine ⟨hx1, hc1, ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        have hA := hs1 cur lst env ist tmps hxF hrel hsz
        rw [evalE_un]
        cases hx : Lang.Sem.evalE E.prog lst env a with
        | none => simp only [hx] at hA ⊢; exact hA
        | some x =>
          simp only [hx] at hA ⊢
          obtain ⟨xa, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) a x .bool hw.1 hx hta)
          simp only [unV, Val.toBool] at hA ⊢
          have : ((!xa) == sense) = (xa == !sense) := by cases xa <;> cases sense <;> rfl
          rw [this]
          exact hA
      | bnot => exact boolJump_ok F L hE _ s sense target hw hty
      | neg => exact boolJump_ok F L hE _ s sense target hw hty
  | .bin op a b, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.bin op a b) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none =>
      simp only []
      by_cases hcmp : op.isCompare = true
      · rw [if_pos hcmp]
        exact cmpJump_ok F L hE op a b s sense target hcmp hw
      · rw [if_neg hcmp]
        by_cases hlog : (op.isLogic && !canTrap b) = true
        · rw [if_pos hlog]
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hlog
          obtain ⟨hl, hnt⟩ := hlog
          have hcond := hw.2.2
          rw [if_pos hl] at hcond
          obtain ⟨hta, htb⟩ := hcond
          have iha := fun (sn : Bool) (l : Nat) (s1 : LS) => condJump_ok F a E s1 sn l L hE hw.1 hta
          have ihb := fun (s1 : LS) => condJump_ok F b E s1 sense target L hE hw.2.1 htb
          by_cases hbr : ((op == .land) != sense) = true
          · rw [if_pos hbr]
            refine logic_or_ok F L op a b s sense target hl hw hta htb hnt ?_ (iha sense target) ihb
            intro x y
            cases op <;> simp [BinOp.isLogic] at hl <;> cases sense <;>
              first
                | exact absurd hbr (by decide)
                | (cases x <;> cases y <;> rfl)
          · rw [if_neg hbr]
            refine logic_skip_ok F L op a b s sense target hl hw hta htb hnt ?_ (fun s1 l => iha (!sense) l s1) ihb
            intro x y
            cases op <;> simp [BinOp.isLogic] at hl <;> cases sense <;>
              first
                | exact absurd hbr (by decide)
                | (cases x <;> cases y <;> rfl)
        · rw [if_neg hlog]
          exact boolJump_ok F L hE _ s sense target hw hty
  | .lit v w, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.lit v w) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .blit b, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.blit b) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .var x, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.var x) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .field b fld, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.field b fld) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .index b i, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.index b i) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .cast w a, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.cast w a) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty
  | .cond cnd a b, E, s, sense, target, L, hE, hw, hty => by
    unfold condJump
    cases hc : closed? (.cond cnd a b) with
    | some k => exact closedJ_ok F L _ s sense target hw hty hc
    | none => exact boolJump_ok F L hE _ s sense target hw hty

end

end Ember.Proof.IRSim
