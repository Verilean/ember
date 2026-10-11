import Ember.Proof.IRWp
import Ember.Proof.CArith

/-!
# Ember.Proof.IRArith — the IR's instructions compute Ember's operators (plan M7.1)

One lemma per kind of instruction the lowering emits for an operator:
its `step`, on operands that hold the values of the Ember operands,
stores the number of the Ember result (`binI_step`, `unI_step`,
`castI_step`).  The Ember side is `Ember.Proof.CArith` (`natOp`,
`natCmp`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record mask_toNat bits_le bits_pos natOp
  natCmp binop_cmp binop_arith mod_pow_bits)

theorem bits8 (w : Width) : 8 * (w.bits / 8) = w.bits := by cases w <;> rfl

theorem size_int (p : Prog) (w : Width) : sizeOf p (.int w) = w.bits / 8 := rfl

theorem size_bool (p : Prog) : sizeOf p .bool = 1 := rfl

theorem size_le8 (p : Prog) {t : Ty} (h : t.isScalar = true) : sizeOf p t ≤ 8 := by
  cases t with
  | int w => cases w <;> simp [IR.sizeOf, Width.bits]
  | bool => simp [IR.sizeOf]
  | arr _ _ => simp [Ty.isScalar] at h
  | record _ => simp [Ty.isScalar] at h

/-- A scalar fits its bytes. -/
theorem toNat_lt {p : Prog} {t : Ty} {v : Val} (h : HasTy p t v) (hs : t.isScalar = true) :
    v.toNat < 2 ^ (8 * sizeOf p t) := by
  cases t with
  | int w =>
    obtain ⟨x, rfl, hx⟩ := hasTy_int h
    rw [size_int, bits8]
    exact hx
  | bool =>
    obtain ⟨b, rfl⟩ := hasTy_bool h
    cases b <;> simp [Val.toNat, size_bool]
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

/-- The value of a closed expression. -/
theorem closed_sem {e : Expr} {k : Nat} (h : closed? e = some k) :
    ∃ val, C.closedVal e = some val ∧ val.toNat = k := by
  unfold closed? at h
  cases hc : C.closedVal e with
  | none => simp [hc] at h
  | some val =>
    cases val with
    | int w v => simp only [hc, Option.some.injEq] at h; exact ⟨_, rfl, h⟩
    | bool b => simp only [hc, Option.some.injEq] at h; exact ⟨_, rfl, h⟩
    | arr _ => simp [hc] at h
    | record _ _ => simp [hc] at h

/-! ## Instructions -/

section
variable (c : Ctx) (ist : St) (tmps : Array Nat)

theorem step_mov (n : Nat) (d : Dst) (o : Opd) :
    step c ist tmps (.mov n d o) = .set (setDst c ist tmps n d (opd c ist tmps n o)) := rfl

theorem step_bin (k : Bin) (n : Nat) (d : Dst) (oa ob : Opd) :
    step c ist tmps (.bin k n d oa ob) =
      .set (setDst c ist tmps n d (binOp k n (opd c ist tmps n oa) (opd c ist tmps n ob))) := rfl

theorem step_shift (left : Bool) (n : Nat) (d : Dst) (oa : Opd) (m : Nat) (amt : Opd) :
    step c ist tmps (.shift left n d oa m amt) =
      .set (setDst c ist tmps n d
        (if opd c ist tmps m amt ≥ 8 * n then 0
         else if left then modN n (opd c ist tmps n oa <<< opd c ist tmps m amt)
         else opd c ist tmps n oa >>> opd c ist tmps m amt)) := rfl

theorem step_cmp (k : Cmp) (n : Nat) (d : Dst) (oa ob : Opd) :
    step c ist tmps (.cmp k n d oa ob) =
      .set (setDst c ist tmps 1 d (if cmpOp k (opd c ist tmps n oa) (opd c ist tmps n ob) then 1 else 0)) := rfl

theorem step_ext (n : Nat) (d : Dst) (m : Nat) (o : Opd) :
    step c ist tmps (.ext n d m o) = .set (setDst c ist tmps n d (modN n (opd c ist tmps m o))) := rfl

theorem binOp_comm (k : Bin) (hk : k.commutes = true) (n a b : Nat) : binOp k n a b = binOp k n b a := by
  cases k <;> simp [Bin.commutes] at hk <;>
    simp [binOp, Nat.add_comm, Nat.mul_comm, Nat.and_comm, Nat.or_comm, Nat.xor_comm]

theorem step_arithI (k : Bin) (n : Nat) (d : Dst) (oa ob : Opd) :
    step c ist tmps (arithI k n d oa ob) =
      .set (setDst c ist tmps n d (binOp k n (opd c ist tmps n oa) (opd c ist tmps n ob))) := by
  unfold arithI
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [step_bin, binOp_comm k h.1.1]
  · rfl

theorem pow2_spec {o : Opd} {s : Nat} (h : pow2? o = some s) : o = .const (2 ^ s) := by
  cases o with
  | const v =>
    simp only [pow2?] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at hv
      rw [← hv]
    · cases h
  | slot _ => simp [pow2?] at h
  | tmp _ => simp [pow2?] at h

theorem pow_lt_inj {s n : Nat} (h : 2 ^ s < 2 ^ n) : s < n := by
  rcases Nat.lt_or_ge s n with h' | h'
  · exact h'
  · exact absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h') (by omega)

/-- Multiplication, division and remainder, also when the lowering turns
them into a shift or a mask. -/
theorem step_scaledI (k : Bin) (hk : k = .mul ∨ k = .div ∨ k = .mod) (n : Nat) (hn : n ≤ 8) (d : Dst)
    (oa ob : Opd) (ha : opd c ist tmps n oa < 2 ^ (8 * n))
    (hca : ∀ v, oa = .const v → v < 2 ^ (8 * n)) (hcb : ∀ v, ob = .const v → v < 2 ^ (8 * n)) :
    step c ist tmps (scaledI k n d oa ob) =
      .set (setDst c ist tmps n d (binOp k n (opd c ist tmps n oa) (opd c ist tmps n ob))) := by
  have key : ∀ (o : Opd) (s : Nat), pow2? o = some s → (∀ v, o = .const v → v < 2 ^ (8 * n)) →
      s < 8 * n ∧ opd c ist tmps n o = 2 ^ s ∧ opd c ist tmps 1 (.const s) = s := by
    intro o s hs hc
    have ho := pow2_spec hs
    subst ho
    have hlt := hc _ rfl
    have hs' := pow_lt_inj hlt
    exact ⟨hs', by rw [opd_const, modN_of_lt hlt], by rw [opd_const]; exact Nat.mod_eq_of_lt (by simp only [Nat.mul_one, Nat.reducePow]; omega)⟩
  unfold scaledI
  rcases hk with rfl | rfl | rfl
  · cases hpb : pow2? ob with
    | some s =>
      obtain ⟨h1, h2, h3⟩ := key ob s hpb hcb
      simp only [step_shift, h3, h2]
      rw [if_neg (by omega)]
      simp only [if_true, binOp, Nat.shiftLeft_eq]
    | none =>
      cases hpa : pow2? oa with
      | some s =>
        obtain ⟨h1, h2, h3⟩ := key oa s hpa hca
        simp only [step_shift, h3, h2]
        rw [if_neg (by omega)]
        simp only [if_true, binOp, Nat.shiftLeft_eq, Nat.mul_comm]
      | none => exact step_arithI c ist tmps _ n d oa ob
  · cases hpb : pow2? ob with
    | some s =>
      obtain ⟨h1, h2, h3⟩ := key ob s hpb hcb
      have hne : (2 ^ s == 0) = false := by simp
      cases hpa : pow2? oa <;>
      · simp only [step_shift, h3, h2]
        rw [if_neg (by omega)]
        simp only [Bool.false_eq_true, if_false, binOp, Nat.shiftRight_eq_div_pow, hne]
        rw [modN_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]
    | none => cases hpa : pow2? oa <;> exact step_arithI c ist tmps _ n d oa ob
  · cases hpb : pow2? ob with
    | some s =>
      obtain ⟨h1, h2, h3⟩ := key ob s hpb hcb
      have hne : (2 ^ s == 0) = false := by simp
      have hm : modN n (2 ^ s - 1) = 2 ^ s - 1 :=
        modN_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) h1))
      cases hpa : pow2? oa <;>
      · simp only [step_bin, opd_const, hm, h2, binOp, hne, Bool.false_eq_true, if_false,
          Nat.and_two_pow_sub_one_eq_mod]
    | none => cases hpa : pow2? oa <;> exact step_arithI c ist tmps _ n d oa ob

theorem set_congr (n : Nat) (d : Dst) {A B : Nat} (h : A = B) :
    Step.set (setDst c ist tmps n d A) = Step.set (setDst c ist tmps n d B) := by rw [h]

/-- Arithmetic on integers of one width (a shift amount may have another). -/
theorem binI_arith (op : BinOp) (hc : op.isCompare = false) (hl : op.isLogic = false) (w w' : Width)
    (a b : Nat) (ha : a < 2 ^ w.bits) (hb : b < 2 ^ w'.bits) (hww : op.isShift = false → w' = w) (d : Dst)
    (oa ob : Opd) (hoa : opd c ist tmps (w.bits / 8) oa = a) (hob : opd c ist tmps (w'.bits / 8) ob = b)
    (hca : ∀ k, oa = .const k → k < 2 ^ (8 * (w.bits / 8)))
    (hcb : ∀ k, ob = .const k → k < 2 ^ (8 * (w'.bits / 8))) :
    step c ist tmps (binI op (w.bits / 8) (w.bits / 8) (if op.isShift then w'.bits / 8 else 0) d oa ob) =
      .set (setDst c ist tmps (w.bits / 8) d (natOp op w.bits a b)) := by
  have h8 : w.bits / 8 ≤ 8 := by cases w <;> decide
  have hb8 := bits8 w
  cases op <;> simp only [BinOp.isCompare, BinOp.isLogic, BinOp.isShift, Bool.true_eq_false, forall_const,
    Bool.false_eq_true, if_false, if_true] at hc hl hww ⊢
  -- add
  · subst hww
    simp only [binI, step_arithI, hoa, hob]
    exact set_congr c ist tmps _ _ (by simp only [binOp, modN, natOp, hb8])
  -- sub
  · subst hww
    simp only [binI, step_arithI, hoa, hob]
    exact set_congr c ist tmps _ _ (by simp only [binOp, modN, natOp, hb8, Nat.add_comm])
  -- mul
  · subst hww
    simp only [binI]
    rw [step_scaledI c ist tmps .mul (.inl rfl) _ h8 d oa ob (by rw [hoa, hb8]; exact ha) hca hcb, hoa, hob]
    exact set_congr c ist tmps _ _ (by simp only [binOp, modN, natOp, hb8])
  -- div
  · subst hww
    simp only [binI]
    rw [step_scaledI c ist tmps .div (.inr (.inl rfl)) _ h8 d oa ob (by rw [hoa, hb8]; exact ha) hca hcb, hoa, hob]
    refine set_congr c ist tmps _ _ ?_
    simp only [binOp, natOp]
    by_cases h0 : b = 0
    · simp [h0, modN]
    · simp only [h0, beq_iff_eq, if_false]
      exact modN_of_lt (by rw [hb8]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)
  -- mod
  · subst hww
    simp only [binI]
    rw [step_scaledI c ist tmps .mod (.inr (.inr rfl)) _ h8 d oa ob (by rw [hoa, hb8]; exact ha) hca hcb, hoa, hob]
    refine set_congr c ist tmps _ _ ?_
    simp only [binOp, natOp]
    by_cases h0 : b = 0
    · simp [h0, modN]
    · simp only [h0, beq_iff_eq, if_false]
      exact modN_of_lt (by rw [hb8]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)
  -- band
  · subst hww
    simp only [binI, step_arithI, hoa, hob]
    refine set_congr c ist tmps _ _ ?_
    simp only [binOp, natOp]
    exact modN_of_lt (by rw [hb8]; exact Nat.lt_of_le_of_lt Nat.and_le_left ha)
  -- bor
  · subst hww
    simp only [binI, step_arithI, hoa, hob]
    refine set_congr c ist tmps _ _ ?_
    simp only [binOp, natOp]
    exact modN_of_lt (by rw [hb8]; exact Nat.or_lt_two_pow ha hb)
  -- bxor
  · subst hww
    simp only [binI, step_arithI, hoa, hob]
    refine set_congr c ist tmps _ _ ?_
    simp only [binOp, natOp]
    exact modN_of_lt (by rw [hb8]; exact Nat.xor_lt_two_pow ha hb)
  -- shl
  · simp only [binI, step_shift, hoa, hob]
    exact set_congr c ist tmps _ _ (by simp only [natOp, modN, hb8, if_true])
  -- shr
  · simp only [binI, step_shift, hoa, hob]
    exact set_congr c ist tmps _ _ (by simp only [natOp, modN, hb8, Bool.false_eq_true, if_false])

/-- A comparison of numbers. -/
theorem binI_cmp (op : BinOp) (hc : op.isCompare = true) (m : Nat) (a b : Nat) (d : Dst) (oa ob : Opd)
    (hoa : opd c ist tmps m oa = a) (hob : opd c ist tmps m ob = b) :
    step c ist tmps (binI op 1 m 0 d oa ob) =
      .set (setDst c ist tmps 1 d (if natCmp op a b then 1 else 0)) := by
  cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;>
    simp only [binI, step_cmp, hoa, hob, cmpOp, natCmp] <;> rfl

end

/-- A well-typed operator has a value. -/
theorem binop_some (p : Prog) (op : BinOp) (x y : Val) (ta tb : Ty) (hx : HasTy p ta x) (hy : HasTy p tb y)
    (hw : if op.isLogic then ta = .bool ∧ tb = .bool
       else if op.isShift then (∃ w, ta = .int w) ∧ ∃ w, tb = .int w
       else if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true
       else ∃ w, ta = .int w ∧ tb = .int w) : ∃ v, Lang.Sem.binop op x y = some v := by
  cases op <;> simp only [BinOp.isLogic, BinOp.isShift, Bool.false_eq_true, if_false, if_true,
    reduceCtorEq, or_false, false_or, or_self] at hw
  all_goals first
    | (obtain ⟨w, rfl, rfl⟩ := hw
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ := hw
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := hw
       obtain ⟨a, rfl⟩ := hasTy_bool hx
       obtain ⟨b, rfl⟩ := hasTy_bool hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨rfl, hs⟩ := hw
       cases ta with
       | int w =>
         obtain ⟨a, rfl, _⟩ := hasTy_int hx
         obtain ⟨b, rfl, _⟩ := hasTy_int hy
         exact ⟨_, rfl⟩
       | bool =>
         obtain ⟨a, rfl⟩ := hasTy_bool hx
         obtain ⟨b, rfl⟩ := hasTy_bool hy
         exact ⟨_, rfl⟩
       | arr _ _ => simp [Ty.isScalar] at hs
       | record _ => simp [Ty.isScalar] at hs)

/-- **The instruction of a binary operator stores the operator's value.** -/
theorem binI_step (c : Ctx) (ist : St) (tmps : Array Nat) (p : Prog) (op : BinOp) (x y v : Val) (ta tb : Ty)
    (d : Dst) (oa ob : Opd) (hx : HasTy p ta x) (hy : HasTy p tb y)
    (hw : if op.isLogic then ta = .bool ∧ tb = .bool
       else if op.isShift then (∃ w, ta = .int w) ∧ ∃ w, tb = .int w
       else if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true
       else ∃ w, ta = .int w ∧ tb = .int w)
    (hb : Lang.Sem.binop op x y = some v)
    (hoa : opd c ist tmps (sizeOf p ta) oa = x.toNat) (hob : opd c ist tmps (sizeOf p tb) ob = y.toNat)
    (hca : ∀ k, oa = .const k → k < 2 ^ (8 * sizeOf p ta)) (hcb : ∀ k, ob = .const k → k < 2 ^ (8 * sizeOf p tb)) :
    step c ist tmps (binI op (sizeOf p (if op.isCompare || op.isLogic then .bool else ta)) (sizeOf p ta)
        (if op.isShift then sizeOf p tb else 0) d oa ob) =
      .set (setDst c ist tmps (sizeOf p (if op.isCompare || op.isLogic then .bool else ta)) d v.toNat) := by
  by_cases hl : op.isLogic = true
  · -- `&&`, `||`
    rw [if_pos hl] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨a, rfl⟩ := hasTy_bool hx
    obtain ⟨b, rfl⟩ := hasTy_bool hy
    cases op <;> simp only [BinOp.isLogic, Bool.false_eq_true] at hl <;>
      simp only [Lang.Sem.binop, Option.some.injEq] at hb <;> subst hb <;>
      simp only [BinOp.isCompare, BinOp.isLogic, BinOp.isShift, Bool.or_true, if_true, Bool.false_eq_true, if_false,
        binI, step_arithI, size_bool] at hoa hob ⊢ <;>
      rw [hoa, hob] <;> refine set_congr c ist tmps _ _ ?_ <;> cases a <;> cases b <;> rfl
  · have hl' : op.isLogic = false := by simpa using hl
    rw [if_neg hl] at hw
    by_cases hc : op.isCompare = true
    · have hsh : op.isShift = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
      simp only [hc, hsh, Bool.true_or, if_true, Bool.false_eq_true, if_false, size_bool] at hw ⊢
      -- both operands have one scalar type
      have key : ∀ (m : Nat), opd c ist tmps m oa = x.toNat → opd c ist tmps m ob = y.toNat →
          v.toNat = (if natCmp op x.toNat y.toNat then 1 else 0) →
          step c ist tmps (binI op 1 m 0 d oa ob) = .set (setDst c ist tmps 1 d v.toNat) := by
        intro m h1 h2 h3
        rw [binI_cmp c ist tmps op hc m _ _ d oa ob h1 h2, h3]
      by_cases he : op = .eq ∨ op = .ne
      · rw [if_pos he] at hw
        obtain ⟨rfl, hs⟩ := hw
        refine key _ hoa hob ?_
        cases ta with
        | int w =>
          obtain ⟨a, rfl, _⟩ := hasTy_int hx
          obtain ⟨b, rfl, _⟩ := hasTy_int hy
          rw [binop_cmp op hc] at hb
          cases hb
          rfl
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
        refine key _ hoa hob ?_
        rw [binop_cmp op hc] at hb
        cases hb
        rfl
    · have hc' : op.isCompare = false := by simpa using hc
      simp only [hc', hl', Bool.or_self, Bool.false_eq_true, if_false] at hw ⊢
      have hty : ∃ w w', ta = .int w ∧ tb = .int w' ∧ (op.isShift = false → w' = w) := by
        by_cases hs : op.isShift = true
        · rw [if_pos hs] at hw
          obtain ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ := hw
          exact ⟨w, w', rfl, rfl, fun h => by rw [hs] at h; cases h⟩
        · rw [if_neg hs] at hw
          have hne : ¬ (op = .eq ∨ op = .ne) := by
            rintro (rfl | rfl) <;> simp [BinOp.isCompare] at hc'
          rw [if_neg hne] at hw
          obtain ⟨w, rfl, rfl⟩ := hw
          exact ⟨w, w, rfl, rfl, fun _ => rfl⟩
      obtain ⟨w, w', rfl, rfl, hww⟩ := hty
      obtain ⟨a, rfl, ha⟩ := hasTy_int hx
      obtain ⟨b, rfl, hb'⟩ := hasTy_int hy
      obtain ⟨r, hr1, hr2⟩ := binop_arith op hc' hl' w w' a b ha (fun h => by rw [hww h] at hb'; exact hb')
      rw [hr1] at hb
      cases hb
      simp only [size_int] at hoa hob hca hcb ⊢
      rw [binI_arith c ist tmps op hc' hl' w w' _ _ ha hb' hww d oa ob hoa hob hca hcb]
      exact set_congr c ist tmps _ _ hr2.symm

/-! ## Unary operators and casts -/

/-- A unary operator on a value. -/
def unV : UnOp → Val → Option Val
  | .lnot, .bool b => some (.bool !b)
  | .bnot, .int w v => some (.int w (mask w (~~~ v)))
  | .neg, .int w v => some (.int w (mask w (0 - v)))
  | _, _ => none

theorem evalE_un (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) (op : UnOp) (a : Expr) :
    Lang.Sem.evalE p st env (.un op a) =
      match Lang.Sem.evalE p st env a with
      | some x => unV op x
      | none => none := by
  simp only [Lang.Sem.evalE]
  cases Lang.Sem.evalE p st env a with
  | none => cases op <;> rfl
  | some x => cases op <;> cases x <;> rfl

theorem unI_step (c : Ctx) (ist : St) (tmps : Array Nat) (p : Prog) (op : UnOp) (x : Val) (ta : Ty) (d : Dst)
    (o : Opd) (hx : HasTy p ta x) (hw : if op = .lnot then ta = .bool else ∃ w, ta = .int w)
    (ho : opd c ist tmps (sizeOf p ta) o = x.toNat) :
    ∃ v, unV op x = some v ∧ HasTy p ta v ∧
      step c ist tmps (unI op (sizeOf p ta) d o) = .set (setDst c ist tmps (sizeOf p ta) d v.toNat) := by
  cases op with
  | lnot =>
    simp only [if_true] at hw
    subst hw
    obtain ⟨b, rfl⟩ := hasTy_bool hx
    refine ⟨_, rfl, trivial, ?_⟩
    simp only [unI, step_bin, size_bool] at ho ⊢
    rw [ho]
    refine set_congr c ist tmps _ _ ?_
    cases b <;> simp [binOp, opd_const, modN, Val.toNat]
  | bnot =>
    simp only [reduceCtorEq, if_false] at hw
    obtain ⟨w, rfl⟩ := hw
    obtain ⟨a, rfl, ha⟩ := hasTy_int hx
    refine ⟨_, rfl, Ember.Proof.CSim.hasTy_mask _ _ _, ?_⟩
    simp only [unI, size_int] at ho ⊢
    show Step.set (setDst c ist tmps (w.bits / 8) d (2 ^ (8 * (w.bits / 8)) - 1 - opd c ist tmps (w.bits / 8) o)) = _
    rw [ho]
    refine set_congr c ist tmps _ _ ?_
    simp only [Val.toNat, mask_toNat, UInt64.toNat_not, bits8]
    cases w <;> simp only [Width.bits, Nat.reducePow, UInt64.size] at ha ⊢ <;> omega
  | neg =>
    simp only [reduceCtorEq, if_false] at hw
    obtain ⟨w, rfl⟩ := hw
    obtain ⟨a, rfl, ha⟩ := hasTy_int hx
    refine ⟨_, rfl, Ember.Proof.CSim.hasTy_mask _ _ _, ?_⟩
    simp only [unI, size_int] at ho ⊢
    show Step.set (setDst c ist tmps (w.bits / 8) d (modN (w.bits / 8) (2 ^ (8 * (w.bits / 8)) - opd c ist tmps (w.bits / 8) o))) = _
    rw [ho]
    refine set_congr c ist tmps _ _ ?_
    simp only [Val.toNat, mask_toNat, UInt64.toNat_sub, UInt64.toNat_zero, modN, bits8]
    cases w <;> simp only [Width.bits, Nat.reducePow] at ha ⊢ <;> omega

/-- A cast of a value. -/
def castV (w : Width) : Val → Option Val
  | .int _ v => some (.int w (mask w v))
  | .bool b => some (.int w (if b then 1 else 0))
  | _ => none

theorem evalE_cast (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) (w : Width) (a : Expr) :
    Lang.Sem.evalE p st env (.cast w a) =
      match Lang.Sem.evalE p st env a with
      | some x => castV w x
      | none => none := by
  simp only [Lang.Sem.evalE]
  cases Lang.Sem.evalE p st env a with
  | none => rfl
  | some x => cases x <;> rfl

theorem cast_val (p : Prog) (w : Width) {x : Val} {ta : Ty} (hx : HasTy p ta x) (hs : ta.isScalar = true) :
    ∃ v, castV w x = some v ∧ HasTy p (.int w) v ∧ v.toNat = x.toNat % 2 ^ w.bits := by
  cases ta with
  | int w' =>
    obtain ⟨a, rfl, _⟩ := hasTy_int hx
    exact ⟨_, rfl, Ember.Proof.CSim.hasTy_mask _ _ _, mask_toNat _ _⟩
  | bool =>
    obtain ⟨b, rfl⟩ := hasTy_bool hx
    refine ⟨_, rfl, Ember.Proof.CSim.hasTy_int_mk _ _ _ ?_, ?_⟩
    · cases b <;> cases w <;> decide
    · cases b <;> cases w <;> rfl
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

theorem castI_step (c : Ctx) (ist : St) (tmps : Array Nat) (n m : Nat) (d : Dst) (o : Opd) (a : Nat)
    (ho : opd c ist tmps m o = a) (ha : a < 2 ^ (8 * m)) :
    step c ist tmps (castI n m d o) = .set (setDst c ist tmps n d (a % 2 ^ (8 * n))) := by
  unfold castI
  by_cases h1 : (n == m) = true
  · rw [if_pos h1]
    rw [beq_iff_eq] at h1
    subst h1
    rw [step_mov, ho, Nat.mod_eq_of_lt ha]
  · rw [if_neg h1]
    by_cases h2 : n < m
    · rw [if_pos h2]
      cases o with
      | slot s =>
        simp only [step_mov, opd_slot] at ho ⊢
        refine set_congr c ist tmps _ _ ?_
        rw [← ho, show m = n + (m - n) by omega, ← rd_low]
      | const k => simp only [step_ext, ho]; rfl
      | tmp t => simp only [step_ext, ho]; rfl
    · rw [if_neg h2]
      simp only [step_ext, ho]
      rfl

/-- The value of a constant scalar global, as the lowering takes it. -/
theorem const_toNat (p : Prog) (g : Global) (hs : g.ty.isScalar = true)
    (hb : g.ty = .bool → ∀ v, v ∈ g.init → v ≤ 1) :
    (initOf p g).toNat = (match g.init with | [v] => v % 2 ^ (8 * sizeOf p g.ty) | _ => 0) := by
  obtain ⟨name, ty, init, cst⟩ := g
  simp only at hs hb ⊢
  cases ty with
  | int w =>
    rcases init with _ | ⟨v, _ | ⟨v2, r⟩⟩
    · simp [initOf, zeroOf, Val.toNat]
    · simp only [initOf, Val.toNat, mask_toNat, UInt64.toNat_ofNat', size_int, bits8]
      exact mod_pow_bits w v
    · simp [initOf, zeroOf, Val.toNat]
  | bool =>
    rcases init with _ | ⟨v, _ | ⟨v2, r⟩⟩
    · simp [initOf, zeroOf, Val.toNat]
    · have := hb rfl v (by simp)
      simp only [initOf, Val.toNat, size_bool]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with rfl | rfl <;> rfl
    · simp [initOf, zeroOf, Val.toNat]
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

end Ember.Proof.IRSim
