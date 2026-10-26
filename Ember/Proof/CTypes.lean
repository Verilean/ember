import Ember.C.Compile
import Ember.Proof.CSem

/-!
# Ember.Proof.CTypes — values, their types, and well-typed expressions (plan M5.8)

* `cval`: the C value of an Ember value;
* `HasTy`: a value has an Ember type (integers are below `2^w`, arrays
  have their length, records the fields of their definition);
* `WT`: what the proofs need of a checked expression (literals in range,
  operands of one type, …), over the emitter's own `Env.tyOf`;
* `evalE_hasTy`: a well-typed expression evaluates to a value of its type;
* `closed_evalE`: a value found without variables is the value anywhere.
-/

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C

/-- The C value of an Ember value. -/
def cval (o : Opts) : Val → C.Sem.CVal
  | .int w v => .int w.bits v.toNat
  | .bool b => .bool b
  | .arr xs => .arr (xs.map (cval o))
  | .record n fs => .strct (o.structName n) (fs.map (cval o))

@[simp] theorem cval_int (o : Opts) (w : Width) (v : UInt64) : cval o (.int w v) = .int w.bits v.toNat := by
  rw [cval]

@[simp] theorem cval_bool (o : Opts) (b : Bool) : cval o (.bool b) = .bool b := by
  rw [cval]

@[simp] theorem cval_arr (o : Opts) (xs : Array Val) : cval o (.arr xs) = .arr (xs.map (cval o)) := by
  rw [cval]

@[simp] theorem cval_record (o : Opts) (n : String) (fs : Array Val) :
    cval o (.record n fs) = .strct (o.structName n) (fs.map (cval o)) := by
  rw [cval]

/-- A value of a type without records. -/
def HasTy0 : Ty → Val → Prop
  | .int w, .int w' v => w' = w ∧ v.toNat < 2 ^ w.bits
  | .bool, .bool _ => True
  | .arr el n, .arr xs => xs.size = n ∧ ∀ x, x ∈ xs → HasTy0 el x
  | _, _ => False

/-- A value of a type. -/
def HasTy (p : Prog) : Ty → Val → Prop
  | .record r, .record r' fs =>
    r' = r ∧ ∃ sd, p.struct? r = some sd ∧ fs.size = sd.fields.length ∧
      ∀ i (h : i < fs.size) (h' : i < sd.fields.length), HasTy0 (sd.fields[i]).2 fs[i]
  | .record _, _ => False
  | t, v => HasTy0 t v

theorem HasTy0.hasTy {p : Prog} {t : Ty} {v : Val} (h : HasTy0 t v) : HasTy p t v := by
  cases t with
  | record r => cases v <;> exact absurd h (by simp [HasTy0])
  | int w => exact h
  | bool => exact h
  | arr el n => exact h

/-- What the proofs need of a checked expression. -/
def WT (g : C.Env) : Expr → Prop
  | .lit v (some w) => v < 2 ^ w.bits
  | .lit _ none => False
  | .blit _ => True
  | .var _ => True
  | .field b _ => WT g b
  | .index b i => WT g b ∧ WT g i ∧ (∃ w, g.tyOf i = .ok (.int w)) ∧
      ∀ el n, g.tyOf b = .ok (.arr el n) → n < 65536
  | .bin op a b => WT g a ∧ WT g b ∧
      (if op.isLogic then g.tyOf a = .ok .bool ∧ g.tyOf b = .ok .bool
       else if op.isShift then (∃ w, g.tyOf a = .ok (.int w)) ∧ ∃ w, g.tyOf b = .ok (.int w)
       else if op = .eq ∨ op = .ne then ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true
       else ∃ w, g.tyOf a = .ok (.int w) ∧ g.tyOf b = .ok (.int w))
  | .un op a => WT g a ∧ (if op = .lnot then g.tyOf a = .ok .bool else ∃ w, g.tyOf a = .ok (.int w))
  | .cast _ a => WT g a ∧ ∃ t, g.tyOf a = .ok t ∧ t.isScalar = true
  | .cond c a b => WT g c ∧ WT g a ∧ WT g b ∧ g.tyOf c = .ok .bool ∧
      ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true

/-- Every variable in scope holds a value of its type. -/
def VarsTyped (g : C.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) : Prop :=
  ∀ x v info, Lang.Sem.lookup st env x = some v → g.varInfo x = .ok info → HasTy g.prog info.ty v

/-! ## Arithmetic stays in range -/

theorem mask_lt (w : Width) (v : UInt64) : (mask w v).toNat < 2 ^ w.bits := by
  cases w with
  | w64 => exact v.toNat_lt
  | w8 =>
    change (v &&& 255).toNat < 2 ^ 8
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  | w16 =>
    change (v &&& 65535).toNat < 2 ^ 16
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  | w32 =>
    change (v &&& 4294967295).toNat < 2 ^ 32
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ## Inversion -/

theorem hasTy_int {p : Prog} {w : Width} {v : Val} (h : HasTy p (.int w) v) :
    ∃ x, v = .int w x ∧ x.toNat < 2 ^ w.bits := by
  cases v with
  | int w' x => obtain ⟨rfl, hx⟩ := h; exact ⟨x, rfl, hx⟩
  | _ => exact absurd h (by simp [HasTy, HasTy0])

theorem hasTy_bool {p : Prog} {v : Val} (h : HasTy p .bool v) : ∃ b, v = .bool b := by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | _ => exact absurd h (by simp [HasTy, HasTy0])

theorem hasTy_arr {p : Prog} {el : Ty} {n : Nat} {v : Val} (h : HasTy p (.arr el n) v) :
    ∃ xs, v = .arr xs ∧ xs.size = n ∧ ∀ x, x ∈ xs → HasTy0 el x := by
  cases v with
  | arr xs => exact ⟨xs, rfl, h.1, h.2⟩
  | _ => exact absurd h (by simp [HasTy, HasTy0])

theorem hasTy_record {p : Prog} {r : String} {v : Val} (h : HasTy p (.record r) v) :
    ∃ fs sd, v = .record r fs ∧ p.struct? r = some sd ∧ fs.size = sd.fields.length ∧
      ∀ i (h : i < fs.size) (h' : i < sd.fields.length), HasTy0 (sd.fields[i]).2 fs[i] := by
  cases v with
  | record r' fs =>
    obtain ⟨rfl, sd, h1, h2, h3⟩ := h
    exact ⟨fs, sd, rfl, h1, h2, h3⟩
  | _ => exact absurd h (by simp [HasTy])

theorem hasTy_int_mk (p : Prog) (w : Width) (x : UInt64) (h : x.toNat < 2 ^ w.bits) : HasTy p (.int w) (.int w x) :=
  ⟨rfl, h⟩

theorem hasTy_mask (p : Prog) (w : Width) (x : UInt64) : HasTy p (.int w) (.int w (mask w x)) :=
  ⟨rfl, mask_lt w x⟩

theorem hasTy_bool_mk (p : Prog) (b : Bool) : HasTy p .bool (.bool b) := trivial

theorem lookup_of_findIdx {α : Type} (l : List (String × α)) (f : String) (i : Nat)
    (h : l.findIdx? (·.1 == f) = some i) : ∃ hi : i < l.length, l.lookup f = some l[i].2 := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    obtain ⟨k, x⟩ := a
    rw [List.findIdx?_cons] at h
    by_cases hk : (k == f) = true
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h
      have hk' : (f == k) = true := by rw [beq_iff_eq] at hk ⊢; exact hk.symm
      exact ⟨by simp, by simp [List.lookup, hk']⟩
    · have hk' : (f == k) = false := by
        cases hfk : f == k
        · rfl
        · rw [beq_iff_eq] at hfk; exact absurd (by rw [beq_iff_eq]; exact hfk.symm) hk
      simp only [hk, Bool.false_eq_true, if_false] at h
      cases hj : t.findIdx? (·.1 == f) with
      | none => simp [hj] at h
      | some j =>
        simp only [hj, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hj', hl⟩ := ih j hj
        exact ⟨by simp; omega, by simp [List.lookup, hk', hl]⟩

/-! ## A well-typed expression has a value of its type -/

theorem binop_hasTy (p : Prog) (op : BinOp) (x y v : Val) (ta tb : Ty)
    (hx : HasTy p ta x) (hy : HasTy p tb y)
    (hw : if op.isLogic then ta = .bool ∧ tb = .bool
       else if op.isShift then (∃ w, ta = .int w) ∧ ∃ w, tb = .int w
       else if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true
       else ∃ w, ta = .int w ∧ tb = .int w)
    (h : Lang.Sem.binop op x y = some v) :
    HasTy p (if op.isCompare || op.isLogic then .bool else ta) v := by
  cases op <;> simp only [BinOp.isLogic, BinOp.isShift, BinOp.isCompare, Bool.false_eq_true, if_false, if_true,
    reduceCtorEq, or_false, false_or, or_self, Bool.or_false, Bool.or_true, Bool.or_self] at hw ⊢
  all_goals first
    | (obtain ⟨w, rfl, rfl⟩ := hw
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       simp only [Lang.Sem.binop, Option.some.injEq] at h
       subst h
       first | exact hasTy_mask p _ _ | exact hasTy_bool_mk p _)
    | (obtain ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ := hw
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       simp only [Lang.Sem.binop, Option.some.injEq] at h
       subst h
       exact hasTy_mask p _ _)
    | (obtain ⟨rfl, rfl⟩ := hw
       obtain ⟨a, rfl⟩ := hasTy_bool hx
       obtain ⟨b, rfl⟩ := hasTy_bool hy
       simp only [Lang.Sem.binop, Option.some.injEq] at h
       subst h
       exact hasTy_bool_mk p _)
    | (obtain ⟨rfl, hs⟩ := hw
       cases ta with
       | int w =>
         obtain ⟨a, rfl, _⟩ := hasTy_int hx
         obtain ⟨b, rfl, _⟩ := hasTy_int hy
         simp only [Lang.Sem.binop, Option.some.injEq] at h
         subst h
         exact hasTy_bool_mk p _
       | bool =>
         obtain ⟨a, rfl⟩ := hasTy_bool hx
         obtain ⟨b, rfl⟩ := hasTy_bool hy
         simp only [Lang.Sem.binop, Option.some.injEq] at h
         subst h
         exact hasTy_bool_mk p _
       | arr _ _ => simp [Ty.isScalar] at hs
       | record _ => simp [Ty.isScalar] at hs)

theorem evalE_hasTy (g : C.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) (hv : VarsTyped g st env) :
    ∀ (e : Expr) (v : Val) (t : Ty), WT g e → Lang.Sem.evalE g.prog st env e = some v → g.tyOf e = .ok t →
      HasTy g.prog t v
  | .lit n (some w), v, t, _, h, ht => by
    simp only [Lang.Sem.evalE, Option.some.injEq] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst h ht
    exact hasTy_mask _ _ _
  | .lit _ none, _, _, hw, _, _ => absurd hw (by simp [WT])
  | .blit b, v, t, _, h, ht => by
    simp only [Lang.Sem.evalE, Option.some.injEq] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst h ht
    exact hasTy_bool_mk _ _
  | .var x, v, t, _, h, ht => by
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hi : g.varInfo x with
    | error m => simp [hi] at ht
    | ok info =>
      simp only [hi, Except.ok.injEq] at ht
      subst ht
      exact hv x v info h hi
  | .field b f, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hb : Lang.Sem.evalE g.prog st env b with
    | none => simp [hb] at h
    | some bv =>
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb =>
        have ih := evalE_hasTy g st env hv b bv tb hw hb htb
        cases tb with
        | record r =>
          obtain ⟨fs, sd, rfl, hsd, hsz, hfs⟩ := hasTy_record ih
          simp only [hb, Lang.Sem.fieldIndex, hsd] at h
          simp only [htb, Env.fieldTy, hsd] at ht
          cases hi : sd.fields.findIdx? (·.1 == f) with
          | none => simp [hi] at h
          | some i =>
            simp only [hi] at h
            obtain ⟨hlt, hl⟩ := lookup_of_findIdx sd.fields f i hi
            simp only [hl, Except.ok.injEq] at ht
            subst ht
            have hlt' : i < fs.size := by omega
            rw [Array.getElem?_eq_getElem hlt'] at h
            simp only [Option.some.injEq] at h
            subst h
            exact (hfs i hlt' hlt).hasTy
        | int _ => simp [htb, Env.err] at ht
        | bool => simp [htb, Env.err] at ht
        | arr _ _ => simp [htb, Env.err] at ht
  | .index b i, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases hb : Lang.Sem.evalE g.prog st env b with
    | none => simp [hb] at h
    | some bv =>
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb =>
        have ih := evalE_hasTy g st env hv b bv tb hw.1 hb htb
        cases tb with
        | arr el n =>
          obtain ⟨xs, rfl, _, hxs⟩ := hasTy_arr ih
          simp only [htb, Except.ok.injEq] at ht
          subst ht
          cases hi : Lang.Sem.evalE g.prog st env i with
          | none => simp [hb, hi] at h
          | some iv =>
            simp only [hb, hi] at h
            exact (hxs v (Array.mem_of_getElem? h)).hasTy
        | int _ => simp [htb, Env.err] at ht
        | bool => simp [htb, Env.err] at ht
        | record _ => simp [htb, Env.err] at ht
  | .bin op a b, v, t, hw, h, ht => by
    simp only [WT] at hw
    obtain ⟨wa, wb, hty⟩ := hw
    simp only [Lang.Sem.evalE] at h
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => simp [ha] at h
    | some x =>
      cases hb : Lang.Sem.evalE g.prog st env b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        have hex : (∃ ta, g.tyOf a = .ok ta) ∧ (∃ tb, g.tyOf b = .ok tb) := by
          split at hty
          · exact ⟨⟨_, hty.1⟩, ⟨_, hty.2⟩⟩
          · split at hty
            · obtain ⟨⟨w, h1⟩, ⟨w', h2⟩⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
            · split at hty
              · obtain ⟨t, h1, h2, _⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
              · obtain ⟨w, h1, h2⟩ := hty; exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
        obtain ⟨hta, htb⟩ := hex
        obtain ⟨ta, hta⟩ := hta
        obtain ⟨tb, htb⟩ := htb
        have iha := evalE_hasTy g st env hv a x ta wa ha hta
        have ihb := evalE_hasTy g st env hv b y tb wb hb htb
        have hres := binop_hasTy g.prog op x y v ta tb iha ihb (by
          simp only [hta, htb, Except.ok.injEq] at hty
          by_cases h1 : op.isLogic = true
          · rw [if_pos h1] at hty ⊢; exact hty
          · rw [if_neg h1] at hty ⊢
            by_cases h2 : op.isShift = true
            · rw [if_pos h2] at hty ⊢; exact hty
            · rw [if_neg h2] at hty ⊢
              by_cases h3 : op = .eq ∨ op = .ne
              · rw [if_pos h3] at hty ⊢; obtain ⟨t', rfl, rfl, hs⟩ := hty; exact ⟨rfl, hs⟩
              · rw [if_neg h3] at hty ⊢; obtain ⟨w, rfl, rfl⟩ := hty; exact ⟨w, rfl, rfl⟩) h
        simp only [Env.tyOf] at ht
        split at ht
        · rename_i hc
          simp only [Except.ok.injEq] at ht
          subst ht
          simpa [hc] using hres
        · rename_i hc
          rw [hta] at ht
          simp only [Except.ok.injEq] at ht
          subst ht
          simpa [hc] using hres
  | .un op a, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => cases op <;> simp [ha] at h
    | some x =>
      have ih := evalE_hasTy g st env hv a x t hw.1 ha ht
      cases op with
      | lnot =>
        simp only [if_true] at hw
        rw [hw.2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl⟩ := hasTy_bool ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_bool_mk _ _
      | bnot =>
        simp only [reduceCtorEq, if_false] at hw
        obtain ⟨w, hw2⟩ := hw.2
        rw [hw2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl, _⟩ := hasTy_int ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
      | neg =>
        simp only [reduceCtorEq, if_false] at hw
        obtain ⟨w, hw2⟩ := hw.2
        rw [hw2] at ht
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨b, rfl, _⟩ := hasTy_int ih
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
  | .cast w a, v, t, hw, h, ht => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf, Except.ok.injEq] at ht
    subst ht
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => simp [ha] at h
    | some x =>
      cases x with
      | int w' xv =>
        simp only [ha, Option.some.injEq] at h
        subst h
        exact hasTy_mask _ _ _
      | bool b =>
        simp only [ha, Option.some.injEq] at h
        subst h
        refine hasTy_int_mk _ _ _ ?_
        cases b <;> cases w <;> decide
      | arr _ => simp [ha] at h
      | record _ _ => simp [ha] at h
  | .cond c a b, v, t, hw, h, ht => by
    simp only [WT] at hw
    obtain ⟨wc, wa, wb, _, t', hta, htb, _⟩ := hw
    simp only [Lang.Sem.evalE] at h
    simp only [Env.tyOf] at ht
    rw [hta] at ht
    simp only [Except.ok.injEq] at ht
    subst ht
    cases hc : Lang.Sem.evalE g.prog st env c with
    | none => simp [hc] at h
    | some cv =>
      cases ha : Lang.Sem.evalE g.prog st env a with
      | none => simp [hc, ha] at h
      | some x =>
        cases hb : Lang.Sem.evalE g.prog st env b with
        | none => simp [hc, ha, hb] at h
        | some y =>
          simp only [hc, ha, hb, Option.some.injEq] at h
          subst h
          split
          · exact evalE_hasTy g st env hv a x _ wa ha hta
          · exact evalE_hasTy g st env hv b y _ wb hb htb

/-! ## Closed expressions -/

/-- The program and state `closedVal` evaluates in: nothing is in scope. -/
def noProg : Prog := { fns := [] }
def noSt : Lang.Sem.St := { globals := [], world := { inputs := #[] } }

theorem closed_evalE' (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) :
    ∀ (e : Expr) (v : Val), Lang.Sem.evalE noProg noSt [] e = some v → Lang.Sem.evalE p st env e = some v
  | .lit n (some w), v, h => by simpa only [Lang.Sem.evalE] using h
  | .lit _ none, _, h => by simp [Lang.Sem.evalE] at h
  | .blit b, v, h => by simpa only [Lang.Sem.evalE] using h
  | .var x, v, h => by simp [Lang.Sem.evalE, Lang.Sem.lookup, noSt] at h
  | .field b f, v, h => by
    simp only [Lang.Sem.evalE] at h
    cases hb : Lang.Sem.evalE noProg noSt [] b with
    | none => simp [hb] at h
    | some bv =>
      cases bv with
      | record r fs =>
        simp only [hb] at h
        simp [Lang.Sem.fieldIndex, noProg, Prog.struct?] at h
      | int _ _ => simp [hb] at h
      | bool _ => simp [hb] at h
      | arr _ => simp [hb] at h
  | .index b i, v, h => by
    simp only [Lang.Sem.evalE] at h ⊢
    cases hb : Lang.Sem.evalE noProg noSt [] b with
    | none => simp [hb] at h
    | some bv =>
      cases hi : Lang.Sem.evalE noProg noSt [] i with
      | none => simp [hb, hi] at h
      | some iv =>
        simp only [hb, hi] at h
        simp only [closed_evalE' p st env b bv hb, closed_evalE' p st env i iv hi]
        exact h
  | .bin op a b, v, h => by
    simp only [Lang.Sem.evalE] at h ⊢
    cases ha : Lang.Sem.evalE noProg noSt [] a with
    | none => simp [ha] at h
    | some x =>
      cases hb : Lang.Sem.evalE noProg noSt [] b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        simp only [closed_evalE' p st env a x ha, closed_evalE' p st env b y hb]
        exact h
  | .un op a, v, h => by
    simp only [Lang.Sem.evalE] at h ⊢
    cases ha : Lang.Sem.evalE noProg noSt [] a with
    | none => cases op <;> simp [ha] at h
    | some x =>
      simp only [ha] at h
      simp only [closed_evalE' p st env a x ha]
      exact h
  | .cast w a, v, h => by
    simp only [Lang.Sem.evalE] at h ⊢
    cases ha : Lang.Sem.evalE noProg noSt [] a with
    | none => simp [ha] at h
    | some x =>
      simp only [ha] at h
      simp only [closed_evalE' p st env a x ha]
      exact h
  | .cond c a b, v, h => by
    simp only [Lang.Sem.evalE] at h ⊢
    cases hc : Lang.Sem.evalE noProg noSt [] c with
    | none => simp [hc] at h
    | some cv =>
      cases ha : Lang.Sem.evalE noProg noSt [] a with
      | none => simp [hc, ha] at h
      | some x =>
        cases hb : Lang.Sem.evalE noProg noSt [] b with
        | none => simp [hc, ha, hb] at h
        | some y =>
          simp only [hc, ha, hb] at h
          simp only [closed_evalE' p st env c cv hc, closed_evalE' p st env a x ha, closed_evalE' p st env b y hb]
          exact h

/-- A value the emitter found without variables is the expression's value in every state. -/
theorem closed_evalE (e : Expr) (v : Val) (h : closedVal e = some v) (p : Prog) (st : Lang.Sem.St)
    (env : Lang.Sem.Env) : Lang.Sem.evalE p st env e = some v :=
  closed_evalE' p st env e v h

end Ember.Proof.CSim
