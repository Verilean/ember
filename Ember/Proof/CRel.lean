import Ember.Proof.CExpr
import Ember.Proof.CFuel

/-!
# Ember.Proof.CRel — the relation between the states, for statements (plan M5.8)

An expression needs `ERel`: every variable's C lvalue holds its value.
Statements change variables and declare them, so the relation is kept
position by position:

* `LRel`: the Ember locals and the C locals are the same list, apart
  from the emitter's temporaries, which only C has;
* `GRel`: every global holds its value, and the two worlds are equal;
* `Same`: two C scopes with the same names, in which the temporaries
  have the same values — what a statement leaves of the scope it ran in;
* `assign_sim`: `Lang.Sem.assign` on a place is `C.Sem.write` at the
  location of its lvalue.

By-reference parameters are not covered: the relation has no pointers.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

/-! ## Names -/

theorem localName_eq (x : String) : localName x = "v_" ++ x := rfl

theorem globalName_eq (o : Opts) (x : String) : o.globalName x = o.namePrefix ++ "g_" ++ x := rfl

theorem fnName_eq (o : Opts) (x : String) : o.fnName x = o.namePrefix ++ "e_" ++ x := rfl

theorem tmp_ne_local (k : Nat) (x : String) : tmpName k ≠ localName x := by
  rw [localName_eq]
  unfold tmpName
  intro h
  have := congrArg String.toList h
  simp at this

theorem localName_inj {x y : String} (h : localName x = localName y) : x = y := by
  rw [localName_eq, localName_eq] at h
  exact (String.append_right_inj _).mp h

theorem globalName_inj {o : Opts} {x y : String} (h : o.globalName x = o.globalName y) : x = y := by
  rw [globalName_eq, globalName_eq] at h
  exact (String.append_right_inj _).mp h

theorem fnName_inj {o : Opts} {x y : String} (h : o.fnName x = o.fnName y) : x = y := by
  rw [fnName_eq, fnName_eq] at h
  exact (String.append_right_inj _).mp h

/-- What the proofs need of the names the emitter makes up: a global is
never called like a local or a temporary, and an Ember function is never
called like one of the runtime's. -/
structure Hyg (o : Opts) : Prop where
  gl : ∀ z x, o.globalName z ≠ localName x
  gt : ∀ z k, o.globalName z ≠ tmpName k
  fh : ∀ f, C.Sem.helper (o.fnName f) = none
  ft : ∀ f, (o.fnName f == "ember_trap") = false

/-- What is fixed for a compiled program: the unit's records, the
widths, its tables and its functions are those of the Ember program. -/
structure Unit (p : Prog) (o : Opts) (cp : CProg) : Prop where
  flds : ∀ r sd, p.struct? r = some sd →
    cp.unit.structs.lookup (o.structName r) = some (sd.fields.map fun ft => (cty o ft.2, ft.1))
  ints : cp.intBits = o.profile.intBits
  i16 : 16 ≤ cp.intBits
  l32 : 32 ≤ cp.longBits
  nobug : o.bugDropCast = false
  hyg : Hyg o
  drops : cp.dropReasons = p.dropReasons
  notes : cp.notes = p.notes
  fns : ∀ f fd, p.fn? f = some fd →
    ∃ cfd, cp.unit.fns.find? (·.name == o.fnName f) = some cfd ∧ compileFn p o fd = .ok cfd
  noeff : ∀ e, cp.unit.fns.find? (·.name == effectCall e) = none

/-! ## Scopes with the same names -/

/-- The same names in the same order, and the same values in the temporaries. -/
inductive Same : C.Sem.Env → C.Sem.Env → Prop
  | nil : Same [] []
  | cons {x y : String × CVal} {a b : C.Sem.Env} : (x.1 = y.1 ∧ ((∃ k, x.1 = tmpName k) → x.2 = y.2)) → Same a b →
      Same (x :: a) (y :: b)

theorem Same.refl (a : C.Sem.Env) : Same a a := by
  induction a with
  | nil => exact .nil
  | cons x r ih => exact .cons ⟨rfl, fun _ => rfl⟩ ih

theorem Same.trans {a b c : C.Sem.Env} (h1 : Same a b) (h2 : Same b c) : Same a c := by
  induction h1 generalizing c with
  | nil => cases h2; exact .nil
  | cons hx _ ih =>
    cases h2 with
    | cons hy h2 =>
      exact .cons ⟨hx.1.trans hy.1, fun hk => (hx.2 hk).trans (hy.2 (by rw [← hx.1]; exact hk))⟩ (ih h2)

theorem Same.length {a b : C.Sem.Env} (h : Same a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Same.lookup_none {a b : C.Sem.Env} (h : Same a b) (y : String) : a.lookup y = none → b.lookup y = none := by
  induction h with
  | nil => intro h; exact h
  | @cons x x' r r' hx _ ih =>
    obtain ⟨n, v⟩ := x
    obtain ⟨n', v'⟩ := x'
    simp only at hx
    obtain ⟨rfl, _⟩ := hx
    intro hl
    simp only [List.lookup] at hl ⊢
    cases hy : y == n with
    | true => simp [hy] at hl
    | false => simp only [hy] at hl ⊢; exact ih hl

theorem Same.append {a b c d : C.Sem.Env} (h1 : Same a b) (h2 : Same c d) : Same (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hx _ ih => exact .cons hx ih

/-- A scope that extends `xs ++ a` splits the same way. -/
theorem Same.split {xs a c : C.Sem.Env} (h : Same (xs ++ a) c) :
    ∃ xs' a', c = xs' ++ a' ∧ Same xs xs' ∧ Same a a' := by
  induction xs generalizing c with
  | nil => exact ⟨[], c, rfl, .nil, h⟩
  | cons x r ih =>
    cases h with
    | @cons _ y _ c' hx h =>
      obtain ⟨xs', a', rfl, h1, h2⟩ := ih h
      exact ⟨y :: xs', a', rfl, .cons hx h1, h2⟩

theorem Same.setFirst (a : C.Sem.Env) (y : String) (v : CVal) (hy : ∀ k, y ≠ tmpName k) :
    Same a (C.Sem.setFirst a y v) := by
  induction a with
  | nil => exact .nil
  | cons x r ih =>
    obtain ⟨n, w⟩ := x
    simp only [C.Sem.setFirst]
    by_cases hn : (n == y) = true
    · rw [if_pos hn]
      refine .cons ⟨rfl, fun ⟨k, hk⟩ => ?_⟩ (Same.refl r)
      simp only at hk
      rw [beq_iff_eq] at hn
      exact absurd (hn ▸ hk) (hy k)
    · rw [if_neg hn]
      exact .cons ⟨rfl, fun _ => rfl⟩ ih

/-- Temporaries keep their values. -/
theorem Same.lookup_tmp {a b : C.Sem.Env} (h : Same a b) (k : Nat) : b.lookup (tmpName k) = a.lookup (tmpName k) := by
  induction h with
  | nil => rfl
  | @cons x x' r r' hx _ ih =>
    obtain ⟨n, v⟩ := x
    obtain ⟨n', v'⟩ := x'
    simp only at hx
    obtain ⟨rfl, hv⟩ := hx
    simp only [List.lookup]
    cases hy : tmpName k == n with
    | true =>
      rw [beq_iff_eq] at hy
      simp only [hv ⟨k, hy.symm⟩]
    | false => exact ih

theorem Fresh.same {t : Nat} {cst cst' : C.Sem.St} {a b : C.Sem.Env} (hf : Fresh t cst a) (h : Same a b)
    (hg : ∀ k, cst'.globals.lookup (tmpName k) = none) : Fresh t cst' b :=
  fun k hk => ⟨h.lookup_none _ (hf k hk).1, hg k⟩

theorem Fresh.mono {t t' : Nat} {cst : C.Sem.St} {a : C.Sem.Env} (hf : Fresh t cst a) (h : t ≤ t') : Fresh t' cst a :=
  fun k hk => hf k (Nat.le_trans h hk)

theorem Fresh.cons_local {t : Nat} {cst : C.Sem.St} {a : C.Sem.Env} (hf : Fresh t cst a) (x : String) (v : CVal) :
    Fresh t cst ((localName x, v) :: a) := by
  intro k hk
  refine ⟨?_, (hf k hk).2⟩
  have hne : (tmpName k == localName x) = false := by
    cases h : tmpName k == localName x
    · rfl
    · rw [beq_iff_eq] at h; exact absurd h (tmp_ne_local k x)
  simp only [List.lookup, hne]
  exact (hf k hk).1

theorem Fresh.cons_tmp {t : Nat} {cst : C.Sem.St} {a : C.Sem.Env} (hf : Fresh t cst a) (v : CVal) :
    Fresh (t + 1) cst ((tmpName t, v) :: a) := by
  have := hf.append (Temps.one t v) (Nat.le_succ t)
  exact this

/-! ## Locals, position by position -/

/-- The Ember locals `env` (as the emitter knows them: `vs`) and the C
locals `cenv`: the same variables with the same values, and temporaries
in between. -/
inductive LRel (p : Prog) (o : Opts) : List (String × VarInfo) → Lang.Sem.Env → C.Sem.Env → Prop
  | nil : LRel p o [] [] []
  | tmp {vs env cenv} (k : Nat) (cv : CVal) : LRel p o vs env cenv → LRel p o vs env ((tmpName k, cv) :: cenv)
  | val {vs env cenv} (x : String) (ty : Ty) (v : Val) : HasTy p ty v → LRel p o vs env cenv →
      LRel p o ((x, { ty, c := .var (localName x) }) :: vs) ((x, v) :: env) ((localName x, cval o v) :: cenv)

section
variable {p : Prog} {o : Opts}

theorem LRel.length {vs env cenv} (h : LRel p o vs env cenv) : vs.length = env.length := by
  induction h with
  | nil => rfl
  | tmp _ _ _ ih => exact ih
  | val _ _ _ _ _ ih => simp [ih]

/-- A local that has a value: the emitter knows it, and C holds the value. -/
theorem LRel.lookup {vs env cenv} (h : LRel p o vs env cenv) {x : String} {v : Val} (hx : env.lookup x = some v) :
    ∃ ty, vs.lookup x = some { ty, c := .var (localName x) } ∧ HasTy p ty v ∧
      cenv.lookup (localName x) = some (cval o v) := by
  induction h with
  | nil => simp at hx
  | tmp k cv _ ih =>
    obtain ⟨ty, h1, h2, h3⟩ := ih hx
    refine ⟨ty, h1, h2, ?_⟩
    have hne : (localName x == tmpName k) = false := by
      cases h : localName x == tmpName k
      · rfl
      · rw [beq_iff_eq] at h; exact absurd h.symm (tmp_ne_local k x)
    simp only [List.lookup, hne]
    exact h3
  | val y ty w hty _ ih =>
    simp only [List.lookup] at hx ⊢
    cases hxy : x == y with
    | true =>
      rw [beq_iff_eq] at hxy
      subst hxy
      simp only [beq_self_eq_true, Option.some.injEq] at hx
      subst hx
      exact ⟨ty, by simp, hty, by simp⟩
    | false =>
      simp only [hxy] at hx
      obtain ⟨ty', h1, h2, h3⟩ := ih hx
      have hne : (localName x == localName y) = false := by
        cases h : localName x == localName y
        · rfl
        · rw [beq_iff_eq] at h; rw [localName_inj h] at hxy; simp at hxy
      simp only [hne]
      exact ⟨ty', h1, h2, h3⟩

theorem LRel.lookup_none {vs env cenv} (h : LRel p o vs env cenv) {x : String} (hx : env.lookup x = none) :
    vs.lookup x = none ∧ cenv.lookup (localName x) = none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | tmp k cv _ ih =>
    obtain ⟨h1, h3⟩ := ih hx
    refine ⟨h1, ?_⟩
    have hne : (localName x == tmpName k) = false := by
      cases h : localName x == tmpName k
      · rfl
      · rw [beq_iff_eq] at h; exact absurd h.symm (tmp_ne_local k x)
    simp only [List.lookup, hne]
    exact h3
  | val y ty w hty _ ih =>
    simp only [List.lookup] at hx ⊢
    cases hxy : x == y with
    | true => simp [hxy] at hx
    | false =>
      simp only [hxy] at hx
      obtain ⟨h1, h3⟩ := ih hx
      have hne : (localName x == localName y) = false := by
        cases h : localName x == localName y
        · rfl
        · rw [beq_iff_eq] at h; rw [localName_inj h] at hxy; simp at hxy
      simp only [hne]
      exact ⟨h1, h3⟩

/-- Every C local is a temporary or the C name of a local. -/
theorem LRel.names {vs env cenv} (h : LRel p o vs env cenv) :
    ∀ y, y ∈ cenv.map (·.1) → (∃ k, y = tmpName k) ∨ ∃ x, y = localName x := by
  induction h with
  | nil => intro y hy; simp at hy
  | tmp k cv _ ih =>
    intro y hy
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl ⟨k, rfl⟩
    · exact ih y hy
  | val x ty v _ _ ih =>
    intro y hy
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inr ⟨x, rfl⟩
    · exact ih y hy

/-- A global's C name is not a local's. -/
theorem LRel.no_global {vs env cenv} (h : LRel p o vs env cenv) (hy : Hyg o) (z : String) :
    cenv.lookup (o.globalName z) = none := by
  apply C.Sem.lookup_eq_none_of_not_mem
  intro hm
  rcases h.names _ hm with ⟨k, e⟩ | ⟨x, e⟩
  · exact hy.gt z k e
  · exact hy.gl z x e

theorem LRel.append {nv ys xs vs env cenv} (h1 : LRel p o nv ys xs) (h2 : LRel p o vs env cenv) :
    LRel p o (nv ++ vs) (ys ++ env) (xs ++ cenv) := by
  induction h1 with
  | nil => exact h2
  | tmp k cv _ ih => exact .tmp k cv ih
  | val x ty v hty _ ih => exact .val x ty v hty ih

/-- Temporaries on top. -/
theorem LRel.temps {vs env cenv} {xs : C.Sem.Env} {t0 t1 : Nat} (ht : Temps xs t0 t1) (h : LRel p o vs env cenv) :
    LRel p o vs env (xs ++ cenv) := by
  induction xs with
  | nil => exact h
  | cons x r ih =>
    obtain ⟨n, v⟩ := x
    obtain ⟨k, _, _, e⟩ := ht n (by simp)
    subst e
    exact .tmp k v (ih fun y hy => ht y (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hy))

/-- Scopes whose names are temporaries only. -/
def AllTmp (xs : C.Sem.Env) : Prop := ∀ y, y ∈ xs.map (·.1) → ∃ k, y = tmpName k

theorem Temps.allTmp {xs : C.Sem.Env} {t0 t1 : Nat} (h : Temps xs t0 t1) : AllTmp xs := fun y hy => by
  obtain ⟨k, _, _, e⟩ := h y hy
  exact ⟨k, e⟩

theorem AllTmp.nil : AllTmp [] := fun y hy => by simp at hy

theorem AllTmp.same {xs xs' : C.Sem.Env} (h : AllTmp xs) (hs : Same xs xs') : AllTmp xs' := by
  induction hs with
  | nil => exact h
  | @cons x x' r r' hx _ ih =>
    intro y hy
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [← hx.1]; exact h _ (by simp)
    · exact ih (fun z hz => h z (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hz)) y hy

theorem LRel.allTmp {xs : C.Sem.Env} (h : AllTmp xs) : LRel p o [] [] xs := by
  induction xs with
  | nil => exact .nil
  | cons x r ih =>
    obtain ⟨n, v⟩ := x
    obtain ⟨k, e⟩ := h n (by simp)
    subst e
    exact .tmp k v (ih fun y hy => h y (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hy))

theorem LRel.tail_tmp {vs env c} (h : LRel p o vs env c) (k : Nat) (v : CVal) (c' : C.Sem.Env)
    (hc : c = (tmpName k, v) :: c') : LRel p o vs env c' := by
  cases h with
  | nil => cases hc
  | tmp k' cv h =>
    simp only [List.cons.injEq] at hc
    rw [← hc.2]; exact h
  | val x ty w _ _ =>
    simp only [List.cons.injEq, Prod.mk.injEq] at hc
    exact absurd hc.1.1.symm (tmp_ne_local k x)

/-- Temporaries on top can be left out. -/
theorem LRel.strip {vs env cenv} {xs : C.Sem.Env} (ht : AllTmp xs) (h : LRel p o vs env (xs ++ cenv)) :
    LRel p o vs env cenv := by
  induction xs with
  | nil => exact h
  | cons x r ih =>
    obtain ⟨n, v⟩ := x
    obtain ⟨k, e⟩ := ht n (by simp)
    subst e
    have hr : AllTmp r := fun y hy => ht y (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hy)
    exact ih hr (h.tail_tmp k v _ rfl)

/-- The innermost local, when the C scope begins with it. -/
theorem LRel.head_val {vs env c} (h : LRel p o vs env c) (x : String) (cv : CVal) (c' : C.Sem.Env)
    (hc : c = (localName x, cv) :: c') :
    ∃ ty v vs' env', vs = (x, { ty, c := .var (localName x) }) :: vs' ∧ env = (x, v) :: env' ∧ cv = cval o v ∧
      HasTy p ty v ∧ LRel p o vs' env' c' := by
  cases h with
  | nil => cases hc
  | tmp k' cv' h =>
    simp only [List.cons.injEq, Prod.mk.injEq] at hc
    exact absurd hc.1.1 (tmp_ne_local k' x)
  | val y ty w hw h =>
    simp only [List.cons.injEq, Prod.mk.injEq] at hc
    obtain ⟨⟨hn, rfl⟩, rfl⟩ := hc
    have := localName_inj hn
    subst this
    exact ⟨ty, w, _, _, rfl, rfl, rfl, hw, h⟩

/-- A local changes on both sides. -/
theorem LRel.set {vs env cenv} (h : LRel p o vs env cenv) {x : String} {ty : Ty} {v' : Val}
    (hx : vs.lookup x = some { ty, c := .var (localName x) }) (hty : HasTy p ty v') :
    LRel p o vs (Lang.Sem.setFirst env x v') (C.Sem.setFirst cenv (localName x) (cval o v')) := by
  induction h with
  | nil => simp at hx
  | tmp k cv _ ih =>
    have hne : ¬ (tmpName k == localName x) = true := by
      rw [beq_iff_eq]; exact tmp_ne_local k x
    simp only [C.Sem.setFirst, if_neg hne]
    exact .tmp k cv (ih hx)
  | val y ty0 w hw _ ih =>
    simp only [List.lookup] at hx
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, Option.some.injEq, VarInfo.mk.injEq, and_true] at hx
      subst hx
      simp only [Lang.Sem.setFirst, C.Sem.setFirst, beq_self_eq_true, if_true]
      exact .val x ty0 v' hty (by assumption)
    · have h1 : (x == y) = false := by simpa using hxy
      have h2 : ¬ (y == x) = true := by
        rw [beq_iff_eq]; exact fun e => hxy e.symm
      have h3 : ¬ (localName y == localName x) = true := by
        rw [beq_iff_eq]; exact fun e => hxy (localName_inj e).symm
      simp only [h1] at hx
      simp only [Lang.Sem.setFirst, C.Sem.setFirst, if_neg h2, if_neg h3]
      exact .val y ty0 w hw (ih hx)

end

/-! ## Globals and the world -/

structure GRel (p : Prog) (o : Opts) (st : Lang.Sem.St) (cst : C.Sem.St) : Prop where
  glob : ∀ z gd, p.global? z = some gd → ∃ v, st.globals.lookup z = some v ∧ HasTy p gd.ty v ∧
    cst.globals.lookup (o.globalName z) = some (cval o v)
  gtmp : ∀ k, cst.globals.lookup (tmpName k) = none
  world : cst.world = st.world

/-- **The relation a statement keeps.** -/
def SRel (g : C.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) (cst : C.Sem.St) (cenv : C.Sem.Env) : Prop :=
  LRel g.prog g.opts g.vars env cenv ∧ GRel g.prog g.opts st cst

/-- The storage of a variable: a local of the current frame, or the global. -/
def xloc (o : Opts) (env : Lang.Sem.Env) (cst : C.Sem.St) (x : String) : C.Sem.Loc :=
  if (env.lookup x).isSome then { base := .frame cst.stack.length (localName x) }
  else { base := .global (o.globalName x) }

theorem cval_ne_ptr (o : Opts) (v : Val) (l : C.Sem.Loc) : cval o v ≠ .ptr l := by
  cases v <;> simp [cval]

section
variable {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env}

/-- What the emitter knows of a variable in scope. -/
theorem SRel.info (h : SRel g st env cst cenv) {x : String} {v : Val} {info : VarInfo}
    (hl : Lang.Sem.lookup st env x = some v) (hi : g.varInfo x = .ok info) :
    HasTy g.prog info.ty v ∧ info.ptr = false ∧
    ((env.lookup x = some v ∧ info.c = .var (localName x) ∧ cenv.lookup (localName x) = some (cval g.opts v) ∧
        g.vars.lookup x = some info) ∨
     (env.lookup x = none ∧ st.globals.lookup x = some v ∧ info.c = .var (g.opts.globalName x) ∧
        cst.globals.lookup (g.opts.globalName x) = some (cval g.opts v) ∧ g.vars.lookup x = none ∧
        ∃ gd, g.prog.global? x = some gd ∧ info.ty = gd.ty)) := by
  obtain ⟨hloc, hglob⟩ := h
  unfold Lang.Sem.lookup at hl
  unfold Env.varInfo at hi
  cases he : env.lookup x with
  | some w =>
    simp only [he, Option.some.injEq] at hl
    subst hl
    obtain ⟨ty, h1, h2, h3⟩ := hloc.lookup he
    simp only [h1, Except.ok.injEq] at hi
    subst hi
    exact ⟨h2, rfl, Or.inl ⟨rfl, rfl, h3, h1⟩⟩
  | none =>
    simp only [he] at hl
    obtain ⟨h1, _⟩ := hloc.lookup_none he
    simp only [h1] at hi
    cases hg : g.prog.global? x with
    | none => simp [hg, Env.err] at hi
    | some gd =>
      obtain ⟨w, hw, hty, hc⟩ := hglob.glob x gd hg
      simp only [hg, Except.ok.injEq] at hi
      subst hi
      rw [hl] at hw
      cases hw
      exact ⟨hty, rfl, Or.inr ⟨rfl, hl, rfl, hc, h1, gd, rfl, rfl⟩⟩

/-- A variable's lvalue designates its storage. -/
theorem SRel.place_loc (h : SRel g st env cst cenv) (hy : Hyg g.opts) {x : String} {v : Val} {info : VarInfo}
    (hl : Lang.Sem.lookup st env x = some v) (hi : g.varInfo x = .ok info) :
    PlaceLoc cp cst cenv info.c info.ptr (cval g.opts v) (xloc g.opts env cst x) := by
  obtain ⟨_, hp, hc⟩ := h.info hl hi
  rcases hc with ⟨he, hc, hcl, _⟩ | ⟨he, _, hc, hcg, _, _⟩
  · rw [hc, hp]
    unfold xloc
    simp only [he, Option.isSome_some, if_true]
    refine ⟨_, ?_, Or.inl ⟨rfl, rfl, ?_⟩⟩
    · simp [C.Sem.lval, C.Sem.varLoc, hcl]
    · simp [C.Sem.read, C.Sem.readBase, hcl, C.Sem.getPath]
  · rw [hc, hp]
    unfold xloc
    simp only [he, Option.isSome_none, Bool.false_eq_true, if_false]
    have hn := h.1.no_global hy x
    refine ⟨_, ?_, Or.inl ⟨rfl, rfl, ?_⟩⟩
    · simp [C.Sem.lval, C.Sem.varLoc, hn, hcg]
    · simp [C.Sem.read, C.Sem.readBase, hcg, C.Sem.getPath]

/-- A statement's relation gives an expression's. -/
theorem SRel.erel (h : SRel g st env cst cenv) (U : Unit g.prog g.opts cp) : ERel g cp st env cst cenv where
  typed := fun x v info hl hi => (h.info hl hi).1
  place := fun x v info hl hi => ⟨_, h.place_loc U.hyg hl hi⟩
  flds := U.flds
  ints := U.ints
  i16 := U.i16
  l32 := U.l32
  nobug := U.nobug
  scope := fun x info hi => by
    obtain ⟨hloc, hglob⟩ := h
    cases he : env.lookup x with
    | some w => exact ⟨w, by simp [Lang.Sem.lookup, he]⟩
    | none =>
      obtain ⟨h1, _⟩ := hloc.lookup_none he
      unfold Env.varInfo at hi
      simp only [h1] at hi
      cases hg : g.prog.global? x with
      | none => simp [hg, Env.err] at hi
      | some gd =>
        obtain ⟨w, hw, _, _⟩ := hglob.glob x gd hg
        exact ⟨w, by simp [Lang.Sem.lookup, he, hw]⟩

theorem SRel.temps (h : SRel g st env cst cenv) {xs : C.Sem.Env} {t0 t1 : Nat} (ht : Temps xs t0 t1) :
    SRel g st env cst (xs ++ cenv) := ⟨h.1.temps ht, h.2⟩

theorem SRel.strip {xs : C.Sem.Env} (ht : AllTmp xs) (h : SRel g st env cst (xs ++ cenv)) : SRel g st env cst cenv :=
  ⟨h.1.strip ht, h.2⟩

theorem SRel.fresh (h : SRel g st env cst cenv) {t : Nat} {cst0 : C.Sem.St} {cenv0 : C.Sem.Env}
    (hf : Fresh t cst0 cenv0) (hs : Same cenv0 cenv) : Fresh t cst cenv := hf.same hs h.2.gtmp

end

/-! ## Uniqueness of a location -/

theorem PlaceLoc.unique {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} {c : CExpr} {ptr : Bool} {cv : CVal}
    {L L' : C.Sem.Loc} (h : PlaceLoc cp cst cenv c ptr cv L) (h' : PlaceLoc cp cst cenv c ptr cv L')
    (hcv : ∀ l, cv ≠ .ptr l) : L = L' := by
  obtain ⟨l0, hl, hr⟩ := h
  obtain ⟨l0', hl', hr'⟩ := h'
  rw [hl] at hl'
  cases hl'
  rcases hr with ⟨_, rfl, hr⟩ | ⟨h1, _, _⟩ <;> rcases hr' with ⟨_, rfl, hr'⟩ | ⟨h1', _, _⟩
  · rfl
  · rw [hr] at h1'; cases h1'; exact absurd rfl (hcv _)
  · rw [hr'] at h1; cases h1; exact absurd rfl (hcv _)
  · rw [h1] at h1'; cases h1'; rfl

/-! ## Changing a variable -/

theorem lsetFirst_length (env : Lang.Sem.Env) (x : String) (v : Val) :
    (Lang.Sem.setFirst env x v).length = env.length := by
  induction env with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨y, w⟩ := a
    simp only [Lang.Sem.setFirst]
    split <;> simp [ih]

theorem lsetFirst_lookup_self (env : Lang.Sem.Env) (x : String) (v w : Val) (h : env.lookup x = some w) :
    (Lang.Sem.setFirst env x v).lookup x = some v := by
  induction env with
  | nil => simp at h
  | cons a r ih =>
    obtain ⟨y, u⟩ := a
    simp only [Lang.Sem.setFirst, List.lookup] at h ⊢
    by_cases hy : y = x
    · subst hy; simp
    · have h1 : ¬ (y == x) = true := by simpa using hy
      have h2 : (x == y) = false := by simpa using fun e : x = y => hy e.symm
      simp only [if_neg h1, List.lookup, h2] at h ⊢
      exact ih h

theorem lsetFirst_lookup_ne (env : Lang.Sem.Env) (x y : String) (v : Val) (hne : y ≠ x) :
    (Lang.Sem.setFirst env x v).lookup y = env.lookup y := by
  induction env with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨z, u⟩ := a
    simp only [Lang.Sem.setFirst]
    by_cases hz : (z == x) = true
    · rw [if_pos hz]
      rw [beq_iff_eq] at hz
      subst hz
      have : (y == z) = false := by simpa using hne
      simp only [List.lookup, this]
    · rw [if_neg hz]
      simp only [List.lookup]
      cases y == z
      · exact ih
      · rfl

theorem csetFirst_lookup_self (env : C.Sem.Env) (x : String) (v w : CVal) (h : env.lookup x = some w) :
    (C.Sem.setFirst env x v).lookup x = some v := by
  induction env with
  | nil => simp at h
  | cons a r ih =>
    obtain ⟨y, u⟩ := a
    simp only [C.Sem.setFirst, List.lookup] at h ⊢
    by_cases hy : y = x
    · subst hy; simp
    · have h1 : ¬ (y == x) = true := by simpa using hy
      have h2 : (x == y) = false := by simpa using fun e : x = y => hy e.symm
      simp only [if_neg h1, List.lookup, h2] at h ⊢
      exact ih h

theorem csetFirst_lookup_ne (env : C.Sem.Env) (x y : String) (v : CVal) (hne : y ≠ x) :
    (C.Sem.setFirst env x v).lookup y = env.lookup y := by
  induction env with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨z, u⟩ := a
    simp only [C.Sem.setFirst]
    by_cases hz : (z == x) = true
    · rw [if_pos hz]
      rw [beq_iff_eq] at hz
      subst hz
      have : (y == z) = false := by simpa using hne
      simp only [List.lookup, this]
    · rw [if_neg hz]
      simp only [List.lookup]
      cases y == z
      · exact ih
      · rfl

/-! ## A changed value keeps its type -/

theorem hasTy_scalar_unique {p : Prog} {t tx : Ty} {u : Val} (hs : t.isScalar = true) (h : HasTy p t u)
    (hx : HasTy p tx u) : tx = t := by
  cases t with
  | int w =>
    obtain ⟨x, rfl, _⟩ := hasTy_int h
    cases tx with
    | int w2 => obtain ⟨x', e, _⟩ := hasTy_int hx; cases e; rfl
    | bool => obtain ⟨b, e⟩ := hasTy_bool hx; cases e
    | arr _ _ => obtain ⟨_, e, _⟩ := hasTy_arr hx; cases e
    | record _ => obtain ⟨_, _, e, _⟩ := hasTy_record hx; cases e
  | bool =>
    obtain ⟨b, rfl⟩ := hasTy_bool h
    cases tx with
    | int w2 => obtain ⟨x', e, _⟩ := hasTy_int hx; cases e
    | bool => rfl
    | arr _ _ => obtain ⟨_, e, _⟩ := hasTy_arr hx; cases e
    | record _ => obtain ⟨_, _, e, _⟩ := hasTy_record hx; cases e
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

theorem hasTy0_of_scalar {p : Prog} {t : Ty} {v : Val} (hs : t.isScalar = true) (h : HasTy p t v) : HasTy0 t v := by
  cases t with
  | int w => exact h
  | bool => exact h
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

theorem vmod_hasTy0 (p : Prog) (t : Ty) (hs : t.isScalar = true) (v : Val) (hv : HasTy p t v) :
    ∀ (q : List Nat) (tx : Ty) (vx vold vx' : Val), HasTy0 tx vx → vget vx q = some vold → HasTy p t vold →
      vmod vx q (fun _ => some v) = some vx' → HasTy0 tx vx'
  | [], tx, vx, vold, vx', h0, hg, ho, hm => by
    simp only [vget, Option.some.injEq] at hg
    subst hg
    simp only [vmod, Option.some.injEq] at hm
    subst hm
    have := hasTy_scalar_unique hs ho h0.hasTy
    subst this
    exact hasTy0_of_scalar hs hv
  | i :: r, tx, vx, vold, vx', h0, hg, ho, hm => by
    cases vx with
    | arr xs =>
      cases tx with
      | arr el n =>
        obtain ⟨hsz, hall⟩ := h0
        simp only [vget] at hg
        simp only [vmod] at hm
        cases hx : xs[i]? with
        | none => simp [hx] at hg
        | some old =>
          simp only [hx] at hg hm
          cases hn : vmod old r (fun _ => some v) with
          | none => simp [hn] at hm
          | some new =>
            simp only [hn, Option.some.injEq] at hm
            subst hm
            have hold : HasTy0 el old := hall old (Array.mem_of_getElem? hx)
            have hnew := vmod_hasTy0 p t hs v hv r el old vold new hold hg ho hn
            refine ⟨by simp [Array.set!_eq_setIfInBounds, hsz], fun x hx' => ?_⟩
            rw [Array.set!_eq_setIfInBounds] at hx'
            rcases Array.mem_or_eq_of_mem_setIfInBounds hx' with h | h
            · exact hall x h
            · rw [h]; exact hnew
      | int _ => exact absurd h0 (by simp [HasTy0])
      | bool => exact absurd h0 (by simp [HasTy0])
      | record _ => exact absurd h0 (by simp [HasTy0])
    | record n fs => cases tx <;> exact absurd h0 (by simp [HasTy0])
    | int _ _ => simp [vget] at hg
    | bool _ => simp [vget] at hg

theorem vmod_hasTy (p : Prog) (t : Ty) (hs : t.isScalar = true) (v : Val) (hv : HasTy p t v) (q : List Nat)
    (tx : Ty) (vx vold vx' : Val) (hx : HasTy p tx vx) (hg : vget vx q = some vold) (ho : HasTy p t vold)
    (hm : vmod vx q (fun _ => some v) = some vx') : HasTy p tx vx' := by
  cases tx with
  | record rn =>
    obtain ⟨fs, sd, rfl, hsd, hsz, hall⟩ := hasTy_record hx
    cases q with
    | nil =>
      simp only [vget, Option.some.injEq] at hg
      subst hg
      have := hasTy_scalar_unique hs ho hx
      subst this
      simp [Ty.isScalar] at hs
    | cons i r =>
      simp only [vget] at hg
      simp only [vmod] at hm
      cases hfi : fs[i]? with
      | none => simp [hfi] at hg
      | some old =>
        simp only [hfi] at hg hm
        cases hn : vmod old r (fun _ => some v) with
        | none => simp [hn] at hm
        | some new =>
          simp only [hn, Option.some.injEq] at hm
          subst hm
          obtain ⟨hi, hio⟩ := Array.getElem?_eq_some_iff.mp hfi
          have hold : HasTy0 (sd.fields[i]'(by omega)).2 old := by rw [← hio]; exact hall i hi (by omega)
          have hnew := vmod_hasTy0 p t hs v hv r _ old vold new hold hg ho hn
          refine ⟨rfl, sd, hsd, by simp [Array.set!_eq_setIfInBounds, hsz], fun j hj hj' => ?_⟩
          have hjf : j < fs.size := by simpa [Array.set!_eq_setIfInBounds] using hj
          have e : (fs.set! i new)[j] = if i = j then new else fs[j] := by
            simp only [Array.set!_eq_setIfInBounds]
            exact Array.getElem_setIfInBounds _
          rw [e]
          by_cases hij : i = j
          · subst hij; rw [if_pos rfl]; exact hnew
          · rw [if_neg hij]; exact hall j hjf hj'
  | int w => exact (vmod_hasTy0 p t hs v hv q _ vx vold vx' hx hg ho hm).hasTy
  | bool => exact (vmod_hasTy0 p t hs v hv q _ vx vold vx' hx hg ho hm).hasTy
  | arr el n => exact (vmod_hasTy0 p t hs v hv q _ vx vold vx' hx hg ho hm).hasTy

/-- The variable of a typed place is one the emitter knows. -/
theorem tyOf_root (g : C.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (t : Ty) (x : String)
    (q : List Nat), g.tyOf e = .ok t → lpath g.prog st env e = some (x, q) → ∃ info, g.varInfo x = .ok info
  | .var y, t, x, q, ht, hl => by
    simp only [lpath, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, _⟩ := hl
    simp only [Env.tyOf] at ht
    cases hv : g.varInfo y with
    | error m => simp [hv] at ht
    | ok info => exact ⟨info, rfl⟩
  | .field b f, t, x, q, ht, hl => by
    simp only [lpath] at hl
    cases hb : lpath g.prog st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      have hx : x0 = x := by
        simp only [hb] at hl
        cases hbv : Lang.Sem.evalE g.prog st env b with
        | none => simp [hbv] at hl
        | some bv =>
          cases bv with
          | record r fs =>
            simp only [hbv] at hl
            cases hi : Lang.Sem.fieldIndex g.prog r f with
            | none => simp [hi] at hl
            | some i => simp only [hi, Option.some.injEq, Prod.mk.injEq] at hl; exact hl.1
          | int _ _ => simp [hbv] at hl
          | bool _ => simp [hbv] at hl
          | arr _ => simp [hbv] at hl
      subst hx
      simp only [Env.tyOf] at ht
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb => exact tyOf_root g st env b tb x0 q0 htb hb
  | .index b i, t, x, q, ht, hl => by
    simp only [lpath] at hl
    cases hb : lpath g.prog st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      have hx : x0 = x := by
        simp only [hb] at hl
        cases hiv : Lang.Sem.evalE g.prog st env i with
        | none => simp [hiv] at hl
        | some iv => simp only [hiv, Option.some.injEq, Prod.mk.injEq] at hl; exact hl.1
      subst hx
      simp only [Env.tyOf] at ht
      cases htb : g.tyOf b with
      | error m => simp [htb] at ht
      | ok tb => exact tyOf_root g st env b tb x0 q0 htb hb
  | .lit _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .blit _, _, _, _, _, hl => by simp [lpath] at hl
  | .bin _ _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .un _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .cast _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .cond _ _ _, _, _, _, _, hl => by simp [lpath] at hl

theorem convLike_scalar (o : Opts) (p : Prog) (t : Ty) (hs : t.isScalar = true) (vold v : Val)
    (ho : HasTy p t vold) (hv : HasTy p t v) : C.Sem.convLike (cval o vold) (cval o v) = some (cval o v) := by
  cases t with
  | int w =>
    obtain ⟨x, rfl, _⟩ := hasTy_int ho
    obtain ⟨y, rfl, hy⟩ := hasTy_int hv
    simp only [cval_int, C.Sem.convLike, Nat.mod_eq_of_lt hy]
  | bool =>
    obtain ⟨b, rfl⟩ := hasTy_bool ho
    obtain ⟨c, rfl⟩ := hasTy_bool hv
    simp [C.Sem.convLike]
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

/-! ## Assignment -/

/-- **`assign` is `write`.**  A typed scalar place that has a value, with
the location its lvalue designates: assigning in Ember and writing in C
lead to related states. -/
theorem assign_sim {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv : C.Sem.Env} (U : Unit g.prog g.opts cp) (hrel : SRel g st env cst cenv) (d : Expr) (cd : CExpr)
    (ptr : Bool) (v vold : Val) (t : Ty) (hsc : t.isScalar = true) (hty : g.tyOf d = .ok t) (hwt : WT g d)
    (hpl : IsPlace d) (hv : HasTy g.prog t v) (hold : Lang.Sem.evalE g.prog st env d = some vold)
    (L : C.Sem.Loc) (hL : PlaceLoc cp cst cenv cd ptr (cval g.opts vold) L)
    (hroot : Rooted g cp d L st env cst cenv) :
    ∃ st' env' cst' cenv', Lang.Sem.assign g.prog st env d v = some (st', env') ∧
      C.Sem.lval cp cst cenv cd = some L ∧ C.Sem.read cst cenv L = some (cval g.opts vold) ∧
      C.Sem.convLike (cval g.opts vold) (cval g.opts v) = some (cval g.opts v) ∧
      C.Sem.write cst cenv L (cval g.opts v) = some (cst', cenv') ∧
      SRel g st' env' cst' cenv' ∧ Same cenv cenv' ∧ env'.length = env.length ∧ cst'.stack = cst.stack := by
  have herel := hrel.erel U
  have hto : HasTy g.prog t vold := evalE_hasTy g st env herel.typed d vold t hwt hold hty
  obtain ⟨x, q, hq⟩ := lpath_some _ _ _ d vold hpl hold
  obtain ⟨vx, hlx, hget⟩ := evalE_lpath _ _ _ d vold x q hold hq
  obtain ⟨info, hinfo⟩ := tyOf_root g st env d t x q hty hq
  obtain ⟨Lx, hLx, rfl⟩ := hroot x q hq info vx hinfo hlx
  have hLx' := hrel.place_loc (cp := cp) U.hyg hlx hinfo
  have hLe := hLx.unique hLx' (cval_ne_ptr _ _)
  subst hLe
  have hsv := cval_scalar g.opts g.prog t vold hsc hto
  have hlr : C.Sem.lval cp cst cenv cd = some { xloc g.opts env cst x with path := (xloc g.opts env cst x).path ++ q } ∧
      C.Sem.read cst cenv { xloc g.opts env cst x with path := (xloc g.opts env cst x).path ++ q }
        = some (cval g.opts vold) := by
    obtain ⟨l0, hl0, hr⟩ := hL
    rcases hr with ⟨_, e, hread⟩ | ⟨_, _, h3⟩
    · rw [← e] at hl0 hread; exact ⟨hl0, hread⟩
    · rcases h3 with ⟨_, n, fs, e⟩ | ⟨_, ys, e⟩
      · exact absurd e (hsv.1 n fs)
      · exact absurd e (hsv.2 ys)
  obtain ⟨vx', hmod⟩ := vmod_some vx q (fun _ => some v) vold v hget rfl
  have hupd : Lang.Sem.assign g.prog st env d v = updVar st env x (fun vx => vmod vx q (fun _ => some v)) :=
    update_lpath g.prog st env d _ vold x q hold hq
  obtain ⟨htx, hptr, hc⟩ := hrel.info hlx hinfo
  have htyx' : HasTy g.prog info.ty vx' := vmod_hasTy g.prog t hsc v hv q info.ty vx vold vx' htx hget hto hmod
  have hsp := setPath_cval g.opts v q vx vx' hmod
  have hcl := convLike_scalar g.opts g.prog t hsc vold v hto hv
  rcases hc with ⟨he, hc, hcl', hvl⟩ | ⟨he, hgl, hc, hcg, hvn, gd, hgd, hgty⟩
  · have hxl : xloc g.opts env cst x = { base := .frame cst.stack.length (localName x) } := by
      simp [xloc, he]
    rw [hxl] at hlr ⊢
    have hinfo' : info = { ty := info.ty, c := .var (localName x) } := by
      cases info; simp only at hc hptr; subst hc; subst hptr; rfl
    rw [hinfo'] at hvl
    refine ⟨st, Lang.Sem.setFirst env x vx', cst, C.Sem.setFirst cenv (localName x) (cval g.opts vx'), ?_, hlr.1,
      hlr.2, hcl, ?_, ⟨hrel.1.set hvl htyx', hrel.2⟩, Same.setFirst _ _ _ (fun k e => tmp_ne_local k x e.symm),
      lsetFirst_length _ _ _, rfl⟩
    · rw [hupd]; simp [updVar, he, hmod]
    · simp [C.Sem.write, C.Sem.readBase, hcl', hsp, C.Sem.writeBase]
  · have hxl : xloc g.opts env cst x = { base := .global (g.opts.globalName x) } := by
      simp [xloc, he]
    rw [hxl] at hlr ⊢
    refine ⟨{ st with globals := Lang.Sem.setFirst st.globals x vx' }, env,
      { cst with globals := C.Sem.setFirst cst.globals (g.opts.globalName x) (cval g.opts vx') }, cenv, ?_, hlr.1,
      hlr.2, hcl, ?_, ⟨hrel.1, ?_⟩, Same.refl _, rfl, rfl⟩
    · rw [hupd]; simp [updVar, he, hgl, hmod]
    · simp [C.Sem.write, C.Sem.readBase, hcg, hsp, C.Sem.writeBase]
    · refine ⟨fun z gd' hz => ?_, fun k => ?_, hrel.2.world⟩
      · by_cases hzx : z = x
        · subst hzx
          rw [hgd] at hz
          cases hz
          refine ⟨vx', lsetFirst_lookup_self _ _ _ _ hgl, by rw [← hgty]; exact htyx',
            csetFirst_lookup_self _ _ _ _ hcg⟩
        · obtain ⟨w, hw, hwt', hwc⟩ := hrel.2.glob z gd' hz
          refine ⟨w, by rw [lsetFirst_lookup_ne _ _ _ _ hzx]; exact hw, hwt', ?_⟩
          rw [csetFirst_lookup_ne _ _ _ _ (fun e => hzx (globalName_inj e))]
          exact hwc
      · rw [csetFirst_lookup_ne _ _ _ _ (fun e => U.hyg.gt x k e.symm)]
        exact hrel.2.gtmp k

end Ember.Proof.CSim
