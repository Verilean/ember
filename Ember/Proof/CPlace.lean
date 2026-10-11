import Ember.Proof.CTypes

/-!
# Ember.Proof.CPlace — places as a variable and a path (plan M5.8)

`Lang.Sem` reads a place with `evalE` and writes it with `update`, both
by recursion on the expression.  The C semantics has locations: a
variable and a path of indices.  Here the Ember side is put in that
form: `lpath` is the variable and the path of a place, `vget` reads a
path of a value, `vmod` changes it, and

* `evalE_lpath`: the value of a place is `vget` of its variable;
* `update_lpath`: `update` changes the variable with `vmod`;
* `setPath_cval`: `vmod` on a value is `setPath` on its C value.
-/

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C

/-- Variables, fields and elements. -/
def IsPlace : Expr → Prop
  | .var _ => True
  | .field b _ => IsPlace b
  | .index b _ => IsPlace b
  | _ => False

/-- The variable a place is rooted at, and the path into it. -/
def lpath (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : Expr → Option (String × List Nat)
  | .var x => some (x, [])
  | .field b f =>
    match lpath p st env b, Lang.Sem.evalE p st env b with
    | some (x, q), some (.record r _) =>
      match Lang.Sem.fieldIndex p r f with
      | some i => some (x, q ++ [i])
      | none => none
    | _, _ => none
  | .index b i =>
    match lpath p st env b, Lang.Sem.evalE p st env i with
    | some (x, q), some iv => some (x, q ++ [iv.toNat])
    | _, _ => none
  | _ => none

def vget : Val → List Nat → Option Val
  | v, [] => some v
  | .arr xs, i :: r =>
    match xs[i]? with
    | some x => vget x r
    | none => none
  | .record _ fs, i :: r =>
    match fs[i]? with
    | some x => vget x r
    | none => none
  | _, _ :: _ => none

/-- Change the value at a path. -/
def vmod : Val → List Nat → (Val → Option Val) → Option Val
  | v, [], f => f v
  | .arr xs, i :: r, f =>
    match xs[i]? with
    | some old =>
      match vmod old r f with
      | some new => some (.arr (xs.set! i new))
      | none => none
    | none => none
  | .record n fs, i :: r, f =>
    match fs[i]? with
    | some old =>
      match vmod old r f with
      | some new => some (.record n (fs.set! i new))
      | none => none
    | none => none
  | _, _ :: _, _ => none

/-- Change a variable: the innermost local of that name, or the global. -/
def updVar (st : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) (F : Val → Option Val) :
    Option (Lang.Sem.St × Lang.Sem.Env) :=
  match env.lookup x with
  | some old =>
    match F old with
    | some v => some (st, Lang.Sem.setFirst env x v)
    | none => none
  | none =>
    match st.globals.lookup x with
    | some old =>
      match F old with
      | some v => some ({ st with globals := Lang.Sem.setFirst st.globals x v }, env)
      | none => none
    | none => none

theorem vget_append (v : Val) (p q : List Nat) : vget v (p ++ q) = (vget v p).bind (vget · q) := by
  induction p generalizing v with
  | nil => rfl
  | cons i r ih =>
    cases v with
    | arr xs =>
      simp only [List.cons_append, vget]
      cases xs[i]? with
      | none => rfl
      | some x => exact ih x
    | record n fs =>
      simp only [List.cons_append, vget]
      cases fs[i]? with
      | none => rfl
      | some x => exact ih x
    | int _ _ => rfl
    | bool _ => rfl

theorem vmod_append (v : Val) (p q : List Nat) (f : Val → Option Val) :
    vmod v (p ++ q) f = vmod v p (fun u => vmod u q f) := by
  induction p generalizing v with
  | nil => rfl
  | cons i r ih =>
    cases v with
    | arr xs =>
      simp only [List.cons_append, vmod]
      cases xs[i]? with
      | none => rfl
      | some x => simp only [ih x]
    | record n fs =>
      simp only [List.cons_append, vmod]
      cases fs[i]? with
      | none => rfl
      | some x => simp only [ih x]
    | int _ _ => rfl
    | bool _ => rfl

theorem vmod_congr (v : Val) (p : List Nat) (F F' : Val → Option Val) (u : Val) (hu : vget v p = some u)
    (h : F u = F' u) : vmod v p F = vmod v p F' := by
  induction p generalizing v with
  | nil =>
    simp only [vget, Option.some.injEq] at hu
    subst hu
    exact h
  | cons i r ih =>
    cases v with
    | arr xs =>
      simp only [vget, vmod] at hu ⊢
      cases hx : xs[i]? with
      | none => rfl
      | some x => rw [hx] at hu; simp only [ih x hu]
    | record n fs =>
      simp only [vget, vmod] at hu ⊢
      cases hx : fs[i]? with
      | none => rfl
      | some x => rw [hx] at hu; simp only [ih x hu]
    | int _ _ => simp [vget] at hu
    | bool _ => simp [vget] at hu

theorem vmod_some (v : Val) (p : List Nat) (F : Val → Option Val) (u u' : Val) (hu : vget v p = some u)
    (h : F u = some u') : ∃ v', vmod v p F = some v' := by
  induction p generalizing v with
  | nil =>
    simp only [vget, Option.some.injEq] at hu
    subst hu
    exact ⟨u', h⟩
  | cons i r ih =>
    cases v with
    | arr xs =>
      simp only [vget, vmod] at hu ⊢
      cases hx : xs[i]? with
      | none => simp [hx] at hu
      | some x =>
        rw [hx] at hu
        obtain ⟨v', hv'⟩ := ih x hu
        simp only [hv']
        exact ⟨_, rfl⟩
    | record n fs =>
      simp only [vget, vmod] at hu ⊢
      cases hx : fs[i]? with
      | none => simp [hx] at hu
      | some x =>
        rw [hx] at hu
        obtain ⟨v', hv'⟩ := ih x hu
        simp only [hv']
        exact ⟨_, rfl⟩
    | int _ _ => simp [vget] at hu
    | bool _ => simp [vget] at hu

theorem updVar_congr (st : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) (F F' : Val → Option Val)
    (h : ∀ vx, Lang.Sem.lookup st env x = some vx → F vx = F' vx) : updVar st env x F = updVar st env x F' := by
  unfold updVar
  cases he : env.lookup x with
  | some old =>
    have := h old (by simp [Lang.Sem.lookup, he])
    simp only [this]
  | none =>
    cases hg : st.globals.lookup x with
    | none => rfl
    | some old =>
      have := h old (by simp [Lang.Sem.lookup, he, hg])
      simp only [this]

/-- The value of a place is read off its variable. -/
theorem evalE_lpath (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (v : Val) (x : String)
    (q : List Nat), Lang.Sem.evalE p st env e = some v → lpath p st env e = some (x, q) →
    ∃ vx, Lang.Sem.lookup st env x = some vx ∧ vget vx q = some v
  | .var y, v, x, q, hv, hl => by
    simp only [lpath, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨v, by simpa [Lang.Sem.evalE] using hv, rfl⟩
  | .field b f, v, x, q, hv, hl => by
    simp only [lpath] at hl
    simp only [Lang.Sem.evalE] at hv
    cases hb : lpath p st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      cases hbv : Lang.Sem.evalE p st env b with
      | none => simp [hb, hbv] at hl
      | some bv =>
        cases bv with
        | record r fs =>
          simp only [hb, hbv] at hl hv
          cases hi : Lang.Sem.fieldIndex p r f with
          | none => simp [hi] at hl
          | some i =>
            simp only [hi, Option.some.injEq, Prod.mk.injEq] at hl hv
            obtain ⟨rfl, rfl⟩ := hl
            obtain ⟨vx, hx, hg⟩ := evalE_lpath p st env b _ _ _ hbv hb
            refine ⟨vx, hx, ?_⟩
            rw [vget_append, hg]
            simp only [Option.bind_some, vget, hv]
        | int _ _ => simp [hb, hbv] at hl
        | bool _ => simp [hb, hbv] at hl
        | arr _ => simp [hb, hbv] at hl
  | .index b i, v, x, q, hv, hl => by
    simp only [lpath] at hl
    simp only [Lang.Sem.evalE] at hv
    cases hb : lpath p st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      cases hiv : Lang.Sem.evalE p st env i with
      | none => simp [hb, hiv] at hl
      | some iv =>
        simp only [hb, hiv, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        cases hbv : Lang.Sem.evalE p st env b with
        | none => simp [hbv] at hv
        | some bv =>
          cases bv with
          | arr xs =>
            simp only [hbv, hiv] at hv
            obtain ⟨vx, hx, hg⟩ := evalE_lpath p st env b _ _ _ hbv hb
            refine ⟨vx, hx, ?_⟩
            rw [vget_append, hg]
            simp only [Option.bind_some, vget, hv]
          | int _ _ => simp [hbv, hiv] at hv
          | bool _ => simp [hbv, hiv] at hv
          | record _ _ => simp [hbv, hiv] at hv
  | .lit _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .blit _, _, _, _, _, hl => by simp [lpath] at hl
  | .bin _ _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .un _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .cast _ _, _, _, _, _, hl => by simp [lpath] at hl
  | .cond _ _ _, _, _, _, _, hl => by simp [lpath] at hl

/-- A place that has a value has a path. -/
theorem lpath_some (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (v : Val), IsPlace e →
    Lang.Sem.evalE p st env e = some v → ∃ x q, lpath p st env e = some (x, q)
  | .var y, v, _, _ => ⟨y, [], rfl⟩
  | .field b f, v, hp, hv => by
    simp only [Lang.Sem.evalE] at hv
    cases hbv : Lang.Sem.evalE p st env b with
    | none => simp [hbv] at hv
    | some bv =>
      cases bv with
      | record r fs =>
        simp only [hbv] at hv
        cases hi : Lang.Sem.fieldIndex p r f with
        | none => simp [hi] at hv
        | some i =>
          obtain ⟨x, q, hl⟩ := lpath_some p st env b _ hp hbv
          exact ⟨x, q ++ [i], by simp [lpath, hl, hbv, hi]⟩
      | int _ _ => simp [hbv] at hv
      | bool _ => simp [hbv] at hv
      | arr _ => simp [hbv] at hv
  | .index b i, v, hp, hv => by
    simp only [Lang.Sem.evalE] at hv
    cases hbv : Lang.Sem.evalE p st env b with
    | none => simp [hbv] at hv
    | some bv =>
      cases hiv : Lang.Sem.evalE p st env i with
      | none => cases bv <;> simp [hbv, hiv] at hv
      | some iv =>
        obtain ⟨x, q, hl⟩ := lpath_some p st env b _ hp hbv
        exact ⟨x, q ++ [iv.toNat], by simp [lpath, hl, hiv]⟩
  | .lit _ _, _, hp, _ => hp.elim
  | .blit _, _, hp, _ => hp.elim
  | .bin _ _ _, _, hp, _ => hp.elim
  | .un _ _, _, hp, _ => hp.elim
  | .cast _ _, _, hp, _ => hp.elim
  | .cond _ _ _, _, hp, _ => hp.elim

/-- `update` succeeds only on a place that has a value, on which `f` succeeds. -/
theorem update_some (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (f : Val → Option Val)
    (r : Lang.Sem.St × Lang.Sem.Env), Lang.Sem.update p st env e f = some r →
    ∃ u, Lang.Sem.evalE p st env e = some u ∧ (f u).isSome = true
  | .var y, f, r, h => by
    simp only [Lang.Sem.update] at h
    simp only [Lang.Sem.evalE, Lang.Sem.lookup]
    cases he : env.lookup y with
    | some old =>
      simp only [he] at h ⊢
      cases hf : f old with
      | none => simp [hf] at h
      | some v => exact ⟨old, rfl, by simp [hf]⟩
    | none =>
      simp only [he] at h ⊢
      cases hg : st.globals.lookup y with
      | none => simp [hg] at h
      | some old =>
        simp only [hg] at h
        cases hf : f old with
        | none => simp [hf] at h
        | some v => exact ⟨old, rfl, by simp [hf]⟩
  | .field b fld, f, r, h => by
    simp only [Lang.Sem.update] at h
    obtain ⟨u, hu, hs⟩ := update_some p st env b _ r h
    cases u with
    | record rn fs =>
      simp only at hs
      cases hi : Lang.Sem.fieldIndex p rn fld with
      | none => simp [hi] at hs
      | some i =>
        simp only [hi] at hs
        cases ho : fs[i]? with
        | none => simp [ho] at hs
        | some old =>
          simp only [ho] at hs
          refine ⟨old, by simp [Lang.Sem.evalE, hu, hi, ho], ?_⟩
          cases hf : f old with
          | none => simp [hf] at hs
          | some v => rfl
    | int _ _ => simp at hs
    | bool _ => simp at hs
    | arr _ => simp at hs
  | .index b i, f, r, h => by
    simp only [Lang.Sem.update] at h
    cases hiv : Lang.Sem.evalE p st env i with
    | none => simp [hiv] at h
    | some iv =>
      simp only [hiv] at h
      obtain ⟨u, hu, hs⟩ := update_some p st env b _ r h
      cases u with
      | arr xs =>
        simp only at hs
        cases ho : xs[iv.toNat]? with
        | none => simp [ho] at hs
        | some old =>
          simp only [ho] at hs
          refine ⟨old, by simp [Lang.Sem.evalE, hu, hiv, ho], ?_⟩
          cases hf : f old with
          | none => simp [hf] at hs
          | some v => rfl
      | int _ _ => simp at hs
      | bool _ => simp at hs
      | record _ _ => simp at hs
  | .lit _ _, _, _, h => by simp [Lang.Sem.update] at h
  | .blit _, _, _, h => by simp [Lang.Sem.update] at h
  | .bin _ _ _, _, _, h => by simp [Lang.Sem.update] at h
  | .un _ _, _, _, h => by simp [Lang.Sem.update] at h
  | .cast _ _, _, _, h => by simp [Lang.Sem.update] at h
  | .cond _ _ _, _, _, h => by simp [Lang.Sem.update] at h

/-- `update` on a place that has a value changes its variable along its path. -/
theorem update_lpath (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (f : Val → Option Val)
    (v : Val) (x : String) (q : List Nat), Lang.Sem.evalE p st env e = some v → lpath p st env e = some (x, q) →
    Lang.Sem.update p st env e f = updVar st env x (fun vx => vmod vx q f)
  | .var y, f, v, x, q, _, hl => by
    simp only [lpath, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp only [Lang.Sem.update, updVar, vmod]
    cases env.lookup y <;> (try cases st.globals.lookup y) <;> rfl
  | .field b fld, f, v, x, q, hv, hl => by
    simp only [lpath] at hl
    simp only [Lang.Sem.evalE] at hv
    cases hb : lpath p st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      cases hbv : Lang.Sem.evalE p st env b with
      | none => simp [hb, hbv] at hl
      | some bv =>
        cases bv with
        | record r fs =>
          simp only [hb, hbv] at hl hv
          cases hi : Lang.Sem.fieldIndex p r fld with
          | none => simp [hi] at hl
          | some i =>
            simp only [hi, Option.some.injEq, Prod.mk.injEq] at hl hv
            obtain ⟨rfl, rfl⟩ := hl
            simp only [Lang.Sem.update]
            rw [update_lpath p st env b _ _ _ _ hbv hb]
            apply updVar_congr
            intro vx hx
            obtain ⟨vx', hx', hg⟩ := evalE_lpath p st env b _ _ _ hbv hb
            rw [hx] at hx'
            cases hx'
            rw [vmod_append]
            apply vmod_congr _ _ _ _ _ hg
            simp only [hi, hv, vmod]
            cases f v <;> rfl
        | int _ _ => simp [hb, hbv] at hl
        | bool _ => simp [hb, hbv] at hl
        | arr _ => simp [hb, hbv] at hl
  | .index b i, f, v, x, q, hv, hl => by
    simp only [lpath] at hl
    simp only [Lang.Sem.evalE] at hv
    cases hb : lpath p st env b with
    | none => simp [hb] at hl
    | some xq =>
      obtain ⟨x0, q0⟩ := xq
      cases hiv : Lang.Sem.evalE p st env i with
      | none => simp [hb, hiv] at hl
      | some iv =>
        simp only [hb, hiv, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        cases hbv : Lang.Sem.evalE p st env b with
        | none => simp [hbv] at hv
        | some bv =>
          cases bv with
          | arr xs =>
            simp only [hbv, hiv] at hv
            simp only [Lang.Sem.update, hiv]
            rw [update_lpath p st env b _ _ _ _ hbv hb]
            apply updVar_congr
            intro vx hx
            obtain ⟨vx', hx', hg⟩ := evalE_lpath p st env b _ _ _ hbv hb
            rw [hx] at hx'
            cases hx'
            rw [vmod_append]
            apply vmod_congr _ _ _ _ _ hg
            simp only [hv, vmod]
            cases f v <;> rfl
          | int _ _ => simp [hbv, hiv] at hv
          | bool _ => simp [hbv, hiv] at hv
          | record _ _ => simp [hbv, hiv] at hv
  | .lit _ _, _, _, _, _, _, hl => by simp [lpath] at hl
  | .blit _, _, _, _, _, _, hl => by simp [lpath] at hl
  | .bin _ _ _, _, _, _, _, _, hl => by simp [lpath] at hl
  | .un _ _, _, _, _, _, _, hl => by simp [lpath] at hl
  | .cast _ _, _, _, _, _, _, hl => by simp [lpath] at hl
  | .cond _ _ _, _, _, _, _, _, hl => by simp [lpath] at hl

/-- Changing a value along a path is `setPath` on its C value. -/
theorem setPath_cval (o : Opts) (u : Val) : ∀ (q : List Nat) (v v' : Val),
    vmod v q (fun _ => some u) = some v' → C.Sem.setPath (cval o v) q (cval o u) = some (cval o v')
  | [], v, v', h => by
    simp only [vmod, Option.some.injEq] at h
    subst h
    rfl
  | i :: r, v, v', h => by
    cases v with
    | arr xs =>
      simp only [vmod] at h
      cases hx : xs[i]? with
      | none => simp [hx] at h
      | some old =>
        simp only [hx] at h
        cases hm : vmod old r (fun _ => some u) with
        | none => simp [hm] at h
        | some new =>
          simp only [hm, Option.some.injEq] at h
          subst h
          have ih := setPath_cval o u r old new hm
          simp only [cval_arr, C.Sem.setPath, Array.getElem?_map, hx, Option.map_some, ih]
          congr 2
          simp [Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]
    | record n fs =>
      simp only [vmod] at h
      cases hx : fs[i]? with
      | none => simp [hx] at h
      | some old =>
        simp only [hx] at h
        cases hm : vmod old r (fun _ => some u) with
        | none => simp [hm] at h
        | some new =>
          simp only [hm, Option.some.injEq] at h
          subst h
          have ih := setPath_cval o u r old new hm
          simp only [cval_record, C.Sem.setPath, Array.getElem?_map, hx, Option.map_some, ih]
          congr 2
          simp [Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]
    | int _ _ => simp [vmod] at h
    | bool _ => simp [vmod] at h

end Ember.Proof.CSim
