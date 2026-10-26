import Ember.Proof.IRRel

/-!
# Ember.Proof.IRPlace — a place and its address (plan M7.1)

`PlaceAt … e ty v A`: the place `e`, of type `ty`, has the value `v`,
which is at the address `A`; and storing another value there — changing
no byte outside it — is `Lang.Sem.update` on `e`, leaving the states
related.  For a variable this is `SRel.var`/`SRel.setVar`; for a field
and an element it follows from the same for the record and the array.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record hasTy_mask hasTy_bool_mk
  hasTy_int_mk FieldOK TyOK)

/-- `update` looks at its function on the place's value only. -/
theorem update_congr (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (e : Expr) (F F' : Val → Option Val)
    (u : Val), Lang.Sem.evalE p st env e = some u → F u = F' u →
    Lang.Sem.update p st env e F = Lang.Sem.update p st env e F'
  | .var x, F, F', u, hu, h => by
    simp only [Lang.Sem.evalE, Lang.Sem.lookup] at hu
    simp only [Lang.Sem.update]
    cases he : env.lookup x with
    | some old =>
      simp only [he, Option.some.injEq] at hu
      subst hu
      simp only [h]
    | none =>
      simp only [he] at hu
      simp only [hu, h]
  | .field b fld, F, F', u, hu, h => by
    simp only [Lang.Sem.evalE] at hu
    simp only [Lang.Sem.update]
    cases hb : Lang.Sem.evalE p st env b with
    | none => simp [hb] at hu
    | some bv =>
      cases bv with
      | record r fs =>
        simp only [hb] at hu
        refine update_congr p st env b _ _ _ hb ?_
        cases hi : Lang.Sem.fieldIndex p r fld with
        | none => simp [hi] at hu
        | some i =>
          simp only [hi] at hu
          simp only [hi, hu, h]
      | int _ _ => simp [hb] at hu
      | bool _ => simp [hb] at hu
      | arr _ => simp [hb] at hu
  | .index b i, F, F', u, hu, h => by
    simp only [Lang.Sem.evalE] at hu
    simp only [Lang.Sem.update]
    cases hb : Lang.Sem.evalE p st env b with
    | none => simp [hb] at hu
    | some bv =>
      cases hi : Lang.Sem.evalE p st env i with
      | none => simp [hb, hi] at hu
      | some iv =>
        cases bv with
        | arr xs =>
          simp only [hb, hi] at hu
          simp only [hi]
          refine update_congr p st env b _ _ _ hb ?_
          simp only [hu, h]
        | int _ _ => simp [hb, hi] at hu
        | bool _ => simp [hb, hi] at hu
        | record _ _ => simp [hb, hi] at hu
  | .lit _ _, _, _, _, _, _ => rfl
  | .blit _, _, _, _, _, _ => rfl
  | .bin _ _ _, _, _, _, _, _ => rfl
  | .un _ _, _, _, _, _, _ => rfl
  | .cast _ _, _, _, _, _, _ => rfl
  | .cond _ _ _, _, _, _, _, _ => rfl

theorem fieldOK_tyOK (p : Prog) {t : Ty} (h : FieldOK t) : TyOK p t := by
  cases t with
  | int w => trivial
  | bool => trivial
  | arr el n => exact h
  | record r => exact absurd h (by simp [FieldOK])

theorem scalar_tyOK (p : Prog) {t : Ty} (h : t.isScalar = true) : TyOK p t := by
  cases t <;> simp [Ty.isScalar] at h <;> trivial

/-- The place `e` has the value `v` at the address `A`, and can be
stored to there. -/
structure PlaceAt (c : Ctx) (E : Env) (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (e : Expr)
    (ty : Ty) (v : Val) (A : Nat) : Prop where
  tyok : TyOK E.prog ty
  hasTy : HasTy E.prog ty v
  holds : Holds E.prog ist.mem A ty v
  bound : A + sizeOf E.prog ty ≤ 65536
  upd : Writable E e → ∀ (v' : Val) (m' : ByteArray), HasTy E.prog ty v' → m'.size = 65536 →
    (∀ x, x < A ∨ A + sizeOf E.prog ty ≤ x → m'.get! x = ist.mem.get! x) → Holds E.prog m' A ty v' →
    ∃ lst' env', Lang.Sem.update E.prog lst env e (fun _ => some v') = some (lst', env') ∧
      SRel c E cur lst' env' { ist with mem := m' } ∧ Keep c E cur ist.mem m' ∧ lst'.world = lst.world

section
variable {c : Ctx} {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}

/-- A variable. -/
theorem PlaceAt.var (L : LayOK E.prog c) (h : SRel c E cur lst env ist) {x : String} {info : VarInfo} {sl : Slot}
    {v : Val} (hx : E.varInfo x = .ok info) (hat : info.at_ = .static sl)
    (hv : Lang.Sem.lookup lst env x = some v) : PlaceAt c E cur lst env ist (.var x) info.ty v (c.layout.addr sl) := by
  obtain ⟨sl', v', h1, h2, h3, h4, h5, h6⟩ := h.var L hx
  rw [hat] at h1
  simp only [Storage.static.injEq] at h1
  subst h1
  rw [hv] at h2
  cases h2
  exact ⟨h3, h4, h5, h6, fun hw v' m' hv' hsz hm hh => h.setVar L hx hat hw hv' hsz hm hh⟩

/-- A field of a record. -/
theorem PlaceAt.field {b : Expr} {r fld : String} {fs : Array Val} {Ab i : Nat} {sd : StructDef}
    (hb : PlaceAt c E cur lst env ist b (.record r) (.record r fs) Ab)
    (hev : Lang.Sem.evalE E.prog lst env b = some (.record r fs)) (hsd : E.prog.struct? r = some sd)
    (hi : sd.fields.findIdx? (·.1 == fld) = some i) (hlt : i < sd.fields.length) (hlt' : i < fs.size) :
    PlaceAt c E cur lst env ist (.field b fld) (sd.fields[i]).2 fs[i] (Ab + fldOff E.prog sd.fields i) := by
  obtain ⟨sd', hsd', hfld⟩ := hb.tyok
  rw [hsd] at hsd'
  cases hsd'
  obtain ⟨fs0, sd0, h0, hsd0, hsz, hfs⟩ := hasTy_record hb.hasTy
  cases h0
  rw [hsd] at hsd0
  cases hsd0
  have hfi : FieldOK (sd.fields[i]).2 := hfld _ (List.getElem_mem hlt)
  have hin := field_in E.prog hsd hfld i hlt
  have hbb := hb.bound
  refine ⟨fieldOK_tyOK _ hfi, (hfs i hlt' hlt).hasTy, (holds_field0 hfi).mpr (Holds.field hb.holds hsd i hlt' hlt),
    by omega, fun hw v' m' hv' hsz' hm hh => ?_⟩
  have hv0 : HasTy0 (sd.fields[i]).2 v' := by
    cases hft : (sd.fields[i]).2 with
    | record _ => rw [hft] at hfi; exact absurd hfi (by simp [FieldOK])
    | int w => rw [hft] at hv'; exact hv'
    | bool => rw [hft] at hv'; exact hv'
    | arr el n => rw [hft] at hv'; exact hv'
  have hnew : HasTy E.prog (.record r) (.record r (fs.set! i v')) := by
    refine ⟨rfl, sd, hsd, by simpa using hsz, fun j hj hj' => ?_⟩
    have hj2 : j < fs.size := by simpa using hj
    by_cases hji : j = i
    · subst hji
      simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds_self]
      exact hv0
    · have hget : (fs.set! i v')[j] = fs[j] := by
        simp only [Array.set!_eq_setIfInBounds]
        exact Array.getElem_setIfInBounds_ne (by omega) (fun h => hji h.symm)
      rw [hget]
      exact hfs j hj2 hj'
  obtain ⟨lst', env', hu, hrel, hkeep, hworld⟩ := hb.upd hw (.record r (fs.set! i v')) m' hnew hsz'
    (fun x hx => hm x (by omega))
    (Holds.set_field hb.hasTy hb.holds hsd hfld hbb i hlt' hlt v' ((holds_field0 hfi).mp hh) (fun x hx => hm x hx))
  refine ⟨lst', env', ?_, hrel, hkeep, hworld⟩
  rw [← hu]
  simp only [Lang.Sem.update]
  refine update_congr E.prog lst env b _ _ _ hev ?_
  simp only [Lang.Sem.fieldIndex, hsd, hi, Array.getElem?_eq_getElem hlt']

/-- An element of an array. -/
theorem PlaceAt.index {b i : Expr} {el : Ty} {n k : Nat} {xs : Array Val} {Ab : Nat} {iv : Val}
    (hb : PlaceAt c E cur lst env ist b (.arr el n) (.arr xs) Ab)
    (hev : Lang.Sem.evalE E.prog lst env b = some (.arr xs)) (hi : Lang.Sem.evalE E.prog lst env i = some iv)
    (hk : iv.toNat = k) (hlt : k < xs.size) :
    PlaceAt c E cur lst env ist (.index b i) el xs[k] (Ab + k * sizeOf E.prog el) := by
  have hel : el.isScalar = true := hb.tyok
  obtain ⟨xs0, h0, hsz, hxs⟩ := hasTy_arr hb.hasTy
  cases h0
  have hbb := hb.bound
  have hs : sizeOf E.prog el = sizeOf0 el := sizeOf_scalar _ hel
  simp only [IR.sizeOf] at hbb
  have hle : (k + 1) * sizeOf E.prog el ≤ n * sizeOf E.prog el := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hle
  have hholds : Holds0 ist.mem Ab (.arr el n) (.arr xs) := hb.holds
  refine ⟨scalar_tyOK _ hel, (hxs _ (Array.getElem_mem hlt)).hasTy, ?_, by omega, fun hw v' m' hv' hsz' hm hh => ?_⟩
  · rw [holds_scalar hel, hs]
    exact hholds k hlt
  · have hv0 : HasTy0 el v' := by
      cases el with
      | record _ => simp [Ty.isScalar] at hel
      | arr _ _ => simp [Ty.isScalar] at hel
      | int w => exact hv'
      | bool => exact hv'
    have hnew : HasTy E.prog (.arr el n) (.arr (xs.set! k v')) := by
      refine ⟨by simpa using hsz, fun x hx => ?_⟩
      simp only [Array.set!_eq_setIfInBounds] at hx
      rcases Array.mem_or_eq_of_mem_setIfInBounds hx with h | h
      · exact hxs x h
      · rw [h]; exact hv0
    rw [holds_scalar hel, hs] at hh
    rw [hs] at hm hbb hle
    obtain ⟨lst', env', hu, hrel, hkeep, hworld⟩ := hb.upd hw (.arr (xs.set! k v')) m' hnew hsz'
      (fun x hx => hm x (by simp only [IR.sizeOf, hs] at hx; omega))
      (Holds0.set_elem hholds hsz (by omega) k hlt v' hh (fun x hx => hm x hx))
    refine ⟨lst', env', ?_, hrel, hkeep, hworld⟩
    rw [← hu]
    simp only [Lang.Sem.update, hi]
    refine update_congr E.prog lst env b _ _ _ hev ?_
    simp only [hk, Array.getElem?_eq_getElem hlt]

end

end Ember.Proof.IRSim
