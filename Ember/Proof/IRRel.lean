import Ember.Proof.IRTypes
import Ember.Proof.Z80Frame

/-!
# Ember.Proof.IRRel — Ember's values in the IR's memory (plan M7.1)

* `Holds`: a value of a type is at an address — scalars little-endian,
  array elements and record fields one after the other;
* `GRel`, `LRel`, `SRel`: the globals and the variables in scope are
  where the lowering's environment says, each holding its value;
* `Keep`: what a statement leaves alone — everything that is neither a
  global, nor a variable in scope, nor in the frame of a function that
  can be called from here.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record hasTy_mask hasTy_bool_mk
  hasTy_int_mk FieldOK TyOK lsetFirst_lookup_self lsetFirst_lookup_ne lsetFirst_length)

/-! ## Sizes -/

theorem sizeOf_scalar (p : Prog) {t : Ty} (h : t.isScalar = true) : sizeOf p t = sizeOf0 t := by
  cases t <;> simp [Ty.isScalar] at h <;> rfl

theorem sizeOf_field (p : Prog) {t : Ty} (h : FieldOK t) : sizeOf p t = sizeOf0 t := by
  cases t with
  | int w => rfl
  | bool => rfl
  | arr el n => simp only [IR.sizeOf, sizeOf0, sizeOf_scalar p h]
  | record r => exact absurd h (by simp [FieldOK])

theorem fldOff_succ (p : Prog) : ∀ (fs : List (String × Ty)) (i : Nat) (h : i < fs.length),
    fldOff p fs (i + 1) = fldOff p fs i + sizeOf p (fs[i]).2
  | [], i, h => by simp at h
  | (_, t) :: rest, 0, _ => by cases rest <;> simp [fldOff]
  | (_, t) :: rest, i + 1, h => by
    simp only [fldOff, List.getElem_cons_succ]
    rw [fldOff_succ p rest i (by simpa using h)]
    omega

theorem fldOff_mono (p : Prog) (fs : List (String × Ty)) {i j : Nat} (h : i ≤ j) (hj : j ≤ fs.length) :
    fldOff p fs i ≤ fldOff p fs j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hle ih =>
    rename_i k
    rw [fldOff_succ p fs k (by omega)]
    have := ih (by omega)
    omega

theorem foldl_sizes (p : Prog) : ∀ (fs : List (String × Ty)) (o : Nat), (∀ ft, ft ∈ fs → FieldOK ft.2) →
    fs.foldl (fun acc (x : String × Ty) => acc + sizeOf0 x.2) o = o + fldOff p fs fs.length
  | [], o, _ => by simp [fldOff]
  | (x, t) :: rest, o, h => by
    simp only [List.foldl_cons, List.length_cons, fldOff]
    rw [foldl_sizes p rest _ (fun ft hft => h ft (List.mem_cons_of_mem _ hft)),
      sizeOf_field p (h (x, t) List.mem_cons_self)]
    dsimp only
    omega

/-- A record is its fields, one after the other. -/
theorem sizeOf_record (p : Prog) {r : String} {sd : StructDef} (hsd : p.struct? r = some sd)
    (hf : ∀ ft, ft ∈ sd.fields → FieldOK ft.2) : sizeOf p (.record r) = fldOff p sd.fields sd.fields.length := by
  have := foldl_sizes p sd.fields 0 hf
  simp only [IR.sizeOf, hsd, Option.map_some, Option.getD_some]
  rw [Nat.zero_add] at this
  exact this

/-- A field lies inside its record. -/
theorem field_in (p : Prog) {r : String} {sd : StructDef} (hsd : p.struct? r = some sd)
    (hf : ∀ ft, ft ∈ sd.fields → FieldOK ft.2) (i : Nat) (h : i < sd.fields.length) :
    fldOff p sd.fields i + sizeOf p (sd.fields[i]).2 ≤ sizeOf p (.record r) := by
  rw [sizeOf_record p hsd hf, ← fldOff_succ p sd.fields i h]
  exact fldOff_mono p sd.fields (by omega) (Nat.le_refl _)

/-- Two fields share no byte. -/
theorem field_apart (p : Prog) (fs : List (String × Ty)) {i j : Nat} (hij : i < j) (hj : j < fs.length) :
    fldOff p fs i + sizeOf p (fs[i]'(by omega)).2 ≤ fldOff p fs j := by
  rw [← fldOff_succ p fs i (by omega)]
  exact fldOff_mono p fs (by omega) (by omega)

/-! ## A value at an address -/

/-- A scalar or an array of scalars at `a`. -/
def Holds0 (m : ByteArray) (a : Nat) : Ty → Val → Prop
  | .arr el _, .arr xs => ∀ i (h : i < xs.size), rd m (a + i * sizeOf0 el) (sizeOf0 el) = xs[i].toNat
  | .arr _ _, _ => False
  | .record _, _ => False
  | t, v => rd m a (sizeOf0 t) = v.toNat

/-- A value at `a`. -/
def Holds (p : Prog) (m : ByteArray) (a : Nat) : Ty → Val → Prop
  | .record r, .record _ fs => ∃ sd, p.struct? r = some sd ∧
      ∀ i (h : i < fs.size) (h' : i < sd.fields.length),
        Holds0 m (a + fldOff p sd.fields i) (sd.fields[i]).2 fs[i]
  | .record _, _ => False
  | t, v => Holds0 m a t v

theorem holds_scalar {p : Prog} {m : ByteArray} {a : Nat} {t : Ty} {v : Val} (ht : t.isScalar = true) :
    Holds p m a t v ↔ rd m a (sizeOf p t) = v.toNat := by
  cases t <;> simp [Ty.isScalar] at ht <;> simp [Holds, Holds0, IR.sizeOf, sizeOf0]

theorem Holds0.frame {m m' : ByteArray} {a : Nat} {t : Ty} {v : Val} (ht : FieldOK t) (hv : HasTy0 t v)
    (hb : a + sizeOf0 t ≤ 65536) (h : Holds0 m a t v)
    (hm : ∀ x, a ≤ x → x < a + sizeOf0 t → m'.get! x = m.get! x) : Holds0 m' a t v := by
  cases t with
  | int w =>
    simp only [Holds0] at h ⊢
    rw [rd_congr m m' a _ hb hm]
    exact h
  | bool =>
    simp only [Holds0] at h ⊢
    rw [rd_congr m m' a _ hb hm]
    exact h
  | record r => exact absurd ht (by simp [FieldOK])
  | arr el n =>
    cases v with
    | arr xs =>
      obtain ⟨hsz, _⟩ := hv
      simp only [Holds0] at h ⊢
      intro i hi
      have hle : (i + 1) * sizeOf0 el ≤ n * sizeOf0 el := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hle
      simp only [sizeOf0] at hb hm
      rw [rd_congr m m' _ _ (by omega) (fun x h1 h2 => hm x (by omega) (by omega))]
      exact h i hi
    | int _ _ => exact absurd hv (by simp [HasTy0])
    | bool _ => exact absurd hv (by simp [HasTy0])
    | record _ _ => exact absurd hv (by simp [HasTy0])

theorem holds_field0 {p : Prog} {m : ByteArray} {a : Nat} {t : Ty} {v : Val} (ht : FieldOK t) :
    Holds p m a t v ↔ Holds0 m a t v := by
  cases t with
  | record r => exact absurd ht (by simp [FieldOK])
  | int w => rfl
  | bool => rfl
  | arr el n => rfl

/-- A value depends on its bytes only. -/
theorem Holds.frame {p : Prog} {m m' : ByteArray} {a : Nat} {t : Ty} {v : Val} (ht : TyOK p t) (hv : HasTy p t v)
    (hb : a + sizeOf p t ≤ 65536) (h : Holds p m a t v)
    (hm : ∀ x, a ≤ x → x < a + sizeOf p t → m'.get! x = m.get! x) : Holds p m' a t v := by
  cases t with
  | int w => exact Holds0.frame (t := .int w) trivial hv hb h hm
  | bool => exact Holds0.frame (t := .bool) trivial hv hb h hm
  | arr el n =>
    have hf : FieldOK (.arr el n) := ht
    rw [sizeOf_field p hf] at hb hm
    exact Holds0.frame hf hv hb h hm
  | record r =>
    obtain ⟨fs, sd, rfl, hsd, hsz, hfs⟩ := hasTy_record hv
    obtain ⟨sd', hsd', hfld⟩ := ht
    rw [hsd] at hsd'
    cases hsd'
    obtain ⟨sd2, hsd2, hh⟩ := h
    rw [hsd] at hsd2
    cases hsd2
    refine ⟨sd, hsd, fun i hi hi' => ?_⟩
    have hin := field_in p hsd hfld i hi'
    have hfi : FieldOK (sd.fields[i]).2 := hfld _ (List.getElem_mem hi')
    rw [sizeOf_field p hfi] at hin
    exact Holds0.frame hfi (hfs i hi hi') (by omega) (hh i hi hi') (fun x h1 h2 => hm x (by omega) (by omega))

/-- The field of a record that is at `a`. -/
theorem Holds.field {p : Prog} {m : ByteArray} {a : Nat} {r : String} {fs : Array Val} {sd : StructDef}
    (h : Holds p m a (.record r) (.record r fs)) (hsd : p.struct? r = some sd) (i : Nat) (hi : i < fs.size)
    (hi' : i < sd.fields.length) : Holds0 m (a + fldOff p sd.fields i) (sd.fields[i]).2 fs[i] := by
  obtain ⟨sd2, hsd2, hh⟩ := h
  rw [hsd] at hsd2
  cases hsd2
  exact hh i hi hi'

/-- A record with one field changed. -/
theorem Holds.set_field {p : Prog} {m m' : ByteArray} {a : Nat} {r : String} {fs : Array Val} {sd : StructDef}
    (hv : HasTy p (.record r) (.record r fs)) (h : Holds p m a (.record r) (.record r fs))
    (hsd : p.struct? r = some sd) (hfld : ∀ ft, ft ∈ sd.fields → FieldOK ft.2)
    (hb : a + sizeOf p (.record r) ≤ 65536) (i : Nat) (hi : i < fs.size) (hi' : i < sd.fields.length) (v' : Val)
    (hnew : Holds0 m' (a + fldOff p sd.fields i) (sd.fields[i]).2 v')
    (hm : ∀ x, x < a + fldOff p sd.fields i ∨ a + fldOff p sd.fields i + sizeOf p (sd.fields[i]).2 ≤ x →
      m'.get! x = m.get! x) :
    Holds p m' a (.record r) (.record r (fs.set! i v')) := by
  obtain ⟨fs0, sd0, h0, hsd0, hsz, hfs⟩ := hasTy_record hv
  cases h0
  rw [hsd] at hsd0
  cases hsd0
  refine ⟨sd, hsd, fun j hj hj' => ?_⟩
  have hj2 : j < fs.size := by simpa using hj
  by_cases hji : j = i
  · subst hji
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds_self]
    exact hnew
  · have hget : (fs.set! i v')[j] = fs[j] := by
      simp only [Array.set!_eq_setIfInBounds]
      exact Array.getElem_setIfInBounds_ne (by omega) (fun h => hji h.symm)
    rw [hget]
    have hfj : FieldOK (sd.fields[j]).2 := hfld _ (List.getElem_mem hj')
    have hin := field_in p hsd hfld j hj'
    rw [sizeOf_field p hfj] at hin
    refine Holds0.frame hfj (hfs j hj2 hj') (by omega) (Holds.field h hsd j hj2 hj') (fun x h1 h2 => hm x ?_)
    rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
    · have := field_apart p sd.fields hlt hi'
      rw [sizeOf_field p hfj] at this
      omega
    · have := field_apart p sd.fields hgt hj'
      omega

/-- An array with one element changed. -/
theorem Holds0.set_elem {m m' : ByteArray} {a : Nat} {el : Ty} {n : Nat} {xs : Array Val}
    (h : Holds0 m a (.arr el n) (.arr xs)) (hsz : xs.size = n) (hb : a + n * sizeOf0 el ≤ 65536)
    (i : Nat) (hi : i < xs.size) (v' : Val)
    (hnew : rd m' (a + i * sizeOf0 el) (sizeOf0 el) = v'.toNat)
    (hm : ∀ x, x < a + i * sizeOf0 el ∨ a + i * sizeOf0 el + sizeOf0 el ≤ x → m'.get! x = m.get! x) :
    Holds0 m' a (.arr el n) (.arr (xs.set! i v')) := by
  simp only [Holds0] at h ⊢
  intro j hj
  have hj2 : j < xs.size := by simpa using hj
  by_cases hji : j = i
  · subst hji
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds_self]
    exact hnew
  · have hget : (xs.set! i v')[j] = xs[j] := by
      simp only [Array.set!_eq_setIfInBounds]
      exact Array.getElem_setIfInBounds_ne (by omega) (fun h => hji h.symm)
    rw [hget, ← h j hj2]
    have hle : (j + 1) * sizeOf0 el ≤ n * sizeOf0 el := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    refine rd_congr m m' _ _ (by omega) (fun x h1 h2 => hm x ?_)
    rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
    · have : (j + 1) * sizeOf0 el ≤ i * sizeOf0 el := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · have : (i + 1) * sizeOf0 el ≤ j * sizeOf0 el := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega

/-! ## Lists of bindings -/

theorem lookup_none_of_not_mem {α : Type} : ∀ (l : List (String × α)) (x : String), x ∉ l.map (·.1) →
    l.lookup x = none
  | [], _, _ => rfl
  | (y, v) :: t, x, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (x == y) = false := by simpa using h.1
    simp only [List.lookup, hne]
    exact lookup_none_of_not_mem t x h.2

theorem lookup_mem {α : Type} : ∀ (l : List (String × α)) (x : String) (v : α), l.lookup x = some v → (x, v) ∈ l
  | [], _, _, h => by simp at h
  | (y, w) :: t, x, v, h => by
    cases hxy : x == y with
    | true =>
      simp only [List.lookup, hxy, Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at hxy
      subst hxy
      exact List.mem_cons_self
    | false =>
      simp only [List.lookup, hxy] at h
      exact List.mem_cons_of_mem _ (lookup_mem t x v h)

theorem eq_of_name : ∀ {l : List Global}, (l.map (·.name)).Nodup → ∀ {a b : Global}, a ∈ l → b ∈ l →
    a.name = b.name → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: t, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd hab.symm (hn.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd hab (hn.1 a ha')
      · exact eq_of_name hn.2 ha' hb' hab

theorem global?_mem {lp : Prog} {x : String} {g : Global} (h : lp.global? x = some g) :
    g ∈ lp.globals ∧ g.name = x := by
  unfold Prog.global? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-! ## Where things are -/

def gaddr (c : Ctx) (x : String) : Nat := c.layout.addr { area := .global x }

def fbase (c : Ctx) (fn : String) : Nat := c.layout.addr { area := .frame fn }

theorem addr_frame (c : Ctx) (fn : String) (off : Nat) :
    c.layout.addr { area := .frame fn, off } = fbase c fn + off := by
  simp [Layout.addr, fbase]

def InGlobals (lp : Prog) (c : Ctx) (A : Nat) : Prop :=
  ∃ g, g ∈ lp.globals ∧ gaddr c g.name ≤ A ∧ A < gaddr c g.name + sizeOf lp g.ty

def InFrame (c : Ctx) (fn : String) (A : Nat) : Prop :=
  ∃ f, c.prog.fn? fn = some f ∧ fbase c fn ≤ A ∧ A < fbase c fn + f.frame

/-- What the proofs need of a layout (`Ember.Proof.Z80Frame` gives it for
one `IR.validate` accepts). -/
structure LayOK (lp : Prog) (c : Ctx) : Prop where
  names : (lp.globals.map (·.name)).Nodup
  gbound : ∀ g, g ∈ lp.globals → gaddr c g.name + sizeOf lp g.ty ≤ 65536
  gapart : ∀ g h, g ∈ lp.globals → h ∈ lp.globals → g.name ≠ h.name →
    gaddr c g.name + sizeOf lp g.ty ≤ gaddr c h.name ∨ gaddr c h.name + sizeOf lp h.ty ≤ gaddr c g.name
  /-- A `bool` starts as 0 or 1. -/
  ginit : ∀ g, g ∈ lp.globals → g.ty = .bool → ∀ v, v ∈ g.init → v ≤ 1
  fbound : ∀ fn f, c.prog.fn? fn = some f → fbase c fn + f.frame ≤ 65536
  fglob : ∀ fn A, InFrame c fn A → ¬ InGlobals lp c A
  fapart : ∀ fn g A, IR.Reach c.prog fn g → InFrame c fn A → ¬ InFrame c g A

/-- Neither a global, nor in the frame of `fn` or of a function it can reach. -/
def Outside (lp : Prog) (c : Ctx) (fn : String) (A : Nat) : Prop :=
  ¬ InGlobals lp c A ∧ ¬ InFrame c fn A ∧ ∀ g, IR.Reach c.prog fn g → ¬ InFrame c g A

/-! ## The globals -/

/-- Every global is at its address with its value; a constant has its initial value. -/
structure GRel (lp : Prog) (c : Ctx) (m : ByteArray) (gs : Lang.Sem.Env) : Prop where
  names : gs.map (·.1) = lp.globals.map (·.name)
  vals : ∀ g, g ∈ lp.globals → ∃ v, gs.lookup g.name = some v ∧ TyOK lp g.ty ∧ HasTy lp g.ty v ∧
    Holds lp m (gaddr c g.name) g.ty v ∧ (g.const = true → v = initOf lp g)

section
variable {lp : Prog} {c : Ctx} {m m' : ByteArray} {gs : Lang.Sem.Env}

theorem GRel.lookup (h : GRel lp c m gs) {x : String} {g : Global} (hg : lp.global? x = some g) :
    ∃ v, gs.lookup x = some v ∧ TyOK lp g.ty ∧ HasTy lp g.ty v ∧ Holds lp m (gaddr c x) g.ty v ∧
      (g.const = true → v = initOf lp g) := by
  obtain ⟨hm, rfl⟩ := global?_mem hg
  exact h.vals g hm

theorem GRel.lookup_none (h : GRel lp c m gs) {x : String} (hg : lp.global? x = none) : gs.lookup x = none := by
  apply lookup_none_of_not_mem
  rw [h.names]
  intro hmem
  obtain ⟨g, hg1, hg2⟩ := List.mem_map.mp hmem
  unfold Prog.global? at hg
  have := List.find?_eq_none.mp hg g hg1
  simp [hg2] at this

theorem GRel.frame (L : LayOK lp c) (h : GRel lp c m gs) (hm : ∀ A, InGlobals lp c A → m'.get! A = m.get! A) :
    GRel lp c m' gs :=
  ⟨h.names, fun g hg => by
    obtain ⟨v, h1, h2, h3, h4, h5⟩ := h.vals g hg
    exact ⟨v, h1, h2, h3, Holds.frame h2 h3 (L.gbound g hg) h4 (fun A ha hb => hm A ⟨g, hg, ha, hb⟩), h5⟩⟩

theorem GRel.set (L : LayOK lp c) (h : GRel lp c m gs) {g : Global} (hg : g ∈ lp.globals) (hc : g.const = false)
    {v' : Val} (hv' : HasTy lp g.ty v') (hh : Holds lp m' (gaddr c g.name) g.ty v')
    (hm : ∀ A, A < gaddr c g.name ∨ gaddr c g.name + sizeOf lp g.ty ≤ A → m'.get! A = m.get! A) :
    GRel lp c m' (Lang.Sem.setFirst gs g.name v') := by
  refine ⟨by rw [Ember.Proof.CSim.lsetFirst_names]; exact h.names, fun g' hg' => ?_⟩
  obtain ⟨v, h1, h2, h3, h4, h5⟩ := h.vals g' hg'
  by_cases hn : g'.name = g.name
  · have : g' = g := eq_of_name L.names hg' hg hn
    subst this
    exact ⟨v', lsetFirst_lookup_self _ _ _ _ h1, h2, hv', hh, fun hc' => by rw [hc] at hc'; cases hc'⟩
  · refine ⟨v, by rw [lsetFirst_lookup_ne _ _ _ _ hn]; exact h1, h2, h3, ?_, h5⟩
    refine Holds.frame h2 h3 (L.gbound g' hg') h4 (fun A ha hb => hm A ?_)
    have := L.gapart g' g hg' hg hn
    omega

end

/-! ## The variables in scope -/

/-- The variables of the lowering's environment and of `Lang.Sem`'s, one
for one, innermost first: each in the frame, above those declared before
it, holding its value.  The last index is the first byte above them. -/
inductive LRel (lp : Prog) (c : Ctx) (fn : String) (m : ByteArray) :
    List (String × VarInfo) → Lang.Sem.Env → Nat → Prop
  | nil : LRel lp c fn m [] [] 0
  | cons {vars : List (String × VarInfo)} {env : Lang.Sem.Env} {top : Nat} (x : String) (ty : Ty) (off : Nat)
      (v : Val) : LRel lp c fn m vars env top → top ≤ off → TyOK lp ty → HasTy lp ty v →
      Holds lp m (fbase c fn + off) ty v →
      LRel lp c fn m ((x, { ty, at_ := .static { area := .frame fn, off } }) :: vars) ((x, v) :: env)
        (off + sizeOf lp ty)

section
variable {lp : Prog} {c : Ctx} {fn : String} {m m' : ByteArray} {vars : List (String × VarInfo)}
  {env : Lang.Sem.Env} {top : Nat}

theorem LRel.length (h : LRel lp c fn m vars env top) : env.length = vars.length := by
  induction h with
  | nil => rfl
  | cons x ty off v _ _ _ _ _ ih => simp [ih]

theorem LRel.frame (h : LRel lp c fn m vars env top) (hb : fbase c fn + top ≤ 65536)
    (hm : ∀ A, fbase c fn ≤ A → A < fbase c fn + top → m'.get! A = m.get! A) : LRel lp c fn m' vars env top := by
  induction h with
  | nil => exact .nil
  | cons x ty off v hrest hle hty hv hh ih =>
    exact .cons x ty off v (ih (by omega) (fun A h1 h2 => hm A h1 (by omega))) hle hty hv
      (Holds.frame hty hv (by omega) hh (fun A h1 h2 => hm A (by omega) (by omega)))

theorem LRel.lookup (h : LRel lp c fn m vars env top) {x : String} {info : VarInfo}
    (hx : vars.lookup x = some info) :
    ∃ off v, info.at_ = .static { area := .frame fn, off } ∧ env.lookup x = some v ∧ TyOK lp info.ty ∧
      HasTy lp info.ty v ∧ Holds lp m (fbase c fn + off) info.ty v ∧ off + sizeOf lp info.ty ≤ top := by
  induction h with
  | nil => simp at hx
  | cons y ty off v hrest hle hty hv hh ih =>
    cases hxy : x == y with
    | true =>
      simp only [List.lookup, hxy, Option.some.injEq] at hx ⊢
      subst hx
      exact ⟨off, v, rfl, rfl, hty, hv, hh, Nat.le_refl _⟩
    | false =>
      simp only [List.lookup, hxy] at hx ⊢
      obtain ⟨o, w, h1, h2, h3, h4, h5, h6⟩ := ih hx
      exact ⟨o, w, h1, h2, h3, h4, h5, by omega⟩

theorem LRel.lookup_none (h : LRel lp c fn m vars env top) {x : String} (hx : vars.lookup x = none) :
    env.lookup x = none := by
  induction h with
  | nil => rfl
  | cons y ty off v hrest hle hty hv hh ih =>
    cases hxy : x == y with
    | true => simp [List.lookup, hxy] at hx
    | false =>
      simp only [List.lookup, hxy] at hx ⊢
      exact ih hx

/-- A variable given a new value, where memory changes inside it only. -/
theorem LRel.set (h : LRel lp c fn m vars env top) (hb : fbase c fn + top ≤ 65536) {x : String} {info : VarInfo}
    {off : Nat} (hx : vars.lookup x = some info) (hat : info.at_ = .static { area := .frame fn, off })
    {v' : Val} (hv' : HasTy lp info.ty v') (hh : Holds lp m' (fbase c fn + off) info.ty v')
    (hm : ∀ A, A < fbase c fn + off ∨ fbase c fn + off + sizeOf lp info.ty ≤ A → m'.get! A = m.get! A) :
    LRel lp c fn m' vars (Lang.Sem.setFirst env x v') top := by
  induction h with
  | nil => simp at hx
  | cons y ty o v hrest hle hty hv hho ih =>
    simp only [Lang.Sem.setFirst]
    cases hxy : x == y with
    | true =>
      simp only [List.lookup, hxy, Option.some.injEq] at hx
      subst hx
      simp only [Storage.static.injEq, Slot.mk.injEq, true_and] at hat
      subst hat
      have hyx : (y == x) = true := by rw [beq_iff_eq] at hxy ⊢; exact hxy.symm
      rw [if_pos hyx]
      exact .cons y ty _ v' (hrest.frame (by omega) (fun A h1 h2 => hm A (by omega))) hle hty hv' hh
    | false =>
      simp only [List.lookup, hxy] at hx
      have hyx : ¬ (y == x) = true := by
        intro e
        rw [beq_iff_eq] at e
        subst e
        simp at hxy
      rw [if_neg hyx]
      obtain ⟨o', w, h1, h2, h3, h4, h5, h6⟩ := hrest.lookup hx
      rw [hat] at h1
      simp only [Storage.static.injEq, Slot.mk.injEq, true_and] at h1
      subst h1
      exact .cons y ty o v (ih (by omega) hx) hle hty hv
        (Holds.frame hty hv (by omega) hho (fun A h1 h2 => hm A (by omega)))

/-- The variables below the innermost ones (the end of a block). -/
theorem LRel.drop : ∀ (pre : List (String × VarInfo)) {env : Lang.Sem.Env} {top : Nat},
    LRel lp c fn m (pre ++ vars) env top → ∃ top', LRel lp c fn m vars (env.drop pre.length) top' ∧ top' ≤ top
  | [], env, top, h => ⟨top, by simpa using h, Nat.le_refl _⟩
  | _ :: pre, _, _, h => by
    cases h with
    | cons x ty off v hrest hle hty hv hh =>
      obtain ⟨top', h1, h2⟩ := LRel.drop pre hrest
      exact ⟨top', by simpa using h1, by omega⟩

end

/-! ## The whole state -/

/-- The first byte above the variables. -/
def topOf (lp : Prog) : List (String × VarInfo) → Nat
  | [] => 0
  | (_, info) :: _ => (match info.at_ with | .static s => s.off | .ref s => s.off) + sizeOf lp info.ty

theorem LRel.top {lp : Prog} {c : Ctx} {fn : String} {m : ByteArray} {vars : List (String × VarInfo)}
    {env : Lang.Sem.Env} {top : Nat} (h : LRel lp c fn m vars env top) : top = topOf lp vars := by
  cases h <;> rfl

/-- An offset in the frame that belongs to a variable in scope. -/
def InVars (lp : Prog) (vars : List (String × VarInfo)) (o : Nat) : Prop :=
  ∃ x info sl, (x, info) ∈ vars ∧ info.at_ = .static sl ∧ sl.off ≤ o ∧ o < sl.off + sizeOf lp info.ty

/-- What a statement leaves alone: everything outside the globals and
the frames of this function and of those it can reach, and in its own
frame the bytes in use (below `cur`) that are not a variable's. -/
def Keep (c : Ctx) (E : Env) (cur : Nat) (m m' : ByteArray) : Prop :=
  ∀ A, Outside E.prog c E.fn A ∨
      (fbase c E.fn ≤ A ∧ A < fbase c E.fn + cur ∧ ¬ InVars E.prog E.vars (A - fbase c E.fn)) →
    m'.get! A = m.get! A

/-- **The states are related**: the same world; every global and every
variable in scope where the lowering's environment `E` says, holding its
value; `cur` bytes of the frame in use. -/
structure SRel (c : Ctx) (E : Env) (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) : Prop where
  size : ist.mem.size = 65536
  world : ist.world = lst.world
  glob : GRel E.prog c ist.mem lst.globals
  loc : ∃ top, LRel E.prog c E.fn ist.mem E.vars env top ∧ top ≤ cur
  fit : ∃ f, c.prog.fn? E.fn = some f ∧ cur ≤ f.frame

/-- The variable a place is rooted at is not a constant. -/
def Writable (g : Env) : Expr → Prop
  | .var x => g.vars.lookup x = none → ∀ gl, g.prog.global? x = some gl → gl.const = false
  | .field b _ => Writable g b
  | .index b _ => Writable g b
  | _ => True

section
variable {c : Ctx} {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}

theorem Keep.refl (m : ByteArray) : Keep c E cur m m := fun _ _ => rfl

theorem Keep.trans {m1 m2 m3 : ByteArray} (h1 : Keep c E cur m1 m2) (h2 : Keep c E cur m2 m3) :
    Keep c E cur m1 m3 := fun A hA => by rw [h2 A hA, h1 A hA]

theorem Keep.weaken {E' : Env} {cur' : Nat} {m m' : ByteArray} (hk : Keep c E' cur' m m')
    (hp : E'.prog = E.prog) (hf : E'.fn = E.fn) (hcur : cur ≤ cur')
    (hv : ∀ o, o < cur → InVars E.prog E'.vars o → InVars E.prog E.vars o) : Keep c E cur m m' := by
  intro A hA
  apply hk A
  rw [hp, hf]
  rcases hA with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, by omega, fun hin => h3 (hv _ (by omega) hin)⟩

theorem SRel.top_le (h : SRel c E cur lst env ist) : topOf E.prog E.vars ≤ cur := by
  obtain ⟨top, hl, htop⟩ := h.loc
  rw [← hl.top]
  exact htop

/-- A variable of the lowering's environment: where it is, and that its
value is there. -/
theorem SRel.var (L : LayOK E.prog c) (h : SRel c E cur lst env ist) {x : String} {info : VarInfo}
    (hx : E.varInfo x = .ok info) :
    ∃ sl v, info.at_ = .static sl ∧ Lang.Sem.lookup lst env x = some v ∧ TyOK E.prog info.ty ∧
      HasTy E.prog info.ty v ∧ Holds E.prog ist.mem (c.layout.addr sl) info.ty v ∧
      c.layout.addr sl + sizeOf E.prog info.ty ≤ 65536 := by
  obtain ⟨top, hl, htop⟩ := h.loc
  obtain ⟨f, hf, hfit⟩ := h.fit
  unfold Env.varInfo at hx
  cases hv : E.vars.lookup x with
  | some i =>
    simp only [hv, Except.ok.injEq] at hx
    subst hx
    obtain ⟨off, v, h1, h2, h3, h4, h5, h6⟩ := hl.lookup hv
    refine ⟨_, v, h1, by simp [Lang.Sem.lookup, h2], h3, h4, by rw [addr_frame]; exact h5, ?_⟩
    rw [addr_frame]
    have := L.fbound _ _ hf
    omega
  | none =>
    simp only [hv] at hx
    cases hg : E.prog.global? x with
    | none => simp [hg, Env.err] at hx
    | some g =>
      simp only [hg, Except.ok.injEq] at hx
      subst hx
      obtain ⟨v, h1, h2, h3, h4, _⟩ := h.glob.lookup hg
      obtain ⟨hm, hn⟩ := global?_mem hg
      refine ⟨_, v, rfl, by simp [Lang.Sem.lookup, hl.lookup_none hv, h1], h2, h3, h4, ?_⟩
      have := L.gbound g hm
      rw [hn] at this
      exact this

theorem SRel.typed (L : LayOK E.prog c) (h : SRel c E cur lst env ist) : VarsTyped E lst env := by
  intro x v info hl hi
  obtain ⟨sl, v', _, hl', _, hv, _⟩ := h.var L hi
  rw [hl] at hl'
  cases hl'
  exact hv

/-- Memory changed where the relation does not look. -/
theorem SRel.frame (L : LayOK E.prog c) (h : SRel c E cur lst env ist) {m' : ByteArray} (hsz : m'.size = 65536)
    (hm : ∀ A, InGlobals E.prog c A ∨ (fbase c E.fn ≤ A ∧ A < fbase c E.fn + cur) →
      m'.get! A = ist.mem.get! A) : SRel c E cur lst env { ist with mem := m' } := by
  obtain ⟨top, hl, htop⟩ := h.loc
  obtain ⟨f, hf, hfit⟩ := h.fit
  have hb := L.fbound _ _ hf
  exact ⟨hsz, h.world, h.glob.frame L (fun A hA => hm A (.inl hA)),
    ⟨top, hl.frame (by omega) (fun A h1 h2 => hm A (.inr ⟨h1, by omega⟩)), htop⟩, ⟨f, hf, hfit⟩⟩

/-- The world moved on, on both sides. -/
theorem SRel.setWorld (h : SRel c E cur lst env ist) (w : World) :
    SRel c E cur { lst with world := w } env { ist with world := w } :=
  ⟨h.size, rfl, h.glob, h.loc, h.fit⟩

theorem SRel.congr {E' : Env} (h : SRel c E cur lst env ist) (hp : E'.prog = E.prog) (hf : E'.fn = E.fn)
    (hv : E'.vars = E.vars) : SRel c E' cur lst env ist := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, by rw [hp]; exact h3, by rw [hp, hf, hv]; exact h4, by rw [hf]; exact h5⟩

/-- More of the frame in use. -/
theorem SRel.grow (h : SRel c E cur lst env ist) {cur' : Nat} (hc : cur ≤ cur')
    (hfit : ∃ f, c.prog.fn? E.fn = some f ∧ cur' ≤ f.frame) : SRel c E cur' lst env ist := by
  obtain ⟨top, hl, htop⟩ := h.loc
  exact ⟨h.size, h.world, h.glob, ⟨top, hl, by omega⟩, hfit⟩

/-- **A variable is given a new value**, memory changing inside it only. -/
theorem SRel.setVar (L : LayOK E.prog c) (h : SRel c E cur lst env ist) {x : String} {info : VarInfo} {sl : Slot}
    (hx : E.varInfo x = .ok info) (hat : info.at_ = .static sl) (hw : Writable E (.var x)) {v' : Val}
    {m' : ByteArray} (hv' : HasTy E.prog info.ty v') (hsz : m'.size = 65536)
    (hm : ∀ A, A < c.layout.addr sl ∨ c.layout.addr sl + sizeOf E.prog info.ty ≤ A → m'.get! A = ist.mem.get! A)
    (hh : Holds E.prog m' (c.layout.addr sl) info.ty v') :
    ∃ lst' env', Lang.Sem.update E.prog lst env (.var x) (fun _ => some v') = some (lst', env') ∧
      SRel c E cur lst' env' { ist with mem := m' } ∧ Keep c E cur ist.mem m' ∧ lst'.world = lst.world := by
  obtain ⟨top, hl, htop⟩ := h.loc
  obtain ⟨f, hf, hfit⟩ := h.fit
  have hfb := L.fbound _ _ hf
  unfold Env.varInfo at hx
  cases hv : E.vars.lookup x with
  | some i =>
    simp only [hv, Except.ok.injEq] at hx
    subst hx
    obtain ⟨off, v, h1, h2, h3, h4, h5, h6⟩ := hl.lookup hv
    rw [hat] at h1
    simp only [Storage.static.injEq] at h1
    subst h1
    rw [addr_frame] at hm hh
    have hin : ∀ A, ¬ (A < fbase c E.fn + off ∨ fbase c E.fn + off + sizeOf E.prog i.ty ≤ A) →
        InFrame c E.fn A := fun A hA => ⟨f, hf, by omega, by omega⟩
    refine ⟨lst, Lang.Sem.setFirst env x v', by simp [Lang.Sem.update, h2], ⟨hsz, h.world, ?_, ?_, ⟨f, hf, hfit⟩⟩,
      ?_, rfl⟩
    · refine h.glob.frame L (fun A hA => ?_)
      by_cases hc : A < fbase c E.fn + off ∨ fbase c E.fn + off + sizeOf E.prog i.ty ≤ A
      · exact hm A hc
      · exact absurd hA (L.fglob _ A (hin A hc))
    · exact ⟨top, hl.set (by omega) hv hat hv' hh hm, htop⟩
    · intro A hA
      by_cases hc : A < fbase c E.fn + off ∨ fbase c E.fn + off + sizeOf E.prog i.ty ≤ A
      · exact hm A hc
      · rcases hA with ⟨_, hnf, _⟩ | ⟨a1, a2, a3⟩
        · exact absurd (hin A hc) hnf
        · exact absurd ⟨x, i, _, lookup_mem _ _ _ hv, hat, by simp only; omega, by simp only; omega⟩ a3
  | none =>
    simp only [hv] at hx
    cases hg : E.prog.global? x with
    | none => simp [hg, Env.err] at hx
    | some g =>
      simp only [hg, Except.ok.injEq] at hx
      subst hx
      simp only [Storage.static.injEq] at hat
      subst hat
      obtain ⟨v, h1, h2, h3, h4, _⟩ := h.glob.lookup hg
      obtain ⟨hmem, hn⟩ := global?_mem hg
      subst hn
      have hc : g.const = false := hw hv g hg
      have hgb := L.gbound g hmem
      have hin : ∀ A, ¬ (A < gaddr c g.name ∨ gaddr c g.name + sizeOf E.prog g.ty ≤ A) → InGlobals E.prog c A :=
        fun A hA => ⟨g, hmem, by omega, by omega⟩
      refine ⟨{ lst with globals := Lang.Sem.setFirst lst.globals g.name v' }, env,
        by simp [Lang.Sem.update, hl.lookup_none hv, h1], ⟨hsz, h.world, ?_, ?_, ⟨f, hf, hfit⟩⟩, ?_, rfl⟩
      · exact h.glob.set L hmem hc hv' hh hm
      · refine ⟨top, hl.frame (by omega) (fun A a1 a2 => ?_), htop⟩
        by_cases hcA : A < gaddr c g.name ∨ gaddr c g.name + sizeOf E.prog g.ty ≤ A
        · exact hm A hcA
        · exact absurd (hin A hcA) (L.fglob _ A ⟨f, hf, a1, by omega⟩)
      · intro A hA
        by_cases hcA : A < gaddr c g.name ∨ gaddr c g.name + sizeOf E.prog g.ty ≤ A
        · exact hm A hcA
        · rcases hA with ⟨hng, _, _⟩ | ⟨a1, a2, a3⟩
          · exact absurd (hin A hcA) hng
          · exact absurd (hin A hcA) (L.fglob _ A ⟨f, hf, a1, by omega⟩)

/-- **A variable is declared**: its value in the next bytes of the frame. -/
theorem SRel.push (L : LayOK E.prog c) (h : SRel c E cur lst env ist) (x : String) (ty : Ty) (v : Val)
    {m' : ByteArray} (hsz : m'.size = 65536) (hty : TyOK E.prog ty) (hv : HasTy E.prog ty v)
    (hfit : ∃ f, c.prog.fn? E.fn = some f ∧ cur + sizeOf E.prog ty ≤ f.frame)
    (hm : ∀ A, A < fbase c E.fn + cur ∨ fbase c E.fn + cur + sizeOf E.prog ty ≤ A → m'.get! A = ist.mem.get! A)
    (hh : Holds E.prog m' (fbase c E.fn + cur) ty v) :
    SRel c { E with vars := (x, { ty, at_ := .static { area := .frame E.fn, off := cur } }) :: E.vars }
      (cur + sizeOf E.prog ty) lst ((x, v) :: env) { ist with mem := m' } := by
  obtain ⟨top, hl, htop⟩ := h.loc
  obtain ⟨f, hf, hfit'⟩ := hfit
  have hfb := L.fbound _ _ hf
  refine ⟨hsz, h.world, h.glob.frame L (fun A hA => ?_), ⟨_, .cons x ty cur v
    (hl.frame (by omega) (fun A a1 a2 => hm A (by omega))) htop hty hv hh, Nat.le_refl _⟩, ⟨f, hf, hfit'⟩⟩
  by_cases hc : A < fbase c E.fn + cur ∨ fbase c E.fn + cur + sizeOf E.prog ty ≤ A
  · exact hm A hc
  · exact absurd hA (L.fglob _ A ⟨f, hf, by omega, by omega⟩)

/-- **The end of a block**: its variables go. -/
theorem SRel.pop (h : SRel c { E with vars := pre ++ E.vars } cur' lst env ist) {pre' : Nat}
    (hpre : pre' = pre.length) (htop : topOf E.prog E.vars ≤ cur) (hcur : cur ≤ cur') :
    SRel c E cur lst (env.drop pre') ist := by
  subst hpre
  obtain ⟨top, hl, _⟩ := h.loc
  obtain ⟨f, hf, hfit⟩ := h.fit
  obtain ⟨top', hl', _⟩ := LRel.drop pre hl
  exact ⟨h.size, h.world, h.glob, ⟨top', hl', by rw [hl'.top]; exact htop⟩, ⟨f, hf, by omega⟩⟩

end

end Ember.Proof.IRSim
