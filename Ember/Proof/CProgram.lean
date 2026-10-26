import Ember.Proof.CFn

/-!
# Ember.Proof.CProgram — whole programs (plan M5.8)

* `compile_unit`: what `C.compile` produces is a `Unit` for the program;
* `init_rel`: the initial states are related;
* `entry_sim`, `iter_sim`: a call of the entry function, and any number
  of them, do in C what they do in Ember.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

/-! ## Names -/

/-- The names of a unit do not collide: `Hyg`, and no Ember function is
called like the entry function or one of the runtime's. -/
structure HygU (o : Opts) : Prop where
  hyg : Hyg o
  fe : ∀ f, o.fnName f ≠ o.entryName
  feff : ∀ f e, o.fnName f ≠ effectCall e
  eeff : ∀ e, o.entryName ≠ effectCall e
  et : (o.entryName == "ember_trap") = false

theorem e_ne (f s : String) (h : ∀ c r, s.toList = 'e' :: c :: r → c ≠ '_') : ("" : String) ++ "e_" ++ f ≠ s := by
  intro e
  have := congrArg String.toList e
  simp at this
  exact h '_' f.toList this.symm rfl

/-- Without a name prefix (one program per C file) the names do not collide. -/
theorem hygU_of_prefix (o : Opts) (h : o.namePrefix = "") : HygU o := by
  have hentry : o.entryName = "entry" := by unfold Opts.entryName; rw [h]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z x e
    rw [globalName_eq, h, localName_eq] at e
    have := congrArg String.toList e
    simp at this
  · intro z k e
    rw [globalName_eq, h] at e
    unfold tmpName at e
    have := congrArg String.toList e
    simp at this
  · intro f
    rw [fnName_eq, h]
    have k : ∀ s : String, (∀ c r, s.toList = 'e' :: c :: r → c ≠ '_') →
        ((("" : String) ++ "e_" ++ f) == s) = false := by
      intro s hs
      cases hb : (("" : String) ++ "e_" ++ f) == s
      · rfl
      · rw [beq_iff_eq] at hb; exact absurd hb (e_ne f s hs)
    unfold C.Sem.helper
    rw [k "ember_div8" (by simp), k "ember_mod8" (by simp), k "ember_div16" (by simp), k "ember_mod16" (by simp),
      k "ember_div32" (by simp), k "ember_mod32" (by simp), k "ember_div64" (by simp), k "ember_mod64" (by simp)]
    rfl
  · intro f
    rw [fnName_eq, h]
    cases hb : (("" : String) ++ "e_" ++ f) == "ember_trap"
    · rfl
    · rw [beq_iff_eq] at hb; exact absurd hb (e_ne f _ (by simp))
  · intro f
    rw [fnName_eq, h, hentry]
    exact e_ne f _ (by simp)
  · intro f e
    rw [fnName_eq, h]
    apply e_ne
    cases e <;> simp [effectCall]
  · intro e
    rw [hentry]
    cases e <;> simp [effectCall]
  · rw [hentry]; rfl

theorem structName_inj {o : Opts} {x y : String} (h : o.structName x = o.structName y) : x = y := by
  have e : ∀ s, o.structName s = o.namePrefix ++ "s_" ++ s := fun _ => rfl
  rw [e, e] at h
  exact (String.append_right_inj _).mp h

/-! ## The unit -/

theorem compile_shape {p : Prog} {o : Opts} {u : CUnit} (h : compile p o = .ok u) :
    ∃ fns, p.fns.mapM (compileFn p o) = .ok fns ∧ u.structs = p.structs.map (structC o) ∧
      u.globals = p.globals.map (globalC o) ∧ u.fns = fns ++ [entryFn p o] := by
  unfold compile at h
  split at h
  · cases h
  · rename_i fns hf
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨fns, hf, rfl, rfl, rfl⟩

theorem structs_lookup (o : Opts) : ∀ (l : List StructDef) (r : String) (sd : StructDef),
    l.find? (·.name == r) = some sd →
    (l.map (structC o)).lookup (o.structName r) = some (sd.fields.map fun ft => (cty o ft.2, ft.1))
  | [], _, _, h => by simp at h
  | a :: l, r, sd, h => by
    simp only [List.find?] at h
    simp only [List.map_cons, structC, List.lookup]
    cases ha : a.name == r with
    | true =>
      simp only [ha, Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at ha
      subst ha
      simp only [beq_self_eq_true]
    | false =>
      simp only [ha] at h
      have hne : (o.structName r == o.structName a.name) = false := by
        cases hb : o.structName r == o.structName a.name
        · rfl
        · rw [beq_iff_eq] at hb
          rw [structName_inj hb] at ha
          simp at ha
      simp only [hne]
      exact structs_lookup o l r sd h

theorem mapM_fns (p : Prog) (o : Opts) : ∀ (l : List Fn) (cl : List CFn), l.mapM (compileFn p o) = .ok cl →
    (∀ c, c ∈ cl → ∃ f, c.name = o.fnName f) ∧
    ∀ f fd, l.find? (·.name == f) = some fd →
      ∃ cfd, cl.find? (·.name == o.fnName f) = some cfd ∧ compileFn p o fd = .ok cfd
  | [], cl, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun c hc => by simp at hc, fun f fd hf => by simp at hf⟩
  | a :: l, cl, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hfa : compileFn p o a with
    | error e => simp [hfa] at h
    | ok b =>
      simp only [hfa] at h
      cases hl : l.mapM (compileFn p o) with
      | error e => simp [hl] at h
      | ok bs =>
        simp only [hl, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ih1, ih2⟩ := mapM_fns p o l bs hl
        have hbn := (compileFn_shape hfa).1
        refine ⟨fun c hc => ?_, fun f fd hf => ?_⟩
        · simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨a.name, hbn⟩
          · exact ih1 c hc
        · simp only [List.find?] at hf ⊢
          cases ha : a.name == f with
          | true =>
            simp only [ha, Option.some.injEq] at hf
            subst hf
            rw [beq_iff_eq] at ha
            subst ha
            refine ⟨b, ?_, hfa⟩
            simp [hbn]
          | false =>
            simp only [ha] at hf
            have hne : (b.name == o.fnName f) = false := by
              cases hb : b.name == o.fnName f
              · rfl
              · rw [beq_iff_eq, hbn] at hb
                rw [fnName_inj hb] at ha
                simp at ha
            simp only [hne]
            exact ih2 f fd hf

/-- **What `C.compile` produces** for a program, with the tables of that program, is a `Unit`. -/
theorem compile_unit {p : Prog} {o : Opts} {u : CUnit} (h : compile p o = .ok u) (hy : HygU o)
    (hb : o.bugDropCast = false) (h16 : 16 ≤ o.profile.intBits) :
    Unit p o (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) := by
  obtain ⟨fns, hfns, hst, hgl, hfn⟩ := compile_shape h
  obtain ⟨hnames, hfind⟩ := mapM_fns p o p.fns fns hfns
  refine ⟨?_, rfl, h16, ?_, hb, hy.hyg, rfl, rfl, ?_, ?_⟩
  · intro r sd hsd
    show u.structs.lookup _ = _
    rw [hst]
    exact structs_lookup o p.structs r sd hsd
  · show 32 ≤ (if o.profile.regBits == 64 then 64 else 32)
    split <;> decide
  · intro f fd hfd
    obtain ⟨cfd, hc, hcomp⟩ := hfind f fd hfd
    refine ⟨cfd, ?_, hcomp⟩
    show u.fns.find? _ = _
    rw [hfn, List.find?_append, hc]
    rfl
  · intro e
    show u.fns.find? _ = _
    rw [hfn]
    apply List.find?_eq_none.mpr
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · obtain ⟨f, hf⟩ := hnames c hc
      simp only [hf, beq_iff_eq]
      exact hy.feff f e
    · simp only [entryFn, beq_iff_eq]
      exact hy.eeff e

/-! ## The initial state -/

/-- The initial values of a global fit its type. -/
def InitFits : Ty → List Nat → Prop
  | .int w, vs => ∀ v, v ∈ vs → v < 2 ^ w.bits
  | .arr (.int w) _, vs => ∀ v, v ∈ vs → v < 2 ^ w.bits
  | _, _ => True

def GlobalOK (p : Prog) (g : Global) : Prop := TyOK p g.ty ∧ InitFits g.ty g.init

theorem mask_ofNat_toNat (w : Width) (v : Nat) (h : v < 2 ^ w.bits) : (mask w (UInt64.ofNat v)).toNat = v := by
  rw [mask_toNat, UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ (pow_bits_dvd w), Nat.mod_eq_of_lt h]

theorem range_map_const {α : Type} (n : Nat) (c : α) : (Array.range n).map (fun _ => c) = Array.replicate n c := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

theorem init_zero {p : Prog} {o : Opts} {cp : CProg} (U : Unit p o cp) (g : Global) (hty : TyOK p g.ty)
    (h1 : Lang.initOf p g = zeroOf p g.ty) (h2 : globalInit g = none) :
    C.Sem.initOf cp (globalC o g) = cval o (Lang.initOf p g) ∧ HasTy p g.ty (Lang.initOf p g) := by
  rw [h1]
  refine ⟨?_, hasTy_zero p _ hty⟩
  rw [cval_zero U _ hty]
  simp only [C.Sem.initOf, globalC, h2]

/-- A global starts with the same value on both sides. -/
theorem init_eq {p : Prog} {o : Opts} {cp : CProg} (U : Unit p o cp) (g : Global) (hg : GlobalOK p g) :
    C.Sem.initOf cp (globalC o g) = cval o (Lang.initOf p g) ∧ HasTy p g.ty (Lang.initOf p g) := by
  obtain ⟨hty, hfit⟩ := hg
  obtain ⟨name, ty, init, const⟩ := g
  simp only at hty hfit
  cases ty with
  | int w =>
    cases init with
    | nil => exact init_zero U _ hty rfl rfl
    | cons v r =>
      cases r with
      | nil =>
        have hv : v < 2 ^ w.bits := hfit v (by simp)
        have hl := evalC_litC cp { globals := [], world := { inputs := #[] } } [] w v hv U.i16 U.l32
        refine ⟨?_, hasTy_mask p w _⟩
        simp only [C.Sem.initOf, globalC, globalInit, cty, List.head?, hl, Option.bind_some, C.Sem.convTo,
          castTo_uint, Nat.mod_eq_of_lt hv, Option.getD_some, Lang.initOf, cval_int, mask_ofNat_toNat w v hv]
      | cons v2 r2 => exact init_zero U _ hty rfl rfl
  | bool =>
    cases init with
    | nil => exact init_zero U _ hty rfl rfl
    | cons v r =>
      cases r with
      | nil =>
        refine ⟨?_, trivial⟩
        simp [C.Sem.initOf, globalC, globalInit, cty, C.Sem.evalC, C.Sem.convTo, C.Sem.castTo, Lang.initOf]
      | cons v2 r2 => exact init_zero U _ hty rfl rfl
  | arr el n =>
    cases el with
    | int w =>
      have hfit' : ∀ v, v ∈ init → v < 2 ^ w.bits := hfit
      have hm0 : (mask w 0).toNat = 0 := by
        have := mask_ofNat_toNat w 0 (Nat.two_pow_pos _)
        simpa using this
      have hL : Lang.initOf p { name, ty := .arr (.int w) n, init, const }
          = .arr ((Array.range n).map fun i => .int w (mask w (UInt64.ofNat (init.getD i 0)))) := by
        cases init <;> rfl
      rw [hL]
      refine ⟨?_, by simp, fun x hx => ?_⟩
      · cases init with
        | nil =>
          simp only [C.Sem.initOf, globalC, globalInit, cty, C.Sem.zero, C.Sem.zero0, cval_arr, Array.map_map]
          rw [← range_map_const]
          congr 1
          apply Array.map_congr_left
          intro i _
          simp [hm0]
        | cons v r =>
          simp only [C.Sem.initOf, globalC, globalInit, cty, cval_arr, Array.map_map]
          congr 1
          apply Array.map_congr_left
          intro i _
          simp only [Function.comp, List.getElem?_map, cval_int]
          cases hvi : (v :: r)[i]? with
          | none =>
            simp [List.getD, hvi, hm0, C.Sem.zero, C.Sem.zero0]
          | some x =>
            have hx : x < 2 ^ w.bits := hfit' x (List.mem_of_getElem? hvi)
            have : (v :: r).getD i 0 = x := by simp [List.getD, hvi]
            have hl := evalC_litC cp { globals := [], world := { inputs := #[] } } [] w x hx U.i16 U.l32
            simp only [Option.map_some, hl, Option.bind_some, C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hx,
              Option.getD_some, this, mask_ofNat_toNat w x hx]
      · simp only [Array.mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact ⟨rfl, mask_lt w _⟩
    | bool =>
      have hL : Lang.initOf p { name, ty := .arr .bool n, init, const }
          = .arr ((Array.range n).map fun i => .bool (init.getD i 0 != 0)) := by
        cases init <;> rfl
      rw [hL]
      refine ⟨?_, by simp, fun x hx => ?_⟩
      · cases init with
        | nil =>
          simp only [C.Sem.initOf, globalC, globalInit, cty, C.Sem.zero, C.Sem.zero0, cval_arr, Array.map_map]
          rw [← range_map_const]
          congr 1
          apply Array.map_congr_left
          intro i _
          simp
        | cons v r =>
          simp only [C.Sem.initOf, globalC, globalInit, cty, cval_arr, Array.map_map]
          congr 1
          apply Array.map_congr_left
          intro i _
          simp only [Function.comp, List.getElem?_map, cval_bool]
          cases hvi : (v :: r)[i]? with
          | none =>
            simp [List.getD, hvi, C.Sem.zero, C.Sem.zero0]
          | some x =>
            simp [List.getD, hvi, C.Sem.evalC, C.Sem.convTo, C.Sem.castTo]
      · simp only [Array.mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx
        trivial
    | arr _ _ => simp [TyOK, Ty.isScalar] at hty
    | record _ => simp [TyOK, Ty.isScalar] at hty
  | record r =>
    refine init_zero U _ hty ?_ ?_
    · cases init with
      | nil => rfl
      | cons h t => cases t <;> rfl
    · cases init with
      | nil => rfl
      | cons h t => cases t <;> rfl

theorem lang_globals_lookup (F : Global → Val) : ∀ (l : List Global) (z : String) (gd : Global),
    l.find? (·.name == z) = some gd → (l.map fun g => (g.name, F g)).lookup z = some (F gd)
  | [], _, _, h => by simp at h
  | a :: l, z, gd, h => by
    simp only [List.find?] at h
    simp only [List.map_cons, List.lookup]
    cases ha : a.name == z with
    | true =>
      simp only [ha, Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at ha
      subst ha
      simp
    | false =>
      simp only [ha] at h
      have hne : (z == a.name) = false := by
        cases hb : z == a.name
        · rfl
        · rw [beq_iff_eq] at hb; rw [hb] at ha; simp at ha
      simp only [hne]
      exact lang_globals_lookup F l z gd h

theorem c_globals_lookup (o : Opts) (F : CGlobal → CVal) : ∀ (l : List Global) (z : String) (gd : Global),
    l.find? (·.name == z) = some gd →
    ((l.map (globalC o)).map fun g => (g.name, F g)).lookup (o.globalName z) = some (F (globalC o gd))
  | [], _, _, h => by simp at h
  | a :: l, z, gd, h => by
    simp only [List.find?] at h
    simp only [List.map_cons, List.lookup]
    cases ha : a.name == z with
    | true =>
      simp only [ha, Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at ha
      subst ha
      simp [globalC]
    | false =>
      simp only [ha] at h
      have hne : (o.globalName z == (globalC o a).name) = false := by
        cases hb : o.globalName z == (globalC o a).name
        · rfl
        · rw [beq_iff_eq] at hb
          have := globalName_inj (o := o) (x := z) (y := a.name) hb
          rw [this] at ha; simp at ha
      simp only [hne]
      exact c_globals_lookup o F l z gd h

/-- **The initial states are related.** -/
theorem init_rel {p : Prog} {o : Opts} {u : CUnit} (h : compile p o = .ok u) (hy : HygU o)
    (hb : o.bugDropCast = false) (h16 : 16 ≤ o.profile.intBits) (hG : ∀ g, g ∈ p.globals → GlobalOK p g)
    (inputs : Array Trace.Input) :
    GRel p o (Lang.Sem.initial p inputs)
      (C.Sem.initial (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) inputs p.framed) := by
  have U := compile_unit h hy hb h16
  obtain ⟨_, _, _, hgl, _⟩ := compile_shape h
  refine ⟨fun z gd hz => ?_, fun k => ?_, rfl⟩
  · have hmem : gd ∈ p.globals := List.mem_of_find?_eq_some hz
    obtain ⟨he, hty⟩ := init_eq U gd (hG gd hmem)
    refine ⟨Lang.initOf p gd, lang_globals_lookup _ p.globals z gd hz, hty, ?_⟩
    show ((C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes).unit.globals.map _).lookup _ = _
    rw [← he]
    show (u.globals.map _).lookup _ = _
    rw [hgl]
    exact c_globals_lookup o _ p.globals z gd hz
  · show (u.globals.map _).lookup _ = none
    rw [hgl]
    apply C.Sem.lookup_eq_none_of_not_mem
    intro hm
    simp only [List.map_map, List.mem_map, Function.comp] at hm
    obtain ⟨g, _, e⟩ := hm
    exact hy.hyg.gt g.name k e

/-! ## The entry function -/

/-- `j` calls of the entry function; `none` when one traps or runs out of fuel. -/
def callIter (fuel : Nat) (p : Prog) : Nat → Lang.Sem.St → Option Lang.Sem.St
  | 0, st => some st
  | j + 1, st =>
    match Lang.Sem.call fuel p st p.entry [] with
    | .ok _ st' => callIter fuel p j st'
    | _ => none

/-- The same in C, as `Ember.C.Sem.run` calls it. -/
def cIter (m : Nat) (cp : CProg) : Nat → C.Sem.St → Option C.Sem.St
  | 0, st => some st
  | j + 1, st =>
    match C.Sem.callC m cp st [] cp.entry [] with
    | .ok st' _ _ => cIter m cp j st'
    | _ => none

theorem cIter_le {cp : CProg} {m m' : Nat} (hm : m ≤ m') : ∀ (j : Nat) (cst cst' : C.Sem.St),
    cIter m cp j cst = some cst' → cIter m' cp j cst = some cst'
  | 0, _, _, h => h
  | j + 1, cst, cst', h => by
    rw [cIter] at h ⊢
    cases hc : C.Sem.callC m cp cst [] cp.entry [] with
    | ok st1 e o1 =>
      rw [hc] at h
      rw [C.Sem.callC_le hm hc trivial]
      exact cIter_le hm j st1 cst' h
    | trap _ => rw [hc] at h; cases h
    | undef => rw [hc] at h; cases h
    | fuel => rw [hc] at h; cases h

section
variable {p : Prog} {o : Opts} {u : CUnit}

theorem entry_find (h : compile p o = .ok u) (hy : HygU o) :
    u.fns.find? (·.name == o.entryName) = some (entryFn p o) := by
  obtain ⟨fns, hfns, _, _, hfn⟩ := compile_shape h
  obtain ⟨hnames, _⟩ := mapM_fns p o p.fns fns hfns
  rw [hfn, List.find?_append]
  have hn : fns.find? (·.name == o.entryName) = none := by
    apply List.find?_eq_none.mpr
    intro c hc
    obtain ⟨f, hf⟩ := hnames c hc
    simp only [hf, beq_iff_eq]
    exact hy.fe f
  rw [hn]
  simp [entryFn]

/-- **A call of the entry function.** -/
theorem entry_sim (h : compile p o = .ok u) (hy : HygU o) (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hP : ProgOK p o) (fd : Fn) (hE : p.fn? p.entry = some fd)
    (hpar : fd.params = []) (k : Nat) (st : Lang.Sem.St) (cst : C.Sem.St) (hG : GRel p o st cst) :
    match Lang.Sem.call k p st p.entry [] with
    | .ok _ st' =>
      ∃ m cst' e o', C.Sem.callC m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst []
          o.entryName [] = .ok cst' e o' ∧ GRel p o st' cst' ∧ cst'.stack = cst.stack
    | .trap st' =>
      ∃ m cst', C.Sem.callC m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst []
          o.entryName [] = .trap cst' ∧ cst'.world = st'.world
    | .fuel => True := by
  have U := compile_unit h hy hb h16
  have hrel : SRel { prog := p, opts := o } st [] { cst with stack := [] :: cst.stack } [] :=
    ⟨.nil, ⟨hG.glob, hG.gtmp, hG.world⟩⟩
  have H := fn_sim p o _ U hP (k + 1) k (Nat.lt_succ_self k)
  have hc := call_sim (g := { prog := p, opts := o }) U k H hrel p.entry fd hE (hP _ fd hE).params [] [] rfl
    (by rw [hpar]; trivial)
  have hac : C.Sem.asCall (.call (o.fnName p.entry) []) = some (o.fnName p.entry, []) := by
    simp [C.Sem.asCall, U.hyg.fh]
  have hfind := entry_find h hy
  have hcall : ∀ (M : Nat) (r : C.Sem.Res),
      C.Sem.execB M (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes)
        { cst with stack := [] :: cst.stack } [] [.expr (.call (o.fnName p.entry) [])] = r →
      C.Sem.callC (M + 1) (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst [] o.entryName []
        = (match r with
          | .ok st' _ out =>
            match st'.stack with
            | env' :: rest =>
              match out with
              | .ret (some v) =>
                match C.Sem.convTo (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) .void v with
                | some v' => .ok { st' with stack := rest } env' (.ret (some v'))
                | none => .undef
              | _ => .ok { st' with stack := rest } env' (.ret none)
            | [] => .undef
          | r => r) := by
    intro M r hr
    rw [C.Sem.callC]
    simp only [hy.et, Bool.false_eq_true, if_false]
    have hf : (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes).unit.fns.find?
        (·.name == o.entryName) = some (entryFn p o) := hfind
    simp only [hf, entryFn, C.Sem.argVals, List.map_nil, List.zip_nil_left]
    rw [hr]
    cases r <;> rfl
  unfold Lang.Sem.call
  rw [hE]
  simp only
  cases hR : Lang.Sem.execB k p st ((fd.params.map (·.name)).zip []) fd.body with
  | fuel => trivial
  | trap st' =>
    rw [hR] at hc
    obtain ⟨cst', ⟨f, args, hac', m, hm⟩, hw⟩ := hc
    rw [hac] at hac'
    cases hac'
    obtain ⟨M, hM⟩ := (Exec.one (exec_expr_trap m _ hac hm) trivial).block_trap
    exact ⟨M + 1, cst', by rw [hcall M _ hM], hw⟩
  | ok st' envL out =>
    rw [hR] at hc
    obtain ⟨cst'', ⟨f, args, hac', m, hm⟩, hrel', hstk, _⟩ := hc
    rw [hac] at hac'
    cases hac'
    obtain ⟨M, hM⟩ := (Exec.one (exec_expr_call m _ _ hac hm) trivial).block
    have hres : C.Sem.callC (M + 1) (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst []
        o.entryName [] = .ok { cst'' with stack := cst.stack } [] (.ret none) := by
      rw [hcall M _ hM]
      simp only [hstk]
    have hG' : GRel p o st' { cst'' with stack := cst.stack } := ⟨hrel'.2.glob, hrel'.2.gtmp, hrel'.2.world⟩
    cases out with
    | normal => exact ⟨M + 1, _, _, _, hres, hG', rfl⟩
    | brk => exact ⟨M + 1, _, _, _, hres, hG', rfl⟩
    | ret v => exact ⟨M + 1, _, _, _, hres, hG', rfl⟩

/-- **The program, call after call.**  If `j` calls of the entry
function end in Ember, they end in C, in a related state. -/
theorem iter_sim (h : compile p o = .ok u) (hy : HygU o) (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hP : ProgOK p o) (fd : Fn) (hE : p.fn? p.entry = some fd)
    (hpar : fd.params = []) (k : Nat) : ∀ (j : Nat) (st st' : Lang.Sem.St) (cst : C.Sem.St), GRel p o st cst →
    callIter k p j st = some st' →
    ∃ m cst', cIter m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) j cst = some cst' ∧
      GRel p o st' cst'
  | 0, st, st', cst, hG, hi => by
    simp only [callIter, Option.some.injEq] at hi
    subst hi
    exact ⟨0, cst, rfl, hG⟩
  | j + 1, st, st', cst, hG, hi => by
    rw [callIter] at hi
    have he := entry_sim h hy hb h16 hP fd hE hpar k st cst hG
    cases hc : Lang.Sem.call k p st p.entry [] with
    | ok v st1 =>
      rw [hc] at hi he
      obtain ⟨m1, cst1, e, o', hm1, hG1, _⟩ := he
      obtain ⟨m2, cst', hm2, hG'⟩ := iter_sim h hy hb h16 hP fd hE hpar k j st1 st' cst1 hG1 hi
      refine ⟨max m1 m2, cst', ?_, hG'⟩
      rw [cIter]
      have : C.Sem.callC (max m1 m2) (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst []
          (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes).entry [] = .ok cst1 e o' :=
        C.Sem.callC_le (Nat.le_max_left m1 m2) hm1 trivial
      rw [this]
      exact cIter_le (Nat.le_max_right m1 m2) j cst1 cst' hm2
    | trap _ => rw [hc] at hi; cases hi
    | fuel => rw [hc] at hi; cases hi

/-- … and if the next call traps in Ember, it traps in C, with the same events. -/
theorem iter_trap (h : compile p o = .ok u) (hy : HygU o) (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hP : ProgOK p o) (fd : Fn) (hE : p.fn? p.entry = some fd)
    (hpar : fd.params = []) (k j : Nat) (st st1 st2 : Lang.Sem.St) (cst : C.Sem.St) (hG : GRel p o st cst)
    (hi : callIter k p j st = some st1) (ht : Lang.Sem.call k p st1 p.entry [] = .trap st2) :
    ∃ m cst1 cst2, cIter m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) j cst = some cst1 ∧
      C.Sem.callC m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) cst1 [] o.entryName []
        = .trap cst2 ∧ cst2.world = st2.world := by
  obtain ⟨m1, cst1, hm1, hG1⟩ := iter_sim h hy hb h16 hP fd hE hpar k j st st1 cst hG hi
  have he := entry_sim h hy hb h16 hP fd hE hpar k st1 cst1 hG1
  rw [ht] at he
  obtain ⟨m2, cst2, hm2, hw⟩ := he
  exact ⟨max m1 m2, cst1, cst2, cIter_le (Nat.le_max_left m1 m2) j cst cst1 hm1,
    C.Sem.callC_le (Nat.le_max_right m1 m2) hm2 trivial, hw⟩

end

/-- info: 'Ember.Proof.CSim.iter_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms iter_sim

end Ember.Proof.CSim
