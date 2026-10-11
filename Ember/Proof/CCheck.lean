import Ember.Proof.CProgram

/-!
# Ember.Proof.CCheck — a checker for what the C proofs assume (plan M5.8)

`progOkB p o`: a function that computes whether a program satisfies
`ProgOK` and `GlobalOK` (well-typed statements in the sense of `WTS`,
scalar parameters by value, initial values that fit).  `progOkB_sound`
proves that it is right; for a given program it is then run
(`#guard`), which is how the stack is known to be covered.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C

deriving instance DecidableEq for Ty

/-! ## Expressions -/

def isTy (g : C.Env) (e : Expr) (t : Ty) : Bool :=
  match g.tyOf e with
  | .ok t' => decide (t' = t)
  | .error _ => false

def isInt (g : C.Env) (e : Expr) : Bool :=
  match g.tyOf e with
  | .ok (.int _) => true
  | _ => false

/-- Both of one scalar type. -/
def sameScalar (g : C.Env) (a b : Expr) : Bool :=
  match g.tyOf a, g.tyOf b with
  | .ok t, .ok t' => decide (t = t') && t.isScalar
  | _, _ => false

def sameInt (g : C.Env) (a b : Expr) : Bool :=
  match g.tyOf a, g.tyOf b with
  | .ok (.int w), .ok (.int w') => decide (w = w')
  | _, _ => false

def wtB (g : C.Env) : Expr → Bool
  | .lit v (some w) => decide (v < 2 ^ w.bits)
  | .lit _ none => false
  | .blit _ => true
  | .var _ => true
  | .field b _ => wtB g b
  | .index b i =>
    wtB g b && wtB g i && isInt g i &&
      (match g.tyOf b with
       | .ok (.arr _ n) => decide (n < 65536)
       | _ => true)
  | .bin op a b =>
    wtB g a && wtB g b &&
      (if op.isLogic then isTy g a .bool && isTy g b .bool
       else if op.isShift then isInt g a && isInt g b
       else if op = .eq ∨ op = .ne then sameScalar g a b
       else sameInt g a b)
  | .un op a => wtB g a && (if op = .lnot then isTy g a .bool else isInt g a)
  | .cast _ a => wtB g a && (match g.tyOf a with | .ok t => t.isScalar | .error _ => false)
  | .cond c a b => wtB g c && wtB g a && wtB g b && isTy g c .bool && sameScalar g a b

def isPlaceB : Expr → Bool
  | .var _ => true
  | .field b _ => isPlaceB b
  | .index b _ => isPlaceB b
  | _ => false

/-! ## Statements -/

def fieldOkB : Ty → Bool
  | .int _ => true
  | .bool => true
  | .arr el _ => el.isScalar
  | .record _ => false

def tyOkB (p : Prog) : Ty → Bool
  | .int _ => true
  | .bool => true
  | .arr el _ => el.isScalar
  | .record r =>
    match p.struct? r with
    | some sd => sd.fields.all fun ft => fieldOkB ft.2
    | none => false

def argsOkB (g : C.Env) : List Ty → List Expr → Bool
  | [], [] => true
  | t :: ts, a :: as => wtB g a && isTy g a t && t.isScalar && argsOkB g ts as
  | _, _ => false

def dstOkB (g : C.Env) (dst : Option Expr) (ret : Option Ty) : Bool :=
  match dst with
  | none => true
  | some d =>
    isPlaceB d && wtB g d &&
      (match ret with
       | some t => isTy g d t && t.isScalar
       | none => false)

mutual
def noWriteSB (x : String) : Stmt → Bool
  | .at _ s => noWriteSB x s
  | .decl y _ _ => y != x
  | .assign l _ => rootOf l != some x
  | .ite _ t e => noWriteLB x t && noWriteLB x e
  | .forRange y _ _ _ b => y != x && noWriteLB x b
  | .loop _ b => noWriteLB x b
  | .call dst _ _ => dst.bind rootOf != some x
  | .eff dst _ _ => dst.bind rootOf != some x
  | .brk => true
  | .ret _ => true
def noWriteLB (x : String) : List Stmt → Bool
  | [] => true
  | s :: r => noWriteSB x s && noWriteLB x r
end

mutual
def wtsB (rt : Option Ty) : Bool → C.Env → Stmt → Bool
  | il, g, .at _ s => wtsB rt il g s
  | _, g, .decl _ ty init =>
    tyOkB g.prog ty &&
      (match init with
       | some e => wtB g e && isTy g e ty && ty.isScalar
       | none => true)
  | _, g, .assign l r => isPlaceB l && wtB g l && wtB g r && sameScalar g l r
  | il, g, .ite c t e => wtB g c && isTy g c .bool && wtbB rt il g.path 1 g t && wtbB rt il g.path 1 g e
  | _, g, .forRange x w lo hi body =>
    wtB g lo && wtB g hi && isTy g lo (.int (w.getD .w32)) && isTy g hi (.int (w.getD .w32)) &&
      noWriteLB x body &&
      wtbB rt true g.path 1
        { g with vars := (x, { ty := .int (w.getD .w32), c := .var (localName x) }) :: g.vars } body
  | _, g, .loop n body => decide (n < 2 ^ 32) && wtbB rt true g.path 1 g body
  | il, _, .brk => il
  | _, _, .ret none => rt.isNone
  | _, g, .ret (some e) =>
    wtB g e &&
      (match rt with
       | some t => isTy g e t && t.isScalar
       | none => false)
  | _, g, .call dst f args =>
    match g.prog.fn? f with
    | some fd => argsOkB g (fd.params.map (·.ty)) args && dstOkB g dst fd.ret
    | none => false
  | _, g, .eff dst e args => argsOkB g e.sig.1 args && dstOkB g dst e.sig.2
def wtbB (rt : Option Ty) : Bool → List Nat → Nat → C.Env → List Stmt → Bool
  | _, _, _, _, [] => true
  | il, base, i, env, s :: rest =>
    wtsB rt il { env with path := base ++ [i] } s &&
      wtbB rt il base (i + 1) { envAfter { env with path := base ++ [i] } s with path := base } rest
end

mutual
def returnsSB : Stmt → Bool
  | .at _ s => returnsSB s
  | .ret _ => true
  | .ite _ t e => returnsLB t && returnsLB e
  | _ => false
def returnsLB : List Stmt → Bool
  | [] => false
  | s :: r => returnsSB s || returnsLB r
end

def fnOkB (p : Prog) (o : Opts) (fd : Fn) : Bool :=
  fd.params.all (fun prm => !prm.byRef && prm.ty.isScalar) && wtbB fd.ret false [] 1 (fnEnv p o fd) fd.body &&
    (fd.ret.isNone || returnsLB fd.body)

def initFitsB : Ty → List Nat → Bool
  | .int w, vs => vs.all fun v => decide (v < 2 ^ w.bits)
  | .arr (.int w) _, vs => vs.all fun v => decide (v < 2 ^ w.bits)
  | _, _ => true

def globalOkB (p : Prog) (g : Global) : Bool := tyOkB p g.ty && initFitsB g.ty g.init

/-- **The checker.** -/
def progOkB (p : Prog) (o : Opts) : Bool :=
  p.fns.all (fnOkB p o) && p.globals.all (globalOkB p) &&
    (match p.fn? p.entry with
     | some fd => fd.params.isEmpty
     | none => false)

/-! ## The checker is right -/

theorem isTy_sound {g : C.Env} {e : Expr} {t : Ty} (h : isTy g e t = true) : g.tyOf e = .ok t := by
  unfold isTy at h
  cases ht : g.tyOf e with
  | error m => simp [ht] at h
  | ok t' =>
    simp only [ht, decide_eq_true_eq] at h
    rw [h]

theorem isInt_sound {g : C.Env} {e : Expr} (h : isInt g e = true) : ∃ w, g.tyOf e = .ok (.int w) := by
  unfold isInt at h
  cases ht : g.tyOf e with
  | error m => simp [ht] at h
  | ok t' =>
    cases t' with
    | int w => exact ⟨w, rfl⟩
    | bool => simp [ht] at h
    | arr _ _ => simp [ht] at h
    | record _ => simp [ht] at h

theorem sameScalar_sound {g : C.Env} {a b : Expr} (h : sameScalar g a b = true) :
    ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true := by
  unfold sameScalar at h
  cases ha : g.tyOf a with
  | error m => simp [ha] at h
  | ok t =>
    cases hb : g.tyOf b with
    | error m => simp [ha, hb] at h
    | ok t' =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, hs⟩ := h
      exact ⟨t, rfl, rfl, hs⟩

theorem sameInt_sound {g : C.Env} {a b : Expr} (h : sameInt g a b = true) :
    ∃ w, g.tyOf a = .ok (.int w) ∧ g.tyOf b = .ok (.int w) := by
  unfold sameInt at h
  cases ha : g.tyOf a with
  | error m => simp [ha] at h
  | ok t =>
    cases hb : g.tyOf b with
    | error m => cases t <;> simp [ha, hb] at h
    | ok t' =>
      cases t with
      | int w =>
        cases t' with
        | int w' =>
          simp only [ha, hb, decide_eq_true_eq] at h
          subst h
          exact ⟨w, rfl, rfl⟩
        | bool => simp [ha, hb] at h
        | arr _ _ => simp [ha, hb] at h
        | record _ => simp [ha, hb] at h
      | bool => simp [ha, hb] at h
      | arr _ _ => simp [ha, hb] at h
      | record _ => simp [ha, hb] at h

theorem wtB_sound (g : C.Env) : ∀ e : Expr, wtB g e = true → WT g e
  | .lit v (some w), h => by simpa [wtB, WT] using h
  | .lit _ none, h => by simp [wtB] at h
  | .blit _, _ => trivial
  | .var _, _ => trivial
  | .field b _, h => wtB_sound g b h
  | .index b i, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hb, hi⟩, hti⟩, hn⟩ := h
    refine ⟨wtB_sound g b hb, wtB_sound g i hi, isInt_sound hti, fun el n htb => ?_⟩
    simpa [htb] using hn
  | .bin op a b, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hop⟩ := h
    refine ⟨wtB_sound g a ha, wtB_sound g b hb, ?_⟩
    by_cases h1 : op.isLogic = true
    · rw [if_pos h1] at hop ⊢
      simp only [Bool.and_eq_true] at hop
      exact ⟨isTy_sound hop.1, isTy_sound hop.2⟩
    · rw [if_neg h1] at hop ⊢
      by_cases h2 : op.isShift = true
      · rw [if_pos h2] at hop ⊢
        simp only [Bool.and_eq_true] at hop
        exact ⟨isInt_sound hop.1, isInt_sound hop.2⟩
      · rw [if_neg h2] at hop ⊢
        by_cases h3 : op = .eq ∨ op = .ne
        · rw [if_pos h3] at hop ⊢
          exact sameScalar_sound hop
        · rw [if_neg h3] at hop ⊢
          exact sameInt_sound hop
  | .un op a, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨ha, hop⟩ := h
    refine ⟨wtB_sound g a ha, ?_⟩
    by_cases h1 : op = .lnot
    · rw [if_pos h1] at hop ⊢
      exact isTy_sound hop
    · rw [if_neg h1] at hop ⊢
      exact isInt_sound hop
  | .cast _ a, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨ha, ht⟩ := h
    refine ⟨wtB_sound g a ha, ?_⟩
    cases hta : g.tyOf a with
    | error m => simp [hta] at ht
    | ok t => exact ⟨t, rfl, by simpa [hta] using ht⟩
  | .cond c a b, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hc, ha⟩, hb⟩, htc⟩, hs⟩ := h
    exact ⟨wtB_sound g c hc, wtB_sound g a ha, wtB_sound g b hb, isTy_sound htc, sameScalar_sound hs⟩

theorem isPlaceB_sound : ∀ e : Expr, isPlaceB e = true → IsPlace e
  | .var _, _ => trivial
  | .field b _, h => isPlaceB_sound b h
  | .index b _, h => isPlaceB_sound b h
  | .lit _ _, h => by simp [isPlaceB] at h
  | .blit _, h => by simp [isPlaceB] at h
  | .bin _ _ _, h => by simp [isPlaceB] at h
  | .un _ _, h => by simp [isPlaceB] at h
  | .cast _ _, h => by simp [isPlaceB] at h
  | .cond _ _ _, h => by simp [isPlaceB] at h

theorem fieldOkB_sound : ∀ t : Ty, fieldOkB t = true → FieldOK t
  | .int _, _ => trivial
  | .bool, _ => trivial
  | .arr _ _, h => h
  | .record _, h => by simp [fieldOkB] at h

theorem tyOkB_sound (p : Prog) : ∀ t : Ty, tyOkB p t = true → TyOK p t
  | .int _, _ => trivial
  | .bool, _ => trivial
  | .arr _ _, h => h
  | .record r, h => by
    simp only [tyOkB] at h
    cases hs : p.struct? r with
    | none => simp [hs] at h
    | some sd =>
      simp only [hs, List.all_eq_true] at h
      exact ⟨sd, hs, fun ft hft => fieldOkB_sound _ (h ft hft)⟩

theorem argsOkB_sound (g : C.Env) : ∀ (ts : List Ty) (as : List Expr), argsOkB g ts as = true → ArgsOK g ts as
  | [], [], _ => trivial
  | [], _ :: _, h => by simp [argsOkB] at h
  | _ :: _, [], h => by simp [argsOkB] at h
  | t :: ts, a :: as, h => by
    simp only [argsOkB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hta⟩, hs⟩, hr⟩ := h
    exact ⟨wtB_sound g a ha, isTy_sound hta, hs, argsOkB_sound g ts as hr⟩

theorem dstOkB_sound {g : C.Env} {dst : Option Expr} {ret : Option Ty} (h : dstOkB g dst ret = true) :
    DstOK g dst ret := by
  cases dst with
  | none => trivial
  | some d =>
    simp only [dstOkB, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hw⟩, hr⟩ := h
    cases ret with
    | none => simp at hr
    | some t =>
      simp only [Bool.and_eq_true] at hr
      exact ⟨isPlaceB_sound d hp, wtB_sound g d hw, t, rfl, isTy_sound hr.1, hr.2⟩

mutual
theorem noWriteSB_sound (x : String) : ∀ s : Stmt, noWriteSB x s = true → NoWriteS x s
  | .at _ s, h => by rw [noWriteSB] at h; rw [NoWriteS]; exact noWriteSB_sound x s h
  | .decl y _ _, h => by simpa [noWriteSB, NoWriteS] using h
  | .assign l _, h => by simpa [noWriteSB, NoWriteS] using h
  | .ite _ t e, h => by
    simp only [noWriteSB, Bool.and_eq_true] at h
    rw [NoWriteS]
    exact ⟨noWriteLB_sound x t h.1, noWriteLB_sound x e h.2⟩
  | .forRange y _ _ _ b, h => by
    simp only [noWriteSB, Bool.and_eq_true] at h
    rw [NoWriteS]
    exact ⟨by simpa using h.1, noWriteLB_sound x b h.2⟩
  | .loop _ b, h => by rw [noWriteSB] at h; rw [NoWriteS]; exact noWriteLB_sound x b h
  | .call dst _ _, h => by simpa [noWriteSB, NoWriteS] using h
  | .eff dst _ _, h => by simpa [noWriteSB, NoWriteS] using h
  | .brk, _ => by rw [NoWriteS]; trivial
  | .ret _, _ => by rw [NoWriteS]; trivial
theorem noWriteLB_sound (x : String) : ∀ ss : List Stmt, noWriteLB x ss = true → NoWriteL x ss
  | [], _ => by rw [NoWriteL]; trivial
  | s :: r, h => by
    simp only [noWriteLB, Bool.and_eq_true] at h
    rw [NoWriteL]
    exact ⟨noWriteSB_sound x s h.1, noWriteLB_sound x r h.2⟩
end

mutual
theorem wtsB_sound (rt : Option Ty) : ∀ (s : Stmt) (il : Bool) (g : C.Env), wtsB rt il g s = true → WTS rt il g s
  | .at _ s, il, g, h => by rw [wtsB] at h; rw [WTS]; exact wtsB_sound rt s il g h
  | .decl _ ty init, il, g, h => by
    cases init with
    | none =>
      simp only [wtsB, Bool.and_eq_true] at h
      exact ⟨tyOkB_sound _ _ h.1, trivial⟩
    | some e =>
      simp only [wtsB, Bool.and_eq_true] at h
      exact ⟨tyOkB_sound _ _ h.1, wtB_sound g e h.2.1.1, isTy_sound h.2.1.2, h.2.2⟩
  | .assign l r, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hl⟩, hr⟩, hs⟩ := h
    rw [WTS]
    exact ⟨isPlaceB_sound l hp, wtB_sound g l hl, wtB_sound g r hr, sameScalar_sound hs⟩
  | .ite c t e, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, htc⟩, ht⟩, he⟩ := h
    rw [WTS]
    exact ⟨wtB_sound g c hc, isTy_sound htc, wtbB_sound rt t il g.path 1 g ht, wtbB_sound rt e il g.path 1 g he⟩
  | .forRange x w lo hi body, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, htlo⟩, hthi⟩, hnw⟩, hb⟩ := h
    rw [WTS]
    exact ⟨wtB_sound g lo hlo, wtB_sound g hi hhi, isTy_sound htlo, isTy_sound hthi, noWriteLB_sound x body hnw,
      wtbB_sound rt body true g.path 1 _ hb⟩
  | .loop n body, il, g, h => by
    simp only [wtsB, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [WTS]
    exact ⟨h.1, wtbB_sound rt body true g.path 1 g h.2⟩
  | .brk, il, g, h => by rw [wtsB] at h; rw [WTS]; exact h
  | .ret none, il, g, h => by
    rw [wtsB] at h
    rw [WTS]
    cases rt with
    | none => rfl
    | some _ => simp at h
  | .ret (some e), il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    rw [WTS]
    cases rt with
    | none => simp at h
    | some t =>
      have h2 := h.2
      simp only [Bool.and_eq_true] at h2
      exact ⟨wtB_sound g e h.1, t, rfl, isTy_sound h2.1, h2.2⟩
  | .call dst f args, il, g, h => by
    simp only [wtsB] at h
    rw [WTS]
    cases hf : g.prog.fn? f with
    | none => simp [hf] at h
    | some fd =>
      simp only [hf, Bool.and_eq_true] at h
      exact ⟨fd, rfl, argsOkB_sound g _ args h.1, dstOkB_sound h.2⟩
  | .eff dst e args, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    rw [WTS]
    exact ⟨argsOkB_sound g _ args h.1, dstOkB_sound h.2⟩
theorem wtbB_sound (rt : Option Ty) : ∀ (ss : List Stmt) (il : Bool) (base : List Nat) (i : Nat) (env : C.Env),
    wtbB rt il base i env ss = true → WTB rt il base i env ss
  | [], _, _, _, _, _ => by rw [WTB]; trivial
  | s :: rest, il, base, i, env, h => by
    simp only [wtbB, Bool.and_eq_true] at h
    rw [WTB]
    exact ⟨wtsB_sound rt s il _ h.1, wtbB_sound rt rest il base (i + 1) _ h.2⟩
end

mutual
theorem returnsSB_sound : ∀ s : Stmt, returnsSB s = true → ReturnsS s
  | .at _ s, h => by rw [returnsSB] at h; rw [ReturnsS]; exact returnsSB_sound s h
  | .ret _, _ => by rw [ReturnsS]; trivial
  | .ite _ t e, h => by
    simp only [returnsSB, Bool.and_eq_true] at h
    rw [ReturnsS]
    exact ⟨returnsLB_sound t h.1, returnsLB_sound e h.2⟩
  | .decl _ _ _, h => by simp [returnsSB] at h
  | .assign _ _, h => by simp [returnsSB] at h
  | .forRange _ _ _ _ _, h => by simp [returnsSB] at h
  | .loop _ _, h => by simp [returnsSB] at h
  | .brk, h => by simp [returnsSB] at h
  | .call _ _ _, h => by simp [returnsSB] at h
  | .eff _ _ _, h => by simp [returnsSB] at h
theorem returnsLB_sound : ∀ ss : List Stmt, returnsLB ss = true → ReturnsL ss
  | [], h => by simp [returnsLB] at h
  | s :: r, h => by
    simp only [returnsLB, Bool.or_eq_true] at h
    rw [ReturnsL]
    rcases h with h | h
    · exact Or.inl (returnsSB_sound s h)
    · exact Or.inr (returnsLB_sound r h)
end

theorem fnOkB_sound {p : Prog} {o : Opts} {fd : Fn} (h : fnOkB p o fd = true) : FnOK p o fd := by
  simp only [fnOkB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨hp, hb⟩, hr⟩ := h
  refine ⟨fun prm hprm => hp prm hprm, wtbB_sound _ _ _ _ _ _ hb, fun hs => ?_⟩
  rcases hr with hr | hr
  · rw [Option.isNone_iff_eq_none] at hr; rw [hr] at hs; simp at hs
  · exact returnsLB_sound _ hr

theorem initFitsB_sound : ∀ (t : Ty) (vs : List Nat), initFitsB t vs = true → InitFits t vs
  | .int w, vs, h => by
    simp only [initFitsB, List.all_eq_true, decide_eq_true_eq] at h
    exact h
  | .arr (.int w) _, vs, h => by
    simp only [initFitsB, List.all_eq_true, decide_eq_true_eq] at h
    exact h
  | .arr .bool _, _, _ => trivial
  | .arr (.arr _ _) _, _, _ => trivial
  | .arr (.record _) _, _, _ => trivial
  | .bool, _, _ => trivial
  | .record _, _, _ => trivial

/-- **A program the checker accepts** satisfies what the C proofs assume. -/
theorem progOkB_sound {p : Prog} {o : Opts} (h : progOkB p o = true) :
    ProgOK p o ∧ (∀ g, g ∈ p.globals → GlobalOK p g) ∧ ∃ fd, p.fn? p.entry = some fd ∧ fd.params = [] := by
  simp only [progOkB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hf, hg⟩, he⟩ := h
  refine ⟨fun f fd hfd => fnOkB_sound (hf fd (List.mem_of_find?_eq_some hfd)), fun g hgm => ?_, ?_⟩
  · have := hg g hgm
    simp only [globalOkB, Bool.and_eq_true] at this
    exact ⟨tyOkB_sound p _ this.1, initFitsB_sound _ _ this.2⟩
  · cases hE : p.fn? p.entry with
    | none => simp [hE] at he
    | some fd =>
      simp only [hE, List.isEmpty_iff] at he
      exact ⟨fd, rfl, he⟩

end Ember.Proof.CSim
