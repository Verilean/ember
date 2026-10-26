import Ember.Proof.IRProgram
import Ember.Proof.CCheck

/-!
# Ember.Proof.IRCheck — a checker for what the IR proofs assume (plan M7.1)

`progOkB p`: a function that computes whether a program satisfies
`ProgOK` (well-typed statements in the sense of `WTS`, over the
lowering's own environment; scalar parameters by value, with different
names).  `progOkB_sound` proves that it is right; for a given program it
is then run (`#guard`).

The checker works in one environment per scope; `WTS` asks for every
offset a variable may get and every loop label, which changes no type
(`WTS_like`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 FieldOK TyOK IsPlace NoWriteL ReturnsL isPlaceB isPlaceB_sound tyOkB tyOkB_sound
  noWriteLB noWriteLB_sound returnsLB returnsLB_sound)

/-! ## Environments with the same types -/

/-- The same names and types, in the same program and function. -/
def Like (g g' : Env) : Prop :=
  g'.prog = g.prog ∧ g'.fn = g.fn ∧
    g'.vars.map (fun v => (v.1, v.2.ty)) = g.vars.map (fun v => (v.1, v.2.ty))

theorem Like.refl (g : Env) : Like g g := ⟨rfl, rfl, rfl⟩

theorem lookup_map_ty : ∀ (vars : List (String × VarInfo)) (x : String),
    (vars.map (fun v => (v.1, v.2.ty))).lookup x = (vars.lookup x).map (·.ty)
  | [], _ => rfl
  | (y, i) :: t, x => by
    simp only [List.map_cons, List.lookup]
    cases x == y
    · exact lookup_map_ty t x
    · rfl

theorem Like.lookup {g g' : Env} (h : Like g g') (x : String) :
    (g'.vars.lookup x).map (·.ty) = (g.vars.lookup x).map (·.ty) := by
  rw [← lookup_map_ty, ← lookup_map_ty, h.2.2]

theorem Like.push {g g' : Env} (h : Like g g') (x : String) (ty : Ty) (a a' : Storage) (l l' : Option Nat) :
    Like { g with vars := (x, { ty, at_ := a }) :: g.vars, loopEnd := l }
      { g' with vars := (x, { ty, at_ := a' }) :: g'.vars, loopEnd := l' } :=
  ⟨h.1, h.2.1, by simp only [List.map_cons, h.2.2]⟩

theorem Like.loop {g g' : Env} (h : Like g g') (l l' : Option Nat) :
    Like { g with loopEnd := l } { g' with loopEnd := l' } := ⟨h.1, h.2.1, h.2.2⟩

theorem Like.after {g g' : Env} (h : Like g g') (off off' : Nat) : ∀ (s : Stmt),
    Like (envAfter g off s) (envAfter g' off' s)
  | .at _ s => Like.after h off off' s
  | .decl x ty _ => ⟨h.1, h.2.1, by simp only [envAfter, List.map_cons, h.2.2]⟩
  | .assign _ _ => h
  | .ite _ _ _ => h
  | .forRange _ _ _ _ _ => h
  | .loop _ _ => h
  | .brk => h
  | .ret _ => h
  | .call _ _ _ => h
  | .eff _ _ _ => h

theorem Like.varTy {g g' : Env} (h : Like g g') (x : String) :
    (match g'.varInfo x with | .ok v => Except.ok v.ty | .error m => .error m) =
      (match g.varInfo x with | .ok v => Except.ok v.ty | .error m => .error m) := by
  unfold Env.varInfo
  have hl := h.lookup x
  cases h1 : g'.vars.lookup x with
  | some i =>
    cases h2 : g.vars.lookup x with
    | some i' =>
      simp only [h1, h2, Option.map_some, Option.some.injEq] at hl
      simp only [hl]
    | none => simp [h1, h2] at hl
  | none =>
    cases h2 : g.vars.lookup x with
    | some i' => simp [h1, h2] at hl
    | none =>
      simp only [h.1]
      cases g.prog.global? x <;> simp [Env.err, h.2.1]

theorem tyOf_like {g g' : Env} (h : Like g g') : ∀ (e : Expr), g'.tyOf e = g.tyOf e
  | .lit _ (some _) => rfl
  | .lit _ none => by simp only [Env.tyOf, Env.err, h.2.1]
  | .blit _ => rfl
  | .var x => by simp only [Env.tyOf]; exact h.varTy x
  | .field b f => by simp only [Env.tyOf, tyOf_like h b, h.1, Env.err, h.2.1]
  | .index b _ => by simp only [Env.tyOf, tyOf_like h b, Env.err, h.2.1]
  | .bin _ a _ => by simp only [Env.tyOf, tyOf_like h a]
  | .un _ a => by simp only [Env.tyOf, tyOf_like h a]
  | .cast _ _ => rfl
  | .cond _ a _ => by simp only [Env.tyOf, tyOf_like h a]

theorem WT_like {g g' : Env} (h : Like g g') : ∀ (e : Expr), WT g e → WT g' e
  | .lit _ (some _), hw => hw
  | .lit _ none, hw => hw
  | .blit _, _ => trivial
  | .var _, _ => trivial
  | .field b _, hw => WT_like h b hw
  | .index b i, hw => by
    simp only [WT, tyOf_like h] at hw ⊢
    exact ⟨WT_like h b hw.1, WT_like h i hw.2.1, hw.2.2⟩
  | .bin op a b, hw => by
    simp only [WT, tyOf_like h] at hw ⊢
    exact ⟨WT_like h a hw.1, WT_like h b hw.2.1, hw.2.2⟩
  | .un op a, hw => by
    simp only [WT, tyOf_like h] at hw ⊢
    exact ⟨WT_like h a hw.1, hw.2⟩
  | .cast _ a, hw => by
    simp only [WT, tyOf_like h] at hw ⊢
    exact ⟨WT_like h a hw.1, hw.2⟩
  | .cond c a b, hw => by
    simp only [WT, tyOf_like h] at hw ⊢
    exact ⟨WT_like h c hw.1, WT_like h a hw.2.1, WT_like h b hw.2.2.1, hw.2.2.2⟩

theorem Writable_like {g g' : Env} (h : Like g g') : ∀ (e : Expr), Writable g e → Writable g' e
  | .var x, hw => by
    intro hn gl hgl
    have hl := h.lookup x
    rw [hn] at hl
    have hn' : g.vars.lookup x = none := by
      cases h2 : g.vars.lookup x with
      | none => rfl
      | some i => simp [h2] at hl
    rw [h.1] at hgl
    exact hw hn' gl hgl
  | .field b _, hw => Writable_like h b hw
  | .index b _, hw => Writable_like h b hw
  | .lit _ _, _ => trivial
  | .blit _, _ => trivial
  | .bin _ _ _, _ => trivial
  | .un _ _, _ => trivial
  | .cast _ _, _ => trivial
  | .cond _ _ _, _ => trivial

theorem ArgsOK_like {g g' : Env} (h : Like g g') : ∀ (ts : List Ty) (as : List Expr), ArgsOK g ts as →
    ArgsOK g' ts as
  | [], [], _ => trivial
  | [], _ :: _, hw => hw.elim
  | _ :: _, [], hw => hw.elim
  | _ :: ts, a :: as, hw =>
    ⟨WT_like h a hw.1, by rw [tyOf_like h]; exact hw.2.1, hw.2.2.1, ArgsOK_like h ts as hw.2.2.2⟩

theorem DstOK_like {g g' : Env} (h : Like g g') {dst : Option Expr} {ret : Option Ty} (hw : DstOK g dst ret) :
    DstOK g' dst ret := by
  cases dst with
  | none => trivial
  | some d =>
    obtain ⟨h1, h2, h3, t, h4, h5, h6⟩ := hw
    exact ⟨h1, Writable_like h d h2, WT_like h d h3, t, h4, by rw [tyOf_like h]; exact h5, h6⟩

theorem InitOK_like {g g' : Env} (h : Like g g') {ty : Ty} {i : Init} (hw : InitOK g ty i) : InitOK g' ty i := by
  cases i with
  | call f args =>
    obtain ⟨fd, h1, h2, h3⟩ := hw
    exact ⟨fd, by rw [h.1]; exact h1, ArgsOK_like h _ _ h2, h3⟩
  | eff e args => exact ⟨ArgsOK_like h _ _ hw.1, hw.2⟩

mutual
theorem WTS_like (rt : Option Ty) : ∀ (s : Stmt) (il : Bool) (g g' : Env), Like g g' → WTS rt il g s →
    WTS rt il g' s
  | .at _ s, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    exact WTS_like rt s il g g' h hw
  | .decl x ty init, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    refine ⟨by rw [h.1]; exact hw.1, ?_⟩
    cases init with
    | none => trivial
    | some e => exact ⟨WT_like h e hw.2.1, by rw [tyOf_like h]; exact hw.2.2.1, hw.2.2.2⟩
  | .assign l r, il, g, g', h, hw => by
    simp only [WTS, tyOf_like h] at hw ⊢
    exact ⟨hw.1, Writable_like h l hw.2.1, WT_like h l hw.2.2.1, WT_like h r hw.2.2.2.1, hw.2.2.2.2⟩
  | .ite c t e, il, g, g', h, hw => by
    simp only [WTS, tyOf_like h] at hw ⊢
    exact ⟨WT_like h c hw.1, hw.2.1, WTB_like rt t il g g' h hw.2.2.1, WTB_like rt e il g g' h hw.2.2.2⟩
  | .forRange x w lo hi body, il, g, g', h, hw => by
    simp only [WTS, tyOf_like h] at hw ⊢
    refine ⟨WT_like h lo hw.1, WT_like h hi hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, fun off l => ?_⟩
    exact WTB_like rt body true _ _ (h.push x _ _ _ none l) (hw.2.2.2.2.2 0 none)
  | .loop n body, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    exact ⟨hw.1, fun l => WTB_like rt body true _ _ (h.loop none l) (hw.2 none)⟩
  | .brk, il, g, g', h, hw => hw
  | .ret v, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    cases v with
    | none => exact hw
    | some e =>
      obtain ⟨h1, t, h2, h3, h4⟩ := hw
      exact ⟨WT_like h e h1, t, h2, by rw [tyOf_like h]; exact h3, h4⟩
  | .call dst f args, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    obtain ⟨fd, h1, h2, h3⟩ := hw
    exact ⟨fd, by rw [h.1]; exact h1, ArgsOK_like h _ _ h2, DstOK_like h h3⟩
  | .eff dst e args, il, g, g', h, hw => by
    simp only [WTS] at hw ⊢
    exact ⟨ArgsOK_like h _ _ hw.1, DstOK_like h hw.2⟩

theorem WTB_like (rt : Option Ty) : ∀ (ss : List Stmt) (il : Bool) (g g' : Env), Like g g' → WTB rt il g ss →
    WTB rt il g' ss
  | [], _, _, _, _, _ => by simp only [WTB]
  | [s], il, g, g', h, hw => by
    simp only [WTB] at hw ⊢
    exact WTS_like rt s il g g' h hw
  | s :: s2 :: rest, il, g, g', h, hw => by
    simp only [WTB] at hw ⊢
    cases hdc : declCall? s s2 with
    | none =>
      simp only [hdc] at hw ⊢
      exact ⟨WTS_like rt s il g g' h hw.1,
        fun off => WTB_like rt (s2 :: rest) il _ _ (h.after off off s) (hw.2 off)⟩
    | some tr =>
      obtain ⟨x, ty, i⟩ := tr
      simp only [hdc] at hw ⊢
      exact ⟨by rw [h.1]; exact hw.1, InitOK_like h hw.2.1,
        fun off => WTB_like rt rest il _ _ (h.push x ty _ _ g.loopEnd g'.loopEnd) (by
          have := hw.2.2 off
          exact this)⟩
end

/-! ## The checker -/

def isTy (g : Env) (e : Expr) (t : Ty) : Bool :=
  match g.tyOf e with
  | .ok t' => decide (t' = t)
  | .error _ => false

def isInt (g : Env) (e : Expr) : Bool :=
  match g.tyOf e with
  | .ok (.int _) => true
  | _ => false

/-- Both of one scalar type. -/
def sameScalar (g : Env) (a b : Expr) : Bool :=
  match g.tyOf a, g.tyOf b with
  | .ok t, .ok t' => decide (t = t') && t.isScalar
  | _, _ => false

def sameInt (g : Env) (a b : Expr) : Bool :=
  match g.tyOf a, g.tyOf b with
  | .ok (.int w), .ok (.int w') => decide (w = w')
  | _, _ => false

def wtB (g : Env) : Expr → Bool
  | .lit v (some w) => decide (v < 2 ^ w.bits)
  | .lit _ none => false
  | .blit _ => true
  | .var _ => true
  | .field b _ => wtB g b
  | .index b i =>
    wtB g b && wtB g i && isInt g i &&
      (match g.tyOf b with
       | .ok (.arr _ n) => decide (n < 65536) && (match i with | .lit v _ => decide (v < n) | _ => true)
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

def writableB (g : Env) : Expr → Bool
  | .var x =>
    (g.vars.lookup x).isSome ||
      (match g.prog.global? x with
       | some gl => !gl.const
       | none => true)
  | .field b _ => writableB g b
  | .index b _ => writableB g b
  | _ => true

def argsOkB (g : Env) : List Ty → List Expr → Bool
  | [], [] => true
  | t :: ts, a :: as => wtB g a && isTy g a t && t.isScalar && argsOkB g ts as
  | _, _ => false

def dstOkB (g : Env) (dst : Option Expr) (ret : Option Ty) : Bool :=
  match dst with
  | none => true
  | some d =>
    isPlaceB d && writableB g d && wtB g d &&
      (match ret with
       | some t => isTy g d t && t.isScalar
       | none => false)

def initOkB (g : Env) (ty : Ty) : Init → Bool
  | .call f args =>
    match g.prog.fn? f with
    | some fd => argsOkB g (fd.params.map (·.ty)) args && decide (fd.ret = some ty)
    | none => false
  | .eff e args => argsOkB g e.sig.1 args && decide (e.sig.2 = some ty)

mutual
def wtsB (rt : Option Ty) : Bool → Env → Stmt → Bool
  | il, g, .at _ s => wtsB rt il g s
  | _, g, .decl _ ty init =>
    tyOkB g.prog ty &&
      (match init with
       | some e => wtB g e && isTy g e ty && ty.isScalar
       | none => true)
  | _, g, .assign l r => isPlaceB l && writableB g l && wtB g l && wtB g r && sameScalar g l r
  | il, g, .ite c t e => wtB g c && isTy g c .bool && wtbB rt il g t && wtbB rt il g e
  | _, g, .forRange x w lo hi body =>
    wtB g lo && wtB g hi && isTy g lo (.int (w.getD .w32)) && isTy g hi (.int (w.getD .w32)) &&
      noWriteLB x body &&
      wtbB rt true
        { g with vars := (x, { ty := .int (w.getD .w32), at_ := .static { area := .frame g.fn, off := 0 } }) :: g.vars,
                 loopEnd := none } body
  | _, g, .loop n body => decide (n < 2 ^ 32) && wtbB rt true { g with loopEnd := none } body
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

def wtbB (rt : Option Ty) : Bool → Env → List Stmt → Bool
  | _, _, [] => true
  | il, g, [s] => wtsB rt il g s
  | il, g, s :: s2 :: rest =>
    match declCall? s s2 with
    | some (x, ty, i) =>
      tyOkB g.prog ty && initOkB g ty i &&
        wtbB rt il { g with vars := (x, { ty, at_ := .static { area := .frame g.fn, off := 0 } }) :: g.vars } rest
    | none => wtsB rt il g s && wtbB rt il (envAfter g 0 s) (s2 :: rest)
end

def fnOkB (p : Prog) (fd : Lang.Fn) : Bool :=
  fd.params.all (fun prm => !prm.byRef && prm.ty.isScalar) && decide (fd.params.map (·.name)).Nodup &&
    wtbB fd.ret false (fnEnv p fd) fd.body && (fd.ret.isNone || returnsLB fd.body) &&
    (match fd.ret with
     | some t => t.isScalar
     | none => true)

/-- **The checker.** -/
def progOkB (p : Prog) : Bool :=
  p.fns.all (fnOkB p) &&
    (match p.fn? p.entry with
     | some fd => fd.params.isEmpty
     | none => false)

/-! ## The checker is right -/

theorem isTy_sound {g : Env} {e : Expr} {t : Ty} (h : isTy g e t = true) : g.tyOf e = .ok t := by
  unfold isTy at h
  cases ht : g.tyOf e with
  | error m => simp [ht] at h
  | ok t' =>
    simp only [ht, decide_eq_true_eq] at h
    rw [h]

theorem isInt_sound {g : Env} {e : Expr} (h : isInt g e = true) : ∃ w, g.tyOf e = .ok (.int w) := by
  unfold isInt at h
  cases ht : g.tyOf e with
  | error m => simp [ht] at h
  | ok t' =>
    cases t' with
    | int w => exact ⟨w, rfl⟩
    | bool => simp [ht] at h
    | arr _ _ => simp [ht] at h
    | record _ => simp [ht] at h

theorem sameScalar_sound {g : Env} {a b : Expr} (h : sameScalar g a b = true) :
    ∃ t, g.tyOf a = .ok t ∧ g.tyOf b = .ok t ∧ t.isScalar = true := by
  unfold sameScalar at h
  cases ha : g.tyOf a with
  | error m => simp [ha] at h
  | ok t =>
    cases hb : g.tyOf b with
    | error m => simp [ha, hb] at h
    | ok t' =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨t, rfl, by rw [h.1], h.2⟩

theorem sameInt_sound {g : Env} {a b : Expr} (h : sameInt g a b = true) :
    ∃ w, g.tyOf a = .ok (.int w) ∧ g.tyOf b = .ok (.int w) := by
  unfold sameInt at h
  cases ha : g.tyOf a with
  | error m => simp [ha] at h
  | ok t =>
    cases hb : g.tyOf b with
    | error m => cases t <;> simp [ha, hb] at h
    | ok t' =>
      cases t <;> cases t' <;> simp [ha, hb] at h
      exact ⟨_, rfl, by rw [h]⟩

theorem wtB_sound (g : Env) : ∀ e : Expr, wtB g e = true → WT g e
  | .lit v (some w), h => by simpa [wtB, WT] using h
  | .lit _ none, h => by simp [wtB] at h
  | .blit _, _ => trivial
  | .var _, _ => trivial
  | .field b _, h => wtB_sound g b h
  | .index b i, h => by
    simp only [wtB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hb, hi⟩, hti⟩, hn⟩ := h
    refine ⟨wtB_sound g b hb, wtB_sound g i hi, isInt_sound hti, fun el n htb => ?_, fun v w el n hiv htb => ?_⟩
    · simp only [htb, Bool.and_eq_true, decide_eq_true_eq] at hn
      exact hn.1
    · subst hiv
      simp only [htb, Bool.and_eq_true, decide_eq_true_eq] at hn
      exact hn.2
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

theorem writableB_sound (g : Env) : ∀ e : Expr, writableB g e = true → Writable g e
  | .var x, h => by
    intro hn gl hgl
    simpa [writableB, hn, hgl] using h
  | .field b _, h => writableB_sound g b h
  | .index b _, h => writableB_sound g b h
  | .lit _ _, _ => trivial
  | .blit _, _ => trivial
  | .bin _ _ _, _ => trivial
  | .un _ _, _ => trivial
  | .cast _ _, _ => trivial
  | .cond _ _ _, _ => trivial

theorem argsOkB_sound (g : Env) : ∀ (ts : List Ty) (as : List Expr), argsOkB g ts as = true → ArgsOK g ts as
  | [], [], _ => trivial
  | [], _ :: _, h => by simp [argsOkB] at h
  | _ :: _, [], h => by simp [argsOkB] at h
  | t :: ts, a :: as, h => by
    simp only [argsOkB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hta⟩, hs⟩, hr⟩ := h
    exact ⟨wtB_sound g a ha, isTy_sound hta, hs, argsOkB_sound g ts as hr⟩

theorem dstOkB_sound {g : Env} {dst : Option Expr} {ret : Option Ty} (h : dstOkB g dst ret = true) :
    DstOK g dst ret := by
  cases dst with
  | none => trivial
  | some d =>
    simp only [dstOkB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hwr⟩, hw⟩, hr⟩ := h
    cases ret with
    | none => simp at hr
    | some t =>
      simp only [Bool.and_eq_true] at hr
      exact ⟨isPlaceB_sound d hp, writableB_sound g d hwr, wtB_sound g d hw, t, rfl, isTy_sound hr.1, hr.2⟩

theorem initOkB_sound {g : Env} {ty : Ty} {i : Init} (h : initOkB g ty i = true) : InitOK g ty i := by
  cases i with
  | call f args =>
    simp only [initOkB] at h
    cases hf : g.prog.fn? f with
    | none => simp [hf] at h
    | some fd =>
      simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨fd, hf, argsOkB_sound g _ _ h.1, h.2⟩
  | eff e args =>
    simp only [initOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨argsOkB_sound g _ _ h.1, h.2⟩

mutual
theorem wtsB_sound (rt : Option Ty) : ∀ (s : Stmt) (il : Bool) (g : Env), wtsB rt il g s = true → WTS rt il g s
  | .at _ s, il, g, h => by
    rw [wtsB] at h
    simp only [WTS]
    exact wtsB_sound rt s il g h
  | .decl x ty init, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    refine ⟨tyOkB_sound _ _ h.1, ?_⟩
    cases init with
    | none => trivial
    | some e =>
      simp only [Bool.and_eq_true] at h
      exact ⟨wtB_sound g e h.2.1.1, isTy_sound h.2.1.2, h.2.2⟩
  | .assign l r, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    obtain ⟨⟨⟨⟨hp, hwr⟩, hl⟩, hr⟩, hs⟩ := h
    exact ⟨isPlaceB_sound l hp, writableB_sound g l hwr, wtB_sound g l hl, wtB_sound g r hr, sameScalar_sound hs⟩
  | .ite c t e, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    obtain ⟨⟨⟨hc, htc⟩, ht⟩, he⟩ := h
    exact ⟨wtB_sound g c hc, isTy_sound htc, wtbB_sound rt t il g ht, wtbB_sound rt e il g he⟩
  | .forRange x w lo hi body, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, htlo⟩, hthi⟩, hnw⟩, hb⟩ := h
    refine ⟨wtB_sound g lo hlo, wtB_sound g hi hhi, isTy_sound htlo, isTy_sound hthi, noWriteLB_sound x body hnw,
      fun off l => ?_⟩
    exact WTB_like rt body true _ _ ((Like.refl g).push x _ _ _ none l) (wtbB_sound rt body true _ hb)
  | .loop n body, il, g, h => by
    simp only [wtsB, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [WTS]
    exact ⟨h.1, fun l => WTB_like rt body true _ _ ((Like.refl g).loop none l) (wtbB_sound rt body true _ h.2)⟩
  | .brk, il, g, h => by
    simp only [wtsB] at h
    simp only [WTS]
    exact h
  | .ret none, il, g, h => by
    simp only [wtsB, Option.isNone_iff_eq_none] at h
    simp only [WTS]
    exact h
  | .ret (some e), il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    cases rt with
    | none => simp at h
    | some t =>
      simp only [Bool.and_eq_true] at h
      exact ⟨wtB_sound g e h.1, t, rfl, isTy_sound h.2.1, h.2.2⟩
  | .call dst f args, il, g, h => by
    simp only [wtsB] at h
    simp only [WTS]
    cases hf : g.prog.fn? f with
    | none => simp [hf] at h
    | some fd =>
      simp only [hf, Bool.and_eq_true] at h
      exact ⟨fd, rfl, argsOkB_sound g _ _ h.1, dstOkB_sound h.2⟩
  | .eff dst e args, il, g, h => by
    simp only [wtsB, Bool.and_eq_true] at h
    simp only [WTS]
    exact ⟨argsOkB_sound g _ _ h.1, dstOkB_sound h.2⟩

theorem wtbB_sound (rt : Option Ty) : ∀ (ss : List Stmt) (il : Bool) (g : Env), wtbB rt il g ss = true →
    WTB rt il g ss
  | [], _, _, _ => by simp only [WTB]
  | [s], il, g, h => by
    simp only [wtbB] at h
    simp only [WTB]
    exact wtsB_sound rt s il g h
  | s :: s2 :: rest, il, g, h => by
    simp only [wtbB] at h
    simp only [WTB]
    cases hdc : declCall? s s2 with
    | none =>
      simp only [hdc, Bool.and_eq_true] at h ⊢
      exact ⟨wtsB_sound rt s il g h.1,
        fun off => WTB_like rt (s2 :: rest) il _ _ ((Like.refl g).after 0 off s) (wtbB_sound rt (s2 :: rest) il _ h.2)⟩
    | some tr =>
      obtain ⟨x, ty, i⟩ := tr
      simp only [hdc, Bool.and_eq_true] at h ⊢
      exact ⟨tyOkB_sound _ _ h.1.1, initOkB_sound h.1.2,
        fun off => WTB_like rt rest il _ _ ((Like.refl g).push x ty _ _ g.loopEnd g.loopEnd)
          (wtbB_sound rt rest il _ h.2)⟩
end

theorem fnOkB_sound {p : Prog} {fd : Lang.Fn} (h : fnOkB p fd = true) : FnOK p fd := by
  simp only [fnOkB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp, hn⟩, hb⟩, hr⟩, hs⟩ := h
  refine ⟨fun prm hprm => hp prm hprm, hn, wtbB_sound _ _ _ _ hb, fun hsome => ?_, fun t ht => ?_⟩
  · rcases hr with hr | hr
    · rw [Option.isNone_iff_eq_none] at hr; rw [hr] at hsome; simp at hsome
    · exact returnsLB_sound _ hr
  · rw [ht] at hs
    exact hs

/-- **A program the checker accepts** satisfies what the IR proofs assume. -/
theorem progOkB_sound {p : Prog} (h : progOkB p = true) :
    ProgOK p ∧ ∃ fd, p.fn? p.entry = some fd ∧ fd.params = [] := by
  simp only [progOkB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hf, he⟩ := h
  refine ⟨fun f fd hfd => fnOkB_sound (hf fd (List.mem_of_find?_eq_some hfd)), ?_⟩
  cases hE : p.fn? p.entry with
  | none => simp [hE] at he
  | some fd =>
    simp only [hE, List.isEmpty_iff] at he
    exact ⟨fd, rfl, he⟩

end Ember.Proof.IRSim
