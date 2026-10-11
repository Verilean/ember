import Ember.Lang.Sem

/-!
# Ember.Proof.LangFrame — what a statement leaves alone (plan M5.8)

Facts about `Ember.Lang.Sem` only:

* `keeps`: a statement that neither assigns nor declares `x` leaves the
  innermost `x` as it was, and the names in scope as they were (so a
  `for` loop's counter is what the loop set it to);
* `returns_all`: statements that end in a `return` on every path do not
  end normally.

For programs without by-reference parameters (`NoRef`).
-/

namespace Ember.Proof.CSim
open Ember Ember.Lang
open Ember.Lang.Sem (execB execL execS forLoop loopN)

def rootOf : Expr → Option String
  | .var x => some x
  | .field b _ => rootOf b
  | .index b _ => rootOf b
  | _ => none

mutual
/-- The statement neither assigns nor declares `x`. -/
def NoWriteS (x : String) : Stmt → Prop
  | .at _ s => NoWriteS x s
  | .decl y _ _ => y ≠ x
  | .assign l _ => rootOf l ≠ some x
  | .ite _ t e => NoWriteL x t ∧ NoWriteL x e
  | .forRange y _ _ _ b => y ≠ x ∧ NoWriteL x b
  | .loop _ b => NoWriteL x b
  | .call dst _ _ => dst.bind rootOf ≠ some x
  | .eff dst _ _ => dst.bind rootOf ≠ some x
  | .brk => True
  | .ret _ => True
def NoWriteL (x : String) : List Stmt → Prop
  | [] => True
  | s :: r => NoWriteS x s ∧ NoWriteL x r
end

mutual
/-- The statement ends in a `return` on every path. -/
def ReturnsS : Stmt → Prop
  | .at _ s => ReturnsS s
  | .ret _ => True
  | .ite _ t e => ReturnsL t ∧ ReturnsL e
  | _ => False
def ReturnsL : List Stmt → Prop
  | [] => False
  | s :: r => ReturnsS s ∨ ReturnsL r
end


/-- No function takes a parameter by reference. -/
def NoRef (p : Prog) : Prop := ∀ f fd, p.fn? f = some fd → ∀ prm, prm ∈ fd.params → prm.byRef = false

theorem copyBack_noref (p : Prog) (callee : Lang.Sem.Env) : ∀ (ps : List Param) (as : List Expr)
    (st : Lang.Sem.St) (env : Lang.Sem.Env), (∀ prm, prm ∈ ps → prm.byRef = false) →
    Lang.Sem.copyBack p callee ps as st env = some (st, env)
  | [], _, _, _, _ => by simp [Lang.Sem.copyBack]
  | _ :: _, [], _, _, _ => by simp [Lang.Sem.copyBack]
  | prm :: ps, a :: as, st, env, h => by
    have h1 : prm.byRef = false := h prm (by simp)
    simp only [Lang.Sem.copyBack, h1, Bool.false_eq_true, if_false]
    exact copyBack_noref p callee ps as st env fun q hq => h q (by simp [hq])

/-! ## Names and the innermost `x` -/

theorem lsetFirst_names (env : Lang.Sem.Env) (x : String) (v : Val) :
    (Lang.Sem.setFirst env x v).map (·.1) = env.map (·.1) := by
  induction env with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨y, w⟩ := a
    simp only [Lang.Sem.setFirst]
    split
    · rfl
    · simp only [List.map_cons, ih]

theorem lsetFirst_lookup_ne' (env : Lang.Sem.Env) (x y : String) (v : Val) (hne : y ≠ x) :
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

/-- The same names, and the same innermost `x`. -/
def KeepsB (x : String) (env env' : Lang.Sem.Env) : Prop :=
  env'.map (·.1) = env.map (·.1) ∧ env'.lookup x = env.lookup x

/-- New variables on top, none called `x`; below, as `KeepsB`. -/
def Keeps (x : String) (env env' : Lang.Sem.Env) : Prop :=
  ∃ ys env1, env' = ys ++ env1 ∧ KeepsB x env env1 ∧ ∀ y, y ∈ ys.map (·.1) → y ≠ x

theorem KeepsB.refl (x : String) (env : Lang.Sem.Env) : KeepsB x env env := ⟨rfl, rfl⟩

theorem KeepsB.trans {x : String} {a b c : Lang.Sem.Env} (h1 : KeepsB x a b) (h2 : KeepsB x b c) : KeepsB x a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem KeepsB.keeps {x : String} {a b : Lang.Sem.Env} (h : KeepsB x a b) : Keeps x a b := ⟨[], b, rfl, h, by simp⟩

theorem Keeps.refl (x : String) (env : Lang.Sem.Env) : Keeps x env env := (KeepsB.refl x env).keeps

theorem lookup_append_notin (ys env : Lang.Sem.Env) (x : String) (h : ∀ y, y ∈ ys.map (·.1) → y ≠ x) :
    (ys ++ env).lookup x = env.lookup x := by
  induction ys with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨y, v⟩ := a
    have hy : (x == y) = false := by
      have := h y (by simp)
      simpa using fun e : x = y => this e.symm
    simp only [List.cons_append, List.lookup, hy]
    exact ih fun z hz => h z (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hz)

/-- More variables on top of a scope that was kept. -/
theorem Keeps.trans {x : String} {a b c : Lang.Sem.Env} (h1 : Keeps x a b) (h2 : Keeps x b c) : Keeps x a c := by
  obtain ⟨ys1, e1, rfl, hk1, hn1⟩ := h1
  obtain ⟨ys2, e2, rfl, hk2, hn2⟩ := h2
  -- e2 has the names of ys1 ++ e1
  have hlen : (e2.map (·.1)).length = (ys1.map (·.1)).length + (e1.map (·.1)).length := by
    rw [hk2.1]; simp
  have hsplit : e2 = e2.take ys1.length ++ e2.drop ys1.length := (List.take_append_drop _ _).symm
  have hnames : (e2.take ys1.length).map (·.1) = ys1.map (·.1) ∧ (e2.drop ys1.length).map (·.1) = e1.map (·.1) := by
    have h := hk2.1
    rw [List.map_append] at h
    constructor
    · rw [List.map_take, h, List.take_left' (by simp)]
    · rw [List.map_drop, h, List.drop_left' (by simp)]
  refine ⟨ys2 ++ e2.take ys1.length, e2.drop ys1.length, by rw [List.append_assoc, ← hsplit],
    ⟨hnames.2.trans hk1.1, ?_⟩, ?_⟩
  · have h := hk2.2
    rw [hsplit, lookup_append_notin _ _ _ (by rw [hnames.1]; exact hn1), lookup_append_notin _ _ _ hn1] at h
    exact h.trans hk1.2
  · intro y hy
    simp only [List.map_append, List.mem_append] at hy
    rcases hy with hy | hy
    · exact hn2 y hy
    · rw [hnames.1] at hy; exact hn1 y hy

/-- At the end of a block. -/
theorem Keeps.drop {x : String} {env env' : Lang.Sem.Env} (h : Keeps x env env') :
    KeepsB x env (env'.drop (env'.length - env.length)) := by
  obtain ⟨ys, e1, rfl, hk, _⟩ := h
  have hlen : e1.length = env.length := by
    have := congrArg List.length hk.1
    simpa using this
  rw [List.length_append, hlen, Nat.add_sub_cancel, List.drop_left]
  exact hk

theorem update_keeps (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) :
    ∀ (e : Expr) (f : Val → Option Val) (st' : Lang.Sem.St) (env' : Lang.Sem.Env),
      Lang.Sem.update p st env e f = some (st', env') → rootOf e ≠ some x → KeepsB x env env'
  | .var y, f, st', env', h, hr => by
    have hyx : x ≠ y := fun e => hr (by rw [rootOf, e])
    simp only [Lang.Sem.update] at h
    cases he : env.lookup y with
    | some old =>
      simp only [he] at h
      cases hf : f old with
      | none => simp [hf] at h
      | some v =>
        simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨lsetFirst_names _ _ _, lsetFirst_lookup_ne' _ _ _ _ hyx⟩
    | none =>
      simp only [he] at h
      cases hg : st.globals.lookup y with
      | none => simp [hg] at h
      | some old =>
        simp only [hg] at h
        cases hf : f old with
        | none => simp [hf] at h
        | some v =>
          simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact KeepsB.refl _ _
  | .field b fld, f, st', env', h, hr => by
    simp only [Lang.Sem.update] at h
    exact update_keeps p st env x b _ st' env' h (by simpa [rootOf] using hr)
  | .index b i, f, st', env', h, hr => by
    simp only [Lang.Sem.update] at h
    cases hiv : Lang.Sem.evalE p st env i with
    | none => simp [hiv] at h
    | some iv =>
      simp only [hiv] at h
      exact update_keeps p st env x b _ st' env' h (by simpa [rootOf] using hr)
  | .lit _ _, _, _, _, h, _ => by simp [Lang.Sem.update] at h
  | .blit _, _, _, _, h, _ => by simp [Lang.Sem.update] at h
  | .bin _ _ _, _, _, _, h, _ => by simp [Lang.Sem.update] at h
  | .un _ _, _, _, _, h, _ => by simp [Lang.Sem.update] at h
  | .cast _ _, _, _, _, h, _ => by simp [Lang.Sem.update] at h
  | .cond _ _ _, _, _, _, h, _ => by simp [Lang.Sem.update] at h

theorem storeResult_keeps (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) (dst : Option Expr)
    (r : Option Val) (st' : Lang.Sem.St) (env' : Lang.Sem.Env) (o : Lang.Sem.Out)
    (h : Lang.Sem.storeResult p st env dst r = .ok st' env' o) (hd : dst.bind rootOf ≠ some x) :
    KeepsB x env env' := by
  unfold Lang.Sem.storeResult at h
  cases dst with
  | none => simp only at h; cases h; exact KeepsB.refl _ _
  | some d =>
    cases r with
    | none => simp only at h; cases h; exact KeepsB.refl _ _
    | some v =>
      simp only at h
      cases ha : Lang.Sem.assign p st env d v with
      | none => simp [ha] at h
      | some se =>
        obtain ⟨st1, env1⟩ := se
        simp only [ha, Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact update_keeps p st env x d _ st1 env1 ha (by simpa using hd)

/-- **A statement that does not write `x` leaves it alone.** -/
theorem keeps (p : Prog) (hnr : NoRef p) (x : String) : ∀ n : Nat,
    (∀ st env ss st' env' o, execB n p st env ss = .ok st' env' o → NoWriteL x ss → KeepsB x env env') ∧
    (∀ st env ss st' env' o, execL n p st env ss = .ok st' env' o → NoWriteL x ss → Keeps x env env') ∧
    (∀ st env s st' env' o, execS n p st env s = .ok st' env' o → NoWriteS x s → Keeps x env env') ∧
    (∀ st env y w cur hi body st' env' o, forLoop n p st env y w cur hi body = .ok st' env' o →
      NoWriteL x body → y ≠ x → KeepsB x env env') ∧
    (∀ st env k body st' env' o, loopN n p st env k body = .ok st' env' o → NoWriteL x body → KeepsB x env env')
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro st env ss st' env' o h; rw [execB] at h; cases h
    · intro st env ss st' env' o h; rw [execL] at h; cases h
    · intro st env s st' env' o h; rw [execS] at h; cases h
    · intro st env y w cur hi body st' env' o h; rw [forLoop] at h; cases h
    · intro st env k body st' env' o h; rw [loopN] at h; cases h
  | n + 1 => by
    obtain ⟨ihB, ihL, ihS, ihF, ihN⟩ := keeps p hnr x n
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro st env ss st' env' o h hw
      rw [execB] at h
      cases hL : execL n p st env ss with
      | ok st1 env1 o1 =>
        rw [hL] at h
        simp only [Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact (ihL _ _ _ _ _ _ hL hw).drop
      | trap _ => rw [hL] at h; cases h
      | fuel => rw [hL] at h; cases h
    · intro st env ss st' env' o h hw
      cases ss with
      | nil =>
        rw [execL] at h
        simp only [Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact Keeps.refl _ _
      | cons s rest =>
        rw [execL] at h
        obtain ⟨hw1, hw2⟩ := hw
        cases hS : execS n p st env s with
        | ok st1 env1 o1 =>
          rw [hS] at h
          have k1 := ihS _ _ _ _ _ _ hS hw1
          cases o1 with
          | normal => exact k1.trans (ihL _ _ _ _ _ _ h hw2)
          | brk =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
          | ret v =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
        | trap _ => rw [hS] at h; cases h
        | fuel => rw [hS] at h; cases h
    · intro st env s st' env' o h hw
      cases s with
      | «at» sp s =>
        simp only [execS] at h
        exact ihS _ _ _ _ _ _ h hw
      | decl y ty init =>
        have hyx : y ≠ x := hw
        cases init with
        | some e =>
          simp only [execS] at h
          cases he : Lang.Sem.evalE p st env e with
          | none => simp [he] at h
          | some v =>
            simp only [he, Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact ⟨[(y, v)], env, rfl, KeepsB.refl _ _, by simpa using hyx⟩
        | none =>
          simp only [execS, Lang.Sem.Res.ok.injEq] at h
          obtain ⟨_, rfl, _⟩ := h
          exact ⟨[(y, _)], env, rfl, KeepsB.refl _ _, by simpa using hyx⟩
      | assign l r =>
        simp only [execS] at h
        cases hr : Lang.Sem.evalE p st env r with
        | none => simp [hr] at h
        | some v =>
          simp only [hr] at h
          cases ha : Lang.Sem.assign p st env l v with
          | none => simp [ha] at h
          | some se =>
            obtain ⟨st1, env1⟩ := se
            simp only [ha, Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact (update_keeps p st env x l _ st1 env1 ha hw).keeps
      | ite c t e =>
        simp only [execS] at h
        cases hc : Lang.Sem.evalE p st env c with
        | none => simp [hc] at h
        | some cv =>
          simp only [hc] at h
          by_cases hb : cv.toBool = true
          · rw [if_pos hb] at h; exact (ihB _ _ _ _ _ _ h hw.1).keeps
          · rw [if_neg hb] at h; exact (ihB _ _ _ _ _ _ h hw.2).keeps
      | forRange y w lo hi body =>
        obtain ⟨hyx, hwb⟩ := hw
        simp only [execS] at h
        cases hlo : Lang.Sem.evalE p st env lo with
        | none => simp [hlo] at h
        | some a =>
          cases hhi : Lang.Sem.evalE p st env hi with
          | none => simp [hlo, hhi] at h
          | some b =>
            simp only [hlo, hhi] at h
            cases hF : forLoop n p st ((y, .int (w.getD .w32) (UInt64.ofNat a.toNat)) :: env) y (w.getD .w32)
                a.toNat b.toNat body with
            | ok st1 env1 o1 =>
              rw [hF] at h
              simp only [Lang.Sem.Res.ok.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              obtain ⟨hn, hl⟩ := ihF _ _ _ _ _ _ _ _ _ _ hF hwb hyx
              cases env1 with
              | nil => simp at hn
              | cons a1 r1 =>
                obtain ⟨y1, v1⟩ := a1
                simp only [List.map_cons, List.cons.injEq] at hn
                obtain ⟨rfl, hn⟩ := hn
                have hxy : (x == y1) = false := by simpa using fun e : x = y1 => hyx e.symm
                simp only [List.lookup, hxy] at hl
                exact KeepsB.keeps ⟨hn, hl⟩
            | trap _ => rw [hF] at h; cases h
            | fuel => rw [hF] at h; cases h
      | loop k body =>
        simp only [execS] at h
        exact (ihN _ _ _ _ _ _ _ h hw).keeps
      | brk =>
        simp only [execS, Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact Keeps.refl _ _
      | ret e =>
        cases e with
        | none =>
          simp only [execS, Lang.Sem.Res.ok.injEq] at h
          obtain ⟨_, rfl, _⟩ := h
          exact Keeps.refl _ _
        | some e =>
          simp only [execS] at h
          cases he : Lang.Sem.evalE p st env e with
          | none => simp [he] at h
          | some v =>
            simp only [he, Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact Keeps.refl _ _
      | call dst f args =>
        simp only [execS] at h
        cases hfd : p.fn? f with
        | none => simp [hfd] at h
        | some fd =>
          simp only [hfd] at h
          cases hvs : Lang.Sem.evalArgs p st env args with
          | none => simp [hvs] at h
          | some vs =>
            simp only [hvs] at h
            cases hB : execB n p st ((fd.params.map (·.name)).zip vs) fd.body with
            | ok st1 cenv o1 =>
              rw [hB] at h
              simp only [copyBack_noref p cenv fd.params args st1 env (hnr f fd hfd)] at h
              exact (storeResult_keeps p st1 env x dst _ st' env' o h hw).keeps
            | trap _ => rw [hB] at h; cases h
            | fuel => rw [hB] at h; cases h
      | eff dst e args =>
        simp only [execS] at h
        cases hvs : Lang.Sem.evalArgs p st env args with
        | none => simp [hvs] at h
        | some vs =>
          simp only [hvs] at h
          exact (storeResult_keeps p _ env x dst _ st' env' o h hw).keeps
    · intro st env y w cur hi body st' env' o h hw hyx
      rw [forLoop] at h
      by_cases hlt : cur < hi
      · rw [if_pos hlt] at h
        have k0 : KeepsB x env (Lang.Sem.setFirst env y (.int w (UInt64.ofNat cur))) :=
          ⟨lsetFirst_names _ _ _, lsetFirst_lookup_ne' _ _ _ _ (fun e => hyx e.symm)⟩
        cases hB : execB n p st (Lang.Sem.setFirst env y (.int w (UInt64.ofNat cur))) body with
        | ok st1 env1 o1 =>
          rw [hB] at h
          have k1 := k0.trans (ihB _ _ _ _ _ _ hB hw)
          cases o1 with
          | normal => exact k1.trans (ihF _ _ _ _ _ _ _ _ _ _ h hw hyx)
          | brk =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
          | ret v =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
        | trap _ => rw [hB] at h; cases h
        | fuel => rw [hB] at h; cases h
      · rw [if_neg hlt] at h
        simp only [Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact KeepsB.refl _ _
    · intro st env k body st' env' o h hw
      cases k with
      | zero =>
        rw [loopN] at h
        simp only [Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact KeepsB.refl _ _
      | succ k =>
        rw [loopN] at h
        cases hB : execB n p st env body with
        | ok st1 env1 o1 =>
          rw [hB] at h
          have k1 := ihB _ _ _ _ _ _ hB hw
          cases o1 with
          | normal => exact k1.trans (ihN _ _ _ _ _ _ _ h hw)
          | brk =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
          | ret v =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact k1
        | trap _ => rw [hB] at h; cases h
        | fuel => rw [hB] at h; cases h

/-! ## Returning -/

theorem returns_all (p : Prog) : ∀ n : Nat,
    (∀ st env ss st' env' o, execB n p st env ss = .ok st' env' o → ReturnsL ss → o ≠ .normal) ∧
    (∀ st env ss st' env' o, execL n p st env ss = .ok st' env' o → ReturnsL ss → o ≠ .normal) ∧
    (∀ st env s st' env' o, execS n p st env s = .ok st' env' o → ReturnsS s → o ≠ .normal)
  | 0 => by
    refine ⟨?_, ?_, ?_⟩
    · intro st env ss st' env' o h; rw [execB] at h; cases h
    · intro st env ss st' env' o h; rw [execL] at h; cases h
    · intro st env s st' env' o h; rw [execS] at h; cases h
  | n + 1 => by
    obtain ⟨ihB, ihL, ihS⟩ := returns_all p n
    refine ⟨?_, ?_, ?_⟩
    · intro st env ss st' env' o h hw
      rw [execB] at h
      cases hL : execL n p st env ss with
      | ok st1 env1 o1 =>
        rw [hL] at h
        simp only [Lang.Sem.Res.ok.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        exact ihL _ _ _ _ _ _ hL hw
      | trap _ => rw [hL] at h; cases h
      | fuel => rw [hL] at h; cases h
    · intro st env ss st' env' o h hw
      cases ss with
      | nil => exact absurd hw (by simp [ReturnsL])
      | cons s rest =>
        rw [execL] at h
        cases hS : execS n p st env s with
        | ok st1 env1 o1 =>
          rw [hS] at h
          cases o1 with
          | normal =>
            rcases hw with hw | hw
            · exact absurd rfl (ihS _ _ _ _ _ _ hS hw)
            · exact ihL _ _ _ _ _ _ h hw
          | brk =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            simp
          | ret v =>
            simp only [Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            simp
        | trap _ => rw [hS] at h; cases h
        | fuel => rw [hS] at h; cases h
    · intro st env s st' env' o h hw
      cases s with
      | «at» sp s => simp only [execS] at h; exact ihS _ _ _ _ _ _ h hw
      | ret e =>
        cases e with
        | none =>
          simp only [execS, Lang.Sem.Res.ok.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp
        | some e =>
          simp only [execS] at h
          cases he : Lang.Sem.evalE p st env e with
          | none => simp [he] at h
          | some v =>
            simp only [he, Lang.Sem.Res.ok.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            simp
      | ite c t e =>
        simp only [execS] at h
        cases hc : Lang.Sem.evalE p st env c with
        | none => simp [hc] at h
        | some cv =>
          simp only [hc] at h
          by_cases hb : cv.toBool = true
          · rw [if_pos hb] at h; exact ihB _ _ _ _ _ _ h hw.1
          · rw [if_neg hb] at h; exact ihB _ _ _ _ _ _ h hw.2
      | decl _ _ _ => exact absurd hw (by simp [ReturnsS])
      | assign _ _ => exact absurd hw (by simp [ReturnsS])
      | forRange _ _ _ _ _ => exact absurd hw (by simp [ReturnsS])
      | loop _ _ => exact absurd hw (by simp [ReturnsS])
      | brk => exact absurd hw (by simp [ReturnsS])
      | call _ _ _ => exact absurd hw (by simp [ReturnsS])
      | eff _ _ _ => exact absurd hw (by simp [ReturnsS])

end Ember.Proof.CSim
