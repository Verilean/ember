import Ember.Proof.CStmt

/-!
# Ember.Proof.CCall — arguments, results, effects and calls (plan M5.8)

* `exprs_ok`: the arguments of a call or an effect;
* `store_ok`: `assignResult` — the result of a call goes where
  `Lang.Sem.storeResult` puts it, the destination being evaluated after
  the call;
* `eff_sim`: the runtime's functions are the effects of `Ember.Lang`;
* `call_sim`: a call of a compiled function, given that function bodies
  are simulated (`FnSim`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

/-! ## Small facts -/

theorem traps_nil_false {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} (h : Traps cp cst cenv []) : False := by
  have := h 0 []
  simp [C.Sem.execL] at this

theorem runs_nil_eq {cp : CProg} {cst : C.Sem.St} {cenv cenv' : C.Sem.Env} (h : Runs cp cst cenv [] cenv') :
    cenv' = cenv := by
  have := h 0 []
  simp [C.Sem.execL] at this
  exact this.symm

theorem PlaceLoc.lval_scalar {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} {c : CExpr} {ptr : Bool} {cv : CVal}
    {L : C.Sem.Loc} (h : PlaceLoc cp cst cenv c ptr cv L) (hs : (∀ n fs, cv ≠ .strct n fs) ∧ ∀ ys, cv ≠ .arr ys) :
    C.Sem.lval cp cst cenv c = some L := by
  obtain ⟨l0, hl0, hr⟩ := h
  rcases hr with ⟨_, e, _⟩ | ⟨_, _, h3⟩
  · rw [e]; exact hl0
  · rcases h3 with ⟨_, n, fs, e⟩ | ⟨_, ys, e⟩
    · exact absurd e (hs.1 n fs)
    · exact absurd e (hs.2 ys)

/-- The location of a place: its variable's storage, at its path. -/
theorem rooted_loc {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv : C.Sem.Env} (U : Unit g.prog g.opts cp) (hrel : SRel g st env cst cenv) {d : Expr} {L : C.Sem.Loc}
    {x : String} {q : List Nat} {t : Ty} {vold : Val} (hroot : Rooted g cp d L st env cst cenv)
    (hq : lpath g.prog st env d = some (x, q)) (hty : g.tyOf d = .ok t)
    (hold : Lang.Sem.evalE g.prog st env d = some vold) :
    L = { xloc g.opts env cst x with path := (xloc g.opts env cst x).path ++ q } := by
  obtain ⟨vx, hlx, _⟩ := evalE_lpath _ _ _ d vold x q hold hq
  obtain ⟨info, hinfo⟩ := tyOf_root g st env d t x q hty hq
  obtain ⟨Lx, hLx, rfl⟩ := hroot x q hq info vx hinfo hlx
  have hLx' := hrel.place_loc (cp := cp) U.hyg hlx hinfo
  rw [hLx.unique hLx' (cval_ne_ptr _ _)]

theorem evalE_congr (p : Prog) (st st' : Lang.Sem.St) (env : Lang.Sem.Env) (h : st'.globals = st.globals) :
    ∀ e : Expr, Lang.Sem.evalE p st' env e = Lang.Sem.evalE p st env e
  | .lit _ (some _) => rfl
  | .lit _ none => rfl
  | .blit _ => rfl
  | .var x => by simp only [Lang.Sem.evalE, Lang.Sem.lookup, h]
  | .field b f => by simp only [Lang.Sem.evalE, evalE_congr p st st' env h b]
  | .index b i => by simp only [Lang.Sem.evalE, evalE_congr p st st' env h b, evalE_congr p st st' env h i]
  | .bin op a b => by simp only [Lang.Sem.evalE, evalE_congr p st st' env h a, evalE_congr p st st' env h b]
  | .un op a => by simp only [Lang.Sem.evalE, evalE_congr p st st' env h a]
  | .cast w a => by simp only [Lang.Sem.evalE, evalE_congr p st st' env h a]
  | .cond c a b => by
    simp only [Lang.Sem.evalE, evalE_congr p st st' env h c, evalE_congr p st st' env h a,
      evalE_congr p st st' env h b]

theorem lpath_congr (p : Prog) (st st' : Lang.Sem.St) (env : Lang.Sem.Env) (h : st'.globals = st.globals) :
    ∀ e : Expr, lpath p st' env e = lpath p st env e
  | .var _ => rfl
  | .field b f => by simp only [lpath, lpath_congr p st st' env h b, evalE_congr p st st' env h b]
  | .index b i => by simp only [lpath, lpath_congr p st st' env h b, evalE_congr p st st' env h i]
  | .lit _ _ => rfl
  | .blit _ => rfl
  | .bin _ _ _ => rfl
  | .un _ _ => rfl
  | .cast _ _ => rfl
  | .cond _ _ _ => rfl

/-- A place without a computed index is at the same path in every state in which it has a value. -/
theorem lpath_stable (g : C.Env) (st st' : Lang.Sem.St) (env env' : Lang.Sem.Env) (ht : VarsTyped g st env)
    (ht' : VarsTyped g st' env') : ∀ (d : Expr) (t : Ty) (v v' : Val), readsIndex d = false → WT g d →
    g.tyOf d = .ok t → Lang.Sem.evalE g.prog st env d = some v → Lang.Sem.evalE g.prog st' env' d = some v' →
    lpath g.prog st' env' d = lpath g.prog st env d
  | .var _, _, _, _, _, _, _, _, _ => rfl
  | .field b f, t, v, v', hr, hw, hty, hv, hv' => by
    simp only [Lang.Sem.evalE] at hv hv'
    simp only [Env.tyOf] at hty
    cases htb : g.tyOf b with
    | error m => simp [htb] at hty
    | ok tb =>
      cases hb : Lang.Sem.evalE g.prog st env b with
      | none => simp [hb] at hv
      | some bv =>
        cases hb' : Lang.Sem.evalE g.prog st' env' b with
        | none => simp [hb'] at hv'
        | some bv' =>
          have h1 := evalE_hasTy g st env ht b bv tb hw hb htb
          have h2 := evalE_hasTy g st' env' ht' b bv' tb hw hb' htb
          have ih := lpath_stable g st st' env env' ht ht' b tb bv bv' (by simpa [readsIndex] using hr) hw htb hb hb'
          cases bv with
          | record r fs =>
            cases bv' with
            | record r' fs' =>
              cases tb with
              | record rn =>
                obtain ⟨_, _, e1, _⟩ := hasTy_record h1
                obtain ⟨_, _, e2, _⟩ := hasTy_record h2
                cases e1; cases e2
                simp only [lpath, ih, hb, hb']
                cases lpath g.prog st env b with
                | none => rfl
                | some xq => rfl
              | int _ => obtain ⟨_, e, _⟩ := hasTy_int h1; cases e
              | bool => obtain ⟨_, e⟩ := hasTy_bool h1; cases e
              | arr _ _ => obtain ⟨_, e, _⟩ := hasTy_arr h1; cases e
            | int _ _ => simp [hb'] at hv'
            | bool _ => simp [hb'] at hv'
            | arr _ => simp [hb'] at hv'
          | int _ _ => simp [hb] at hv
          | bool _ => simp [hb] at hv
          | arr _ => simp [hb] at hv
  | .index b i, t, v, v', hr, hw, hty, hv, hv' => by
    simp only [WT] at hw
    simp only [Lang.Sem.evalE] at hv hv'
    simp only [Env.tyOf] at hty
    cases htb : g.tyOf b with
    | error m => simp [htb] at hty
    | ok tb =>
      cases hb : Lang.Sem.evalE g.prog st env b with
      | none => simp [hb] at hv
      | some bv =>
        cases hb' : Lang.Sem.evalE g.prog st' env' b with
        | none => simp [hb'] at hv'
        | some bv' =>
          cases i with
          | lit n w =>
            have ih := lpath_stable g st st' env env' ht ht' b tb bv bv' (by simpa [readsIndex] using hr) hw.1 htb
              hb hb'
            have hi : Lang.Sem.evalE g.prog st' env' (.lit n w) = Lang.Sem.evalE g.prog st env (.lit n w) := by
              cases w <;> rfl
            simp only [lpath, ih, hi]
          | blit _ => simp [readsIndex] at hr
          | var _ => simp [readsIndex] at hr
          | field _ _ => simp [readsIndex] at hr
          | index _ _ => simp [readsIndex] at hr
          | bin _ _ _ => simp [readsIndex] at hr
          | un _ _ => simp [readsIndex] at hr
          | cast _ _ => simp [readsIndex] at hr
          | cond _ _ _ => simp [readsIndex] at hr
  | .lit _ _, _, _, _, _, _, _, _, _ => rfl
  | .blit _, _, _, _, _, _, _, _, _ => rfl
  | .bin _ _ _, _, _, _, _, _, _, _, _ => rfl
  | .un _ _, _, _, _, _, _, _, _, _ => rfl
  | .cast _ _, _, _, _, _, _, _, _, _ => rfl
  | .cond _ _ _, _, _, _, _, _, _, _, _ => rfl

/-- Code after a prefix that declared temporaries. -/
theorem Sim.prefix {g : C.Env} {K : List (String × VarInfo) → Prop} {cp : CProg} {rt : Option Ty} {il : Bool}
    {t' : Nat} {pre code : List CStmt} {R : Lang.Sem.Res} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv xs : C.Sem.Env} (hruns : Runs cp cst cenv pre (xs ++ cenv)) (ht : AllTmp xs)
    (h : Sim g K cp rt il t' code R env cst (xs ++ cenv)) : Sim g K cp rt il t' (pre ++ code) R env cst cenv := by
  cases R with
  | ok st' env' out =>
    obtain ⟨cst', cenv', hx, ⟨ys, env1, xs', cenv1, rfl, rfl, hlen, hsame, hrel, hstk, hfr, hn⟩, hout⟩ := h
    obtain ⟨xs1, c1, rfl, h1, h2⟩ := hsame.split
    have ht1 := ht.same h1
    refine ⟨cst', _, hruns.exec hx, ⟨ys, env1, xs' ++ xs1, c1, rfl, by rw [List.append_assoc], hlen, h2,
      hrel.strip ht1, hstk, hfr, fun ho => ?_⟩, hout⟩
    obtain ⟨nv, hK, hl⟩ := hn ho
    refine ⟨nv, hK, ?_⟩
    have := hl.append (LRel.allTmp (p := g.prog) (o := g.opts) ht1)
    simpa using this
  | trap st' =>
    obtain ⟨cst', hx, hw⟩ := h
    exact ⟨cst', hruns.exec hx, hw⟩
  | fuel => trivial

/-! ## Arguments -/

def ArgsOk (g : C.Env) (args : List Expr) : Lang.Sem.St → Lang.Sem.Env → Prop :=
  fun st env => (Lang.Sem.evalArgs g.prog st env args).isSome = true

def ArgsRes (g : C.Env) (cp : CProg) (args : List Expr) (cargs : List CExpr) :
    Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop :=
  fun st env cst cenv => ∀ vs, Lang.Sem.evalArgs g.prog st env args = some vs →
    C.Sem.evalCs cp cst cenv cargs = some (vs.map (cval g.opts))

theorem ArgsRes.stable (g : C.Env) (cp : CProg) (args : List Expr) (cargs : List CExpr) :
    Stable (ArgsRes g cp args cargs) :=
  fun _ _ _ _ _ hx h vs hv => C.Sem.evalCs_ext hx cargs (h vs hv)

/-- Values of the given types, all scalars. -/
def ValsTy (p : Prog) : List Ty → List Val → Prop
  | [], [] => True
  | t :: ts, v :: vs => HasTy p t v ∧ t.isScalar = true ∧ ValsTy p ts vs
  | _, _ => False

theorem args_typed (g : C.Env) (st : Lang.Sem.St) (env : Lang.Sem.Env) (ht : VarsTyped g st env) :
    ∀ (tys : List Ty) (args : List Expr) (vs : List Val), ArgsOK g tys args →
      Lang.Sem.evalArgs g.prog st env args = some vs → ValsTy g.prog tys vs
  | [], [], vs, _, h => by simp only [Lang.Sem.evalArgs, Option.some.injEq] at h; subst h; trivial
  | [], _ :: _, _, hw, _ => hw.elim
  | _ :: _, [], _, hw, _ => hw.elim
  | t :: ts, a :: as, vs, hw, h => by
    obtain ⟨wa, hta, hsc, hrest⟩ := hw
    simp only [Lang.Sem.evalArgs] at h
    cases ha : Lang.Sem.evalE g.prog st env a with
    | none => simp [ha] at h
    | some v =>
      cases has : Lang.Sem.evalArgs g.prog st env as with
      | none => simp [ha, has] at h
      | some vs' =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        exact ⟨evalE_hasTy g st env ht a v t wa ha hta, hsc, args_typed g st env ht ts as vs' hrest has⟩

theorem exprs_ok (cp : CProg) : ∀ (args : List Expr) (tys : List Ty) (g : C.Env) (cs : CS), EnvOK g →
    ArgsOK g tys args →
    wpc (exprs args) g (fun cargs cs' => ∃ pre, cs'.out = cs.out ++ pre.toArray ∧
      Frag g cp cs.tmp cs'.tmp pre (ArgsOk g args) (ArgsRes g cp args cargs)) cs
  | [], [], g, cs, _, _ => by
    rw [exprs, wpc_pure]
    refine ⟨[], by simp, Frag.nil _ ?_ ?_⟩
    · intro st env cst cenv _ _ vs hv
      simp only [Lang.Sem.evalArgs, Option.some.injEq] at hv
      subst hv
      rfl
    · intro st env cst cenv _
      simp [ArgsOk, Lang.Sem.evalArgs]
  | [], _ :: _, _, _, _, hw => hw.elim
  | _ :: _, [], _, _, _, hw => hw.elim
  | a :: as, t :: ts, g, cs, hg, hw => by
    obtain ⟨wa, hta, hsc, hrest⟩ := hw
    rw [exprs]
    simp only [wpc_bind, wpc_pure]
    refine wpc_mono (expr_ok cp a g cs hg wa t hta hsc) ?_
    rintro ca cs1 ⟨pre1, ho1, _, F1⟩
    refine wpc_mono (exprs_ok cp as ts g cs1 hg hrest) ?_
    rintro cas cs2 ⟨pre2, ho2, F2⟩
    refine ⟨pre1 ++ pre2, by simp [ho1, ho2], ?_⟩
    refine (F1.seq F2 (ERes.stable g cp a ca)).conseq ?_ ?_
    · intro st env cst cenv _
      simp only [ArgsOk, EOk, Lang.Sem.evalArgs]
      cases Lang.Sem.evalE g.prog st env a <;> cases Lang.Sem.evalArgs g.prog st env as <;> simp
    · intro st env cst cenv _ _ hr vs hv
      simp only [Lang.Sem.evalArgs] at hv
      cases ha : Lang.Sem.evalE g.prog st env a with
      | none => simp [ha] at hv
      | some v =>
        cases has : Lang.Sem.evalArgs g.prog st env as with
        | none => simp [ha, has] at hv
        | some vs' =>
          simp only [ha, has, Option.some.injEq] at hv
          subst hv
          simp only [C.Sem.evalCs, hr.1 v ha, hr.2 vs' has, List.map_cons]

theorem callArgs_eq (g : C.Env) : ∀ (ps : List Param) (args : List Expr), (∀ prm, prm ∈ ps → prm.byRef = false) →
    ArgsOK g (ps.map (·.ty)) args → callArgs ps args = exprs args
  | [], [], _, _ => rfl
  | [], _ :: _, _, hw => hw.elim
  | _ :: _, [], _, hw => hw.elim
  | prm :: ps, a :: as, h, hw => by
    have h1 : prm.byRef = false := h prm (by simp)
    rw [callArgs, exprs, callArgs_eq g ps as (fun q hq => h q (by simp [hq])) hw.2.2.2]
    simp only [h1, Bool.false_eq_true, if_false]

theorem evalCs_cons_inv {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} {a : CExpr} {as : List CExpr}
    {v : CVal} {vs : List CVal} (h : C.Sem.evalCs cp cst cenv (a :: as) = some (v :: vs)) :
    C.Sem.evalC cp cst cenv a = some v ∧ C.Sem.evalCs cp cst cenv as = some vs := by
  simp only [C.Sem.evalCs] at h
  cases ha : C.Sem.evalC cp cst cenv a with
  | none => simp [ha] at h
  | some v' =>
    cases has : C.Sem.evalCs cp cst cenv as with
    | none => simp [ha, has] at h
    | some vs' =>
      simp only [ha, has, Option.some.injEq, List.cons.injEq] at h
      exact ⟨by rw [h.1], by rw [h.2]⟩

theorem evalCs_length {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} : ∀ {as : List CExpr} {vs : List CVal},
    C.Sem.evalCs cp cst cenv as = some vs → as.length = vs.length
  | [], vs, h => by simp only [C.Sem.evalCs, Option.some.injEq] at h; subst h; rfl
  | a :: as, vs, h => by
    simp only [C.Sem.evalCs] at h
    cases ha : C.Sem.evalC cp cst cenv a with
    | none => simp [ha] at h
    | some v' =>
      cases has : C.Sem.evalCs cp cst cenv as with
      | none => simp [ha, has] at h
      | some vs' =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        simp [evalCs_length has]

/-- The arguments as the C function receives them. -/
theorem argVals_ok (o : Opts) (cp : CProg) (p : Prog) (cst : C.Sem.St) (cenv : C.Sem.Env) :
    ∀ (ps : List Param) (cargs : List CExpr) (vs : List Val),
      (∀ prm, prm ∈ ps → prm.byRef = false ∧ prm.ty.isScalar = true) →
      C.Sem.evalCs cp cst cenv cargs = some (vs.map (cval o)) → ValsTy p (ps.map (·.ty)) vs →
      C.Sem.argVals cp cst cenv (ps.map (paramC o)) cargs = some (vs.map (cval o))
  | [], cargs, [], _, hc, _ => by
    cases cargs with
    | nil => rfl
    | cons a as => have := evalCs_length hc; simp at this
  | [], _, _ :: _, _, _, hv => hv.elim
  | _ :: _, _, [], _, _, hv => hv.elim
  | prm :: ps, cargs, v :: vs, hp, hc, hv => by
    obtain ⟨hty, hsc, hrest⟩ := hv
    cases cargs with
    | nil => have := evalCs_length hc; simp at this
    | cons a as =>
      rw [List.map_cons] at hc
      obtain ⟨ha, has⟩ := evalCs_cons_inv hc
      have ih := argVals_ok o cp p cst cenv ps as vs (fun q hq => hp q (by simp [hq])) has hrest
      obtain ⟨hbr, _⟩ := hp prm (by simp)
      have hpc : paramC o prm = (cty o prm.ty, localName prm.name) := by
        unfold paramC
        cases prm.ty <;> simp [hbr]
      have hsc' : prm.ty.isScalar = true := hsc
      have hty' : HasTy p prm.ty v := hty
      have hconv := convTo_cty o cp p prm.ty v hsc' hty'
      simp only [List.map_cons, hpc, C.Sem.argVals, ih]
      cases hpt : prm.ty with
      | int w =>
        rw [hpt] at hconv
        simp only [cty] at hconv ⊢
        simp only [ha, hconv]
      | bool =>
        rw [hpt] at hconv
        simp only [cty] at hconv ⊢
        simp only [ha, hconv]
      | arr _ _ => rw [hpt] at hsc'; simp [Ty.isScalar] at hsc'
      | record _ => rw [hpt] at hsc'; simp [Ty.isScalar] at hsc'

/-! ## Calls as C statements -/

/-- The C call `call`, from `cst` in the scope `cX`, returns `rv` in the state `cst'`. -/
def CallStep (cp : CProg) (call : CExpr) (cst : C.Sem.St) (cX : C.Sem.Env) (cst' : C.Sem.St) (rv : Option CVal) :
    Prop :=
  ∃ f args, C.Sem.asCall call = some (f, args) ∧ ∃ m, C.Sem.callC m cp cst cX f args = .ok cst' cX (.ret rv)

def CallTrap (cp : CProg) (call : CExpr) (cst : C.Sem.St) (cX : C.Sem.Env) (cst' : C.Sem.St) : Prop :=
  ∃ f args, C.Sem.asCall call = some (f, args) ∧ ∃ m, C.Sem.callC m cp cst cX f args = .trap cst'

section
variable {cp : CProg} {cst cst' cst'' : C.Sem.St} {cenv cenv' cenv'' : C.Sem.Env} {f : String} {args : List CExpr}

theorem exec_expr_call (m : Nat) (e : CExpr) (o : C.Sem.Out) (hc : C.Sem.asCall e = some (f, args))
    (hm : C.Sem.callC m cp cst cenv f args = .ok cst' cenv' o) :
    C.Sem.execS (m + 1) cp cst cenv (.expr e) = .ok cst' cenv' .normal := by
  simp only [C.Sem.execS, hc, hm]

theorem exec_expr_trap (m : Nat) (e : CExpr) (hc : C.Sem.asCall e = some (f, args))
    (hm : C.Sem.callC m cp cst cenv f args = .trap cst') :
    C.Sem.execS (m + 1) cp cst cenv (.expr e) = .trap cst' := by
  simp only [C.Sem.execS, hc, hm]

theorem exec_decl_call (m : Nat) (t : CTy) (x : String) (e : CExpr) (v v' : CVal)
    (hc : C.Sem.asCall e = some (f, args))
    (hm : C.Sem.callC m cp cst cenv f args = .ok cst' cenv' (.ret (some v)))
    (hconv : C.Sem.convTo cp t v = some v') :
    C.Sem.execS (m + 1) cp cst cenv (.decl t x (some e)) = .ok cst' ((x, v') :: cenv') .normal := by
  simp only [C.Sem.execS, hc, hm, hconv]

theorem exec_decl_trap (m : Nat) (t : CTy) (x : String) (e : CExpr) (hc : C.Sem.asCall e = some (f, args))
    (hm : C.Sem.callC m cp cst cenv f args = .trap cst') :
    C.Sem.execS (m + 1) cp cst cenv (.decl t x (some e)) = .trap cst' := by
  simp only [C.Sem.execS, hc, hm]

theorem exec_assign_call (m : Nat) (l r : CExpr) (v old v' : CVal) (loc : C.Sem.Loc)
    (hc : C.Sem.asCall r = some (f, args)) (hl : C.Sem.lval cp cst cenv l = some loc)
    (hm : C.Sem.callC m cp cst cenv f args = .ok cst' cenv' (.ret (some v)))
    (hl' : C.Sem.lval cp cst' cenv' l = some loc) (hrd : C.Sem.read cst' cenv' loc = some old)
    (hcv : C.Sem.convLike old v = some v') (hw : C.Sem.write cst' cenv' loc v' = some (cst'', cenv'')) :
    C.Sem.execS (m + 1) cp cst cenv (.assign l r) = .ok cst'' cenv'' .normal := by
  simp only [C.Sem.execS, hc, hl, hm, hl', hrd, hcv, hw, if_true]

theorem exec_assign_trap (m : Nat) (l r : CExpr) (loc : C.Sem.Loc) (hc : C.Sem.asCall r = some (f, args))
    (hl : C.Sem.lval cp cst cenv l = some loc) (hm : C.Sem.callC m cp cst cenv f args = .trap cst') :
    C.Sem.execS (m + 1) cp cst cenv (.assign l r) = .trap cst' := by
  simp only [C.Sem.execS, hc, hl, hm]

end

/-! ## The result of a call -/

/-- What `assignResult dst call …` yields: code that, when the call
returns `rv`, stores it as `Lang.Sem.storeResult` does; and that traps
when the call traps. -/
def StorePost (g : C.Env) (cp : CProg) (dst : Option Expr) (call : CExpr) (fnCall : Bool) (rty : Option Ty)
    (cs : CS) (_ : _root_.Unit) (cs' : CS) : Prop :=
  cs.tmp ≤ cs'.tmp ∧ ∃ code, cs'.out = cs.out ++ code.toArray ∧
    (∀ (st st' : Lang.Sem.St) (env : Lang.Sem.Env) (cst cst' : C.Sem.St) (cX : C.Sem.Env) (rv : Option Val)
        (rt : Option Ty) (il : Bool),
      SRel g st env cst cX → SRel g st' env cst' cX → Fresh cs.tmp cst cX → cst'.stack = cst.stack →
      CallStep cp call cst cX cst' (rv.map (cval g.opts)) →
      (∀ t, rty = some t → ∃ v, rv = some v ∧ HasTy g.prog t v) →
      (∀ d, dst = some d → (fnCall && readsIndex d) = false → ∀ v v', Lang.Sem.evalE g.prog st env d = some v →
        Lang.Sem.evalE g.prog st' env d = some v' → lpath g.prog st' env d = lpath g.prog st env d) →
      Sim g (fun nv => g.vars = nv ++ g.vars) cp rt il cs'.tmp code
        (Lang.Sem.storeResult g.prog st' env dst rv) env cst cX) ∧
    (∀ (st : Lang.Sem.St) (env : Lang.Sem.Env) (cst cst' : C.Sem.St) (cX : C.Sem.Env),
      SRel g st env cst cX → Fresh cs.tmp cst cX → CallTrap cp call cst cX cst' → Exec cp cst cX code (.trap cst'))

theorem store_ok {g : C.Env} {cp : CProg} {cs : CS} (U : Unit g.prog g.opts cp) (hg : EnvOK g)
    (dst : Option Expr) (call : CExpr) (fnCall : Bool) (rty : Option Ty) (hdst : DstOK g dst rty) :
    wpc (assignResult dst call ((rty.map (cty g.opts)).getD .void) fnCall) g
      (StorePost g cp dst call fnCall rty cs) cs := by
  unfold assignResult
  cases dst with
  | none =>
    simp only [wpc_emit]
    refine ⟨Nat.le_refl _, [.expr call], by simp, ?_, ?_⟩
    · intro st st' env cst cst' cX rv rt il hrel hrel' hfr hstk ⟨f, args, hac, m, hm⟩ _ _
      simp only [Lang.Sem.storeResult, Sim]
      refine ⟨cst', cX, Exec.one (exec_expr_call m call _ hac hm) trivial, ?_, trivial⟩
      exact After.mk0 (xs := []) rfl AllTmp.nil (Same.refl _) hrel' rfl hstk (hrel'.fresh hfr (Same.refl _))
    · intro st env cst cst' cX _ _ ⟨f, args, hac, m, hm⟩
      exact Exec.one (exec_expr_trap m call hac hm) trivial
  | some d =>
    obtain ⟨hpl, wd, t, hrt, htd, hsc⟩ := hdst
    subst hrt
    simp only [wpc_bind, wpc_get]
    refine wpc_mono (place_ok cp d g cs hg wd) ?_
    rintro ⟨cd, td, ptr⟩ cs1 ⟨pre, ho, _, Fd⟩
    by_cases hcond : (cs1.out.size == cs.out.size && !(fnCall && readsIndex d)) = true
    · rw [if_pos hcond, wpc_emit]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      obtain ⟨hsz, hnr⟩ := hcond
      have hpre : pre = [] := by
        have := congrArg Array.size ho
        simp only [Array.size_append, List.size_toArray] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hpre
      have hloc : ∀ {st env cst cX}, SRel g st env cst cX → Fresh cs.tmp cst cX →
          ∃ vold L, Lang.Sem.evalE g.prog st env d = some vold ∧ PlaceLoc cp cst cX cd ptr (cval g.opts vold) L ∧
            Rooted g cp d L st env cst cX := by
        intro st env cst cX hrel hfr
        obtain ⟨hok, htr⟩ := Fd.2 st env cst cX (hrel.erel U) hfr
        have hk : EOk g d st env := by
          by_cases hk : EOk g d st env
          · exact hk
          · exact (traps_nil_false (htr hk)).elim
        obtain ⟨xs, ht, hruns, hres⟩ := hok hk
        have hxs := runs_nil_eq hruns
        obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨L, hL, hroot⟩ := hres vold hvold
        rw [hxs] at hL hroot
        exact ⟨vold, L, hvold, hL, hroot⟩
      refine ⟨Fd.1, [.assign cd call], by simp [ho], ?_, ?_⟩
      · intro st st' env cst cst' cX rv rt il hrel hrel' hfr hstk ⟨f, args, hac, m, hm⟩ hrv hq
        obtain ⟨v, rfl, hv⟩ := hrv t rfl
        obtain ⟨vold, L, hvold, hL, hroot⟩ := hloc hrel hfr
        obtain ⟨vold', L', hvold', hL', hroot'⟩ := hloc hrel' (hrel'.fresh hfr (Same.refl _))
        obtain ⟨x, q, hlq⟩ := lpath_some _ _ _ d vold hpl hvold
        have hlq' : lpath g.prog st' env d = some (x, q) := by rw [hq d rfl hnr vold vold' hvold hvold']; exact hlq
        have eL := rooted_loc U hrel hroot hlq htd hvold
        have eL' := rooted_loc U hrel' hroot' hlq' htd hvold'
        have hLL : L' = L := by rw [eL, eL']; simp only [xloc, hstk]
        subst hLL
        have hsv := cval_scalar g.opts g.prog t vold hsc
          (evalE_hasTy g st env (hrel.erel U).typed d vold t wd hvold htd)
        have hlv := hL.lval_scalar hsv
        obtain ⟨st'', env'', cst'', cenv'', hasg, hlv', hrd', hcl', hwr', hrel2, hsame, hlen, hstk2⟩ :=
          assign_sim U hrel' d cd ptr v vold' t hsc htd wd hpl hv hvold' L' hL' hroot'
        simp only [Lang.Sem.storeResult, hasg, Sim]
        refine ⟨cst'', cenv'',
          Exec.one (exec_assign_call m cd call _ _ _ L' hac hlv hm hlv' hrd' hcl' hwr') trivial, ?_, trivial⟩
        exact After.mk0 (xs := []) rfl AllTmp.nil hsame hrel2 hlen (hstk2.trans hstk)
          (hrel2.fresh (hfr.mono Fd.1) hsame)
      · intro st env cst cst' cX hrel hfr ⟨f, args, hac, m, hm⟩
        obtain ⟨vold, L, hvold, hL, hroot⟩ := hloc hrel hfr
        have hsv := cval_scalar g.opts g.prog t vold hsc
          (evalE_hasTy g st env (hrel.erel U).typed d vold t wd hvold htd)
        exact Exec.one (exec_assign_trap m cd call L hac (hL.lval_scalar hsv) hm) trivial
    · rw [if_neg hcond]
      simp only [wpc_bind, wpc_set, wpc_fresh, wpc_emit]
      refine wpc_mono (place_ok cp d g _ hg wd) ?_
      rintro ⟨cd2, td2, ptr2⟩ cs2 ⟨pre2, ho2, _, Fd2⟩
      have h12 : cs.tmp + 1 ≤ cs2.tmp := Fd2.1
      refine ⟨Nat.le_trans (Nat.le_succ _) h12,
        [.decl (cty g.opts t) (tmpName cs.tmp) (some call)] ++ (pre2 ++ [.assign cd2 (.var (tmpName cs.tmp))]),
        by simp [ho2], ?_, ?_⟩
      · intro st st' env cst cst' cX rv rt il hrel hrel' hfr hstk ⟨f, args, hac, m, hm⟩ hrv hq
        obtain ⟨v, rfl, hv⟩ := hrv t rfl
        have e1 := exec_decl_call (cp := cp) m (cty g.opts t) (tmpName cs.tmp) call _ _ hac hm
          (convTo_cty g.opts cp g.prog t v hsc hv)
        have hrelX : SRel g st' env cst' ((tmpName cs.tmp, cval g.opts v) :: cX) := ⟨.tmp _ _ hrel'.1, hrel'.2⟩
        have hfrX : Fresh (cs.tmp + 1) cst' ((tmpName cs.tmp, cval g.opts v) :: cX) :=
          (hrel'.fresh hfr (Same.refl _)).cons_tmp _
        obtain ⟨hok, htr⟩ := Fd2.2 st' env cst' _ (hrelX.erel U) hfrX
        simp only [Lang.Sem.storeResult]
        by_cases hk : EOk g d st' env
        · obtain ⟨xs, ht, hruns, hres⟩ := hok hk
          obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hk
          obtain ⟨L, hL, hroot⟩ := hres vold hvold
          obtain ⟨st'', env'', cst'', cenv'', hasg, hlv, hrd, hcl, hwr, hrel2, hsame, hlen, hstk2⟩ :=
            assign_sim U (hrelX.temps ht) d cd2 ptr2 v vold t hsc htd wd hpl hv hvold L hL hroot
          have hx : C.Sem.evalC cp cst' (xs ++ (tmpName cs.tmp, cval g.opts v) :: cX) (.var (tmpName cs.tmp))
              = some (cval g.opts v) := C.Sem.evalC_ext (hfrX.ext ht) _ (evalC_var_head _ _)
          simp only [hasg, Sim]
          refine ⟨cst'', cenv'', (Exec.one e1 trivial).seq (hruns.exec (Exec.one
            (exec_assign 0 cd2 (.var (tmpName cs.tmp)) _ _ _ L cst'' cenv'' rfl hx hlv hrd hcl hwr) trivial)), ?_,
            trivial⟩
          have hs' : Same ((xs ++ [(tmpName cs.tmp, cval g.opts v)]) ++ cX) cenv'' := by simpa using hsame
          have hall : AllTmp (xs ++ [(tmpName cs.tmp, cval g.opts v)]) := by
            intro y hy
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | hy
            · exact ht.allTmp y hy
            · exact ⟨cs.tmp, hy⟩
          exact After.mk0 rfl hall hs' hrel2 hlen (hstk2.trans hstk) (hrel2.fresh (hfrX.append ht h12) hsame)
        · have hnone : Lang.Sem.assign g.prog st' env d v = none := by
            cases h : Lang.Sem.assign g.prog st' env d v with
            | none => rfl
            | some r' =>
              obtain ⟨u, hu, _⟩ := update_some g.prog st' env d _ r' h
              exact absurd (by simp [EOk, hu]) hk
          simp only [hnone, Sim]
          exact ⟨cst', (Exec.one e1 trivial).seq ((htr hk).exec _), hrel'.2.world⟩
      · intro st env cst cst' cX hrel hfr ⟨f, args, hac, m, hm⟩
        exact (Exec.one (exec_decl_trap m _ _ call hac hm) trivial).stop _ trivial

/-! ## Effects -/

theorem valsTy_nil {p : Prog} {vs : List Val} (h : ValsTy p [] vs) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons _ _ => exact h.elim

theorem valsTy_one {p : Prog} {t : Ty} {vs : List Val} (h : ValsTy p [t] vs) : ∃ v, vs = [v] ∧ HasTy p t v := by
  cases vs with
  | nil => exact h.elim
  | cons v r =>
    obtain ⟨hv, _, hr⟩ := h
    rw [valsTy_nil hr]
    exact ⟨v, rfl, hv⟩

theorem valsTy_two {p : Prog} {t1 t2 : Ty} {vs : List Val} (h : ValsTy p [t1, t2] vs) :
    ∃ v1 v2, vs = [v1, v2] ∧ HasTy p t1 v1 ∧ HasTy p t2 v2 := by
  cases vs with
  | nil => exact h.elim
  | cons v r =>
    obtain ⟨hv, _, hr⟩ := h
    obtain ⟨v2, rfl, hv2⟩ := valsTy_one hr
    exact ⟨v, v2, rfl, hv, hv2⟩

/-- **The runtime's functions are the effects.** -/
theorem eff_sim {p : Prog} {o : Opts} {cp : CProg} (U : Unit p o cp) (e : Effect) (st : Lang.Sem.St)
    (cst : C.Sem.St) (vs : List Val) (hg : GRel p o st cst) (hty : ValsTy p e.sig.1 vs) :
    ∃ cst', C.Sem.effect cp cst (effectCall e) (vs.map (cval o))
        = some ((Lang.Sem.effect p st e vs).1.map (cval o), cst') ∧
      GRel p o (Lang.Sem.effect p st e vs).2 cst' ∧ cst'.stack = cst.stack ∧
      (Lang.Sem.effect p st e vs).2.globals = st.globals ∧
      (∀ t, e.sig.2 = some t → ∃ v, (Lang.Sem.effect p st e vs).1 = some v ∧ HasTy p t v) := by
  have hw := hg.world
  cases e with
  | inputNext =>
    refine ⟨{ cst with world := st.world.next.2 }, ?_, ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Width.bits]
    · intro t ht
      simp only [Effect.sig, Option.some.injEq] at ht
      subst ht
      exact ⟨_, rfl, rfl, by simpa [Width.bits] using UInt16.toNat_lt _⟩
  | ringPop =>
    refine ⟨{ cst with world := st.world.next.2 }, ?_, ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Width.bits]
    · intro t ht
      simp only [Effect.sig, Option.some.injEq] at ht
      subst ht
      exact ⟨_, rfl, rfl, by simpa [Width.bits] using UInt16.toNat_lt _⟩
  | inputFrame =>
    refine ⟨{ cst with world := st.world.nextFramed.2 }, ?_, ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Width.bits]
    · intro t ht
      simp only [Effect.sig, Option.some.injEq] at ht
      subst ht
      exact ⟨_, rfl, rfl, by simpa [Width.bits] using UInt16.toNat_lt _⟩
  | outByte =>
    obtain ⟨v, rfl, hv⟩ := valsTy_one hty
    obtain ⟨x, rfl, hx⟩ := hasTy_int hv
    refine ⟨{ cst with world := { st.world with frame := st.world.frame.push x.toNat.toUInt8 } }, ?_,
      ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · have hx' : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hx)
      simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Val.toNat, hx', Width.bits]
    · intro t ht; simp [Effect.sig] at ht
  | outEnd =>
    refine ⟨{ cst with world := { (st.world.emit (.tx st.world.frame)) with frame := .empty } }, ?_,
      ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Width.bits]
    · intro t ht; simp [Effect.sig] at ht
  | drop =>
    obtain ⟨v, rfl, hv⟩ := valsTy_one hty
    obtain ⟨x, rfl, hx⟩ := hasTy_int hv
    refine ⟨{ cst with world := st.world.emit (.drop (p.dropReasons.getD x.toNat s!"code-{x.toNat}")) }, ?_,
      ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · have hx' : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hx)
      simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Val.toNat, hx', U.drops]
    · intro t ht; simp [Effect.sig] at ht
  | note =>
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := valsTy_two hty
    obtain ⟨x, rfl, hx⟩ := hasTy_int hv1
    obtain ⟨y, rfl, hy⟩ := hasTy_int hv2
    refine ⟨{ cst with world := (Lang.Sem.effect p st .note [.int .w8 x, .int .w32 y]).2.world }, ?_,
      ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · have hx' : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hx)
      have hy' : y.toNat % 4294967296 = y.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hy)
      simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Val.toNat, hx', hy', U.notes]
    · intro t ht; simp [Effect.sig] at ht
  | mmioRead32 =>
    obtain ⟨v, rfl, hv⟩ := valsTy_one hty
    obtain ⟨x, rfl, hx⟩ := hasTy_int hv
    refine ⟨cst, ?_, hg, rfl, rfl, ?_⟩
    · have hx' : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hx)
      simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Val.toNat, hx', Width.bits]
    · intro t ht
      simp only [Effect.sig, Option.some.injEq] at ht
      subst ht
      exact ⟨_, rfl, rfl, by simpa [Width.bits] using UInt32.toNat_lt _⟩
  | mmioWrite32 =>
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := valsTy_two hty
    obtain ⟨x, rfl, hx⟩ := hasTy_int hv1
    obtain ⟨y, rfl, hy⟩ := hasTy_int hv2
    refine ⟨{ cst with world := { st.world with mmio := st.world.mmio.insert x.toNat.toUInt32 y.toNat.toUInt32 } },
      ?_, ⟨hg.glob, hg.gtmp, rfl⟩, rfl, rfl, ?_⟩
    · have hx' : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hx)
      have hy' : y.toNat % 4294967296 = y.toNat := Nat.mod_eq_of_lt (by simpa [Width.bits] using hy)
      simp [C.Sem.effect, Lang.Sem.effect, effectCall, hw, Val.toNat, hx', hy']
    · intro t ht; simp [Effect.sig] at ht

theorem asCall_effect (e : Effect) (cargs : List CExpr) :
    C.Sem.asCall (.call (effectCall e) cargs) = some (effectCall e, cargs) := by
  cases e <;> simp [C.Sem.asCall, C.Sem.helper, effectCall]

theorem effect_not_trap (e : Effect) : (effectCall e == "ember_trap") = false := by
  cases e <;> simp [effectCall]

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem eff_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (dst : Option Expr) (e : Effect) (args : List Expr)
    (hw : WTS rt il g (.eff dst e args)) :
    wpc (C.stmt (.eff dst e args)) g (SPost N rt il g (.eff dst e args) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_pure]
  obtain ⟨hargs, hdst⟩ := hw
  refine wpc_mono (exprs_ok cp args e.sig.1 g cs hg hargs) ?_
  rintro cargs cs1 ⟨pre, ho, Fa⟩
  refine wpc_mono (store_ok U hg dst (.call (effectCall e) cargs) false e.sig.2 hdst) ?_
  rintro ⟨⟩ cs2 ⟨htmp, code, ho2, hstore, _⟩
  refine ⟨rfl, Nat.le_trans Fa.1 htmp, pre ++ code, by simp [ho, ho2], fun k hk st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    obtain ⟨hok, htrap⟩ := Fa.2 st env cst cenv (hrel.erel U) hfr
    simp only [Lang.Sem.execS]
    cases hvs : Lang.Sem.evalArgs g.prog st env args with
    | none =>
      simp only [Sim]
      exact ⟨cst, (htrap (by simp [ArgsOk, hvs])).exec _, hrel.2.world⟩
    | some vs =>
      simp only
      obtain ⟨xs, ht, hruns, hres⟩ := hok (by simp [ArgsOk, hvs])
      have hcs := hres vs hvs
      have htys := args_typed g st env (hrel.erel U).typed _ _ vs hargs hvs
      obtain ⟨cst', heff, hg', hstk, hglob, hrv⟩ := eff_sim U e st cst vs hrel.2 htys
      have hstep : CallStep cp (.call (effectCall e) cargs) cst (xs ++ cenv) cst'
          ((Lang.Sem.effect g.prog st e vs).1.map (cval g.opts)) := by
        refine ⟨effectCall e, cargs, asCall_effect e cargs, 1, ?_⟩
        rw [C.Sem.callC]
        simp only [effect_not_trap, Bool.false_eq_true, if_false, U.noeff e, hcs, heff]
      exact Sim.prefix hruns ht.allTmp (hstore st _ env cst cst' (xs ++ cenv) _ rt il (hrel.temps ht)
        ⟨(hrel.temps ht).1, hg'⟩ (hfr.append ht Fa.1) hstk hstep hrv
        (fun d _ _ _ _ _ _ => lpath_congr _ _ _ _ hglob d))

end

/-! ## Calls of Ember functions -/

/-- What a function may end with. -/
def FnOut (p : Prog) (rt : Option Ty) (out : Lang.Sem.Out) : Prop :=
  match rt with
  | none => ∀ v, out ≠ .ret (some v)
  | some t => ∃ v, out = .ret (some v) ∧ HasTy p t v ∧ t.isScalar = true

/-- **A compiled function does what its body does**, with `k` units of fuel on the Ember side. -/
def FnSim (p : Prog) (o : Opts) (cp : CProg) (k : Nat) : Prop :=
  ∀ f fd cfd, p.fn? f = some fd → compileFn p o fd = .ok cfd →
    ∀ (st : Lang.Sem.St) (cst : C.Sem.St) (vs : List Val), GRel p o st cst → ValsTy p (fd.params.map (·.ty)) vs →
    match Lang.Sem.execB k p st ((fd.params.map (·.name)).zip vs) fd.body with
    | .ok st' _ out =>
      ∃ m cst' cenv', C.Sem.execB m cp cst ((cfd.params.map (·.2)).zip (vs.map (cval o))) cfd.body
          = .ok cst' cenv' (cout o out) ∧
        GRel p o st' cst' ∧ cst'.stack = cst.stack ∧ FnOut p fd.ret out
    | .trap st' =>
      ∃ m cst', C.Sem.execB m cp cst ((cfd.params.map (·.2)).zip (vs.map (cval o))) cfd.body = .trap cst' ∧
        cst'.world = st'.world
    | .fuel => True

/-- The value a call yields. -/
def retVal : Lang.Sem.Out → Option Val
  | .ret v => v
  | _ => none

theorem compileFn_shape {p : Prog} {o : Opts} {fd : Fn} {cfd : CFn} (h : compileFn p o fd = .ok cfd) :
    cfd.name = o.fnName fd.name ∧ cfd.ret = (fd.ret.map (cty o)).getD .void ∧
    cfd.params = fd.params.map (paramC o) ∧
    ∃ cs', ((block fd.body).run (fnEnv p o fd)).run {} = .ok ((), cs') ∧
      cfd.body = (if o.lines && fd.span.line > 0 then [CStmt.line fd.span.line fd.span.file] else []) ++
        fd.params.map (fun prm => CStmt.expr (.cast .void (.var (localName prm.name)))) ++
        voidUnread (declared fd.body) cs'.out.toList := by
  unfold compileFn at h
  split at h
  · cases h
  · rename_i cs' hrun
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, cs', hrun, rfl⟩

theorem call_sim {g : C.Env} {cp : CProg} (U : Unit g.prog g.opts cp) (j : Nat)
    (H : FnSim g.prog g.opts cp j) {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St} {cX : C.Sem.Env}
    (hrel : SRel g st env cst cX) (f : String) (fd : Fn) (hfd : g.prog.fn? f = some fd)
    (hp : ∀ prm, prm ∈ fd.params → prm.byRef = false ∧ prm.ty.isScalar = true) (cargs : List CExpr)
    (vs : List Val) (hcs : C.Sem.evalCs cp cst cX cargs = some (vs.map (cval g.opts)))
    (hty : ValsTy g.prog (fd.params.map (·.ty)) vs) :
    match Lang.Sem.execB j g.prog st ((fd.params.map (·.name)).zip vs) fd.body with
    | .ok st' _ out =>
      ∃ cst', CallStep cp (.call (g.opts.fnName f) cargs) cst cX cst' ((retVal out).map (cval g.opts)) ∧
        SRel g st' env cst' cX ∧ cst'.stack = cst.stack ∧
        (∀ t, fd.ret = some t → ∃ v, retVal out = some v ∧ HasTy g.prog t v)
    | .trap st' => ∃ cst', CallTrap cp (.call (g.opts.fnName f) cargs) cst cX cst' ∧ cst'.world = st'.world
    | .fuel => True := by
  obtain ⟨cfd, hfind, hcomp⟩ := U.fns f fd hfd
  obtain ⟨_, hret, hparams, _⟩ := compileFn_shape hcomp
  have hG : GRel g.prog g.opts st { cst with stack := cX :: cst.stack } := ⟨hrel.2.glob, hrel.2.gtmp, hrel.2.world⟩
  have hH := H f fd cfd hfd hcomp st _ vs hG hty
  have hav : C.Sem.argVals cp cst cX cfd.params cargs = some (vs.map (cval g.opts)) := by
    rw [hparams]; exact argVals_ok g.opts cp g.prog cst cX fd.params cargs vs hp hcs hty
  have hac : C.Sem.asCall (.call (g.opts.fnName f) cargs) = some (g.opts.fnName f, cargs) := by
    simp [C.Sem.asCall, U.hyg.fh]
  cases hR : Lang.Sem.execB j g.prog st ((fd.params.map (·.name)).zip vs) fd.body with
  | fuel => trivial
  | trap st' =>
    rw [hR] at hH
    obtain ⟨m, cst', hm, hw⟩ := hH
    refine ⟨cst', ⟨_, _, hac, m + 1, ?_⟩, hw⟩
    rw [C.Sem.callC]
    simp only [U.hyg.ft, Bool.false_eq_true, if_false, hfind, hav, hm]
  | ok st' envL out =>
    rw [hR] at hH
    obtain ⟨m, cst', cenv', hm, hG', hstk, hout⟩ := hH
    refine ⟨{ cst' with stack := cst.stack }, ⟨_, _, hac, m + 1, ?_⟩,
      ⟨hrel.1, ⟨hG'.glob, hG'.gtmp, hG'.world⟩⟩, rfl, ?_⟩
    · rw [C.Sem.callC]
      simp only [U.hyg.ft, Bool.false_eq_true, if_false, hfind, hav, hm, hstk]
      cases hfr : fd.ret with
      | none =>
        rw [hfr] at hout
        cases out with
        | normal => rfl
        | brk => rfl
        | ret v =>
          cases v with
          | none => rfl
          | some v => exact absurd rfl (hout v)
      | some t =>
        rw [hfr] at hout
        obtain ⟨v, rfl, hv, hsc⟩ := hout
        have hc := convTo_cty g.opts cp g.prog t v hsc hv
        simp only [cout, Option.map_some, hret, hfr, Option.getD_some, hc, retVal]
    · intro t ht
      rw [ht] at hout
      obtain ⟨v, rfl, hv, _⟩ := hout
      exact ⟨v, rfl, hv⟩

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem call_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (hP : ProgOK g.prog g.opts)
    (H : ∀ j, j < N → FnSim g.prog g.opts cp j) (dst : Option Expr) (f : String) (args : List Expr)
    (hw : WTS rt il g (.call dst f args)) :
    wpc (C.stmt (.call dst f args)) g (SPost N rt il g (.call dst f args) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read]
  obtain ⟨fd, hfd, hargs, hdst⟩ := hw
  simp only [hfd, wpc_bind, wpc_pure]
  have hfok := hP f fd hfd
  rw [callArgs_eq g fd.params args (fun prm h => (hfok.params prm h).1) hargs]
  refine wpc_mono (exprs_ok cp args _ g cs hg hargs) ?_
  rintro cargs cs1 ⟨pre, ho, Fa⟩
  refine wpc_mono (store_ok U hg dst (.call (g.opts.fnName f) cargs) true fd.ret hdst) ?_
  rintro ⟨⟩ cs2 ⟨htmp, code, ho2, hstore, htrapc⟩
  refine ⟨rfl, Nat.le_trans Fa.1 htmp, pre ++ code, by simp [ho, ho2], fun k hk st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    obtain ⟨hok, htrap⟩ := Fa.2 st env cst cenv (hrel.erel U) hfr
    simp only [Lang.Sem.execS, hfd]
    cases hvs : Lang.Sem.evalArgs g.prog st env args with
    | none =>
      simp only [Sim]
      exact ⟨cst, (htrap (by simp [ArgsOk, hvs])).exec _, hrel.2.world⟩
    | some vs =>
      simp only
      obtain ⟨xs, ht, hruns, hres⟩ := hok (by simp [ArgsOk, hvs])
      have hcs := hres vs hvs
      have htys := args_typed g st env (hrel.erel U).typed _ _ vs hargs hvs
      have hc := call_sim U j (H j (by omega)) (hrel.temps ht) f fd hfd hfok.params cargs vs hcs htys
      cases hR : Lang.Sem.execB j g.prog st ((fd.params.map (·.name)).zip vs) fd.body with
      | fuel => trivial
      | trap st' =>
        rw [hR] at hc
        obtain ⟨cst', hct, hw'⟩ := hc
        exact ⟨cst', hruns.exec (htrapc st env cst cst' (xs ++ cenv) (hrel.temps ht) (hfr.append ht Fa.1) hct), hw'⟩
      | ok st' envL out =>
        rw [hR] at hc
        obtain ⟨cst', hstep, hrel', hstk, hrv⟩ := hc
        simp only [copyBack_noref g.prog envL fd.params args st' env (fun prm h => (hfok.params prm h).1)]
        show Sim g (fun nv => g.vars = nv ++ g.vars) cp rt il cs2.tmp (pre ++ code)
          (Lang.Sem.storeResult g.prog st' env dst (retVal out)) env cst cenv
        refine Sim.prefix hruns ht.allTmp (hstore st st' env cst cst' (xs ++ cenv) (retVal out) rt il
          (hrel.temps ht) hrel' (hfr.append ht Fa.1) hstk hstep hrv ?_)
        intro d hd hnr v v' hv hv'
        subst hd
        obtain ⟨_, wd, t, _, htd, _⟩ := hdst
        simp only [Bool.true_and] at hnr
        exact lpath_stable g st st' env env ((hrel.temps ht).erel U).typed (hrel'.erel U).typed d t v v' hnr wd htd hv
          hv'

end

end Ember.Proof.CSim
