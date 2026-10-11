import Ember.Proof.IRBlock

/-!
# Ember.Proof.IRSim — every statement, and every function (plan M7.1)

`stmt_ok`/`block_ok`: the instructions the lowering emits for a
well-typed statement do, from related states, what `Lang.Sem.execS`
does, given that the functions it calls are simulated by their code for
less fuel.  `fn_sim` closes the induction: the code of every function
simulates the function.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK IsPlace NoWriteL
  ReturnsL NoRef hasTy_zero returns_all)

/-! ## A declaration and the call that gives it its value, on the Ember side -/

/-- An expression that does not mention `x` has the same value without it. -/
theorem evalE_skip (p : Prog) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) (v : Val) :
    ∀ (e : Expr), mentions x e = false → Lang.Sem.evalE p lst ((x, v) :: env) e = Lang.Sem.evalE p lst env e
  | .lit _ _, _ => by cases ‹Option Width› <;> rfl
  | .blit _, _ => rfl
  | .var y, h => by
    simp only [mentions] at h
    have hyx : (y == x) = false := by
      cases hc : y == x
      · rfl
      · rw [beq_iff_eq] at hc; subst hc; simp at h
    simp only [Lang.Sem.evalE, Lang.Sem.lookup, List.lookup, hyx]
  | .field b f, h => by
    simp only [mentions] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v b h]
  | .index b i, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v b h.1, evalE_skip p lst env x v i h.2]
  | .bin op a b, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v a h.1, evalE_skip p lst env x v b h.2]
  | .un op a, h => by
    simp only [mentions] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v a h]
  | .cast w a, h => by
    simp only [mentions] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v a h]
  | .cond c a b, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    simp only [Lang.Sem.evalE, evalE_skip p lst env x v c h.1.1, evalE_skip p lst env x v a h.1.2,
      evalE_skip p lst env x v b h.2]

theorem evalArgs_skip (p : Prog) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (x : String) (v : Val) :
    ∀ (args : List Expr), args.any (mentions x) = false →
    Lang.Sem.evalArgs p lst ((x, v) :: env) args = Lang.Sem.evalArgs p lst env args
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [Lang.Sem.evalArgs, evalE_skip p lst env x v a h.1, evalArgs_skip p lst env x v as h.2]

/-- A statement behind its position marks. -/
theorem execS_core (p : Prog) : ∀ (st : Stmt) (n : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env),
    Lang.Sem.execS n p lst env st = .fuel ∨
      ∃ j, j ≤ n ∧ 0 < j ∧ Lang.Sem.execS n p lst env st = Lang.Sem.execS j p lst env st.core
  | .at sp st, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k =>
      have : Lang.Sem.execS (k + 1) p lst env (.at sp st) = Lang.Sem.execS k p lst env st := by
        simp only [Lang.Sem.execS]
      rw [this]
      rcases execS_core p st k lst env with h | ⟨j, hj, hj0, h⟩
      · exact .inl h
      · exact .inr ⟨j, by omega, hj0, by rw [h]; rfl⟩
  | .decl x ty init, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .assign l r, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .ite c t e, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .forRange x w lo hi b, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .loop m b, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .brk, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .ret v, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .call d g a, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩
  | .eff d e a, n, lst, env => by
    cases n with
    | zero => exact .inl (by rw [Lang.Sem.execS])
    | succ k => exact .inr ⟨k + 1, Nat.le_refl _, by omega, rfl⟩

/-- What `declCall?` finds. -/
theorem declCall_spec {st s2 : Stmt} {x : String} {ty : Ty} {i : Init} (h : declCall? st s2 = some (x, ty, i)) :
    st.core = .decl x ty none ∧ (initArgs i).any (mentions x) = false ∧
      ((∃ g args, i = .call g args ∧ s2.core = .call (some (.var x)) g args) ∨
       (∃ e args, i = .eff e args ∧ s2.core = .eff (some (.var x)) e args)) := by
  unfold declCall? at h
  split at h
  · rename_i x' ty' y g args h1 h2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, hxy⟩, hm⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      subst hxy
      exact ⟨h1, hm, .inl ⟨g, args, rfl, h2⟩⟩
    · cases h
  · rename_i x' ty' y e args h1 h2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, hxy⟩, hm⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      subst hxy
      exact ⟨h1, hm, .inr ⟨e, args, rfl, h2⟩⟩
    · cases h
  · cases h

/-- **The two statements as one**: the arguments, the invocation, and
the variable declared with its result. -/
theorem execL_pair (lp : Prog) (st s2 : Stmt) (rest : List Stmt) (x : String) (ty : Ty) (i : Init)
    (hdc : declCall? st s2 = some (x, ty, i))
    (hcall : ∀ g args, i = .call g args → ∃ fd, lp.fn? g = some fd ∧ ∀ prm, prm ∈ fd.params → prm.byRef = false)
    (n : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) :
    Lang.Sem.execL n lp lst env (st :: s2 :: rest) = .fuel ∨
      ∃ k m, k < m ∧ m < n ∧ Lang.Sem.execL n lp lst env (st :: s2 :: rest) =
        match Lang.Sem.evalArgs lp lst env (initArgs i) with
        | none => .trap lst
        | some vs =>
          match initAct lp i k lst vs with
          | .fuel => .fuel
          | .trap lst' => .trap lst'
          | .ok v lst' => Lang.Sem.execL m lp lst' ((x, v.getD (zeroOf lp ty)) :: env) rest := by
  obtain ⟨hcore, hment, hi⟩ := declCall_spec hdc
  cases n with
  | zero => exact .inl (by rw [Lang.Sem.execL])
  | succ n =>
    rw [Lang.Sem.execL]
    rcases execS_core lp st n lst env with h | ⟨j, hj, hj0, h⟩
    · exact .inl (by rw [h])
    · rw [h, hcore]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Lang.Sem.execS]
      cases n with
      | zero => omega
      | succ m =>
        rw [Lang.Sem.execL]
        rcases execS_core lp s2 m lst ((x, zeroOf lp ty) :: env) with h2 | ⟨j2, hj2, hj20, h2⟩
        · exact .inl (by rw [h2])
        · obtain ⟨k, rfl⟩ : ∃ k, j2 = k + 1 := ⟨j2 - 1, by omega⟩
          refine .inr ⟨k, m, by omega, by omega, ?_⟩
          rw [h2]
          -- the result goes to the new variable
          have hstore : ∀ (lst' : Lang.Sem.St) (v : Option Val),
              Lang.Sem.storeResult lp lst' ((x, zeroOf lp ty) :: env) (some (.var x)) v =
                .ok lst' ((x, v.getD (zeroOf lp ty)) :: env) .normal := by
            intro lst' v
            cases v with
            | none => rfl
            | some xv => simp [Lang.Sem.storeResult, Lang.Sem.assign, Lang.Sem.update, List.lookup, Lang.Sem.setFirst]
          rcases hi with ⟨g, args, rfl, hs2⟩ | ⟨e, args, rfl, hs2⟩
          · obtain ⟨fd, hfd, hnr⟩ := hcall g args rfl
            rw [hs2, execS_call lp k lst _ _ g args fd hfd hnr, evalArgs_skip lp lst env x _ args hment]
            simp only [initArgs, initAct]
            cases Lang.Sem.evalArgs lp lst env args with
            | none => rfl
            | some vs =>
              simp only []
              cases Lang.Sem.call k lp lst g vs with
              | fuel => rfl
              | trap lst' => rfl
              | ok v lst' => simp only [hstore]
          · rw [hs2, execS_eff lp k lst _ _ e args, evalArgs_skip lp lst env x _ args hment]
            simp only [initArgs, initAct]
            cases Lang.Sem.evalArgs lp lst env args with
            | none => rfl
            | some vs => simp only [hstore]

/-! ## Statements, one after the other -/

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

theorem at_ok {N : Nat} {rt : Option Ty} {E E' : Env} {sp : Span} {st : Stmt} {s s' : LS}
    (h : SPost c f sF N rt E st s E' s') : SPost c f sF N rt E (.at sp st) s E' s' := by
  obtain ⟨hx, hE', hcur, hsem⟩ := h
  refine ⟨hx, hE', hcur, ?_⟩
  intro n lst env ist tmps hn hxF hrel hsz hend
  cases n with
  | zero => rw [Lang.Sem.execS]; trivial
  | succ k =>
    have : Lang.Sem.execS (k + 1) E.prog lst env (.at sp st) = Lang.Sem.execS k E.prog lst env st := by
      simp only [Lang.Sem.execS]
    rw [this]
    exact hsem k lst env ist tmps (by omega) hxF hrel hsz hend

/-- The environment after a statement: the one before, with at most one more variable, at `off`. -/
theorem envAfter_eq (E : Env) (off : Nat) : ∀ (st : Stmt), ∃ pre, envAfter E off st = { E with vars := pre ++ E.vars } ∧
    (∀ o, o < off → InVars E.prog (pre ++ E.vars) o → InVars E.prog E.vars o) ∧
    (∀ x info, (x, info) ∈ pre → ∃ sl, info.at_ = .static sl)
  | .at _ st => envAfter_eq E off st
  | .decl x ty _ => by
    refine ⟨[(x, { ty, at_ := .static { area := .frame E.fn, off } })], rfl, fun o ho hin => ?_, fun y info hm => ?_⟩
    · obtain ⟨y, info, sl, hmem, hat, h1, h2⟩ := hin
      rcases List.mem_cons.mp hmem with he | hr
      · cases he
        simp only [Storage.static.injEq] at hat
        subst hat
        simp only at h1
        omega
      · exact ⟨y, info, sl, hr, hat, h1, h2⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨_, rfl⟩ := hm
      exact ⟨_, rfl⟩
  | .assign _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .ite _ _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .forRange _ _ _ _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .loop _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .brk => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .ret _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .call _ _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩
  | .eff _ _ _ => ⟨[], rfl, fun _ _ h => h, fun _ _ h => by simp at h⟩

theorem EnvOK.append {E : Env} (h : EnvOK E) (pre : List (String × VarInfo))
    (hp : ∀ x info, (x, info) ∈ pre → ∃ sl, info.at_ = .static sl) : EnvOK { E with vars := pre ++ E.vars } := by
  intro x info hx
  simp only [List.lookup_append] at hx
  cases hl : pre.lookup x with
  | some i =>
    simp only [hl, Option.some_or, Option.some.injEq] at hx
    subst hx
    exact hp x i (lookup_mem _ _ _ hl)
  | none =>
    simp only [hl, Option.none_or] at hx
    exact h x info hx

/-- How a statement ends, as a list of statements does. -/
theorem SOut.toL {rt : Option Ty} {E : Env} {cur cur' : Nat} {env : Lang.Sem.Env} {ist : St} {tmps : Array Nat}
    {pc pc' pc'' : Nat} {lst' : Lang.Sem.St} {env' : Lang.Sem.Env} {o : Lang.Sem.Out}
    {pre : List (String × VarInfo)}
    (h : SOut c f rt E cur ist tmps pc lst' env' o { E with vars := pre ++ E.vars } cur' pc')
    (hcur : cur ≤ cur') (hlen : env.length = E.vars.length) (hpc : o = .normal → pc'' = pc') :
    LOut c f rt E cur env ist tmps pc lst' env' o pc'' := by
  cases o with
  | normal =>
    obtain ⟨ist', t', r, sz, hrel', hkeep⟩ := h
    have hl := hrel'.loc.1.length
    rw [hpc rfl]
    exact ⟨ist', t', pre, cur', r, sz, hrel', by simp only [List.length_append] at hl; omega, hcur, hkeep⟩
  | brk =>
    obtain ⟨l, i, ist', t', hle, hi, r, sz, hrel', hkeep⟩ := h
    have hl := hrel'.loc.1.length
    exact ⟨l, i, ist', t', pre, cur', hle, hi, r, sz, hrel', by simp only [List.length_append] at hl; omega, hcur,
      hkeep⟩
  | ret v => exact h

/-- A statement (or two that are one), then the rest. -/
theorem LOut.cons {rt : Option Ty} {E : Env} {pre1 : List (String × VarInfo)} {cur cur1 : Nat} (hc : cur ≤ cur1)
    (hv : ∀ o, o < cur → InVars E.prog (pre1 ++ E.vars) o → InVars E.prog E.vars o) {ist ist1 : St}
    {tmps t1 : Array Nat} {pc pc1 : Nat} (r : Reach c f pc tmps ist pc1 t1 ist1) (sz : t1.size = tmps.size)
    (hk : Keep c E cur ist.mem ist1.mem) {env env1 : Lang.Sem.Env} (hlen : env1.length = pre1.length + env.length)
    {lst' : Lang.Sem.St} {env' : Lang.Sem.Env} {o : Lang.Sem.Out} {pc' : Nat}
    (h : LOut c f rt { E with vars := pre1 ++ E.vars } cur1 env1 ist1 t1 pc1 lst' env' o pc') :
    LOut c f rt E cur env ist tmps pc lst' env' o pc' := by
  cases o with
  | normal =>
    obtain ⟨ist', t', pre2, cur', r', sz', hrel', hlen', hcur', hkeep'⟩ := h
    exact ⟨ist', t', pre2 ++ pre1, cur', r.trans r', by rw [sz', sz],
      SRel.congr hrel' rfl rfl (by simp only [List.append_assoc]), by simp only [List.length_append]; omega,
      by omega, hk.trans (hkeep'.weaken rfl rfl hc hv)⟩
  | brk =>
    obtain ⟨l, i, ist', t', pre2, cur', hle, hi, r', sz', hrel', hlen', hcur', hkeep'⟩ := h
    exact ⟨l, i, ist', t', pre2 ++ pre1, cur', hle, hi, r.trans r', by rw [sz', sz],
      SRel.congr hrel' rfl rfl (by simp only [List.append_assoc]), by simp only [List.length_append]; omega,
      by omega, hk.trans (hkeep'.weaken rfl rfl hc hv)⟩
  | ret v =>
    obtain ⟨ist', he, hgs, hko, hret⟩ := h
    exact ⟨ist', r.ends he, hgs, hk.out.trans hko, hret⟩

end

/-! ## Every statement -/

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

theorem progOK_noref {lp : Prog} (hok : ProgOK lp) : NoRef lp :=
  fun g fd h prm hp => ((hok g fd h).params prm hp).1

theorem inVars_push (lp : Prog) (fnm x : String) (ty : Ty) (off : Nat) (vars : List (String × VarInfo)) (o : Nat)
    (ho : o < off) (hin : InVars lp ((x, { ty, at_ := .static { area := .frame fnm, off } }) :: vars) o) :
    InVars lp vars o := by
  obtain ⟨y, info, sl, hmem, hat, h1, h2⟩ := hin
  rcases List.mem_cons.mp hmem with he | hr
  · cases he
    simp only [Storage.static.injEq] at hat
    subst hat
    simp only at h1
    omega
  · exact ⟨y, info, sl, hr, hat, h1, h2⟩

theorem EnvOK.push {E : Env} (h : EnvOK E) (x : String) (ty : Ty) (sl : Slot) (l : Option Nat) :
    EnvOK { E with vars := (x, { ty, at_ := .static sl }) :: E.vars, loopEnd := l } := by
  intro y info hy
  simp only [List.lookup] at hy
  cases hyx : y == x with
  | true =>
    simp only [hyx, Option.some.injEq] at hy
    subst hy
    exact ⟨sl, rfl⟩
  | false =>
    simp only [hyx] at hy
    exact h y info hy

mutual

/-- **The code for a statement simulates the statement.** -/
theorem stmt_ok (F : Final c fn f sF) (lp : Prog) (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) (N : Nat)
    (H : ∀ k, k < N → FnSim c lp k) : ∀ (stm : Stmt) (E : Env) (s : LS) (rt : Option Ty) (il : Bool),
    E.prog = lp → E.fn = fn → EnvOK E → WTS rt il E stm → wp (IR.stmt stm) E (SPost c f sF N rt E stm s) s
  | .at sp st, E, s, rt, il, hp, hfn, hE, hw => by
    rw [IR.stmt]
    simp only [WTS] at hw
    exact wp_mono (stmt_ok F lp L hlow hok N H st E s rt il hp hfn hE hw) (fun _ _ h => at_ok h)
  | .decl x ty init, E, s, rt, il, hp, hfn, hE, hw => by
    subst hp
    rw [IR.stmt]
    simp only [WTS] at hw
    exact decl_ok F L hE hfn N rt x ty init s hw
  | .assign l r, E, s, rt, il, hp, hfn, hE, hw => by
    subst hp
    rw [IR.stmt]
    simp only [WTS] at hw
    exact assign_ok F L hE N rt l r s hw
  | .ite cnd t e, E, s, rt, il, hp, hfn, hE, hw => by
    simp only [WTS] at hw
    have iht := fun s1 => block_ok F lp L hlow hok N H t E E s1 rt il hp hfn hE hw.2.2.1
    have ihe := fun s1 => block_ok F lp L hlow hok N H e E E s1 rt il hp hfn hE hw.2.2.2
    subst hp
    exact ite_ok F L hE N rt cnd t e s hw.1 hw.2.1 iht ihe
  | .forRange x w lo hi body, E, s, rt, il, hp, hfn, hE, hw => by
    simp only [WTS] at hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
    have ihb := fun off l s1 => block_ok F lp L hlow hok N H body E
      { E with vars := (x, { ty := .int (w.getD .w32), at_ := .static { area := .frame E.fn, off } }) :: E.vars,
               loopEnd := l } s1 rt true hp hfn (hE.push x _ _ l) (h6 off l)
    subst hp
    exact for_ok F L hE hfn (progOK_noref hok) N rt x w lo hi body s ⟨h1, h2, h3, h4, h5⟩ ihb
  | .loop max body, E, s, rt, il, hp, hfn, hE, hw => by
    simp only [WTS] at hw
    have ihb := fun l s1 => block_ok F lp L hlow hok N H body E { E with loopEnd := l } s1 rt true hp hfn hE (hw.2 l)
    subst hp
    exact loop_ok F L hfn N rt max body s hw.1 ihb
  | .brk, E, s, rt, il, hp, hfn, hE, hw => by
    rw [IR.stmt]
    exact brk_ok F N rt s
  | .ret v, E, s, rt, il, hp, hfn, hE, hw => by
    subst hp
    rw [IR.stmt]
    simp only [WTS] at hw
    exact ret_ok F L hE N rt v s hw
  | .call dst g args, E, s, rt, il, hp, hfn, hE, hw => by
    subst hp
    rw [IR.stmt]
    simp only [WTS] at hw
    exact call_ok F L hE hfn hlow hok N H rt dst g args s hw
  | .eff dst e args, E, s, rt, il, hp, hfn, hE, hw => by
    subst hp
    rw [IR.stmt]
    simp only [WTS] at hw
    exact eff_ok F L hE hlow N rt dst e args s hw

/-- **The code for a list of statements simulates the list.** -/
theorem block_ok (F : Final c fn f sF) (lp : Prog) (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) (N : Nat)
    (H : ∀ k, k < N → FnSim c lp k) : ∀ (ss : List Stmt) (E0 E : Env) (s : LS) (rt : Option Ty) (il : Bool),
    E.prog = lp → E.fn = fn → EnvOK E → WTB rt il E ss → wp (blockFrom E ss) E0 (BPost c f sF N rt E ss s) s
  | [], E0, E, s, rt, il, hp, hfn, hE, hw => by
    rw [blockFrom, wp_pure]
    refine ⟨Ext.refl s, Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execL]; trivial
    | succ k =>
      rw [Lang.Sem.execL]
      exact ⟨ist, tmps, [], s.cur, Reach.refl, rfl, hrel, by simp, Nat.le_refl _, Keep.refl _⟩
  | [st], E0, E, s, rt, il, hp, hfn, hE, hw => by
    rw [blockFrom]
    simp only [WTB] at hw
    simp only [wp_bind, wp_withReader, wp_pure]
    refine wp_mono (stmt_ok F lp L hlow hok N H st E s rt il hp hfn hE hw) ?_
    intro E' s' ⟨hx, hE', hcur, hsem⟩
    refine ⟨hx, hcur, ?_⟩
    obtain ⟨pre, hpre, hinv, _⟩ := envAfter_eq E s.cur st
    rw [hpre] at hE'
    subst hE'
    intro n lst env ist tmps hn hxF hrel hsz hend
    have hlen := hrel.loc.1.length
    cases n with
    | zero => rw [Lang.Sem.execL]; trivial
    | succ k =>
      rw [Lang.Sem.execL]
      have hS := hsem k lst env ist tmps (by omega) hxF hrel hsz hend
      cases hR : Lang.Sem.execS k E.prog lst env st with
      | fuel => trivial
      | trap lst' => simp only [hR] at hS ⊢; exact hS
      | ok lst' env' o =>
        simp only [hR] at hS ⊢
        cases o with
        | normal =>
          dsimp only
          cases k with
          | zero => rw [Lang.Sem.execS] at hR; cases hR
          | succ k' =>
            rw [Lang.Sem.execL]
            exact hS.toL hcur hlen (fun _ => rfl)
        | brk => exact hS.toL hcur hlen (fun h => by cases h)
        | ret v => exact hS.toL hcur hlen (fun h => by cases h)
  | st :: s2 :: rest, E0, E, s, rt, il, hp, hfn, hE, hw => by
    rw [blockFrom]
    simp only [WTB] at hw
    cases hdc : declCall? st s2 with
    | none =>
      simp only [hdc] at hw ⊢
      obtain ⟨hw1, hw2⟩ := hw
      simp only [wp_bind, wp_withReader]
      refine wp_mono (stmt_ok F lp L hlow hok N H st E s rt il hp hfn hE hw1) ?_
      intro E' s1 ⟨hx1, hE', hcur1, hsem1⟩
      obtain ⟨pre, hpre, hinv, hstat⟩ := envAfter_eq E s.cur st
      have hw2' := hw2 s.cur
      rw [hpre] at hE' hw2'
      subst hE'
      refine wp_mono (block_ok F lp L hlow hok N H (s2 :: rest) E0 _ s1 rt il hp hfn (hE.append pre hstat) hw2') ?_
      intro _ s' ⟨hx2, hcur2, hsem2⟩
      refine ⟨hx1.trans hx2, by omega, ?_⟩
      intro n lst env ist tmps hn hxF hrel hsz hend
      have hlen := hrel.loc.1.length
      cases n with
      | zero => rw [Lang.Sem.execL]; trivial
      | succ k =>
        rw [Lang.Sem.execL]
        have hS := hsem1 k lst env ist tmps (by omega) (hx2.trans hxF) hrel hsz hend
        cases hR : Lang.Sem.execS k E.prog lst env st with
        | fuel => trivial
        | trap lst' => simp only [hR] at hS ⊢; exact hS
        | ok lst1 env1 o =>
          simp only [hR] at hS ⊢
          cases o with
          | normal =>
            dsimp only
            obtain ⟨ist1, t1, r1, sz1, hrel1, hkeep1⟩ := hS
            have hl1 := hrel1.loc.1.length
            have hL := hsem2 k lst1 env1 ist1 t1 (by omega) hxF hrel1 (by rw [sz1]; exact hsz) hend
            cases hR2 : Lang.Sem.execL k E.prog lst1 env1 (s2 :: rest) with
            | fuel => trivial
            | trap lst' =>
              simp only [hR2] at hL ⊢
              obtain ⟨ist', he, hw'⟩ := hL
              exact ⟨ist', r1.ends he, hw'⟩
            | ok lst' env' o' =>
              simp only [hR2] at hL ⊢
              exact LOut.cons hcur1 hinv r1 sz1 hkeep1 (by simp only [List.length_append] at hl1; omega) hL
          | brk => exact hS.toL hcur1 hlen (fun h => by cases h)
          | ret v => exact hS.toL hcur1 hlen (fun h => by cases h)
    | some tr =>
      obtain ⟨x, ty, i⟩ := tr
      simp only [hdc] at hw ⊢
      obtain ⟨hty, hi, hw2⟩ := hw
      simp only [wp_bind, wp_withReader]
      have L' : LayOK E.prog c := by rw [hp]; exact L
      have hlow' : Lowered E.prog c := by rw [hp]; exact hlow
      have hok' : ProgOK E.prog := by rw [hp]; exact hok
      have H' : ∀ k, k < N → FnSim c E.prog k := by rw [hp]; exact H
      refine wp_mono (declCall_ok F L' hE hfn hlow' hok' N H' x ty i s hty hi) ?_
      intro E' s1 ⟨hx1, hE', hcur1, hsem1⟩
      subst hE'
      refine wp_mono (block_ok F lp L hlow hok N H rest E0 _ s1 rt il hp hfn (hE.push x ty _ E.loopEnd)
        (hw2 s.cur)) ?_
      intro _ s' ⟨hx2, hcur2, hsem2⟩
      refine ⟨hx1.trans hx2, by omega, ?_⟩
      intro n lst env ist tmps hn hxF hrel hsz hend
      have hlen := hrel.loc.1.length
      have hcall : ∀ g args, i = .call g args →
          ∃ fd, E.prog.fn? g = some fd ∧ ∀ prm, prm ∈ fd.params → prm.byRef = false := by
        intro g args hig
        subst hig
        obtain ⟨fd, hfd, _⟩ := hi
        exact ⟨fd, hfd, fun p hp' => ((hok' g fd hfd).params p hp').1⟩
      rcases execL_pair E.prog st s2 rest x ty i hdc hcall n lst env with h0 | ⟨k, m, hkm, hmn, heq⟩
      · rw [h0]; trivial
      · rw [heq]
        have hD := hsem1 k lst env ist tmps (by omega) (hx2.trans hxF) hrel hsz
        cases hev : Lang.Sem.evalArgs E.prog lst env (initArgs i) with
        | none => simp only [hev] at hD ⊢; exact hD
        | some vs =>
          simp only [hev] at hD ⊢
          cases hact : initAct E.prog i k lst vs with
          | fuel => trivial
          | trap lst' => simp only [hact] at hD ⊢; exact hD
          | ok v lst1 =>
            simp only [hact] at hD ⊢
            obtain ⟨xv, ist1, t1, rfl, r1, sz1, hrel1, hkeep1⟩ := hD
            simp only [Option.getD_some]
            have hL := hsem2 m lst1 ((x, xv) :: env) ist1 t1 (by omega) hxF (by rw [hcur1]; exact hrel1)
              (by rw [sz1]; exact hsz) hend
            cases hR2 : Lang.Sem.execL m E.prog lst1 ((x, xv) :: env) rest with
            | fuel => trivial
            | trap lst' =>
              simp only [hR2] at hL ⊢
              obtain ⟨ist', he, hw'⟩ := hL
              exact ⟨ist', r1.ends he, hw'⟩
            | ok lst' env' o' =>
              simp only [hR2] at hL ⊢
              exact LOut.cons (pre1 := [(x, { ty, at_ := .static { area := .frame E.fn, off := s.cur } })])
                (by omega) (fun o ho hin => inVars_push _ _ _ _ _ _ o ho hin) r1 sz1 hkeep1
                (by simp only [List.length_cons, List.length_nil]; omega) hL

end

end

/-! ## Every function -/

/-- Two elements that `f` maps to one value, in a list whose values are all different. -/
theorem nodup_filterMap_idx {α β : Type} (g : α → Option β) : ∀ (l : List α) (i j : Nat) (a b : α) (y : β),
    (l.filterMap g).Nodup → l[i]? = some a → l[j]? = some b → g a = some y → g b = some y → i = j
  | [], i, _, _, _, _, _, hi, _, _, _ => by simp at hi
  | x :: t, i, j, a, b, y, hn, hi, hj, ha, hb => by
    have hn' : (t.filterMap g).Nodup := by
      simp only [List.filterMap_cons] at hn
      split at hn
      · exact hn
      · exact (List.nodup_cons.mp hn).2
    have hx : ∀ (k : Nat) (d : α), g x = some y → t[k]? = some d → g d = some y → False := by
      intro k d hgx hk hgd
      simp only [List.filterMap_cons, hgx] at hn
      exact (List.nodup_cons.mp hn).1 (List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, hgd⟩)
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      cases j with
      | zero => rfl
      | succ j' => exact (hx j' b ha (by simpa using hj) hb).elim
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact (hx i' a hb (by simpa using hi) ha).elim
      | succ j' =>
        have := nodup_filterMap_idx g t i' j' a b y hn' (by simpa using hi) (by simpa using hj) ha hb
        omega

theorem labels_unique {body : Array Instr} (h : (labelsOf body).Nodup) (i j l : Nat)
    (hi : body[i]? = some (Instr.label l)) (hj : body[j]? = some (Instr.label l)) : i = j := by
  unfold labelsOf at h
  exact nodup_filterMap_idx _ body.toList i j _ _ l h (by simpa using hi) (by simpa using hj) rfl rfl

theorem wp_elim {α : Type} {m : LM α} {E : Env} {Q : α → LS → Prop} {s s' : LS} {a : α} (h : wp m E Q s)
    (hrun : m E s = .ok (a, s')) : Q a s' := by
  unfold wp at h
  rw [hrun] at h
  exact h

theorem wp_of_run {α : Type} {m : LM α} {E : Env} {Q : α → LS → Prop} {s : LS}
    (h : ∀ a s', m E s = .ok (a, s') → Q a s') : wp m E Q s := by
  unfold wp
  cases hm : m E s with
  | error e => trivial
  | ok r => exact h r.1 r.2 hm

/-- The body with the trap that index checks jump to. -/
def epilogue (out : Array Instr) : Option Nat → Array Instr
  | some l => (out.push (.label l)).push .trap
  | none => out

theorem wp_trapEpilogue {E : Env} {s : LS} (Q : Unit → LS → Prop) :
    wp trapEpilogue E Q s ↔ Q () { s with out := epilogue s.out s.trapLabel } := by
  obtain ⟨out, tmps, labels, cur, max, tl⟩ := s
  unfold wp trapEpilogue epilogue
  cases tl <;> rfl

/-- What `lowerFnRaw` made: the block's code, a `ret`, the trap. -/
theorem lowerFnRaw_run {lp : Prog} {fd : Lang.Fn} {gf : IR.Fn} (h : lowerFnRaw lp fd = .ok gf) :
    ∃ s1 : LS, blockFrom (fnEnv lp fd) fd.body (fnEnv lp fd)
        { cur := (paramSlots lp fd).2, max := (paramSlots lp fd).2 } = .ok ((), s1) ∧
      gf.body = epilogue (s1.out.push (.ret none)) s1.trapLabel ∧ gf.tmps = s1.tmps ∧
      gf.frame = Nat.max s1.max (paramSlots lp fd).2 := by
  unfold lowerFnRaw at h
  split at h
  · rename_i u st hrun
    have hwp : wp (lowerBody fd.body) (fnEnv lp fd) (fun _ st' => ∃ s1 : LS,
        blockFrom (fnEnv lp fd) fd.body (fnEnv lp fd)
          { cur := (paramSlots lp fd).2, max := (paramSlots lp fd).2 } = .ok ((), s1) ∧
        st'.out = epilogue (s1.out.push (.ret none)) s1.trapLabel ∧ st'.tmps = s1.tmps ∧ st'.max = s1.max)
        { cur := (paramSlots lp fd).2, max := (paramSlots lp fd).2 } := by
      unfold lowerBody IR.block
      rw [wp_bind, wp_inScope]
      refine wp_of_run (m := fun e => blockFrom e fd.body e) (fun a s1 hb => ?_)
      rw [wp_bind, wp_emit, wp_trapEpilogue]
      exact ⟨s1, hb, rfl, rfl, rfl⟩
    obtain ⟨s1, hb, h1, h2, h3⟩ := wp_elim hwp hrun
    cases h
    exact ⟨s1, hb, h1, h2, by simp only [h3]⟩
  · cases h

/-- The parameters, as the variables the body starts with. -/
theorem params_lrel {c : Ctx} {lp : Prog} {g : String} {m : ByteArray} : ∀ (ps : List Lang.Param) (lo : Nat)
    (vs : List Val), (∀ prm, prm ∈ ps → prm.byRef = false ∧ prm.ty.isScalar = true) →
    ParamsAt c lp g m (paramSlotsFrom lp ps lo).1 vs →
    LRel lp c g m (paramVars g (paramSlotsFrom lp ps lo).1) ((ps.map (·.name)).zip vs) ∧
      (∀ o, InVars lp (paramVars g (paramSlotsFrom lp ps lo).1) o → lo ≤ o) ∧
      topOf lp (paramVars g (paramSlotsFrom lp ps lo).1) ≤ (paramSlotsFrom lp ps lo).2 ∧
      EnvOK { prog := lp, fn := g, vars := paramVars g (paramSlotsFrom lp ps lo).1 }
  | [], lo, vs, _, h => by
    cases vs with
    | nil => exact ⟨.nil, fun o ho => by obtain ⟨_, _, _, hm, _⟩ := ho; simp [paramSlotsFrom, paramVars] at hm,
        Nat.zero_le _, fun x info hx => by simp [paramSlotsFrom, paramVars] at hx⟩
    | cons v vs => simp [paramSlotsFrom, ParamsAt] at h
  | prm :: ps, lo, vs, hps, h => by
    have hbr := (hps prm (by simp)).1
    have hsc := (hps prm (by simp)).2
    rw [slots_cons lp prm ps lo hbr] at h ⊢
    cases vs with
    | nil => simp [ParamsAt] at h
    | cons v vs =>
      obtain ⟨hty, hrd, hrest⟩ := h
      obtain ⟨ih1, ih2, ih3, ih4⟩ := params_lrel ps (lo + sizeOf lp prm.ty) vs
        (fun r hr => hps r (by simp [hr])) hrest
      have hend := slots_end_ge lp ps (lo + sizeOf lp prm.ty)
      simp only [paramVars, List.map_cons, hbr, Bool.false_eq_true, if_false, List.zip_cons_cons]
      refine ⟨.cons prm.name prm.ty lo v ih1 (fun o h1 h2 hin => by have := ih2 o hin; omega) (scalar_tyOK _ hsc) hty
        ((holds_scalar hsc).mpr hrd), fun o ho => ?_, ?_, ?_⟩
      · obtain ⟨y, info, sl, hmem, hat, h1, h2⟩ := ho
        rcases List.mem_cons.mp hmem with he | hr
        · cases he
          simp only [Storage.static.injEq] at hat
          subst hat
          exact h1
        · have := ih2 o ⟨y, info, sl, hr, hat, h1, h2⟩
          omega
      · simp only [topOf]
        exact Nat.max_le.mpr ⟨ih3, hend⟩
      · intro y info hy
        simp only [List.lookup] at hy
        cases hyx : y == prm.name with
        | true =>
          simp only [hyx, Option.some.injEq] at hy
          subst hy
          exact ⟨_, rfl⟩
        | false =>
          simp only [hyx] at hy
          exact ih4 y info hy

/-- **The code of every function simulates the function.** -/
theorem fn_sim {c : Ctx} {lp : Prog} (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) :
    ∀ N, FnSim c lp N := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro g fd lst vs ist hfd hgs hpar
    obtain ⟨gf, hgf, hraw⟩ := hlow.fns g fd hfd
    obtain ⟨s1, hb, hbody, htmps, hframe⟩ := lowerFnRaw_run hraw
    have hname := fn?_name hfd
    subst hname
    have hFn := hok fd.name fd hfd
    obtain ⟨hl, _, htop, hEnv⟩ := params_lrel (c := c) (g := fd.name) (m := ist.mem) fd.params 0 vs hFn.params hpar
    -- the state before the trap's epilogue
    have F : Final c fd.name gf { s1 with cur := (paramSlots lp fd).2, out := s1.out.push (.ret none) } := by
      refine ⟨hgf, fun i hi => ?_, by rw [htmps]; exact Nat.le_refl _,
        fun i j l hi hj => labels_unique (hlow.uniq _ _ hgf) i j l hi hj, fun t ht => ?_,
        by rw [hframe]; exact Nat.le_max_left _ _⟩
      · rw [hbody]
        unfold epilogue
        cases s1.trapLabel with
        | none => rfl
        | some l =>
          simp only [Array.size_push] at hi
          simp only
          rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
            if_neg (by simp only [Array.size_push]; omega)]
      · rw [hbody]
        simp only at ht
        rw [ht]
        unfold epilogue
        exact ⟨(s1.out.push (.ret none)).size, (push2 _ _ _).1, (push2 _ _ _).2⟩
    have hblock := block_ok F lp L hlow hok N (fun k hk => ih k hk) fd.body (fnEnv lp fd) (fnEnv lp fd)
      { cur := (paramSlots lp fd).2, max := (paramSlots lp fd).2 } fd.ret false rfl rfl hEnv hFn.body
    obtain ⟨hx01, hcur01, hsem⟩ := wp_elim hblock hb
    have hxF : Ext s1 { s1 with cur := (paramSlots lp fd).2, out := s1.out.push (.ret none) } :=
      ⟨fun i hi => by simp only [Array.getElem?_push]; rw [if_neg (by omega)], by simp, Nat.le_refl _,
        fun _ h => h, Nat.le_refl _⟩
    have hrel0 : SRel c (fnEnv lp fd) (paramSlots lp fd).2 lst ((fd.params.map (·.name)).zip vs) ist :=
      ⟨hgs.1, hgs.2.1, hgs.2.2, ⟨hl, htop⟩, ⟨gf, hgf, by rw [hframe]; exact Nat.le_max_right _ _⟩⟩
    have hret : gf.body[s1.out.size]? = some (Instr.ret none) := F.at_ (Ext.refl _) (by simp)
    cases N with
    | zero => rw [Lang.Sem.execB]; trivial
    | succ k =>
      rw [Lang.Sem.execB]
      have hL := hsem k lst _ ist (Array.replicate gf.tmps.size 0) (by omega) hxF hrel0 (by simp)
        (fun l hl' => by simp [fnEnv] at hl')
      rw [show (fnEnv lp fd).prog = lp from rfl] at hL
      cases hR : Lang.Sem.execL k lp lst ((fd.params.map (·.name)).zip vs) fd.body with
      | fuel => trivial
      | trap lst' =>
        have hL' : ∃ ist', Ends c gf 0 (Array.replicate gf.tmps.size 0) ist (.trap ist') ∧ ist'.world = lst'.world := by
          simp only [hR] at hL
          exact hL
        obtain ⟨ist', he, hw⟩ := hL'
        obtain ⟨m, hm⟩ := callF_of_ends hgf he
        exact ⟨m, ist', hm, hw⟩
      | ok lst' env' o =>
        have hL' : LOut c gf fd.ret (fnEnv lp fd) (paramSlots lp fd).2 ((fd.params.map (·.name)).zip vs) ist
            (Array.replicate gf.tmps.size 0) 0 lst' env' o s1.out.size := by
          simp only [hR] at hL
          exact hL
        cases o with
        | normal =>
          obtain ⟨ist', t', pre, cur', r, sz, hrel', hlen, hcur, hkeep⟩ := hL'
          have he : Ends c gf 0 (Array.replicate gf.tmps.size 0) ist (.ok none ist') :=
            r.ends (Ends.stop hret (step_ret c ist' t' none) (by simp))
          obtain ⟨m, hm⟩ := callF_of_ends hgf he
          refine ⟨m, ist', hm, hrel'.gs, hkeep.out, ?_⟩
          cases hrt : fd.ret with
          | none => rfl
          | some t =>
            exact absurd rfl ((returns_all lp k).2.1 _ _ _ _ _ _ hR (hFn.returns (by rw [hrt]; rfl)))
        | brk =>
          obtain ⟨l, i, _, _, _, _, hle, _⟩ := hL'
          simp [fnEnv] at hle
        | ret v =>
          obtain ⟨ist', he, hgs', hko, hret'⟩ := hL'
          obtain ⟨m, hm⟩ := callF_of_ends hgf he
          exact ⟨m, ist', hm, hgs', hko, hret'⟩

/-- info: 'Ember.Proof.IRSim.fn_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_sim

end Ember.Proof.IRSim
