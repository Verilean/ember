import Ember.Proof.CSim
import Ember.Proof.CVoid

/-!
# Ember.Proof.CFn — a compiled function does what its body does (plan M5.8)

`fn_sim`: for every amount of fuel on the Ember side, `FnSim` — the
induction that `stmt_ok` leaves open for calls.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

theorem paramVar_noref (prm : Param) (h : prm.byRef = false) :
    paramVar prm = (prm.name, { ty := prm.ty, c := .var (localName prm.name) }) := by
  unfold paramVar
  cases prm.ty <;> simp [h]

theorem paramC_noref (o : Opts) (prm : Param) (h : prm.byRef = false) :
    paramC o prm = (cty o prm.ty, localName prm.name) := by
  unfold paramC
  cases prm.ty <;> simp [h]

/-- The parameters at the entry of a function. -/
theorem params_rel (p : Prog) (o : Opts) : ∀ (ps : List Param) (vs : List Val),
    (∀ prm, prm ∈ ps → prm.byRef = false ∧ prm.ty.isScalar = true) → ValsTy p (ps.map (·.ty)) vs →
    LRel p o (ps.map paramVar) ((ps.map (·.name)).zip vs) (((ps.map (paramC o)).map (·.2)).zip (vs.map (cval o))) ∧
    ∀ k, (((ps.map (paramC o)).map (·.2)).zip (vs.map (cval o))).lookup (tmpName k) = none
  | [], [], _, _ => ⟨.nil, fun _ => rfl⟩
  | [], _ :: _, _, hv => hv.elim
  | _ :: _, [], _, hv => hv.elim
  | prm :: ps, v :: vs, hp, hv => by
    obtain ⟨hty, _, hrest⟩ := hv
    obtain ⟨hbr, _⟩ := hp prm (by simp)
    obtain ⟨ih1, ih2⟩ := params_rel p o ps vs (fun q hq => hp q (by simp [hq])) hrest
    simp only [List.map_cons, paramVar_noref prm hbr, paramC_noref o prm hbr, List.zip_cons_cons]
    refine ⟨.val prm.name prm.ty v hty ih1, fun k => ?_⟩
    have hne : (tmpName k == localName prm.name) = false := by
      cases h : tmpName k == localName prm.name
      · rfl
      · rw [beq_iff_eq] at h; exact absurd h (tmp_ne_local _ _)
    simp only [List.lookup, hne]
    exact ih2 k

theorem fnEnv_ok (p : Prog) (o : Opts) (fd : Fn) (hb : o.bugDropCast = false) : EnvOK (fnEnv p o fd) := by
  refine ⟨fun x info hi => ?_, hb⟩
  unfold Env.varInfo at hi
  have key : ∀ (ps : List Param) (v : VarInfo), (ps.map paramVar).lookup x = some v → ∃ nm, v.c = .var nm := by
    intro ps
    induction ps with
    | nil => intro v h; simp at h
    | cons prm r ih =>
      intro v h
      simp only [List.map_cons, List.lookup] at h
      have hk : ∃ nm, (paramVar prm).2.c = .var nm := by
        unfold paramVar
        split <;> exact ⟨_, rfl⟩
      cases hx : x == (paramVar prm).1 with
      | true =>
        simp only [hx, Option.some.injEq] at h
        rw [← h]; exact hk
      | false =>
        simp only [hx] at h
        exact ih v h
  cases hl : (fnEnv p o fd).vars.lookup x with
  | some v =>
    simp only [hl, Except.ok.injEq] at hi
    subst hi
    exact key fd.params v hl
  | none =>
    simp only [hl] at hi
    cases hg : (fnEnv p o fd).prog.global? x with
    | none => simp [hg, Env.err] at hi
    | some gd =>
      simp only [hg, Except.ok.injEq] at hi
      subst hi
      exact ⟨_, rfl⟩

theorem runs_voids {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} (ps : List Param) :
    Runs cp cst cenv (ps.map fun prm => CStmt.expr (.cast .void (.var (localName prm.name)))) cenv := by
  induction ps with
  | nil => exact Runs.nil
  | cons prm r ih =>
    have h1 : Runs cp cst cenv [CStmt.expr (.cast .void (.var (localName prm.name)))] cenv :=
      Runs.single fun m => exec_void (m + 4) _
    exact h1.append ih

/-- The body of a compiled function: its statements with the lines that do nothing. -/
theorem body_exec {p : Prog} {o : Opts} {cp : CProg} {fd : Fn} {code : List CStmt} {cst : C.Sem.St}
    {cenv : C.Sem.Env} {r : C.Sem.Res} (h : Exec cp cst cenv code r) :
    Exec cp cst cenv
      ((if o.lines && fd.span.line > 0 then [CStmt.line fd.span.line fd.span.file] else []) ++
        fd.params.map (fun prm => CStmt.expr (.cast .void (.var (localName prm.name)))) ++
        voidUnread (declared fd.body) code) r := by
  have hl : Runs cp cst cenv (if o.lines && fd.span.line > 0 then [CStmt.line fd.span.line fd.span.file] else [])
      cenv := by
    split
    · exact Runs.single fun m => rfl
    · exact Runs.nil
  exact (hl.append (runs_voids fd.params)).exec (h.void _)

theorem wpc_block {g : C.Env} {cs : CS} (ss : List Stmt) (Q : _root_.Unit → CS → Prop) :
    wpc (C.block ss) g Q cs ↔ wpc (blockFrom g.path 1 g ss) g Q cs := by
  unfold C.block
  simp only [wpc_bind, wpc_read]

/-- **Functions.**  A call of a compiled function, with the values of
its arguments, does what the Ember function does — the same result, the
globals and the world related again — or traps when it traps. -/
theorem fn_sim (p : Prog) (o : Opts) (cp : CProg) (U : Unit p o cp) (hP : ProgOK p o) :
    ∀ N j, j < N → FnSim p o cp j := by
  intro N
  induction N with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ N ih =>
    intro j hj
    by_cases hjN : j < N
    · exact ih j hjN
    · have hj' : j = N := by omega
      subst hj'
      intro f fd cfd hfd hcomp st cst vs hG hty
      obtain ⟨_, hret, hparams, cs', hrun, hbody⟩ := compileFn_shape hcomp
      have hfok := hP f fd hfd
      have hb := (wpc_block (g := fnEnv p o fd) (cs := {}) fd.body _).mpr
        (block_ok cp j fd.body [] 1 (fnEnv p o fd) (fnEnv p o fd) {} fd.ret false U hP ih
          (fnEnv_ok p o fd U.nobug) hfok.body)
      unfold wpc at hb
      rw [hrun] at hb
      obtain ⟨_, code, hcode, hsim⟩ := hb
      have hcode' : cs'.out.toList = code := by rw [hcode]; simp
      rw [hparams]
      cases j with
      | zero => rw [Lang.Sem.execB]; trivial
      | succ n =>
        rw [Lang.Sem.execB]
        obtain ⟨hl0, hnt⟩ := params_rel p o fd.params vs hfok.params hty
        have hrel0 : SRel (fnEnv p o fd) st ((fd.params.map (·.name)).zip vs) cst
            (((fd.params.map (paramC o)).map (·.2)).zip (vs.map (cval o))) := ⟨hl0, hG⟩
        have hfr0 : Fresh 0 cst (((fd.params.map (paramC o)).map (·.2)).zip (vs.map (cval o))) :=
          fun k _ => ⟨hnt k, hG.gtmp k⟩
        have h := hsim n (by omega) st _ cst _ hrel0 hfr0
        cases hR : Lang.Sem.execL n p st ((fd.params.map (·.name)).zip vs) fd.body with
        | fuel => trivial
        | trap st' =>
          have hR' : Lang.Sem.execL n (fnEnv p o fd).prog st ((fd.params.map (·.name)).zip vs) fd.body = .trap st' :=
            hR
          rw [hR'] at h
          obtain ⟨cst', hx, hw⟩ := h
          have hx' := body_exec (p := p) (o := o) (fd := fd) hx
          rw [← hcode', ← hbody] at hx'
          obtain ⟨m, hm⟩ := hx'.block_trap
          exact ⟨m, cst', hm, hw⟩
        | ok st' env' out =>
          have hR' : Lang.Sem.execL n (fnEnv p o fd).prog st ((fd.params.map (·.name)).zip vs) fd.body
              = .ok st' env' out := hR
          rw [hR'] at h
          obtain ⟨cst', cenv', hx, ⟨ys, env1, xs, cenv1, rfl, rfl, hlen, hsame, hrel, hstk, _, _⟩, hout⟩ := h
          have hx' := body_exec (p := p) (o := o) (fd := fd) hx
          rw [← hcode', ← hbody] at hx'
          obtain ⟨m, hm⟩ := hx'.block
          refine ⟨m, cst', _, hm, hrel.2, hstk, ?_⟩
          cases hfr : fd.ret with
          | none =>
            intro v hv
            subst hv
            rw [hfr] at hout
            obtain ⟨t, e, _⟩ := hout
            cases e
          | some t =>
            have hne := (returns_all p (n + 1)).1 st _ fd.body st' _ out (by rw [Lang.Sem.execB, hR])
              (hfok.returns (by simp [hfr]))
            rw [hfr] at hout
            cases out with
            | normal => exact absurd rfl hne
            | brk => exact absurd hout (by simp [OutOK])
            | ret v =>
              cases v with
              | none => exact absurd hout (by simp [OutOK])
              | some v =>
                obtain ⟨t', e, hsc, hv⟩ := hout
                cases e
                exact ⟨v, rfl, hv, hsc⟩

/-- info: 'Ember.Proof.CSim.fn_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_sim

end Ember.Proof.CSim
