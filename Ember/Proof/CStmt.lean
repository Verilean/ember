import Ember.Proof.CRel
import Ember.Proof.LangFrame

/-!
# Ember.Proof.CStmt — the emitter is right about statements (plan M5.8)

`stmt_ok`/`block_ok`: the C statements `C.stmt` emits for a well-typed
Ember statement do, from related states, what `Lang.Sem.execS` does —
the same result, a related state — or end in `ember_trap` when it traps.
`fn_ok`: so does a compiled function, called with the values of its
arguments.

Outside: by-reference parameters (the stack has none).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

/-! ## Well-typed statements -/

/-- A field's type: a scalar or an array of scalars. -/
def FieldOK : Ty → Prop
  | .int _ => True
  | .bool => True
  | .arr el _ => el.isScalar = true
  | .record _ => False

/-- A type a local can have. -/
def TyOK (p : Prog) : Ty → Prop
  | .int _ => True
  | .bool => True
  | .arr el _ => el.isScalar = true
  | .record r => ∃ sd, p.struct? r = some sd ∧ ∀ ft, ft ∈ sd.fields → FieldOK ft.2

/-- The emitter's environment after a statement. -/
def envAfter (g : C.Env) : Stmt → C.Env
  | .at _ s => envAfter g s
  | .decl x ty _ => { g with vars := (x, { ty, c := .var (localName x) }) :: g.vars }
  | _ => g

/-- Arguments of the parameters' types, all scalars. -/
def ArgsOK (g : C.Env) : List Ty → List Expr → Prop
  | [], [] => True
  | t :: ts, a :: as => WT g a ∧ g.tyOf a = .ok t ∧ t.isScalar = true ∧ ArgsOK g ts as
  | _, _ => False

/-- A destination for a result of type `ret`. -/
def DstOK (g : C.Env) (dst : Option Expr) (ret : Option Ty) : Prop :=
  match dst with
  | none => True
  | some d => IsPlace d ∧ WT g d ∧ ∃ t, ret = some t ∧ g.tyOf d = .ok t ∧ t.isScalar = true

mutual
/-- **What the proofs need of a checked statement**, in the emitter's
environment `g`, in a function returning `rt`; `il`: inside a loop. -/
def WTS (rt : Option Ty) : Bool → C.Env → Stmt → Prop
  | il, g, .at _ s => WTS rt il g s
  | _, g, .decl _ ty init =>
    TyOK g.prog ty ∧
      (match init with
       | some e => WT g e ∧ g.tyOf e = .ok ty ∧ ty.isScalar = true
       | none => True)
  | _, g, .assign l r => IsPlace l ∧ WT g l ∧ WT g r ∧ ∃ t, g.tyOf l = .ok t ∧ g.tyOf r = .ok t ∧ t.isScalar = true
  | il, g, .ite c t e => WT g c ∧ g.tyOf c = .ok .bool ∧ WTB rt il g.path 1 g t ∧ WTB rt il g.path 1 g e
  | _, g, .forRange x w lo hi body =>
    WT g lo ∧ WT g hi ∧ g.tyOf lo = .ok (.int (w.getD .w32)) ∧ g.tyOf hi = .ok (.int (w.getD .w32)) ∧
      NoWriteL x body ∧
      WTB rt true g.path 1
        { g with vars := (x, { ty := .int (w.getD .w32), c := .var (localName x) }) :: g.vars } body
  | _, g, .loop n body => n < 2 ^ 32 ∧ WTB rt true g.path 1 g body
  | il, _, .brk => il = true
  | _, _, .ret none => rt = none
  | _, g, .ret (some e) => WT g e ∧ ∃ t, rt = some t ∧ g.tyOf e = .ok t ∧ t.isScalar = true
  | _, g, .call dst f args =>
    ∃ fd, g.prog.fn? f = some fd ∧ ArgsOK g (fd.params.map (·.ty)) args ∧ DstOK g dst fd.ret
  | _, g, .eff dst e args => ArgsOK g e.sig.1 args ∧ DstOK g dst e.sig.2
/-- The statements of a block, numbered from `i`, as `C.blockFrom` compiles them. -/
def WTB (rt : Option Ty) : Bool → List Nat → Nat → C.Env → List Stmt → Prop
  | _, _, _, _, [] => True
  | il, base, i, env, s :: rest =>
    WTS rt il { env with path := base ++ [i] } s ∧
      WTB rt il base (i + 1) { envAfter { env with path := base ++ [i] } s with path := base } rest
end

/-- What the proofs need of a function: scalar parameters by value, a
well-typed body, and a result on every path if it has one. -/
structure FnOK (p : Prog) (o : Opts) (fd : Fn) : Prop where
  params : ∀ prm, prm ∈ fd.params → prm.byRef = false ∧ prm.ty.isScalar = true
  body : WTB fd.ret false [] 1 (fnEnv p o fd) fd.body
  returns : fd.ret.isSome = true → ReturnsL fd.body

def ProgOK (p : Prog) (o : Opts) : Prop := ∀ f fd, p.fn? f = some fd → FnOK p o fd

theorem envAfter_prog (g : C.Env) : ∀ s, (envAfter g s).prog = g.prog ∧ (envAfter g s).opts = g.opts
  | .at _ s => by rw [envAfter]; exact envAfter_prog g s
  | .decl _ _ _ => ⟨rfl, rfl⟩
  | .assign _ _ => ⟨rfl, rfl⟩
  | .ite _ _ _ => ⟨rfl, rfl⟩
  | .forRange _ _ _ _ _ => ⟨rfl, rfl⟩
  | .loop _ _ => ⟨rfl, rfl⟩
  | .brk => ⟨rfl, rfl⟩
  | .ret _ => ⟨rfl, rfl⟩
  | .call _ _ _ => ⟨rfl, rfl⟩
  | .eff _ _ _ => ⟨rfl, rfl⟩

theorem EnvOK.push {g : C.Env} (h : EnvOK g) (x : String) (ty : Ty) (nm : String) :
    EnvOK { g with vars := (x, { ty, c := .var nm }) :: g.vars } := by
  refine ⟨fun y info hy => ?_, h.2⟩
  unfold Env.varInfo at hy
  simp only [List.lookup] at hy
  cases hyx : y == x with
  | true =>
    simp only [hyx, Except.ok.injEq] at hy
    subst hy
    exact ⟨nm, rfl⟩
  | false =>
    simp only [hyx] at hy
    exact h.1 y info hy

theorem EnvOK.after {g : C.Env} (h : EnvOK g) : ∀ s, EnvOK (envAfter g s)
  | .at _ s => by rw [envAfter]; exact h.after s
  | .decl x ty _ => h.push x ty _
  | .assign _ _ => h
  | .ite _ _ _ => h
  | .forRange _ _ _ _ _ => h
  | .loop _ _ => h
  | .brk => h
  | .ret _ => h
  | .call _ _ _ => h
  | .eff _ _ _ => h

theorem EnvOK.path {g : C.Env} (h : EnvOK g) (π : List Nat) : EnvOK { g with path := π } := h

/-! ## The emitter's monad, again -/

theorem wpc_get {g : C.Env} {cs : CS} (Q : CS → CS → Prop) : wpc (get : CM CS) g Q cs ↔ Q cs cs := Iff.rfl

theorem wpc_set {g : C.Env} {cs : CS} (s : CS) (Q : PUnit → CS → Prop) : wpc (set s : CM PUnit) g Q cs ↔ Q ⟨⟩ s :=
  Iff.rfl

theorem wpc_collect {g : C.Env} {cs : CS} (m : CM _root_.Unit) (Q : List CStmt → CS → Prop) :
    wpc (collect m) g Q cs ↔
      wpc m g (fun _ cs' => Q cs'.out.toList { cs' with out := cs.out }) { cs with out := #[] } := by
  unfold collect
  simp only [wpc_bind, wpc_get, wpc_pure]
  rfl

/-! ## Results -/

def cout (o : Opts) : Lang.Sem.Out → C.Sem.Out
  | .normal => .normal
  | .brk => .brk
  | .ret v => .ret (v.map (cval o))

/-- What a statement may end with: `break` only in a loop, `return`
with a value of the function's result type. -/
def OutOK (p : Prog) (rt : Option Ty) (il : Bool) : Lang.Sem.Out → Prop
  | .normal => True
  | .brk => il = true
  | .ret none => rt = none
  | .ret (some v) => ∃ t, rt = some t ∧ t.isScalar = true ∧ HasTy p t v

/-- The states after statements that ran in the scope `env`/`cenv`: on
top, what they declared (`ys`, `xs`); below, the scope they started in,
related again, the C one with the same names and temporaries. -/
def After (g : C.Env) (K : List (String × VarInfo) → Prop) (t' : Nat) (st' : Lang.Sem.St)
    (env' : Lang.Sem.Env) (out : Lang.Sem.Out) (env : Lang.Sem.Env) (cst : C.Sem.St) (cenv : C.Sem.Env)
    (cst' : C.Sem.St) (cenv' : C.Sem.Env) : Prop :=
  ∃ ys env1 xs cenv1, env' = ys ++ env1 ∧ cenv' = xs ++ cenv1 ∧ env1.length = env.length ∧ Same cenv cenv1 ∧
    SRel g st' env1 cst' cenv1 ∧ cst'.stack = cst.stack ∧ Fresh t' cst' cenv' ∧
    (out = .normal → ∃ nv, K nv ∧ LRel g.prog g.opts nv ys xs)

/-- **The C code does what the Ember result says.** -/
def Sim (g : C.Env) (K : List (String × VarInfo) → Prop) (cp : CProg) (rt : Option Ty) (il : Bool) (t' : Nat)
    (code : List CStmt) (R : Lang.Sem.Res) (env : Lang.Sem.Env) (cst : C.Sem.St) (cenv : C.Sem.Env) : Prop :=
  match R with
  | .ok st' env' out =>
    ∃ cst' cenv', Exec cp cst cenv code (.ok cst' cenv' (cout g.opts out)) ∧
      After g K t' st' env' out env cst cenv cst' cenv' ∧ OutOK g.prog rt il out
  | .trap st' => ∃ cst', Exec cp cst cenv code (.trap cst') ∧ cst'.world = st'.world
  | .fuel => True

/-- What `C.stmt s` yields. -/
def SPost (N : Nat) (rt : Option Ty) (il : Bool) (g : C.Env) (s : Stmt) (cp : CProg) (cs : CS) (g' : C.Env)
    (cs' : CS) : Prop :=
  g' = envAfter g s ∧ cs.tmp ≤ cs'.tmp ∧ ∃ code, cs'.out = cs.out ++ code.toArray ∧
    ∀ k, k ≤ N → ∀ st env cst cenv, SRel g st env cst cenv → Fresh cs.tmp cst cenv →
      Sim g (fun nv => g'.vars = nv ++ g.vars) cp rt il cs'.tmp code (Lang.Sem.execS k g.prog st env s) env cst cenv

/-- What `C.blockFrom … ss` yields. -/
def BPost (N : Nat) (rt : Option Ty) (il : Bool) (g : C.Env) (ss : List Stmt) (cp : CProg) (cs : CS)
    (_ : _root_.Unit) (cs' : CS) : Prop :=
  cs.tmp ≤ cs'.tmp ∧ ∃ code, cs'.out = cs.out ++ code.toArray ∧
    ∀ k, k ≤ N → ∀ st env cst cenv, SRel g st env cst cenv → Fresh cs.tmp cst cenv →
      Sim g (fun _ => True) cp rt il cs'.tmp code (Lang.Sem.execL k g.prog st env ss) env cst cenv

/-- The scope is as it was, apart from temporaries on top. -/
theorem After.mk0 {g : C.Env} {K : List (String × VarInfo) → Prop} {t' : Nat} {st' : Lang.Sem.St}
    {env' env : Lang.Sem.Env} {out : Lang.Sem.Out} {cst cst' : C.Sem.St} {cenv c' xs : C.Sem.Env}
    (hK : K []) (ht : AllTmp xs) (hsame : Same (xs ++ cenv) c') (hrel : SRel g st' env' cst' c')
    (hlen : env'.length = env.length) (hstk : cst'.stack = cst.stack) (hfr : Fresh t' cst' c') :
    After g K t' st' env' out env cst cenv cst' c' := by
  obtain ⟨xs', a', rfl, h1, h2⟩ := hsame.split
  have ht' := ht.same h1
  exact ⟨[], env', xs', a', rfl, rfl, hlen, h2, hrel.strip ht', hstk, hfr, fun _ => ⟨[], hK, LRel.allTmp ht'⟩⟩

theorem After.decl {g : C.Env} {t0 t1 : Nat} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv xs : C.Sem.Env} (x : String) (ty : Ty) (v : Val) (hrel : SRel g st env cst cenv) (ht : Temps xs t0 t1)
    (h01 : t0 ≤ t1) (hfr : Fresh t0 cst cenv) (hty : HasTy g.prog ty v) :
    After g (fun nv => (x, ({ ty, c := .var (localName x) } : VarInfo)) :: g.vars = nv ++ g.vars) t1 st
      ((x, v) :: env) .normal env cst cenv cst ((localName x, cval g.opts v) :: (xs ++ cenv)) :=
  ⟨[(x, v)], env, (localName x, cval g.opts v) :: xs, cenv, rfl, rfl, rfl, Same.refl _, hrel, rfl,
    (hfr.append ht h01).cons_local x _, fun _ => ⟨[(x, { ty, c := .var (localName x) })], rfl,
      LRel.val x ty v hty (LRel.allTmp ht.allTmp)⟩⟩

/-! ## C statements, one at a time -/

section
variable {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env}

theorem exec_assign (m : Nat) (l r : CExpr) (v old v' : CVal) (loc : C.Sem.Loc) (st' : C.Sem.St)
    (env' : C.Sem.Env) (hcall : C.Sem.asCall r = none) (hev : C.Sem.evalC cp cst cenv r = some v)
    (hl : C.Sem.lval cp cst cenv l = some loc) (hrd : C.Sem.read cst cenv loc = some old)
    (hcv : C.Sem.convLike old v = some v') (hw : C.Sem.write cst cenv loc v' = some (st', env')) :
    C.Sem.execS (m + 1) cp cst cenv (.assign l r) = .ok st' env' .normal := by
  simp only [C.Sem.execS, hcall, hev, hl, hrd, hcv, hw]

theorem exec_ret (m : Nat) (e : CExpr) (v : CVal) (hev : C.Sem.evalC cp cst cenv e = some v) :
    C.Sem.execS (m + 1) cp cst cenv (.ret (some e)) = .ok cst cenv (.ret (some v)) := by
  simp only [C.Sem.execS, hev]

end

/-! ## Zero -/

theorem cval_zero_field (o : Opts) (cp : CProg) (t : Ty) : FieldOK t →
    cval o (match t with
      | .int w => Val.int w 0
      | .bool => .bool false
      | .arr (.int w) n => .arr (Array.replicate n (.int w 0))
      | .arr _ n => .arr (Array.replicate n (.bool false))
      | .record _ => .bool false) = C.Sem.zero0 cp (cty o t) := by
  intro h
  cases t with
  | int w => simp [cty, C.Sem.zero0]
  | bool => simp [cty, C.Sem.zero0]
  | arr el n =>
    cases el with
    | int w => simp [cty, C.Sem.zero0]
    | bool => simp [cty, C.Sem.zero0]
    | arr _ _ => simp [FieldOK, Ty.isScalar] at h
    | record _ => simp [FieldOK, Ty.isScalar] at h
  | record _ => exact absurd h (by simp [FieldOK])

theorem cval_zero {p : Prog} {o : Opts} {cp : CProg} (U : Unit p o cp) (ty : Ty) (h : TyOK p ty) :
    cval o (zeroOf p ty) = C.Sem.zero cp (cty o ty) := by
  cases ty with
  | int w => simp [zeroOf, cty, C.Sem.zero, C.Sem.zero0]
  | bool => simp [zeroOf, cty, C.Sem.zero, C.Sem.zero0]
  | arr el n =>
    cases el with
    | int w => simp [zeroOf, cty, C.Sem.zero, C.Sem.zero0]
    | bool => simp [zeroOf, cty, C.Sem.zero, C.Sem.zero0]
    | arr _ _ => simp [TyOK, Ty.isScalar] at h
    | record _ => simp [TyOK, Ty.isScalar] at h
  | record r =>
    obtain ⟨sd, hsd, hf⟩ := h
    simp only [zeroOf, hsd, Option.map_some, Option.getD_some, cval_record, cty, C.Sem.zero, U.flds r sd hsd,
      List.map_map]
    congr 1
    simp only [List.map_toArray, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ft hft
    exact cval_zero_field o cp ft.2 (hf ft hft)

theorem hasTy0_zero_field (t : Ty) : FieldOK t →
    HasTy0 t (match t with
      | .int w => Val.int w 0
      | .bool => .bool false
      | .arr (.int w) n => .arr (Array.replicate n (.int w 0))
      | .arr _ n => .arr (Array.replicate n (.bool false))
      | .record _ => .bool false) := by
  intro h
  cases t with
  | int w => exact ⟨rfl, Nat.two_pow_pos _⟩
  | bool => trivial
  | arr el n =>
    cases el with
    | int w =>
      refine ⟨by simp, fun x hx => ?_⟩
      rw [Array.mem_replicate] at hx
      rw [hx.2]
      exact ⟨rfl, Nat.two_pow_pos _⟩
    | bool =>
      refine ⟨by simp, fun x hx => ?_⟩
      rw [Array.mem_replicate] at hx
      rw [hx.2]
      trivial
    | arr _ _ => simp [FieldOK, Ty.isScalar] at h
    | record _ => simp [FieldOK, Ty.isScalar] at h
  | record _ => exact absurd h (by simp [FieldOK])

theorem hasTy_zero (p : Prog) (ty : Ty) (h : TyOK p ty) : HasTy p ty (zeroOf p ty) := by
  cases ty with
  | int w => exact ⟨rfl, Nat.two_pow_pos _⟩
  | bool => trivial
  | arr el n =>
    cases el with
    | int w =>
      refine ⟨by simp, fun x hx => ?_⟩
      rw [Array.mem_replicate] at hx
      rw [hx.2]
      exact ⟨rfl, Nat.two_pow_pos _⟩
    | bool =>
      refine ⟨by simp, fun x hx => ?_⟩
      rw [Array.mem_replicate] at hx
      rw [hx.2]
      trivial
    | arr _ _ => simp [TyOK, Ty.isScalar] at h
    | record _ => simp [TyOK, Ty.isScalar] at h
  | record r =>
    obtain ⟨sd, hsd, hf⟩ := h
    refine ⟨rfl, sd, hsd, by simp [hsd], fun i hi hi' => ?_⟩
    simp only [hsd, Option.map_some, Option.getD_some, List.getElem_toArray, List.getElem_map]
    exact hasTy0_zero_field _ (hf _ (List.getElem_mem hi'))

/-! ## Declarations -/

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem sim_fuel {K : List (String × VarInfo) → Prop} {t' : Nat} {code : List CStmt} {env : Lang.Sem.Env}
    {cst : C.Sem.St} {cenv : C.Sem.Env} : Sim g K cp rt il t' code .fuel env cst cenv := trivial

/-- A declaration whose C form is one statement that cannot fail. -/
theorem decl_zero_ok (U : Unit g.prog g.opts cp) (x : String) (ty : Ty) (hty : TyOK g.prog ty) (d : CStmt)
    (hd : ∀ m (cst : C.Sem.St) (cenv : C.Sem.Env),
      C.Sem.execS (m + 1) cp cst cenv d = .ok cst ((localName x, cval g.opts (zeroOf g.prog ty)) :: cenv) .normal) :
    SPost N rt il g (.decl x ty none) cp cs
      { g with vars := (x, { ty, c := .var (localName x) }) :: g.vars } { cs with out := cs.out.push d } := by
  refine ⟨rfl, Nat.le_refl _, [d], by simp, fun k _ st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    simp only [Lang.Sem.execS, Sim]
    refine ⟨cst, _, Exec.one (hd 0 cst cenv) trivial, ?_, trivial⟩
    exact After.decl (xs := []) x ty _ hrel Temps.nil (Nat.le_refl _) hfr (hasTy_zero _ _ hty)

theorem decl_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (x : String) (ty : Ty) (init : Option Expr)
    (hw : WTS rt il g (.decl x ty init)) :
    wpc (C.stmt (.decl x ty init)) g (SPost N rt il g (.decl x ty init) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read]
  obtain ⟨htyok, hinit⟩ := hw
  cases init with
  | some e =>
    obtain ⟨we, hty, hsc⟩ := hinit
    simp only [wpc_bind, wpc_emit, wpc_pure]
    refine wpc_mono (expr_ok cp e g cs hg we ty hty hsc) ?_
    rintro ce cs1 ⟨pre, ho, sh, F⟩
    refine ⟨rfl, F.1, pre ++ [.decl (cty g.opts ty) (localName x) (some ce)], by simp [ho],
      fun k _ st env cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      obtain ⟨hok, htrap⟩ := F.2 st env cst cenv (hrel.erel U) hfr
      simp only [Lang.Sem.execS]
      cases he : Lang.Sem.evalE g.prog st env e with
      | none =>
        simp only [Sim]
        exact ⟨cst, (htrap (by simp [EOk, he])).exec _, hrel.2.world⟩
      | some v =>
        simp only [Sim]
        obtain ⟨xs, ht, hruns, hres⟩ := hok (by simp [EOk, he])
        have hev := hres v he
        have htv := evalE_hasTy g st env (hrel.erel U).typed e v ty we he hty
        refine ⟨cst, (localName x, cval g.opts v) :: (xs ++ cenv),
          hruns.exec (Exec.one (exec_decl 0 _ _ ce _ _ sh.nocall hev (convTo_cty g.opts cp g.prog ty v hsc htv))
            trivial), ?_, trivial⟩
        exact After.decl x ty v hrel ht F.1 hfr htv
  | none =>
    cases ty with
    | int w =>
      simp only [wpc_bind, wpc_emit, wpc_pure]
      refine decl_zero_ok U x _ htyok _ fun m cst cenv => ?_
      have := exec_decl (cp := cp) (cst := cst) (cenv := cenv) m (cty g.opts (.int w)) (localName x) (litC w 0)
        (.int w.bits 0) (.int w.bits 0) rfl (evalC_litC cp cst cenv w 0 (Nat.two_pow_pos _) U.i16 U.l32)
        (by simp [cty, C.Sem.convTo, C.Sem.castTo])
      simpa [zeroOf] using this
    | bool =>
      simp only [wpc_bind, wpc_emit, wpc_pure]
      refine decl_zero_ok U x _ htyok _ fun m cst cenv => ?_
      have := exec_decl (cp := cp) (cst := cst) (cenv := cenv) m .bool (localName x) (.blit false)
        (.bool false) (.bool false) rfl rfl rfl
      simpa [zeroOf] using this
    | arr el n =>
      simp only [wpc_bind, wpc_emit, wpc_pure]
      refine decl_zero_ok U x _ htyok _ fun m cst cenv => ?_
      rw [cval_zero U _ htyok]
      simp only [C.Sem.execS]
    | record r =>
      simp only [wpc_bind, wpc_emit, wpc_pure]
      refine decl_zero_ok U x _ htyok _ fun m cst cenv => ?_
      rw [cval_zero U _ htyok]
      simp only [C.Sem.execS]

end

/-! ## Assignment, `break`, `return` -/

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem assign_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (l r : Expr) (hw : WTS rt il g (.assign l r)) :
    wpc (C.stmt (.assign l r)) g (SPost N rt il g (.assign l r) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure]
  obtain ⟨hpl, wl, wr, t, htl, htr, hsc⟩ := hw
  refine wpc_mono (expr_ok cp r g cs hg wr t htr hsc) ?_
  rintro cr cs1 ⟨pre1, ho1, sh, Fr⟩
  refine wpc_mono (place_ok cp l g cs1 hg wl) ?_
  rintro ⟨cl, tl, ptr⟩ cs2 ⟨pre2, ho2, _, Fl⟩
  have F := Fr.seq Fl (ERes.stable g cp r cr)
  refine ⟨rfl, F.1, (pre1 ++ pre2) ++ [.assign cl cr], by simp [ho1, ho2], fun k _ st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    obtain ⟨hok, htrap⟩ := F.2 st env cst cenv (hrel.erel U) hfr
    simp only [Lang.Sem.execS]
    cases hr : Lang.Sem.evalE g.prog st env r with
    | none =>
      simp only [Sim]
      exact ⟨cst, (htrap (fun h => by simp [EOk, hr] at h)).exec _, hrel.2.world⟩
    | some v =>
      simp only
      by_cases hkl : EOk g l st env
      · obtain ⟨xs, ht, hruns, hres1, hres2⟩ := hok ⟨by simp [EOk, hr], hkl⟩
        obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hkl
        obtain ⟨L, hL, hroot⟩ := hres2 vold hvold
        have htv := evalE_hasTy g st env (hrel.erel U).typed r v t wr hr htr
        obtain ⟨st', env', cst', cenv', hasg, hlv, hrd, hcl, hwr, hrel2, hsame, hlen, hstk⟩ :=
          assign_sim U (hrel.temps ht) l cl ptr v vold t hsc htl wl hpl htv hvold L hL hroot
        simp only [hasg, Sim]
        refine ⟨cst', cenv', hruns.exec (Exec.one
          (exec_assign 0 cl cr _ _ _ L cst' cenv' sh.nocall (hres1 v hr) hlv hrd hcl hwr) trivial), ?_, trivial⟩
        exact After.mk0 rfl ht.allTmp hsame hrel2 hlen hstk (hrel2.fresh (hfr.append ht F.1) hsame)
      · have hnone : Lang.Sem.assign g.prog st env l v = none := by
          cases h : Lang.Sem.assign g.prog st env l v with
          | none => rfl
          | some r' =>
            obtain ⟨u, hu, _⟩ := update_some g.prog st env l _ r' h
            exact absurd (by simp [EOk, hu]) hkl
        simp only [hnone, Sim]
        exact ⟨cst, (htrap (fun h => hkl h.2)).exec _, hrel.2.world⟩

theorem brk_ok (U : Unit g.prog g.opts cp) (hw : WTS rt il g .brk) :
    wpc (C.stmt .brk) g (SPost N rt il g .brk cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure]
  refine ⟨rfl, Nat.le_refl _, [.brk], by simp, fun k _ st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    simp only [Lang.Sem.execS, Sim]
    refine ⟨cst, cenv, Exec.one (m := 1) rfl trivial, ?_, hw⟩
    exact After.mk0 (xs := []) rfl AllTmp.nil (Same.refl _) hrel rfl rfl hfr

theorem ret_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (e : Option Expr) (hw : WTS rt il g (.ret e)) :
    wpc (C.stmt (.ret e)) g (SPost N rt il g (.ret e) cp cs) cs := by
  cases e with
  | none =>
    rw [C.stmt]
    simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure]
    refine ⟨rfl, Nat.le_refl _, [.ret none], by simp, fun k _ st env cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      simp only [Lang.Sem.execS, Sim]
      refine ⟨cst, cenv, Exec.one (m := 1) rfl trivial, ?_, hw⟩
      exact After.mk0 (xs := []) rfl AllTmp.nil (Same.refl _) hrel rfl rfl hfr
  | some e =>
    obtain ⟨we, t, hrt, hty, hsc⟩ := hw
    rw [C.stmt]
    simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure]
    refine wpc_mono (expr_ok cp e g cs hg we t hty hsc) ?_
    rintro ce cs1 ⟨pre, ho, sh, F⟩
    refine ⟨rfl, F.1, pre ++ [.ret (some ce)], by simp [ho], fun k _ st env cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      obtain ⟨hok, htrap⟩ := F.2 st env cst cenv (hrel.erel U) hfr
      simp only [Lang.Sem.execS]
      cases he : Lang.Sem.evalE g.prog st env e with
      | none =>
        simp only [Sim]
        exact ⟨cst, (htrap (by simp [EOk, he])).exec _, hrel.2.world⟩
      | some v =>
        simp only [Sim]
        obtain ⟨xs, ht, hruns, hres⟩ := hok (by simp [EOk, he])
        have htv := evalE_hasTy g st env (hrel.erel U).typed e v t we he hty
        refine ⟨cst, xs ++ cenv, hruns.exec (Exec.one (exec_ret 0 ce _ (hres v he)) trivial), ?_,
          ⟨t, hrt, hsc, htv⟩⟩
        exact After.mk0 rfl ht.allTmp (Same.refl _) (hrel.temps ht) rfl rfl (hfr.append ht F.1)

/-- A prefix that does nothing. -/
theorem Sim.line {K : List (String × VarInfo) → Prop} {t' : Nat} {code : List CStmt} {R : Lang.Sem.Res}
    {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env} (n : Nat) (f : String)
    (h : Sim g K cp rt il t' code R env cst cenv) : Sim g K cp rt il t' (.line n f :: code) R env cst cenv := by
  have hr : Runs cp cst cenv [.line n f] cenv := Runs.single fun m => rfl
  cases R with
  | ok st' env' out =>
    obtain ⟨cst', cenv', hx, ha, ho⟩ := h
    exact ⟨cst', cenv', hr.exec hx, ha, ho⟩
  | trap st' =>
    obtain ⟨cst', hx, hw⟩ := h
    exact ⟨cst', hr.exec hx, hw⟩
  | fuel => trivial

/-- A statement with its source position. -/
theorem at_ok (sp : Span) (s : Stmt)
    (ih : ∀ cs0 : CS, wpc (C.stmt s) g (SPost N rt il g s cp cs0) cs0) :
    wpc (C.stmt (.at sp s)) g (SPost N rt il g (.at sp s) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read]
  by_cases hl : (g.opts.lines && decide (sp.line > 0)) = true
  · rw [if_pos hl]
    simp only [wpc_bind, wpc_emit]
    refine wpc_mono (ih _) ?_
    rintro g' cs' ⟨hg', htmp, code, ho, hsim⟩
    refine ⟨hg', htmp, .line sp.line sp.file :: code, by simp [ho], fun k hk st env cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      simp only [Lang.Sem.execS]
      exact (hsim j (by omega) st env cst cenv hrel hfr).line _ _
  · rw [if_neg hl]
    refine wpc_mono (ih _) ?_
    rintro g' cs' ⟨hg', htmp, code, ho, hsim⟩
    refine ⟨hg', htmp, code, ho, fun k hk st env cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      simp only [Lang.Sem.execS]
      exact hsim j (by omega) st env cst cenv hrel hfr

end

/-! ## Blocks -/

/-- A block as a whole: the scope it ran in is related again. -/
def BSim (g : C.Env) (cp : CProg) (rt : Option Ty) (il : Bool) (code : List CStmt) (R : Lang.Sem.Res)
    (env : Lang.Sem.Env) (cst : C.Sem.St) (cenv : C.Sem.Env) : Prop :=
  match R with
  | .ok st' env' out =>
    ∃ m cst' cenv', C.Sem.execB m cp cst cenv code = .ok cst' cenv' (cout g.opts out) ∧
      env'.length = env.length ∧ Same cenv cenv' ∧ SRel g st' env' cst' cenv' ∧ cst'.stack = cst.stack ∧
      OutOK g.prog rt il out
  | .trap st' => ∃ m cst', C.Sem.execB m cp cst cenv code = .trap cst' ∧ cst'.world = st'.world
  | .fuel => True

section
variable {g : C.Env} {cp : CProg} {rt : Option Ty} {il : Bool}

theorem Sim.block {K : List (String × VarInfo) → Prop} {t' : Nat} {code : List CStmt} {ss : List Stmt} {j : Nat}
    {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env}
    (h : Sim g K cp rt il t' code (Lang.Sem.execL j g.prog st env ss) env cst cenv) :
    BSim g cp rt il code (Lang.Sem.execB (j + 1) g.prog st env ss) env cst cenv := by
  rw [Lang.Sem.execB]
  cases hR : Lang.Sem.execL j g.prog st env ss with
  | ok st' env' out =>
    rw [hR] at h
    obtain ⟨cst', cenv', hx, ⟨ys, env1, xs, cenv1, rfl, rfl, hlen, hsame, hrel, hstk, _, _⟩, hout⟩ := h
    obtain ⟨m, hm⟩ := hx.block
    have e1 : (ys ++ env1).drop ((ys ++ env1).length - env.length) = env1 := by
      rw [List.length_append, hlen, Nat.add_sub_cancel]; exact List.drop_left
    have e2 : (xs ++ cenv1).drop ((xs ++ cenv1).length - cenv.length) = cenv1 := by
      rw [List.length_append, ← hsame.length, Nat.add_sub_cancel]; exact List.drop_left
    simp only [BSim, e1]
    rw [e2] at hm
    exact ⟨m, cst', cenv1, hm, hlen, hsame, hrel, hstk, hout⟩
  | trap st' =>
    rw [hR] at h
    obtain ⟨cst', hx, hw⟩ := h
    obtain ⟨m, hm⟩ := hx.block_trap
    exact ⟨m, cst', hm, hw⟩
  | fuel => trivial

/-- A C statement that runs a block, after a prefix that declared temporaries. -/
theorem Sim.of_block {K : List (String × VarInfo) → Prop} (hK : K []) {t' : Nat} {pre cb : List CStmt}
    {stm : CStmt} {R : Lang.Sem.Res} {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv xs : C.Sem.Env}
    (hruns : Runs cp cst cenv pre (xs ++ cenv)) (ht : AllTmp xs)
    (hstm : ∀ m, C.Sem.execS (m + 1) cp cst (xs ++ cenv) stm = C.Sem.execB m cp cst (xs ++ cenv) cb)
    (hfr : Fresh t' cst (xs ++ cenv)) (hb : BSim g cp rt il cb R env cst (xs ++ cenv)) :
    Sim g K cp rt il t' (pre ++ [stm]) R env cst cenv := by
  cases R with
  | ok st' env' out =>
    obtain ⟨m, cst', cenv', hm, hlen, hsame, hrel, hstk, hout⟩ := hb
    refine ⟨cst', cenv', hruns.exec (Exec.one (m := m + 1) (by rw [hstm, hm]) trivial), ?_, hout⟩
    exact After.mk0 hK ht hsame hrel hlen hstk (hrel.fresh hfr hsame)
  | trap st' =>
    obtain ⟨m, cst', hm, hw⟩ := hb
    exact ⟨cst', hruns.exec (Exec.one (m := m + 1) (by rw [hstm, hm]) trivial), hw⟩
  | fuel => trivial

end

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem ite_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (c : Expr) (t e : List Stmt)
    (hw : WTS rt il g (.ite c t e))
    (iht : ∀ cs0 : CS, wpc (blockFrom g.path 1 g t) g (BPost N rt il g t cp cs0) cs0)
    (ihe : ∀ cs0 : CS, wpc (blockFrom g.path 1 g e) g (BPost N rt il g e cp cs0) cs0) :
    wpc (C.stmt (.ite c t e)) g (SPost N rt il g (.ite c t e) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure]
  obtain ⟨wc, htc, _, _⟩ := hw
  refine wpc_mono (expr_ok cp c g cs hg wc .bool htc rfl) ?_
  rintro cc cs1 ⟨pre, ho, sh, F⟩
  rw [wpc_collect]
  refine wpc_mono (iht _) ?_
  rintro ⟨⟩ cs2 ⟨htmp2, ct, hct, hsimT⟩
  rw [wpc_collect]
  refine wpc_mono (ihe _) ?_
  rintro ⟨⟩ cs3 ⟨htmp3, ce, hce, hsimE⟩
  simp only [Array.empty_append] at hct hce
  have h12 : cs1.tmp ≤ cs2.tmp := htmp2
  have h23 : cs2.tmp ≤ cs3.tmp := htmp3
  refine ⟨rfl, Nat.le_trans F.1 (Nat.le_trans h12 h23), pre ++ [.ite cc ct ce], by simp [ho, hct, hce],
    fun k hk st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    obtain ⟨hok, htrap⟩ := F.2 st env cst cenv (hrel.erel U) hfr
    simp only [Lang.Sem.execS]
    cases hc : Lang.Sem.evalE g.prog st env c with
    | none =>
      simp only [Sim]
      exact ⟨cst, (htrap (by simp [EOk, hc])).exec _, hrel.2.world⟩
    | some cv =>
      simp only
      obtain ⟨xs, ht, hruns, hres⟩ := hok (by simp [EOk, hc])
      obtain ⟨b, rfl⟩ := hasTy_bool (evalE_hasTy g st env (hrel.erel U).typed c cv .bool wc hc htc)
      have hcc := hres _ hc
      rw [cval_bool] at hcc
      have hfr1 := hfr.append ht F.1
      cases b with
      | true =>
        simp only [Val.toBool, if_true]
        cases j with
        | zero => exact sim_fuel
        | succ i =>
          refine Sim.of_block (K := fun nv => g.vars = nv ++ g.vars) (stm := .ite cc ct ce) (cb := ct) rfl hruns ht.allTmp
            (fun m => by simp only [C.Sem.execS, hcc, C.Sem.truthy]) (hfr1.mono (Nat.le_trans h12 h23)) ?_
          exact (hsimT i (by omega) st env cst (xs ++ cenv) (hrel.temps ht) hfr1).block
      | false =>
        simp only [Val.toBool, Bool.false_eq_true, if_false]
        cases j with
        | zero => exact sim_fuel
        | succ i =>
          refine Sim.of_block (K := fun nv => g.vars = nv ++ g.vars) (stm := .ite cc ct ce) (cb := ce) rfl hruns ht.allTmp
            (fun m => by simp only [C.Sem.execS, hcc, C.Sem.truthy]) (hfr1.mono (Nat.le_trans h12 h23)) ?_
          exact (hsimE i (by omega) st env cst (xs ++ cenv) (hrel.temps ht) (hfr1.mono h12)).block

end

/-! ## `loop (max := n)` -/

theorem Same.cons_tmp_inv {k : Nat} {v : CVal} {a c : C.Sem.Env} (h : Same ((tmpName k, v) :: a) c) :
    ∃ a', c = (tmpName k, v) :: a' ∧ Same a a' := by
  cases h with
  | @cons _ y _ b hx h =>
    obtain ⟨n, w⟩ := y
    simp only at hx
    obtain ⟨rfl, hv⟩ := hx
    rw [hv ⟨k, rfl⟩]
    exact ⟨b, rfl, h⟩

theorem Same.cons_inv {x : String} {v : CVal} {a c : C.Sem.Env} (h : Same ((x, v) :: a) c) :
    ∃ v' a', c = (x, v') :: a' ∧ Same a a' := by
  cases h with
  | @cons _ y _ b hx h =>
    obtain ⟨n, w⟩ := y
    simp only at hx
    obtain ⟨rfl, _⟩ := hx
    exact ⟨w, b, rfl, h⟩

theorem OutOK.ret_il {p : Prog} {rt : Option Ty} {il il' : Bool} {v : Option Val}
    (h : OutOK p rt il (.ret v)) : OutOK p rt il' (.ret v) := by
  cases v <;> exact h

/-- What the C loop does from the counter value `v`. -/
def LSim (g : C.Env) (cp : CProg) (rt : Option Ty) (il : Bool) (k : String) (bits v : Nat) (hi : CExpr)
    (cb : List CStmt) (R : Lang.Sem.Res) (env : Lang.Sem.Env) (cst : C.Sem.St) (cT : C.Sem.Env) : Prop :=
  match R with
  | .ok st' env' out =>
    ∃ m cst' x cT', C.Sem.forC m cp cst ((k, .int bits v) :: cT) k hi cb
        = .ok cst' ((k, x) :: cT') (cout g.opts out) ∧
      env'.length = env.length ∧ Same cT cT' ∧ SRel g st' env' cst' cT' ∧ cst'.stack = cst.stack ∧
      OutOK g.prog rt il out
  | .trap st' =>
    ∃ m cst', C.Sem.forC m cp cst ((k, .int bits v) :: cT) k hi cb = .trap cst' ∧ cst'.world = st'.world
  | .fuel => True

theorem loop_sim {g : C.Env} {cp : CProg} {rt : Option Ty} {il : Bool} {N : Nat} {body : List Stmt}
    {cb : List CStmt} {tk t' : Nat} {bits bh n : Nat} {hi : CExpr}
    (hbody : ∀ i, i ≤ N → ∀ st env cst cenv, SRel g st env cst cenv → Fresh (tk + 1) cst cenv →
      Sim g (fun _ => True) cp rt true t' cb (Lang.Sem.execL i g.prog st env body) env cst cenv)
    (hn : n < 2 ^ bits)
    (hhi : ∀ (cst : C.Sem.St) (cenv : C.Sem.Env), C.Sem.evalC cp cst cenv hi = some (.int bh n)) :
    ∀ j, j ≤ N + 1 → ∀ r v, v + r = n → ∀ st env cst cT, SRel g st env cst cT → Fresh tk cst cT →
      LSim g cp rt il (tmpName tk) bits v hi cb (Lang.Sem.loopN j g.prog st env r body) env cst cT := by
  intro j
  induction j with
  | zero => intro _ r v _ st env cst cT _ _; rw [Lang.Sem.loopN]; trivial
  | succ j ih =>
    intro hj r v hv st env cst cT hrel hfr
    cases r with
    | zero =>
      rw [Lang.Sem.loopN]
      refine ⟨1, cst, .int bits v, cT, ?_, rfl, Same.refl _, hrel, rfl, trivial⟩
      have hvn : ¬ v < n := by omega
      rw [C.Sem.forC]
      simp only [List.lookup, beq_self_eq_true, hhi, hvn, if_false, cout]
    | succ r =>
      rw [Lang.Sem.loopN]
      have hlt : v < n := by omega
      cases j with
      | zero => rw [Lang.Sem.execB]; trivial
      | succ i =>
        have hb := (hbody i (by omega) st env cst ((tmpName tk, .int bits v) :: cT) ⟨.tmp tk _ hrel.1, hrel.2⟩
          (hfr.cons_tmp _)).block
        cases hR : Lang.Sem.execB (i + 1) g.prog st env body with
        | fuel => trivial
        | trap st' =>
          rw [hR] at hb
          obtain ⟨m, cst', hm, hw⟩ := hb
          refine ⟨m + 1, cst', ?_, hw⟩
          rw [C.Sem.forC]
          simp only [List.lookup, beq_self_eq_true, hhi, hlt, if_true, hm]
        | ok st' env' out =>
          rw [hR] at hb
          obtain ⟨m, cst', cB, hm, hlen, hsame, hrel', hstk, hout⟩ := hb
          obtain ⟨cT', rfl, hsT⟩ := hsame.cons_tmp_inv
          have hrelT : SRel g st' env' cst' cT' := ⟨hrel'.1.tail_tmp tk _ _ rfl, hrel'.2⟩
          cases out with
          | brk =>
            refine ⟨m + 1, cst', .int bits v, cT', ?_, hlen, hsT, hrelT, hstk, trivial⟩
            rw [C.Sem.forC]
            simp only [List.lookup, beq_self_eq_true, hhi, hlt, if_true, hm, cout]
          | ret rv =>
            refine ⟨m + 1, cst', .int bits v, cT', ?_, hlen, hsT, hrelT, hstk, hout.ret_il⟩
            rw [C.Sem.forC]
            simp only [List.lookup, beq_self_eq_true, hhi, hlt, if_true, hm, cout]
          | normal =>
            have ih' := ih (by omega) r (v + 1) (by omega) st' env' cst' cT' hrelT (hrelT.fresh hfr hsT)
            have hv1 : (v + 1) % 2 ^ bits = v + 1 := Nat.mod_eq_of_lt (by omega)
            have step : ∀ M, m ≤ M → C.Sem.forC (M + 1) cp cst ((tmpName tk, .int bits v) :: cT) (tmpName tk) hi cb
                = C.Sem.forC M cp cst' ((tmpName tk, .int bits (v + 1)) :: cT') (tmpName tk) hi cb := by
              intro M hM
              rw [C.Sem.forC]
              simp only [List.lookup, beq_self_eq_true, hhi, hlt, if_true, C.Sem.execB_le hM hm trivial, cout,
                C.Sem.setFirst, hv1]
            simp only
            cases hR2 : Lang.Sem.loopN (i + 1) g.prog st' env' r body with
            | fuel => trivial
            | trap st'' =>
              rw [hR2] at ih'
              obtain ⟨m2, cst'', hm2, hw⟩ := ih'
              refine ⟨max m m2 + 1, cst'', ?_, hw⟩
              rw [step _ (Nat.le_max_left m m2)]
              exact C.Sem.forC_le (Nat.le_max_right m m2) hm2 trivial
            | ok st'' env'' out2 =>
              rw [hR2] at ih'
              obtain ⟨m2, cst'', x, cT'', hm2, hlen2, hs2, hrel2, hstk2, hout2⟩ := ih'
              refine ⟨max m m2 + 1, cst'', x, cT'', ?_, hlen2.trans hlen, hsT.trans hs2, hrel2, hstk2.trans hstk,
                hout2⟩
              rw [step _ (Nat.le_max_left m m2)]
              exact C.Sem.forC_le (Nat.le_max_right m m2) hm2 trivial

theorem counter_lt (n : Nat) (hn : n < 2 ^ 32) : n < 2 ^ (counterTy n).bits := by
  unfold counterTy
  split
  · simpa [Width.bits] using ‹n < 256›
  · split
    · simpa [Width.bits] using ‹n < 65536›
    · simpa [Width.bits] using hn

theorem evalC_lit_counter (cp : CProg) (n : Nat) (hn : n < 2 ^ 32) (h16 : 16 ≤ cp.intBits) (h32 : 32 ≤ cp.longBits) :
    ∃ b, ∀ (cst : C.Sem.St) (cenv : C.Sem.Env),
      C.Sem.evalC cp cst cenv (.lit n (suffix (counterTy n))) = some (.int b n) := by
  have hb : ∃ b, C.Sem.litBits cp (suffix (counterTy n)) = some b ∧ n < 2 ^ b := by
    unfold counterTy
    split
    · exact ⟨cp.intBits, rfl, Nat.lt_of_lt_of_le (Nat.lt_trans ‹n < 256› (by decide : 256 < 2 ^ 16))
        (Nat.pow_le_pow_right (by decide) h16)⟩
    · split
      · exact ⟨cp.intBits, rfl, Nat.lt_of_lt_of_le (by simpa using ‹n < 65536›)
          (Nat.pow_le_pow_right (by decide) h16)⟩
      · exact ⟨cp.longBits, rfl, Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) h32)⟩
  obtain ⟨b, hb, hlt⟩ := hb
  exact ⟨b, fun cst cenv => by simp only [C.Sem.evalC, hb, hlt, if_true]⟩

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem loop_ok (U : Unit g.prog g.opts cp) (n : Nat) (body : List Stmt) (hw : WTS rt il g (.loop n body))
    (ihb : ∀ cs0 : CS, wpc (blockFrom g.path 1 g body) g (BPost N rt true g body cp cs0) cs0) :
    wpc (C.stmt (.loop n body)) g (SPost N rt il g (.loop n body) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure, wpc_fresh]
  rw [wpc_collect]
  refine wpc_mono (ihb _) ?_
  rintro ⟨⟩ cs2 ⟨htmp2, cb, hcb, hsim⟩
  simp only [Array.empty_append] at hcb
  have h12 : cs.tmp + 1 ≤ cs2.tmp := htmp2
  obtain ⟨bh, hhi⟩ := evalC_lit_counter cp n hw.1 U.i16 U.l32
  refine ⟨rfl, Nat.le_trans (Nat.le_succ _) h12,
    [.forUp (.uint (counterTy n).bits) (tmpName cs.tmp) (litC (counterTy n) 0) (.lit n (suffix (counterTy n))) cb],
    by simp [hcb], fun k hk st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    simp only [Lang.Sem.execS]
    have hl := loop_sim (il := il) (tk := cs.tmp) hsim (counter_lt n hw.1) hhi j (by omega) n 0 (by omega) st env
      cst cenv hrel hfr
    have hlo := evalC_litC cp cst cenv (counterTy n) 0 (Nat.two_pow_pos _) U.i16 U.l32
    cases hR : Lang.Sem.loopN j g.prog st env n body with
    | fuel => trivial
    | trap st' =>
      rw [hR] at hl
      obtain ⟨m, cst', hm, hw'⟩ := hl
      refine ⟨cst', Exec.one (m := m + 1) ?_ trivial, hw'⟩
      simp only [C.Sem.execS, hlo, C.Sem.convTo, castTo_uint, Nat.zero_mod, hm]
    | ok st' env' out =>
      rw [hR] at hl
      obtain ⟨m, cst', x, cT', hm, hlen, hsame, hrel', hstk, hout⟩ := hl
      refine ⟨cst', cT', Exec.one (m := m + 1) ?_ trivial, ?_, hout⟩
      · simp only [C.Sem.execS, hlo, C.Sem.convTo, castTo_uint, Nat.zero_mod, hm, List.drop]
      · exact After.mk0 (xs := []) rfl AllTmp.nil hsame hrel' hlen hstk
          (hrel'.fresh (hfr.mono (Nat.le_trans (Nat.le_succ _) h12)) hsame)

end

/-! ## `for` -/

theorem evalC_var_lookup {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} {y : String} {v : CVal}
    (h : cenv.lookup y = some v) : C.Sem.evalC cp cst cenv (.var y) = some v := by
  simp [C.Sem.evalC, C.Sem.varLoc, h, C.Sem.read, C.Sem.readBase, C.Sem.getPath]

/-- What the C `for` does from the counter value `cur`. -/
def FSim (g : C.Env) (cp : CProg) (rt : Option Ty) (il : Bool) (x : String) (bits : Nat) (th tl : String)
    (hiv : Nat) (lov : CVal) (cur : Nat) (cb : List CStmt) (R : Lang.Sem.Res) (envT : Lang.Sem.Env)
    (cst : C.Sem.St) (cT : C.Sem.Env) : Prop :=
  match R with
  | .ok st' env' out =>
    ∃ m cst' y cT' v' envT',
      C.Sem.forC m cp cst ((localName x, .int bits cur) :: (th, .int bits hiv) :: (tl, lov) :: cT) (localName x)
          (.var th) cb
        = .ok cst' ((localName x, y) :: (th, .int bits hiv) :: (tl, lov) :: cT') (cout g.opts out) ∧
      env' = (x, v') :: envT' ∧ envT'.length = envT.length ∧ Same cT cT' ∧
      SRel g st' envT' cst' ((th, .int bits hiv) :: (tl, lov) :: cT') ∧ cst'.stack = cst.stack ∧
      OutOK g.prog rt il out
  | .trap st' =>
    ∃ m cst', C.Sem.forC m cp cst ((localName x, .int bits cur) :: (th, .int bits hiv) :: (tl, lov) :: cT)
        (localName x) (.var th) cb = .trap cst' ∧ cst'.world = st'.world
  | .fuel => True

theorem for_sim {g : C.Env} {cp : CProg} {rt : Option Ty} {il : Bool} {N : Nat} {x : String} {w : Width}
    {body : List Stmt} {cb : List CStmt} {t0 t' : Nat} {hiv : Nat} {lov : CVal}
    (hnr : NoRef g.prog) (hnw : NoWriteL x body)
    (hbody : ∀ i, i ≤ N → ∀ st env cst cenv,
      SRel { g with vars := (x, { ty := .int w, c := .var (localName x) }) :: g.vars } st env cst cenv →
      Fresh (t0 + 2) cst cenv →
      Sim { g with vars := (x, { ty := .int w, c := .var (localName x) }) :: g.vars } (fun _ => True) cp rt true t' cb
        (Lang.Sem.execL i g.prog st env body) env cst cenv)
    (hhi : hiv < 2 ^ w.bits) :
    ∀ j, j ≤ N + 1 → ∀ cur st v0 envT cst cT,
      SRel g st envT cst ((tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT) → Fresh t0 cst cT →
      FSim g cp rt il x w.bits (tmpName (t0 + 1)) (tmpName t0) hiv lov cur cb
        (Lang.Sem.forLoop j g.prog st ((x, v0) :: envT) x w cur hiv body) envT cst cT := by
  have hth : ∀ (cst : C.Sem.St) (y : CVal) (cT : C.Sem.Env),
      C.Sem.evalC cp cst ((localName x, y) :: (tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT)
        (.var (tmpName (t0 + 1))) = some (.int w.bits hiv) := by
    intro cst y cT
    apply evalC_var_lookup
    have hne : (tmpName (t0 + 1) == localName x) = false := by
      cases h : tmpName (t0 + 1) == localName x
      · rfl
      · rw [beq_iff_eq] at h; exact absurd h (tmp_ne_local _ _)
    simp [List.lookup, hne]
  intro j
  induction j with
  | zero => intro _ cur st v0 envT cst cT _ _; rw [Lang.Sem.forLoop]; trivial
  | succ j ih =>
    intro hj cur st v0 envT cst cT hrel hfr
    rw [Lang.Sem.forLoop]
    by_cases hlt : cur < hiv
    · rw [if_pos hlt]
      simp only [Lang.Sem.setFirst, beq_self_eq_true, if_true]
      cases j with
      | zero => rw [Lang.Sem.execB]; trivial
      | succ i =>
        have hc64 : cur < 2 ^ 64 :=
          Nat.lt_of_lt_of_le (Nat.lt_trans hlt hhi) (Nat.pow_le_pow_right (by decide) (by cases w <;> decide))
        have hcn : (UInt64.ofNat cur).toNat = cur := by
          rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hc64
        have hcv : cval g.opts (.int w (UInt64.ofNat cur)) = .int w.bits cur := by rw [cval_int, hcn]
        have hrelI : SRel { g with vars := (x, { ty := .int w, c := .var (localName x) }) :: g.vars } st
            ((x, .int w (UInt64.ofNat cur)) :: envT) cst
            ((localName x, .int w.bits cur) :: (tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT) := by
          refine ⟨?_, hrel.2⟩
          rw [← hcv]
          exact .val x (.int w) _ (hasTy_int_mk _ w _ (by rw [hcn]; exact Nat.lt_trans hlt hhi)) hrel.1
        have hfrI : Fresh (t0 + 2) cst
            ((localName x, .int w.bits cur) :: (tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT) :=
          (((hfr.cons_tmp lov).cons_tmp _).cons_local x _)
        have hb := (hbody i (by omega) st _ cst _ hrelI hfrI).block
        cases hR : Lang.Sem.execB (i + 1) g.prog st ((x, .int w (UInt64.ofNat cur)) :: envT) body with
        | fuel => trivial
        | trap st' =>
          rw [hR] at hb
          obtain ⟨m, cst', hm, hw⟩ := hb
          refine ⟨m + 1, cst', ?_, hw⟩
          rw [C.Sem.forC]
          simp only [List.lookup, beq_self_eq_true, hth, hlt, if_true, hm]
        | ok st' env' out =>
          rw [hR] at hb
          obtain ⟨m, cst', cB, hm, hlen, hsame, hrel', hstk, hout⟩ := hb
          obtain ⟨y, c1, rfl, hs1⟩ := hsame.cons_inv
          obtain ⟨c2, rfl, hs2⟩ := hs1.cons_tmp_inv
          obtain ⟨cT', rfl, hsT⟩ := hs2.cons_tmp_inv
          obtain ⟨ty, v', vs', envT', hvs, rfl, rfl, hty', hlrel⟩ := hrel'.1.head_val x y _ rfl
          simp only [List.cons.injEq] at hvs
          obtain ⟨_, rfl⟩ := hvs
          have hrelT : SRel g st' envT' cst'
              ((tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT') := ⟨hlrel, hrel'.2⟩
          have hlenT : envT'.length = envT.length := by simpa using hlen
          have hk := ((keeps g.prog hnr x (i + 1)).1 _ _ _ _ _ _ hR hnw).2
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hk
          subst hk
          rw [hcv] at hm
          cases out with
          | brk =>
            refine ⟨m + 1, cst', .int w.bits cur, cT', _, envT', ?_, rfl, hlenT, hsT, hrelT, hstk, trivial⟩
            rw [C.Sem.forC]
            simp only [List.lookup, beq_self_eq_true, hth, hlt, if_true, hm, cout]
          | ret rv =>
            refine ⟨m + 1, cst', .int w.bits cur, cT', _, envT', ?_, rfl, hlenT, hsT, hrelT, hstk, hout.ret_il⟩
            rw [C.Sem.forC]
            simp only [List.lookup, beq_self_eq_true, hth, hlt, if_true, hm, cout]
          | normal =>
            have ih' := ih (by omega) (cur + 1) st' (.int w (UInt64.ofNat cur)) envT' cst' cT' hrelT
              (hfr.same hsT hrelT.2.gtmp)
            have hv1 : (cur + 1) % 2 ^ w.bits = cur + 1 := Nat.mod_eq_of_lt (by omega)
            have step : ∀ M, m ≤ M →
                C.Sem.forC (M + 1) cp cst
                  ((localName x, .int w.bits cur) :: (tmpName (t0 + 1), .int w.bits hiv) :: (tmpName t0, lov) :: cT)
                  (localName x) (.var (tmpName (t0 + 1))) cb
                = C.Sem.forC M cp cst'
                  ((localName x, .int w.bits (cur + 1)) :: (tmpName (t0 + 1), .int w.bits hiv) ::
                    (tmpName t0, lov) :: cT') (localName x) (.var (tmpName (t0 + 1))) cb := by
              intro M hM
              rw [C.Sem.forC]
              simp only [List.lookup, beq_self_eq_true, hth, hlt, if_true, C.Sem.execB_le hM hm trivial, cout,
                C.Sem.setFirst, hv1]
            simp only
            cases hR2 : Lang.Sem.forLoop (i + 1) g.prog st' ((x, .int w (UInt64.ofNat cur)) :: envT') x w (cur + 1)
                hiv body with
            | fuel => trivial
            | trap st'' =>
              rw [hR2] at ih'
              obtain ⟨m2, cst'', hm2, hw⟩ := ih'
              refine ⟨max m m2 + 1, cst'', ?_, hw⟩
              rw [step _ (Nat.le_max_left m m2)]
              exact C.Sem.forC_le (Nat.le_max_right m m2) hm2 trivial
            | ok st'' env'' out2 =>
              rw [hR2] at ih'
              obtain ⟨m2, cst'', y2, cT'', v2, envT'', hm2, he2, hlen2, hs2', hrel2, hstk2, hout2⟩ := ih'
              refine ⟨max m m2 + 1, cst'', y2, cT'', v2, envT'', ?_, he2, hlen2.trans hlenT, hsT.trans hs2', hrel2,
                hstk2.trans hstk, hout2⟩
              rw [step _ (Nat.le_max_left m m2)]
              exact C.Sem.forC_le (Nat.le_max_right m m2) hm2 trivial
    · rw [if_neg hlt]
      refine ⟨1, cst, .int w.bits cur, cT, v0, envT, ?_, rfl, rfl, Same.refl _, hrel, rfl, trivial⟩
      rw [C.Sem.forC]
      simp only [List.lookup, beq_self_eq_true, hth, hlt, if_false, cout]

section
variable {g : C.Env} {cp : CProg} {cs : CS} {N : Nat} {rt : Option Ty} {il : Bool}

theorem for_ok (U : Unit g.prog g.opts cp) (hg : EnvOK g) (hnr : NoRef g.prog) (x : String) (w : Option Width)
    (lo hi : Expr) (body : List Stmt) (hw : WTS rt il g (.forRange x w lo hi body))
    (ihb : ∀ cs0 : CS,
      wpc (blockFrom g.path 1
        { g with vars := (x, { ty := .int (w.getD .w32), c := .var (localName x) }) :: g.vars } body) g
        (BPost N rt true { g with vars := (x, { ty := .int (w.getD .w32), c := .var (localName x) }) :: g.vars }
          body cp cs0) cs0) :
    wpc (C.stmt (.forRange x w lo hi body)) g (SPost N rt il g (.forRange x w lo hi body) cp cs) cs := by
  rw [C.stmt]
  simp only [wpc_bind, wpc_read, wpc_emit, wpc_pure, wpc_fresh]
  obtain ⟨wlo, whi, htlo, hthi, hnw, _⟩ := hw
  refine wpc_mono (expr_ok cp lo g cs hg wlo _ htlo rfl) ?_
  rintro clo cs1 ⟨pre1, ho1, sh1, Flo⟩
  refine wpc_mono (expr_ok cp hi g cs1 hg whi _ hthi rfl) ?_
  rintro chi cs2 ⟨pre2, ho2, sh2, Fhi⟩
  rw [wpc_collect]
  refine wpc_mono (ihb _) ?_
  rintro ⟨⟩ cs3 ⟨htmp3, cb, hcb, hsim⟩
  simp only [Array.empty_append] at hcb
  have h23 : cs2.tmp + 2 ≤ cs3.tmp := htmp3
  have F := Flo.seq Fhi (ERes.stable g cp lo clo)
  have h02 : cs.tmp ≤ cs2.tmp := F.1
  refine ⟨rfl, by show cs.tmp ≤ cs3.tmp; omega,
    (pre1 ++ pre2) ++ [.block [.decl (.uint (w.getD .w32).bits) (tmpName cs2.tmp) (some clo),
      .decl (.uint (w.getD .w32).bits) (tmpName (cs2.tmp + 1)) (some chi),
      .forUp (.uint (w.getD .w32).bits) (localName x) (.var (tmpName cs2.tmp)) (.var (tmpName (cs2.tmp + 1))) cb]],
    by simp [ho1, ho2, hcb], fun k hk st env cst cenv hrel hfr => ?_⟩
  cases k with
  | zero => exact sim_fuel
  | succ j =>
    obtain ⟨hok, htrap⟩ := F.2 st env cst cenv (hrel.erel U) hfr
    simp only [Lang.Sem.execS]
    cases hlo : Lang.Sem.evalE g.prog st env lo with
    | none =>
      have ht' := htrap (fun h => by simp [EOk, hlo] at h)
      cases hhi : Lang.Sem.evalE g.prog st env hi <;> exact ⟨cst, ht'.exec _, hrel.2.world⟩
    | some a =>
      cases hhi : Lang.Sem.evalE g.prog st env hi with
      | none => exact ⟨cst, (htrap (fun h => by simp [EOk, hhi] at h)).exec _, hrel.2.world⟩
      | some b =>
        simp only
        obtain ⟨xs, ht, hruns, hres1, hres2⟩ := hok ⟨by simp [EOk, hlo], by simp [EOk, hhi]⟩
        obtain ⟨av, rfl, hav⟩ := hasTy_int (evalE_hasTy g st env (hrel.erel U).typed lo a _ wlo hlo htlo)
        obtain ⟨bv, rfl, hbv⟩ := hasTy_int (evalE_hasTy g st env (hrel.erel U).typed hi b _ whi hhi hthi)
        have hclo := hres1 _ hlo
        have hchi := hres2 _ hhi
        rw [cval_int] at hclo hchi
        have hfrX : Fresh cs2.tmp cst (xs ++ cenv) := hfr.append ht F.1
        have r1 : Runs cp cst (xs ++ cenv) [.decl (.uint (w.getD .w32).bits) (tmpName cs2.tmp) (some clo)]
            ((tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv)) :=
          Runs.single fun m => exec_decl (m + 4) _ _ clo _ _ sh1.nocall hclo
            (by simp only [C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hav])
        have hx1 : Ext [(tmpName cs2.tmp, CVal.int (w.getD .w32).bits av.toNat)] (xs ++ cenv) cst :=
          hfrX.ext (Temps.one cs2.tmp _)
        have hchi' := C.Sem.evalC_ext hx1 chi hchi
        have r2 : Runs cp cst ((tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv))
            [.decl (.uint (w.getD .w32).bits) (tmpName (cs2.tmp + 1)) (some chi)]
            ((tmpName (cs2.tmp + 1), .int (w.getD .w32).bits bv.toNat) ::
              (tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv)) :=
          Runs.single fun m => exec_decl (m + 4) _ _ chi _ _ sh2.nocall hchi'
            (by simp only [C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hbv])
        have htl : C.Sem.evalC cp cst ((tmpName (cs2.tmp + 1), .int (w.getD .w32).bits bv.toNat) ::
              (tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv)) (.var (tmpName cs2.tmp))
            = some (.int (w.getD .w32).bits av.toNat) := by
          apply evalC_var_lookup
          have hne : (tmpName cs2.tmp == tmpName (cs2.tmp + 1)) = false := by
            cases h : tmpName cs2.tmp == tmpName (cs2.tmp + 1)
            · rfl
            · rw [beq_iff_eq] at h; have := tmpName_inj h; omega
          simp [List.lookup, hne]
        have hsimF := for_sim (il := il) (t0 := cs2.tmp) (lov := .int (w.getD .w32).bits av.toNat) hnr hnw hsim hbv
          j (by omega) av.toNat st (.int (w.getD .w32) (UInt64.ofNat av.toNat)) env cst (xs ++ cenv)
          ⟨.tmp _ _ (.tmp _ _ (hrel.temps ht).1), hrel.2⟩ hfrX
        simp only [Val.toNat]
        cases hR : Lang.Sem.forLoop j g.prog st ((x, .int (w.getD .w32) (UInt64.ofNat av.toNat)) :: env) x
            (w.getD .w32) av.toNat bv.toNat body with
        | fuel => trivial
        | trap st' =>
          rw [hR] at hsimF
          obtain ⟨m, cst', hm, hw'⟩ := hsimF
          have e3 : C.Sem.execS (m + 1) cp cst ((tmpName (cs2.tmp + 1), .int (w.getD .w32).bits bv.toNat) ::
                (tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv))
              (.forUp (.uint (w.getD .w32).bits) (localName x) (.var (tmpName cs2.tmp))
                (.var (tmpName (cs2.tmp + 1))) cb) = .trap cst' := by
            simp only [C.Sem.execS, htl, C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hav, hm]
          have hx := (r1.append r2).exec (Exec.one e3 trivial)
          obtain ⟨M, hM⟩ := hx.block_trap
          exact ⟨cst', hruns.exec (Exec.one (m := M + 1) (by simp only [C.Sem.execS]; exact hM) trivial), hw'⟩
        | ok st' env' out =>
          rw [hR] at hsimF
          obtain ⟨m, cst', y, cT', v', envT', hm, rfl, hlenT, hsT, hrelT, hstk, hout⟩ := hsimF
          have e3 : C.Sem.execS (m + 1) cp cst ((tmpName (cs2.tmp + 1), .int (w.getD .w32).bits bv.toNat) ::
                (tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: (xs ++ cenv))
              (.forUp (.uint (w.getD .w32).bits) (localName x) (.var (tmpName cs2.tmp))
                (.var (tmpName (cs2.tmp + 1))) cb)
              = .ok cst' ((tmpName (cs2.tmp + 1), .int (w.getD .w32).bits bv.toNat) ::
                (tmpName cs2.tmp, .int (w.getD .w32).bits av.toNat) :: cT') (cout g.opts out) := by
            simp only [C.Sem.execS, htl, C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hav, hm, List.drop]
          have hx := (r1.append r2).exec (Exec.one e3 trivial)
          obtain ⟨M, hM⟩ := hx.block
          have ed : ((tmpName (cs2.tmp + 1), CVal.int (w.getD .w32).bits bv.toNat) ::
                (tmpName cs2.tmp, CVal.int (w.getD .w32).bits av.toNat) :: cT').drop
              (((tmpName (cs2.tmp + 1), CVal.int (w.getD .w32).bits bv.toNat) ::
                (tmpName cs2.tmp, CVal.int (w.getD .w32).bits av.toNat) :: cT').length - (xs ++ cenv).length)
              = cT' := by
            rw [hsT.length]
            have e2 : cT'.length + 1 + 1 - cT'.length = 2 := by omega
            simp only [List.length_cons, e2, List.drop]
          rw [ed] at hM
          simp only [Sim, List.drop]
          refine ⟨cst', cT', hruns.exec (Exec.one (m := M + 1) (by simp only [C.Sem.execS]; exact hM) trivial), ?_,
            hout⟩
          exact After.mk0 rfl ht.allTmp hsT ⟨(hrelT.1.tail_tmp _ _ _ rfl).tail_tmp _ _ _ rfl, hrelT.2⟩ hlenT hstk
            ((hfrX.mono (by omega)).same hsT hrelT.2.gtmp)

end

end Ember.Proof.CSim
