import Ember.Proof.CCall

/-!
# Ember.Proof.CSim — statements and blocks (plan M5.8)

`stmt_ok` and `block_ok`: by recursion on the statement, the cases of
`Ember.Proof.CStmt` and `Ember.Proof.CCall` put together.  Calls rely on
`FnSim` for less fuel; `Ember.Proof.CFn` closes that induction.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
open Ember.C.Sem (CVal CProg Runs Traps Ext Exec)

/-- A scope whose top is as `xs` (the variables `nv` and temporaries) splits there. -/
theorem LRel.split {p : Prog} {o : Opts} {nv : List (String × VarInfo)} {ys : Lang.Sem.Env} {xs : C.Sem.Env}
    (h : LRel p o nv ys xs) : ∀ {vs : List (String × VarInfo)} {E : Lang.Sem.Env} {xs' c : C.Sem.Env},
    Same xs xs' → LRel p o (nv ++ vs) E (xs' ++ c) →
    ∃ ys' e, E = ys' ++ e ∧ LRel p o nv ys' xs' ∧ LRel p o vs e c ∧ ys'.length = ys.length := by
  induction h with
  | nil =>
    intro vs E xs' c hs hl
    cases hs
    exact ⟨[], E, rfl, .nil, hl, rfl⟩
  | tmp k cv _ ih =>
    intro vs E xs' c hs hl
    obtain ⟨a', rfl, hs'⟩ := hs.cons_tmp_inv
    obtain ⟨ys', e, rfl, h1, h2, h3⟩ := ih hs' (hl.tail_tmp k cv _ rfl)
    exact ⟨ys', e, rfl, .tmp k cv h1, h2, h3⟩
  | val x ty v hty _ ih =>
    intro vs E xs' c hs hl
    obtain ⟨cv', a', rfl, hs'⟩ := hs.cons_inv
    obtain ⟨ty', v', vs', env', hvs, rfl, rfl, hty', hl'⟩ := hl.head_val x cv' _ rfl
    simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq, VarInfo.mk.injEq, true_and, and_true] at hvs
    obtain ⟨rfl, rfl⟩ := hvs
    obtain ⟨ys', e, rfl, h1, h2, h3⟩ := ih hs' hl'
    exact ⟨(x, v') :: ys', e, rfl, .val x _ v' hty' h1, h2, by simp [h3]⟩

theorem After.weaken {g : C.Env} {K K' : List (String × VarInfo) → Prop} {t t2 : Nat} {st' : Lang.Sem.St}
    {env' env : Lang.Sem.Env} {out : Lang.Sem.Out} {cst cst' : C.Sem.St} {cenv cenv' : C.Sem.Env}
    (h : After g K t st' env' out env cst cenv cst' cenv') (ht : t ≤ t2) (hK : ∀ nv, K nv → K' nv) :
    After g K' t2 st' env' out env cst cenv cst' cenv' := by
  obtain ⟨ys, env1, xs, cenv1, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨ys, env1, xs, cenv1, h1, h2, h3, h4, h5, h6, h7.mono ht, fun ho => by
    obtain ⟨nv, hk, hl⟩ := h8 ho
    exact ⟨nv, hK nv hk, hl⟩⟩

/-- **Statements in sequence.**  After the first ran normally, the rest
runs in the environment `g1` (with the variables `nv` it declared); what
the rest does there is what the whole does. -/
theorem Sim.cont {g g1 : C.Env} {K2 : List (String × VarInfo) → Prop} {cp : CProg} {rt : Option Ty} {il : Bool}
    {t' : Nat} {code1 code2 : List CStmt} {R : Lang.Sem.Res} {lenv ys e1 : Lang.Sem.Env} {cst cst1 : C.Sem.St}
    {cenv xs c1 : C.Sem.Env} {nv : List (String × VarInfo)} (hp : g1.prog = g.prog) (ho : g1.opts = g.opts)
    (hv : g1.vars = nv ++ g.vars) (hx1 : Exec cp cst cenv code1 (.ok cst1 (xs ++ c1) .normal))
    (hlen : e1.length = lenv.length) (hsame : Same cenv c1) (hstk : cst1.stack = cst.stack)
    (hl : LRel g.prog g.opts nv ys xs)
    (h2 : Sim g1 K2 cp rt il t' code2 R (ys ++ e1) cst1 (xs ++ c1)) :
    Sim g (fun _ => True) cp rt il t' (code1 ++ code2) R lenv cst cenv := by
  cases R with
  | ok st2 env2 out =>
    obtain ⟨cst2, cenv2, hx2, ⟨ys2, e2, xs2, c2, rfl, rfl, hlen2, hsame2, hrel2, hstk2, hfr2, hn2⟩, hout⟩ := h2
    obtain ⟨xs', c1', rfl, hs1, hs2⟩ := hsame2.split
    have hl2 := hrel2.1
    rw [hp, ho, hv] at hl2
    obtain ⟨ys', e', rfl, hl3, hl4, hlen3⟩ := hl.split hs1 hl2
    have hg2 := hrel2.2
    rw [hp, ho] at hg2
    rw [ho] at hx2
    rw [hp] at hout
    refine ⟨cst2, _, hx1.seq hx2, ⟨ys2 ++ ys', e', xs2 ++ xs', c1', by rw [List.append_assoc],
      by rw [List.append_assoc], ?_, hsame.trans hs2, ⟨hl4, hg2⟩, hstk2.trans hstk, hfr2, fun ho' => ?_⟩, hout⟩
    · simp only [List.length_append] at hlen2
      omega
    · obtain ⟨nv2, _, hln⟩ := hn2 ho'
      rw [hp, ho] at hln
      exact ⟨nv2 ++ nv, trivial, hln.append hl3⟩
  | trap st2 =>
    obtain ⟨cst2, hx2, hw⟩ := h2
    exact ⟨cst2, hx1.seq hx2, hw⟩
  | fuel => trivial

mutual

/-- **A statement.**  `C.stmt s` emits code that does what
`Lang.Sem.execS` does with `s`, with up to `N` units of fuel, given that
function calls are right with less. -/
theorem stmt_ok (cp : CProg) (N : Nat) : ∀ (s : Stmt) (g : C.Env) (cs : CS) (rt : Option Ty) (il : Bool),
    Unit g.prog g.opts cp → ProgOK g.prog g.opts → (∀ j, j < N → FnSim g.prog g.opts cp j) → EnvOK g →
    WTS rt il g s → wpc (C.stmt s) g (SPost N rt il g s cp cs) cs
  | .at sp s, g, cs, rt, il, U, hP, H, hg, hw =>
    at_ok sp s fun cs0 => stmt_ok cp N s g cs0 rt il U hP H hg hw
  | .decl x ty init, g, cs, rt, il, U, hP, H, hg, hw => decl_ok U hg x ty init hw
  | .assign l r, g, cs, rt, il, U, hP, H, hg, hw => assign_ok U hg l r hw
  | .ite c t e, g, cs, rt, il, U, hP, H, hg, hw =>
    ite_ok U hg c t e hw (fun cs0 => block_ok cp N t g.path 1 g g cs0 rt il U hP H hg hw.2.2.1)
      (fun cs0 => block_ok cp N e g.path 1 g g cs0 rt il U hP H hg hw.2.2.2)
  | .forRange x w lo hi body, g, cs, rt, il, U, hP, H, hg, hw =>
    for_ok U hg (fun f fd hfd prm hprm => ((hP f fd hfd).params prm hprm).1) x w lo hi body hw
      (fun cs0 => block_ok cp N body g.path 1
        { g with vars := (x, { ty := .int (w.getD .w32), c := .var (localName x) }) :: g.vars } g cs0 rt true U hP H
        (hg.push x _ _) hw.2.2.2.2.2)
  | .loop n body, g, cs, rt, il, U, hP, H, hg, hw =>
    loop_ok U n body hw (fun cs0 => block_ok cp N body g.path 1 g g cs0 rt true U hP H hg hw.2)
  | .brk, g, cs, rt, il, U, hP, H, hg, hw => brk_ok U hw
  | .ret e, g, cs, rt, il, U, hP, H, hg, hw => ret_ok U hg e hw
  | .call dst f args, g, cs, rt, il, U, hP, H, hg, hw => call_ok U hg hP H dst f args hw
  | .eff dst e args, g, cs, rt, il, U, hP, H, hg, hw => eff_ok U hg dst e args hw

/-- **A list of statements**, as `C.blockFrom` compiles it. -/
theorem block_ok (cp : CProg) (N : Nat) : ∀ (ss : List Stmt) (base : List Nat) (i : Nat) (env g0 : C.Env) (cs : CS)
    (rt : Option Ty) (il : Bool), Unit env.prog env.opts cp → ProgOK env.prog env.opts →
    (∀ j, j < N → FnSim env.prog env.opts cp j) → EnvOK env → WTB rt il base i env ss →
    wpc (blockFrom base i env ss) g0 (BPost N rt il env ss cp cs) cs
  | [], base, i, env, g0, cs, rt, il, U, hP, H, hg, hw => by
    rw [blockFrom, wpc_pure]
    refine ⟨Nat.le_refl _, [], by simp, fun k hk st lenv cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      simp only [Lang.Sem.execL, Sim]
      refine ⟨cst, cenv, Exec.nil, ?_, trivial⟩
      exact After.mk0 (xs := []) trivial AllTmp.nil (Same.refl _) hrel rfl rfl hfr
  | s :: rest, base, i, env, g0, cs, rt, il, U, hP, H, hg, hw => by
    rw [blockFrom]
    simp only [wpc_bind, wpc_withReader]
    refine wpc_mono (stmt_ok cp N s { env with path := base ++ [i] } cs rt il U hP H (hg.path _) hw.1) ?_
    rintro g' cs1 ⟨hg', htmp1, code1, ho1, hsim1⟩
    subst hg'
    have e := envAfter_prog { env with path := base ++ [i] } s
    have hp1 : ({ envAfter { env with path := base ++ [i] } s with path := base } : C.Env).prog = env.prog := e.1
    have ho1' : ({ envAfter { env with path := base ++ [i] } s with path := base } : C.Env).opts = env.opts := e.2
    refine wpc_mono (block_ok cp N rest base (i + 1) { envAfter { env with path := base ++ [i] } s with path := base }
      g0 cs1 rt il (by rw [hp1, ho1']; exact U) (by rw [hp1, ho1']; exact hP) (by rw [hp1, ho1']; exact H)
      (((hg.path _).after s).path _) hw.2) ?_
    rintro ⟨⟩ cs2 ⟨htmp2, code2, ho2, hsim2⟩
    refine ⟨Nat.le_trans htmp1 htmp2, code1 ++ code2, by simp [ho1, ho2],
      fun k hk st lenv cst cenv hrel hfr => ?_⟩
    cases k with
    | zero => exact sim_fuel
    | succ j =>
      rw [Lang.Sem.execL]
      have h1 := hsim1 j (by omega) st lenv cst cenv hrel hfr
      cases hS : Lang.Sem.execS j env.prog st lenv s with
      | fuel => trivial
      | trap st' =>
        rw [hS] at h1
        obtain ⟨cst', hx, hw'⟩ := h1
        exact ⟨cst', hx.stop _ trivial, hw'⟩
      | ok st1 env1 o1 =>
        rw [hS] at h1
        obtain ⟨cst1, cenv1, hx1, haft, hout1⟩ := h1
        cases o1 with
        | brk => exact ⟨cst1, cenv1, hx1.stop _ trivial, haft.weaken htmp2 (fun _ _ => trivial), hout1⟩
        | ret v => exact ⟨cst1, cenv1, hx1.stop _ trivial, haft.weaken htmp2 (fun _ _ => trivial), hout1⟩
        | normal =>
          obtain ⟨ys, e1, xs, c1, rfl, rfl, hlen, hsame, hrelB, hstk, hfr1, hn⟩ := haft
          obtain ⟨nv, hK, hl⟩ := hn rfl
          have hrel1 : SRel { envAfter { env with path := base ++ [i] } s with path := base } st1 (ys ++ e1) cst1
              (xs ++ c1) := by
            refine ⟨?_, ?_⟩
            · rw [hp1, ho1']
              show LRel env.prog env.opts (envAfter { env with path := base ++ [i] } s).vars _ _
              rw [hK]
              exact hl.append hrelB.1
            · rw [hp1, ho1']
              exact hrelB.2
          have h2 := hsim2 j (by omega) st1 (ys ++ e1) cst1 (xs ++ c1) hrel1 hfr1
          rw [hp1] at h2
          exact Sim.cont hp1 ho1' hK hx1 hlen hsame hstk hl h2

end

/-- info: 'Ember.Proof.CSim.stmt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stmt_ok

end Ember.Proof.CSim
