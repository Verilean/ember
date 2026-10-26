import Ember.Proof.CNet
import Ember.C.DropChecks

/-!
# Ember.Proof.CDrop — bounds checks the proofs make unnecessary (plan M5.9, first part)

`C.compile` emits `if (t >= n) { ember_trap("…"); }` before every access
whose index it cannot show in range by its form.  `C.dropUnit` takes
those statements out (`Ember/C/DropChecks.lean`).

* `drop_sim`: under the C semantics, a statement, a list, a call or a
  loop of the unit that ends normally (`Res.ok`) ends the same way —
  same state, same variables, same way out — in the unit without checks,
  with the same fuel.  A check that does not trap does nothing (`check_ok`):
  its condition is an expression, which has no effect.
* `cIter_drop`: so do the calls of the entry function as `C.Sem.run`
  makes them.
* **`stack_c_dropped`**: with `stack_c` (M5.8 composed with M5.6, whose
  proofs show that every index the SLIP build computes is in range, so
  that no call of `main` traps), **the C of the SLIP build without any of
  its bounds checks, called again and again from its initial state under
  the C semantics, never traps, is never undefined, and transmits and
  drops what the Spec does**, for any input.

What is used of the program is what `stack_c` uses (`TcpAll`, `TcpReasons`,
`main_fn`, the globals and records of `Net.prog`, the checker): the
range facts are those of the refinement proofs, not a check of the
emitter.  For any other program `drop_sim` says nothing about runs that
trap — there the check is what makes an out-of-range index a trap
rather than undefined behaviour, and the tools keep it.
-/

namespace Ember.Proof.CDrop
open Ember Ember.Lang Ember.C
open Ember.C.Sem
open Ember.Proof.CSim (cIter progOkB)
open Ember.Proof.Refine (kept specKept witems later main_fn TcpAll TcpReasons)

/-- The program with the unit's checks taken out. -/
def dropProg (cp : CProg) : CProg := { cp with unit := dropUnit cp.unit }

section
variable (cp : CProg) (st : St) (env : C.Sem.Env)

mutual
theorem lval_drop : ∀ e : CExpr, lval (dropProg cp) st env e = lval cp st env e
  | .var _ => rfl
  | .index a i => by simp only [lval, lval_drop a, evalC_drop i]
  | .dot a f => by simp only [lval, lval_drop a]; rfl
  | .arrow a f => by simp only [lval, lval_drop a]; rfl
  | .lit _ _ => rfl
  | .blit _ => rfl
  | .bin _ _ _ => rfl
  | .un _ _ => rfl
  | .cast _ _ => rfl
  | .cond _ _ _ => rfl
  | .addr _ => rfl
  | .call _ _ => rfl
  | .str _ => rfl

theorem evalC_drop : ∀ e : CExpr, evalC (dropProg cp) st env e = evalC cp st env e
  | .var _ => rfl
  | .index a i => by simp only [evalC, lval_drop a, evalC_drop i]
  | .dot a f => by simp only [evalC, lval_drop a]; rfl
  | .arrow a f => by simp only [evalC, lval_drop a]; rfl
  | .lit _ _ => rfl
  | .blit _ => rfl
  | .bin op a b => by simp only [evalC, evalC_drop a, evalC_drop b]; rfl
  | .un op a => by simp only [evalC, evalC_drop a]; rfl
  | .cast t a => by simp only [evalC, evalC_drop a]; rfl
  | .cond c a b => by simp only [evalC, evalC_drop c, evalC_drop a, evalC_drop b]
  | .addr _ => rfl
  | .call f args => by simp only [evalC, evalCs_drop args]
  | .str _ => rfl

theorem evalCs_drop : ∀ es : List CExpr, evalCs (dropProg cp) st env es = evalCs cp st env es
  | [] => rfl
  | e :: es => by simp only [evalCs, evalC_drop e, evalCs_drop es]
end

theorem ptrArg_drop (a : CExpr) : ptrArg (dropProg cp) st env a = ptrArg cp st env a := by
  unfold ptrArg
  split <;> simp only [lval_drop]

theorem argVals_drop : ∀ (ps : List (CTy × String)) (as : List CExpr),
    argVals (dropProg cp) st env ps as = argVals cp st env ps as
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (t, _) :: ps, a :: as => by
    simp only [argVals, argVals_drop ps as, ptrArg_drop, evalC_drop]
    rfl

theorem zero0_drop : ∀ t : CTy, zero0 (dropProg cp) t = zero0 cp t
  | .uint _ => rfl
  | .unsigned => rfl
  | .bool => rfl
  | .arr t _ => by simp only [zero0, zero0_drop t]
  | .void => rfl
  | .strct _ => rfl
  | .ptr _ => rfl

theorem zero_drop (t : CTy) : zero (dropProg cp) t = zero cp t := by
  cases t <;> simp only [zero, zero0_drop] <;> rfl

theorem find_drop (f : String) :
    (dropProg cp).unit.fns.find? (·.name == f) = (cp.unit.fns.find? (·.name == f)).map dropFn := by
  simp only [dropProg, dropUnit, List.find?_map]
  rfl

end

/-- A check that ends normally does nothing. -/
theorem check_ok {cp : CProg} {st st' : St} {env env' : C.Sem.Env} {o : Out} {s : CStmt} (hs : isCheck s = true) :
    ∀ {n : Nat}, execS n cp st env s = .ok st' env' o → st' = st ∧ env' = env ∧ o = .normal := by
  intro n h
  unfold isCheck at hs
  split at hs
  · rename_i a b m
    rcases n with _ | k
    · simp [execS] at h
    · simp only [execS] at h
      split at h
      · rename_i cv _
        split at h
        · rcases k with _ | _ | _ | i
          · simp [execB] at h
          · simp [execB, execL] at h
          · simp [execB, execL, execS] at h
          · simp [execB, execL, execS, asCall, helper] at h
            rcases i with _ | i <;> simp [callC] at h
        · rcases k with _ | k
          · simp [execB] at h
          · simp only [execB] at h
            rcases k with _ | k
            · simp [execL] at h
            · simp only [execL, Res.ok.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp
        · cases h
      · cases h
  · cases hs

/-- **Without the checks, what ends normally ends the same way.** -/
theorem drop_sim (cp : CProg) (n : Nat) :
    (∀ st env ss st' env' o, execB n cp st env ss = .ok st' env' o →
      execB n (dropProg cp) st env (dropL ss) = .ok st' env' o) ∧
    (∀ st env ss st' env' o, execL n cp st env ss = .ok st' env' o →
      execL n (dropProg cp) st env (dropL ss) = .ok st' env' o) ∧
    (∀ st env f args st' env' o, callC n cp st env f args = .ok st' env' o →
      callC n (dropProg cp) st env f args = .ok st' env' o) ∧
    (∀ st env s st' env' o, execS n cp st env s = .ok st' env' o →
      execS n (dropProg cp) st env (dropS s) = .ok st' env' o) ∧
    (∀ st env i hi body st' env' o, forC n cp st env i hi body = .ok st' env' o →
      forC n (dropProg cp) st env i hi (dropL body) = .ok st' env' o) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [execB, execL, callC, execS, forC]
  | succ n ih =>
    obtain ⟨iB, iL, iC, iS, iF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- execB
      intro st env ss st' env' o h
      simp only [execB] at h ⊢
      cases hl : execL n cp st env ss with
      | ok s1 e1 o1 => rw [hl] at h; rw [iL _ _ _ _ _ _ hl]; exact h
      | trap _ => rw [hl] at h; cases h
      | undef => rw [hl] at h; cases h
      | fuel => rw [hl] at h; cases h
    · -- execL
      intro st env ss st' env' o h
      cases ss with
      | nil => simp only [dropL]; exact h
      | cons s rest =>
        simp only [execL] at h
        cases hs : execS n cp st env s with
        | ok s1 e1 o1 =>
          rw [hs] at h
          cases hc : isCheck s
          · simp only [dropL, hc, Bool.false_eq_true, if_false, execL]
            rw [iS _ _ _ _ _ _ hs]
            cases o1 with
            | normal => exact iL _ _ _ _ _ _ h
            | brk => exact h
            | ret v => exact h
          · obtain ⟨rfl, rfl, rfl⟩ := check_ok hc hs
            simp only [dropL, hc, if_true]
            exact execL_le (Nat.le_succ n) (iL _ _ _ _ _ _ h) trivial
        | trap _ => rw [hs] at h; cases h
        | undef => rw [hs] at h; cases h
        | fuel => rw [hs] at h; cases h
    · -- callC
      intro st env f args st' env' o h
      simp only [callC] at h ⊢
      split at h
      · cases h
      · rename_i hf
        rw [if_neg hf, find_drop]
        cases hfd : cp.unit.fns.find? (·.name == f) with
        | none =>
          rw [hfd] at h
          simp only [Option.map_none]
          rw [evalCs_drop]
          exact h
        | some fd =>
          rw [hfd] at h
          simp only at h
          simp only [Option.map_some, dropFn]
          rw [argVals_drop]
          cases ha : argVals cp st env fd.params args with
          | none => rw [ha] at h; cases h
          | some vs =>
            rw [ha] at h
            simp only at h ⊢
            cases hb : execB n cp { st with stack := env :: st.stack } ((fd.params.map (·.2)).zip vs) fd.body with
            | ok s1 e1 o1 =>
              rw [hb] at h
              rw [iB _ _ _ _ _ _ hb]
              exact h
            | trap _ => rw [hb] at h; cases h
            | undef => rw [hb] at h; cases h
            | fuel => rw [hb] at h; cases h
    · -- execS
      intro st env s st' env' o h
      cases s with
      | decl t x init =>
        simp only [dropS]
        cases init with
        | none => simp [execS] at h
        | some e =>
          simp only [execS] at h ⊢
          cases hc : asCall e with
          | some fa =>
            rw [hc] at h
            obtain ⟨f, args⟩ := fa
            simp only at h ⊢
            cases hr : callC n cp st env f args with
            | ok s1 e1 o1 => rw [hr] at h; rw [iC _ _ _ _ _ _ _ hr]; exact h
            | trap _ => rw [hr] at h; cases h
            | undef => rw [hr] at h; cases h
            | fuel => rw [hr] at h; cases h
          | none =>
            rw [hc] at h
            simp only at h ⊢
            rw [evalC_drop]
            exact h
      | declZero t x =>
        simp only [dropS, execS] at h ⊢
        rw [zero_drop]
        exact h
      | assign l r =>
        simp only [dropS, execS] at h ⊢
        cases hc : asCall r with
        | some fa =>
          rw [hc] at h
          obtain ⟨f, args⟩ := fa
          simp only at h ⊢
          rw [lval_drop]
          cases hl : lval cp st env l with
          | none => rw [hl] at h; cases h
          | some loc =>
            rw [hl] at h
            simp only at h ⊢
            cases hr : callC n cp st env f args with
            | ok s1 e1 o1 =>
              rw [hr] at h
              rw [iC _ _ _ _ _ _ _ hr]
              simp only [lval_drop]
              exact h
            | trap _ => rw [hr] at h; cases h
            | undef => rw [hr] at h; cases h
            | fuel => rw [hr] at h; cases h
        | none =>
          rw [hc] at h
          simp only at h ⊢
          rw [evalC_drop, lval_drop]
          exact h
      | expr e =>
        simp only [dropS, execS] at h ⊢
        cases hc : asCall e with
        | some fa =>
          rw [hc] at h
          obtain ⟨f, args⟩ := fa
          simp only at h ⊢
          cases hr : callC n cp st env f args with
          | ok s1 e1 o1 => rw [hr] at h; rw [iC _ _ _ _ _ _ _ hr]; exact h
          | trap _ => rw [hr] at h; cases h
          | undef => rw [hr] at h; cases h
          | fuel => rw [hr] at h; cases h
        | none =>
          rw [hc] at h
          simp only at h ⊢
          simp only [evalC_drop]
          exact h
      | ite c t e =>
        simp only [dropS, execS] at h ⊢
        rw [evalC_drop]
        cases hv : evalC cp st env c with
        | none => rw [hv] at h; cases h
        | some cv =>
          rw [hv] at h
          simp only at h ⊢
          cases ht : truthy cv with
          | none => rw [ht] at h; cases h
          | some b =>
            rw [ht] at h
            cases b with
            | true => exact iB _ _ _ _ _ _ h
            | false => exact iB _ _ _ _ _ _ h
      | forUp t i lo hi body =>
        simp only [dropS, execS] at h ⊢
        rw [evalC_drop]
        cases hv : evalC cp st env lo with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h
          simp only at h ⊢
          have hcv : convTo (dropProg cp) t v = convTo cp t v := rfl
          rw [hcv]
          cases hc : convTo cp t v with
          | none => rw [hc] at h; cases h
          | some v' =>
            rw [hc] at h
            simp only at h ⊢
            cases hf : forC n cp st ((i, v') :: env) i hi body with
            | ok s1 e1 o1 => rw [hf] at h; rw [iF _ _ _ _ _ _ _ _ hf]; exact h
            | trap _ => rw [hf] at h; cases h
            | undef => rw [hf] at h; cases h
            | fuel => rw [hf] at h; cases h
      | brk => exact h
      | ret e =>
        cases e with
        | none => exact h
        | some e =>
          simp only [dropS, execS] at h ⊢
          rw [evalC_drop]
          exact h
      | block ss =>
        simp only [dropS, execS] at h ⊢
        exact iB _ _ _ _ _ _ h
      | line _ _ => exact h
      | comment _ => exact h
    · -- forC
      intro st env i hi body st' env' o h
      simp only [forC] at h ⊢
      rw [evalC_drop]
      split at h
      · rename_i v hv hl hh
        try simp only [hl, hh]
        try simp only at h ⊢
        split at h
        · rename_i hlt
          rw [if_pos hlt]
          cases hb : execB n cp st env body with
          | ok s1 e1 o1 =>
            rw [hb] at h
            rw [iB _ _ _ _ _ _ hb]
            cases o1 with
            | normal =>
              simp only at h ⊢
              split at h
              · rename_i b v' hv'
                try rw [hv']
                exact iF _ _ _ _ _ _ _ _ h
              · cases h
            | brk => exact h
            | ret r => exact h
          | trap _ => rw [hb] at h; cases h
          | undef => rw [hb] at h; cases h
          | fuel => rw [hb] at h; cases h
        · rename_i hlt
          rw [if_neg hlt]
          exact h
      · cases h

/-- The calls of the entry function, as `C.Sem.run` makes them. -/
theorem cIter_drop (cp : CProg) (m : Nat) : ∀ (j : Nat) (st st' : St),
    cIter m cp j st = some st' → cIter m (dropProg cp) j st = some st'
  | 0, _, _, h => h
  | j + 1, st, st', h => by
    simp only [cIter] at h ⊢
    cases hc : callC m cp st [] cp.entry [] with
    | ok s1 e1 o1 =>
      rw [hc] at h
      have := (drop_sim cp m).2.2.1 _ _ _ _ _ _ _ hc
      rw [show (dropProg cp).entry = cp.entry from rfl, this]
      exact cIter_drop cp m j s1 st' h
    | trap _ => rw [hc] at h; cases h
    | undef => rw [hc] at h; cases h
    | fuel => rw [hc] at h; cases h

theorem initOf_drop (cp : CProg) (g : CGlobal) : C.Sem.initOf (dropProg cp) g = C.Sem.initOf cp g := by
  unfold C.Sem.initOf
  split
  · exact zero_drop cp _
  · simp only [evalC_drop, zero_drop]; rfl
  · simp only [evalC_drop, zero_drop]; rfl

theorem initial_drop (cp : CProg) (inputs : Array Trace.Input) (framed : Bool) :
    initial (dropProg cp) inputs framed = initial cp inputs framed := by
  simp only [initial, initOf_drop]
  rfl

/-- **The C of the stack without its bounds checks.**  For the checked
SLIP build `p`, as in `stack_c`, with every bounds check taken out of the
unit (`dropUnit`): once every item of the input has been read, the calls
of the entry function have all ended normally (no trap, nothing
undefined), and the kept lines of the trace are those of the Spec's
steps.  The checks are unnecessary because the refinement proofs (M5.6)
show every index of the SLIP build in range in every call of `main`. -/
theorem stack_c_dropped (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (hentry : p.entry = "main") (hg : p.globals = Net.prog.globals) (hs : p.structs = Net.prog.structs)
    (hf : p.framed = Net.prog.framed) (o : Opts) (hpre : o.namePrefix = "") (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hok : progOkB p o = true) (u : CUnit) (hc : compile p o = .ok u)
    (inputs : Array Trace.Input) (j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ m cst', cIter m (C.Sem.CProg.ofUnit (dropUnit u) o.profile o.entryName p.dropReasons p.notes) (j + 1)
        (C.Sem.initial (C.Sem.CProg.ofUnit (dropUnit u) o.profile o.entryName p.dropReasons p.notes) inputs
          p.framed) = some cst' ∧
      kept cst'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems cst'.world = [] := by
  obtain ⟨m, cst', hi, hk, hw⟩ := CSim.stack_c p hP hR hp hentry hg hs hf o hpre hb h16 hok u hc inputs j hj
  let cp := C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes
  have e : C.Sem.CProg.ofUnit (dropUnit u) o.profile o.entryName p.dropReasons p.notes = dropProg cp := rfl
  refine ⟨m, cst', ?_, hk, hw⟩
  rw [e, initial_drop]
  exact cIter_drop cp m (j + 1) _ _ hi

/-- info: 'Ember.Proof.CDrop.stack_c_dropped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stack_c_dropped

/-! ## The SLIP build: what is taken out -/

-- the C of the SLIP build has bounds checks (17), on every profile, and `dropUnit` takes them all out
#guard (Net.prog.check.toOption.bind fun q =>
  Profile.all.mapM fun prof => (compile q { profile := prof }).toOption.map fun u =>
    (checksUnit u, checksUnit (dropUnit u))) ==
  some [(17, 0), (17, 0), (17, 0)]

end Ember.Proof.CDrop
