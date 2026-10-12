import Ember.Proof.IRSim

/-!
# Ember.Proof.IRPass — the IR's passes keep what a function does (plan M7.1)

`IR.lower` tidies every body after it is lowered: `cleanup` drops what
cannot run, jumps to the next instruction and labels nothing jumps to;
`dropChecks` drops an index check where a comparison on the way already
established it.  `Ember/Proof/IRSim.lean` is about the bodies before
that.  This file carries its results over:

* `sim_exec`: a relation between the points of two bodies that every
  step keeps (`Sim`) makes the second body end as the first does;
* `del_sim`: dropping instructions a mask selects is such a relation,
  when what is dropped does nothing and what is kept jumps to what is
  kept (`DelOK`); the three masks of `cleanupPass` are of that kind;
* `drop_sim`: so is `dropChecks`, the facts it collects holding at every
  point (`FactsHold`), when a slot the body compares and one it writes
  are where the layout keeps them apart (`SlotsOK`, checked by `slotsOkB`);
* `tidy_ref`: a call in the tidied program ends as in the program as
  lowered.
-/

namespace Ember.Proof.IRSim
open Ember Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run

/-- Finished: not out of fuel, and not malformed. -/
def Done : Res → Prop
  | .ok _ _ | .trap _ => True
  | _ => False

theorem Done.ne_fuel {r : Res} (h : Done r) : r ≠ .fuel := by
  intro e; subst e; exact h

/-! ## Two contexts that differ in the bodies only -/

structure CtxEq (c c' : Ctx) : Prop where
  layout : c'.layout = c.layout
  drops : c'.dropReasons = c.dropReasons
  notes : c'.notes = c.notes
  reg : ∀ g, (c'.prog.fn? g).bind (·.regParam) = (c.prog.fn? g).bind (·.regParam)

theorem CtxEq.refl (c : Ctx) : CtxEq c c := ⟨rfl, rfl, rfl, fun _ => rfl⟩

section
variable {c c' : Ctx}

theorem opd_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (n : Nat) (o : Opd) :
    opd c' st tmps n o = opd c st tmps n o := by
  cases o <;> simp [opd, h.layout]

theorem addr_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (a : Addr) : addr c' st tmps a = addr c st tmps a := by
  simp only [addr, h.layout, opd_ctx h]

theorem inBound_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (a : Addr) :
    inBound c' st tmps a = inBound c st tmps a := by
  simp only [inBound, opd_ctx h]

theorem setDst_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (n : Nat) (d : Dst) (v : Nat) :
    setDst c' st tmps n d v = setDst c st tmps n d v := by
  cases d <;> simp [setDst, h.layout]

theorem setRet_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (ret : Option (Nat × Dst)) (r : Option Nat) :
    setRet c' st tmps ret r = setRet c st tmps ret r := by
  cases ret with
  | none => rfl
  | some x => simp only [setRet, setDst_ctx h]

theorem effect_ctx (h : CtxEq c c') (w : Lang.World) (e : Lang.Effect) (vs : List Nat) :
    IR.Sem.effect c' w e vs = IR.Sem.effect c w e vs := by
  cases e <;> simp [IR.Sem.effect, h.drops, h.notes]

theorem step_ctx (h : CtxEq c c') (st : St) (tmps : Array Nat) (ins : Instr) :
    step c' st tmps ins = step c st tmps ins := by
  cases ins with
  | call g ret reg =>
    have hr := h.reg g
    simp only [step, opd_ctx h, h.layout]
    cases reg with
    | none => rfl
    | some x =>
      cases hf : c.prog.fn? g with
      | none =>
        cases hf' : c'.prog.fn? g with
        | none => rfl
        | some gf' =>
          rw [hf, hf'] at hr
          simp only [Option.bind] at hr
          simp [hr]
      | some gf =>
        cases hf' : c'.prog.fn? g with
        | none =>
          rw [hf, hf'] at hr
          simp only [Option.bind] at hr
          simp [← hr]
        | some gf' =>
          rw [hf, hf'] at hr
          simp only [Option.bind] at hr
          simp [hr]
  | _ => simp only [step, opd_ctx h, addr_ctx h, inBound_ctx h, setDst_ctx h, setRet_ctx h, effect_ctx h, h.layout]

end

/-! ## One body simulating another -/

/-- The calls of `c` end in `c'` as they do in `c`, up to the fuel `N`. -/
def CallRef (c c' : Ctx) (N : Nat) : Prop :=
  ∀ n, n < N → ∀ g st r, callF n c g st = r → Done r → ∃ n', callF n' c' g st = r

/-- `f'` in `c'` ends as `f` does in `c`, when the calls do. -/
def FRef (c c' : Ctx) (f f' : Fn) : Prop :=
  ∀ N, CallRef c c' N → ∀ n, n ≤ N → ∀ tmps st r, exec n c f 0 tmps st = r → Done r →
    ∃ n', exec n' c' f' 0 tmps st = r

/-- A relation between the points of two bodies that every step keeps:
the first body takes a step that changes nothing, or both take the same
step. -/
structure Sim (c : Ctx) (f f' : Fn) (R : Nat → Nat → St → Array Nat → Prop) : Prop where
  step : ∀ pc pc' st tmps ins, R pc pc' st tmps → f.body[pc]? = some ins →
    (step c st tmps ins = .next st tmps ∧ R (pc + 1) pc' st tmps) ∨
    (∃ l i, step c st tmps ins = .goto l ∧ labelAt f l = some i ∧ R i pc' st tmps) ∨
    (∃ ins', f'.body[pc']? = some ins' ∧ step c st tmps ins' = step c st tmps ins ∧
      match step c st tmps ins with
      | .next st2 tmps2 => R (pc + 1) (pc' + 1) st2 tmps2
      | .goto l => ∀ i, labelAt f l = some i → ∃ i', labelAt f' l = some i' ∧ R i i' st tmps
      | .call _ _ ret => ∀ r st2, R (pc + 1) (pc' + 1) (setRet c st2 tmps ret r).1 (setRet c st2 tmps ret r).2
      | .stop _ => True)
  fin : ∀ pc pc' st tmps, R pc pc' st tmps → f.body[pc]? = none → f'.body[pc']? = none

theorem sim_exec {c c' : Ctx} (hc : CtxEq c c') {f f' : Fn} {R : Nat → Nat → St → Array Nat → Prop}
    (S : Sim c f f' R) (N : Nat) (hN : CallRef c c' N) :
    ∀ n, n ≤ N → ∀ pc pc' tmps st r, R pc pc' st tmps → exec n c f pc tmps st = r → Done r →
      ∃ n', exec n' c' f' pc' tmps st = r
  | 0, _, pc, pc', tmps, st, r, _, he, hd => by
    rw [exec_zero] at he
    subst he
    exact hd.elim
  | k + 1, hk, pc, pc', tmps, st, r, hR, he, hd => by
    have ih := sim_exec hc S N hN k (by omega)
    rw [exec_succ] at he
    cases hb : f.body[pc]? with
    | none =>
      simp only [hb] at he
      refine ⟨1, ?_⟩
      rw [exec_succ, S.fin pc pc' st tmps hR hb]
      exact he
    | some ins =>
      simp only [hb] at he
      rcases S.step pc pc' st tmps ins hR hb with ⟨hs, hR'⟩ | ⟨l, i, hs, hl, hR'⟩ | ⟨ins', hb', hs', hnext⟩
      · simp only [hs] at he
        exact ih _ _ _ _ _ hR' he hd
      · simp only [hs, hl] at he
        exact ih _ _ _ _ _ hR' he hd
      · cases hs : step c st tmps ins with
        | next st2 tmps2 =>
          simp only [hs] at he hnext
          obtain ⟨n', hn'⟩ := ih _ _ _ _ _ hnext he hd
          refine ⟨n' + 1, ?_⟩
          rw [exec_succ]
          simp only [hb', step_ctx hc, hs', hs]
          exact hn'
        | goto l =>
          simp only [hs] at he hnext
          cases hl : labelAt f l with
          | none =>
            simp only [hl] at he
            subst he
            exact hd.elim
          | some i =>
            simp only [hl] at he
            obtain ⟨i', hl', hR'⟩ := hnext i hl
            obtain ⟨n', hn'⟩ := ih _ _ _ _ _ hR' he hd
            refine ⟨n' + 1, ?_⟩
            rw [exec_succ]
            simp only [hb', step_ctx hc, hs', hs, hl']
            exact hn'
        | call g st1 ret =>
          simp only [hs] at he hnext
          cases hcall : callF k c g st1 with
          | ok rv st2 =>
            simp only [hcall] at he
            obtain ⟨m, hm⟩ := hN k (by omega) g st1 _ hcall trivial
            obtain ⟨n', hn'⟩ := ih _ _ _ _ _ (hnext rv st2) he hd
            refine ⟨max m n' + 1, ?_⟩
            rw [exec_succ]
            simp only [hb', step_ctx hc, hs', hs]
            rw [callF_mono (by rw [hm]; simp) (Nat.le_max_left m n'), hm]
            simp only [setRet_ctx hc]
            rw [exec_mono (by rw [hn']; exact hd.ne_fuel) (Nat.le_max_right m n'), hn']
          | trap st2 =>
            simp only [hcall] at he
            obtain ⟨m, hm⟩ := hN k (by omega) g st1 _ hcall trivial
            refine ⟨m + 1, ?_⟩
            rw [exec_succ]
            simp only [hb', step_ctx hc, hs', hs, hm]
            exact he
          | fuel =>
            simp only [hcall] at he
            subst he
            exact hd.elim
          | bad =>
            simp only [hcall] at he
            subst he
            exact hd.elim
        | stop r0 =>
          simp only [hs] at he
          refine ⟨1, ?_⟩
          rw [exec_succ]
          simp only [hb', step_ctx hc, hs', hs]
          exact he

theorem fref_of_sim {c c' : Ctx} (hc : CtxEq c c') {f f' : Fn} {R : Nat → Nat → St → Array Nat → Prop}
    (S : Sim c f f' R) (h0 : ∀ st tmps, R 0 0 st tmps) : FRef c c' f f' :=
  fun N hN n hn tmps st r he hd => sim_exec hc S N hN n hn 0 0 tmps st r (h0 st tmps) he hd

/-- The same body in the other context. -/
theorem fref_refl {c c' : Ctx} (hc : CtxEq c c') (f : Fn) : FRef c c' f f := by
  refine fref_of_sim hc (R := fun pc pc' _ _ => pc' = pc) ⟨fun pc pc' st tmps ins hR hb => ?_, fun pc pc' st tmps hR hb => ?_⟩
    (fun _ _ => rfl)
  · subst hR
    refine Or.inr (Or.inr ⟨ins, hb, rfl, ?_⟩)
    cases hs : step c st tmps ins with
    | next _ _ => rfl
    | goto l => exact fun i hi => ⟨i, hi, rfl⟩
    | call _ _ _ => exact fun _ _ => rfl
    | stop _ => trivial
  · subst hR
    exact hb

theorem FRef.trans {c c' : Ctx} {f f' f'' : Fn} (h1 : FRef c c' f f') (h2 : FRef c' c' f' f'') : FRef c c' f f'' := by
  intro N hN n hn tmps st r he hd
  obtain ⟨n', hn'⟩ := h1 N hN n hn tmps st r he hd
  exact h2 n' (fun m _ g st r h _ => ⟨m, h⟩) n' (Nat.le_refl _) tmps st r hn' hd

/-- Every function simulated, every call ends the same. -/
theorem callRef_all {c c' : Ctx}
    (h : ∀ g f, c.prog.fn? g = some f → ∃ f', c'.prog.fn? g = some f' ∧ f'.tmps.size = f.tmps.size ∧ FRef c c' f f') :
    ∀ N, CallRef c c' N
  | 0 => fun n hn => by omega
  | N + 1 => by
    have ih := callRef_all h N
    intro n hn g st r he hd
    cases n with
    | zero =>
      rw [callF_zero] at he
      subst he
      exact hd.elim
    | succ k =>
      rw [callF_succ] at he
      cases hf : c.prog.fn? g with
      | none =>
        simp only [hf] at he
        subst he
        exact hd.elim
      | some f =>
        simp only [hf] at he
        obtain ⟨f', hf', hsz, href⟩ := h g f hf
        obtain ⟨n', hn'⟩ := href N ih k (by omega) _ st r he hd
        refine ⟨n' + 1, ?_⟩
        rw [callF_succ]
        simp only [hf', hsz]
        exact hn'

/-! ## Dropping instructions -/

/-- Where the instruction at `pc` is after a mask. -/
def ren (ks : List Bool) (pc : Nat) : Nat := (ks.take pc).count true

theorem ren_zero (ks : List Bool) : ren ks 0 = 0 := by simp [ren]

theorem ren_cons (k : Bool) (ks : List Bool) (pc : Nat) :
    ren (k :: ks) (pc + 1) = (if k then 1 else 0) + ren ks pc := by
  cases k <;> simp [ren, List.take_succ_cons, List.count_cons] <;> omega

theorem ren_succ : ∀ (ks : List Bool) (pc : Nat),
    ren ks (pc + 1) = ren ks pc + (if ks[pc]? = some true then 1 else 0)
  | [], pc => by simp [ren]
  | k :: ks, 0 => by cases k <;> simp [ren]
  | k :: ks, pc + 1 => by
    rw [ren_cons, ren_cons, ren_succ ks pc]
    by_cases h : ks[pc]? = some true <;> simp [h] <;> omega

theorem sel_get {α : Type} : ∀ (ks : List Bool) (xs : List α) (pc : Nat), ks.length = xs.length →
    ks[pc]? = some true → (sel ks xs)[ren ks pc]? = xs[pc]?
  | [], _, pc, _, h => by simp at h
  | k :: ks, [], _, hl, _ => by simp at hl
  | k :: ks, x :: xs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [sel, ren_zero]
  | k :: ks, x :: xs, pc + 1, hl, h => by
    have ih := sel_get ks xs pc (by simpa using hl) (by simpa using h)
    rw [ren_cons]
    cases k
    · simpa [sel] using ih
    · simp only [sel, if_true, List.getElem?_cons_succ]
      rw [Nat.add_comm, List.getElem?_cons_succ]
      exact ih

theorem sel_length {α : Type} : ∀ (ks : List Bool) (xs : List α) (pc : Nat), ks.length = xs.length →
    xs.length ≤ pc → (sel ks xs).length = ren ks pc
  | [], [], pc, _, _ => by simp [sel, ren]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | k :: ks, x :: xs, 0, _, h => by simp at h
  | k :: ks, x :: xs, pc + 1, hl, h => by
    have ih := sel_length ks xs pc (by simpa using hl) (by simpa using h)
    rw [ren_cons]
    cases k <;> simp [sel, ih] <;> omega

theorem sel_find {α : Type} (p : α → Bool) : ∀ (ks : List Bool) (xs : List α) (i : Nat), ks.length = xs.length →
    xs.findIdx? p = some i → ks[i]? = some true → (sel ks xs).findIdx? p = some (ren ks i)
  | [], _, i, _, _, h => by simp at h
  | k :: ks, [], _, hl, _, _ => by simp at hl
  | k :: ks, x :: xs, i, hl, hf, hk => by
    rw [List.findIdx?_cons] at hf
    cases hp : p x with
    | true =>
      simp only [hp, if_true, Option.some.injEq] at hf
      subst hf
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [sel, List.findIdx?_cons, hp, ren_zero]
    | false =>
      simp only [hp, Bool.false_eq_true, if_false] at hf
      cases hj : xs.findIdx? p with
      | none => simp [hj] at hf
      | some j =>
        simp only [hj, Option.map_some, Option.some.injEq] at hf
        subst hf
        have ih := sel_find p ks xs j (by simpa using hl) hj (by simpa using hk)
        rw [ren_cons]
        cases k
        · simpa [sel] using ih
        · simp only [sel, List.findIdx?_cons, hp, Bool.false_eq_true, if_false, ih, if_true, Option.map_some]
          rw [Nat.add_comm]

theorem sel_sublist {α : Type} : ∀ (ks : List Bool) (xs : List α), (sel ks xs).Sublist xs
  | [], xs => by cases xs <;> simp [sel]
  | k :: ks, [] => by cases k <;> simp [sel]
  | true :: ks, x :: xs => by simpa [sel] using sel_sublist ks xs
  | false :: ks, x :: xs => by simpa [sel] using (sel_sublist ks xs).cons x

theorem find_get {α : Type} (p : α → Bool) : ∀ (xs : List α) (i : Nat), xs.findIdx? p = some i →
    ∃ x, xs[i]? = some x ∧ p x = true
  | [], _, h => by simp at h
  | x :: xs, i, h => by
    rw [List.findIdx?_cons] at h
    cases hp : p x with
    | true =>
      simp only [hp, if_true, Option.some.injEq] at h
      subst h
      exact ⟨x, rfl, hp⟩
    | false =>
      simp only [hp, Bool.false_eq_true, if_false] at h
      cases hj : xs.findIdx? p with
      | none => simp [hj] at h
      | some j =>
        simp only [hj, Option.map_some, Option.some.injEq] at h
        subst h
        simpa using find_get p xs j hj

/-- The body after a mask. -/
def selFn (f : Fn) (ks : List Bool) : Fn := { f with body := (sel ks f.body.toList).toArray }

theorem labelAt_list (f : Fn) (l : Nat) : labelAt f l = f.body.toList.findIdx? (isLabel l) := by
  unfold labelAt
  rcases f.body with ⟨xs⟩
  simp

theorem label_get {f : Fn} {l i : Nat} (h : labelAt f l = some i) : f.body[i]? = some (.label l) := by
  rw [labelAt_list] at h
  obtain ⟨x, hx, hp⟩ := find_get _ _ _ h
  rw [isLabel_iff] at hp
  subst hp
  simpa using hx

/-- A label that is defined once is where it is found. -/
theorem label_at {f : Fn} (hu : (labelsOf f.body).Nodup) {l i : Nat} (h : f.body[i]? = some (.label l)) :
    labelAt f l = some i := by
  unfold labelAt
  rw [Array.findIdx?_eq_some_iff_getElem]
  have hi : i < f.body.size := by
    rcases Nat.lt_or_ge i f.body.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  have h' := h
  rw [Array.getElem?_eq_getElem hi] at h'
  simp only [Option.some.injEq] at h'
  refine ⟨hi, by rw [h']; simp [isLabel], fun j hj hp => ?_⟩
  have hj' : j < f.body.size := by omega
  rw [isLabel_iff] at hp
  have := labels_unique hu j i l (by rw [Array.getElem?_eq_getElem hj', hp]) h
  omega

/-- Goes on to the next instruction (when it does not jump). -/
def falls : Instr → Bool
  | .ret _ | .jmp _ | .trap => false
  | _ => true

theorem step_next_falls {c : Ctx} {st st' : St} {tmps tmps' : Array Nat} {ins : Instr}
    (h : step c st tmps ins = .next st' tmps') : falls ins = true := by
  cases ins <;> first | rfl | simp [step] at h

theorem step_call_falls {c : Ctx} {st st' : St} {tmps : Array Nat} {ins : Instr} {g : String} {ret : Option (Nat × Dst)}
    (h : step c st tmps ins = .call g st' ret) : falls ins = true := by
  cases ins <;> first | rfl | simp [step] at h

theorem step_goto_target {c : Ctx} {st : St} {tmps : Array Nat} {ins : Instr} {l : Nat}
    (h : step c st tmps ins = .goto l) : ins.target? = some l := by
  cases ins <;> simp only [step, Step.set] at h <;> (try split at h) <;> (try split at h) <;> simp_all [Instr.target?]

/-- What a mask may drop: instructions that do nothing where they are
(a label, a jump to the next instruction), and nothing a kept
instruction leads to.  `Live`: the points that can be reached. -/
structure DelOK (f : Fn) (ks : List Bool) (Live : Nat → Prop) : Prop where
  len : ks.length = f.body.size
  zero : Live 0
  del : ∀ pc ins, Live pc → f.body[pc]? = some ins → ks[pc]? = some false →
    Live (pc + 1) ∧ ((∃ l, ins = .label l) ∨ ∃ l, ins = .jmp l ∧ labelAt f l = some (pc + 1))
  keep : ∀ pc ins, Live pc → f.body[pc]? = some ins → ks[pc]? = some true →
    (falls ins = true → Live (pc + 1)) ∧
      ∀ l, ins.target? = some l → ∀ i, labelAt f l = some i → ks[i]? = some true ∧ Live i

theorem del_sim (c : Ctx) {f : Fn} {ks : List Bool} {Live : Nat → Prop} (D : DelOK f ks Live) :
    Sim c f (selFn f ks) (fun pc pc' _ _ => pc' = ren ks pc ∧ Live pc) := by
  have hlen : ks.length = f.body.toList.length := by simpa using D.len
  refine ⟨fun pc pc' st tmps ins hR hb => ?_, fun pc pc' st tmps hR hb => ?_⟩
  · obtain ⟨rfl, hlive⟩ := hR
    have hpc : pc < ks.length := by
      rw [D.len]
      rcases Nat.lt_or_ge pc f.body.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hb; cases hb
    have hk : ks[pc]? = some ks[pc] := List.getElem?_eq_getElem hpc
    cases hkv : ks[pc] with
    | false =>
      rw [hkv] at hk
      obtain ⟨hl1, hdel⟩ := D.del pc ins hlive hb hk
      have hren : ren ks (pc + 1) = ren ks pc := by rw [ren_succ, hk]; simp
      rcases hdel with ⟨l, rfl⟩ | ⟨l, rfl, hl⟩
      · exact Or.inl ⟨rfl, hren.symm, hl1⟩
      · exact Or.inr (Or.inl ⟨l, pc + 1, rfl, hl, hren.symm, hl1⟩)
    | true =>
      rw [hkv] at hk
      obtain ⟨hfall, htgt⟩ := D.keep pc ins hlive hb hk
      have hren : ren ks (pc + 1) = ren ks pc + 1 := by rw [ren_succ, hk]; simp
      have hb' : (selFn f ks).body[ren ks pc]? = some ins := by
        simp only [selFn, List.getElem?_toArray]
        rw [sel_get ks _ pc hlen hk]
        simpa using hb
      refine Or.inr (Or.inr ⟨ins, hb', rfl, ?_⟩)
      cases hs : step c st tmps ins with
      | next st2 tmps2 => exact ⟨hren.symm, hfall (step_next_falls hs)⟩
      | goto l =>
        intro i hi
        obtain ⟨hki, hli⟩ := htgt l (step_goto_target hs) i hi
        refine ⟨ren ks i, ?_, rfl, hli⟩
        rw [labelAt_list] at hi ⊢
        simp only [selFn]
        exact sel_find _ ks _ i hlen hi hki
      | call g st1 ret => exact fun _ _ => ⟨hren.symm, hfall (step_call_falls hs)⟩
      | stop _ => trivial
  · obtain ⟨rfl, _⟩ := hR
    have hpc : f.body.toList.length ≤ pc := by
      rcases Nat.lt_or_ge pc f.body.size with h' | h'
      · rw [Array.getElem?_eq_getElem h'] at hb; cases hb
      · simpa using h'
    simp only [selFn, List.getElem?_toArray]
    rw [List.getElem?_eq_none]
    rw [sel_length ks _ pc hlen hpc]
    exact Nat.le_refl _

theorem del_ref (c : Ctx) {f : Fn} {ks : List Bool} {Live : Nat → Prop} (D : DelOK f ks Live) :
    FRef c c f (selFn f ks) :=
  fref_of_sim (CtxEq.refl c) (del_sim c D) (fun _ _ => ⟨(ren_zero ks).symm, D.zero⟩)

theorem sel_nodup {f : Fn} (ks : List Bool) (hu : (labelsOf f.body).Nodup) : (labelsOf (selFn f ks).body).Nodup := by
  unfold labelsOf at hu ⊢
  simp only [selFn]
  exact hu.sublist ((sel_sublist ks _).filterMap _)

/-! ## `cleanup` -/

theorem deadMask_length : ∀ (d : Bool) (b : List Instr), (deadMask d b).length = b.length
  | _, [] => rfl
  | d, x :: r => by cases x <;> simp [deadMask, deadMask_length _ r]

theorem dead_label : ∀ (d : Bool) (b : List Instr) (i l : Nat), b[i]? = some (.label l) →
    (deadMask d b)[i]? = some true
  | _, [], _, _, h => by simp at h
  | d, x :: r, 0, l, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [deadMask]
  | d, x :: r, i + 1, l, h => by
    have h' : r[i]? = some (.label l) := by simpa using h
    cases x <;> simp only [deadMask, List.getElem?_cons_succ] <;> exact dead_label _ r i l h'

theorem dead_head : ∀ (b : List Instr), (deadMask false b)[0]? ≠ some false
  | [] => by simp [deadMask]
  | x :: r => by cases x <;> simp [deadMask]

theorem dead_next : ∀ (d : Bool) (b : List Instr) (pc : Nat) (ins : Instr), b[pc]? = some ins →
    (deadMask d b)[pc]? = some true → falls ins = true → (deadMask d b)[pc + 1]? ≠ some false
  | _, [], _, _, h, _, _ => by simp at h
  | d, x :: r, 0, ins, hb, hk, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    subst hb
    cases d <;> cases x <;>
      first
        | (simp [deadMask] at hk; done)
        | (simp only [deadMask, List.getElem?_cons_succ]; exact dead_head r)
        | (simp [falls] at hf)
  | d, x :: r, pc + 1, ins, hb, hk, hf => by
    have hb' : r[pc]? = some ins := by simpa using hb
    cases x <;> simp only [deadMask, List.getElem?_cons_succ] at hk ⊢ <;> exact dead_next _ r pc ins hb' hk hf

theorem dead_ok (f : Fn) :
    DelOK f (deadMask false f.body.toList) (fun pc => (deadMask false f.body.toList)[pc]? ≠ some false) := by
  refine ⟨by simp [deadMask_length], dead_head _, fun pc ins hl _ hk => absurd hk hl, fun pc ins _ hb hk => ?_⟩
  refine ⟨fun hf => dead_next false _ pc ins (by simpa using hb) hk hf, fun l _ i hi => ?_⟩
  have := dead_label false f.body.toList i l (by simpa using label_get hi)
  exact ⟨this, by rw [this]; simp⟩

theorem jmpMask_length : ∀ (b : List Instr), (jmpMask b).length = b.length
  | [] => rfl
  | x :: r => by simp [jmpMask, jmpMask_length r]

theorem jmp_del : ∀ (b : List Instr) (pc : Nat), (jmpMask b)[pc]? = some false →
    ∃ l, b[pc]? = some (.jmp l) ∧ b[pc + 1]? = some (.label l)
  | [], _, h => by simp [jmpMask] at h
  | x :: r, 0, h => by
    simp only [jmpMask, List.getElem?_cons_zero, Option.some.injEq] at h
    split at h
    · rename_i l m t
      have : l = m := by simpa using h
      subst this
      exact ⟨l, rfl, rfl⟩
    · cases h
  | x :: r, pc + 1, h => by
    simp only [jmpMask, List.getElem?_cons_succ] at h
    simpa using jmp_del r pc h

theorem jmp_keep : ∀ (b : List Instr) (i : Nat) (ins : Instr), b[i]? = some ins → (∀ l, ins ≠ .jmp l) →
    (jmpMask b)[i]? = some true
  | [], _, _, h, _ => by simp at h
  | x :: r, 0, ins, h, hn => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [jmpMask, List.getElem?_cons_zero, Option.some.injEq]
    split
    · rename_i l m t
      exact absurd rfl (hn l)
    · rfl
  | x :: r, i + 1, ins, h, hn => by
    simp only [jmpMask, List.getElem?_cons_succ]
    exact jmp_keep r i ins (by simpa using h) hn

theorem jmp_ok (f : Fn) (hu : (labelsOf f.body).Nodup) : DelOK f (jmpMask f.body.toList) (fun _ => True) := by
  refine ⟨by simp [jmpMask_length], trivial, fun pc ins _ hb hk => ?_, fun pc ins _ hb hk => ?_⟩
  · obtain ⟨l, h1, h2⟩ := jmp_del _ pc hk
    have h1' : f.body[pc]? = some (.jmp l) := by simpa using h1
    rw [hb] at h1'
    cases h1'
    exact ⟨trivial, Or.inr ⟨l, rfl, label_at hu (by simpa using h2)⟩⟩
  · refine ⟨fun _ => trivial, fun l _ i hi => ⟨?_, trivial⟩⟩
    exact jmp_keep _ i (.label l) (by simpa using label_get hi) (fun l' h => by cases h)

theorem lab_ok (f : Fn) : DelOK f (labelMask (targetsOf f.body.toList) f.body.toList) (fun _ => True) := by
  refine ⟨by simp [labelMask], trivial, fun pc ins _ hb hk => ?_, fun pc ins _ hb hk => ?_⟩
  · have hb' : f.body.toList[pc]? = some ins := by simpa using hb
    simp only [labelMask, List.getElem?_map, hb', Option.map_some, Option.some.injEq] at hk
    refine ⟨trivial, Or.inl ?_⟩
    cases ins <;> first | exact ⟨_, rfl⟩ | cases hk
  · refine ⟨fun _ => trivial, fun l ht i hi => ⟨?_, trivial⟩⟩
    have hb' : f.body.toList[pc]? = some ins := by simpa using hb
    have hi' : f.body.toList[i]? = some (.label l) := by simpa using label_get hi
    have hmem : l ∈ targetsOf f.body.toList := List.mem_filterMap.mpr ⟨ins, List.mem_of_getElem? hb', ht⟩
    simp only [labelMask, List.getElem?_map, hi', Option.map_some, Option.some.injEq]
    simpa using hmem

/-- The function with another body. -/
def withBody (f : Fn) (b : Array Instr) : Fn := { f with body := b }

theorem nodup_of_sub {b b' : Array Instr} (h : b'.toList.Sublist b.toList) (hu : (labelsOf b).Nodup) :
    (labelsOf b').Nodup := by
  unfold labelsOf at hu ⊢
  exact hu.sublist (h.filterMap _)

theorem pass_sub (b : Array Instr) : (cleanupPass b).toList.Sublist b.toList := by
  simp only [cleanupPass]
  exact ((sel_sublist _ _).trans (sel_sublist _ _)).trans (sel_sublist _ _)

theorem cleanupN_sub : ∀ (n : Nat) (b : Array Instr), (cleanupN n b).toList.Sublist b.toList
  | 0, b => by simp [cleanupN]
  | n + 1, b => by
    simp only [cleanupN]
    split
    · exact (cleanupN_sub n _).trans (pass_sub b)
    · exact pass_sub b

theorem pass_ref (c : Ctx) (f : Fn) (hu : (labelsOf f.body).Nodup) : FRef c c f (withBody f (cleanupPass f.body)) := by
  have h1 := del_ref c (dead_ok f)
  have h2 := del_ref c (jmp_ok (selFn f (deadMask false f.body.toList)) (sel_nodup _ hu))
  have h3 := del_ref c (lab_ok (selFn (selFn f (deadMask false f.body.toList))
    (jmpMask (selFn f (deadMask false f.body.toList)).body.toList)))
  exact (h1.trans h2).trans h3

theorem cleanupN_ref (c : Ctx) : ∀ (n : Nat) (f : Fn), (labelsOf f.body).Nodup →
    FRef c c f (withBody f (cleanupN n f.body))
  | 0, f, _ => fref_refl (CtxEq.refl c) f
  | n + 1, f, hu => by
    simp only [cleanupN]
    have hp := pass_ref c f hu
    split
    · exact hp.trans (cleanupN_ref c n (withBody f (cleanupPass f.body)) (nodup_of_sub (pass_sub _) hu))
    · exact hp

/-! ## `dropChecks` -/

def dstUse (n : Nat) : Dst → List (Slot × Nat)
  | .slot s => [(s, n)]
  | .tmp _ => []

def opdUse (n : Nat) : Opd → List (Slot × Nat)
  | .slot s => [(s, n)]
  | _ => []

/-- The slots an instruction compares in a branch: those `dropChecks`
may have a fact about. -/
def brUses : Instr → List (Slot × Nat)
  | .br _ n x _ _ => opdUse n x
  | _ => []

/-- The slots an instruction writes as a destination. -/
def dstUses : Instr → List (Slot × Nat)
  | .mov n d _ | .bin _ n d _ _ | .shift _ n d _ _ _ | .not n d _ | .neg n d _ | .ext n d _ _ | .load n d _ => dstUse n d
  | .cmp _ _ d _ _ => dstUse 1 d
  | .lea d _ => dstUse 2 d
  | .call _ r _ | .eff _ _ r =>
    (match r with
     | some (n, d) => dstUse n d
     | none => [])
  | _ => []

/-- The slots of `U` (compared) and of `D` (written) are in memory, and
one of `U` and one of `D` that do not overlap by their offsets do not
overlap in memory.  (Two of `D` may: the frames of two callees.) -/
def SlotsOK (l : Layout) (U D : Slot × Nat → Prop) : Prop :=
  (∀ b bn, D (b, bn) → l.addr b + bn ≤ 65536) ∧
    ∀ a an, U (a, an) → l.addr a + an ≤ 65536 ∧
      ∀ b bn, D (b, bn) → slotsOverlap a an b bn = true ∨ l.addr a + an ≤ l.addr b ∨ l.addr b + bn ≤ l.addr a

/-- Every fact holds, and is about a slot of `U` or a temporary. -/
def FactsHold (c : Ctx) (U : Slot × Nat → Prop) (fs : Facts) (st : St) (tmps : Array Nat) : Prop :=
  ∀ o sz b, (o, sz, b) ∈ fs → opd c st tmps sz o < b ∧ ∀ a, o = .slot a → U (a, sz)

section
variable {c : Ctx} {U D : Slot × Nat → Prop} {fs : Facts} {st : St} {tmps : Array Nat}

theorem hold_written (h : FactsHold c U fs st tmps) (hS : SlotsOK c.layout U D) {n : Nat} {d : Dst}
    (hd : ∀ u, u ∈ dstUse n d → D u) (v : Nat) :
    FactsHold c U (written d n fs) (setDst c st tmps n d v).1 (setDst c st tmps n d v).2 := by
  intro o sz b hm
  simp only [written, List.mem_filter] at hm
  obtain ⟨hm, hcond⟩ := hm
  obtain ⟨hlt, hU⟩ := h o sz b hm
  refine ⟨?_, hU⟩
  cases o with
  | const v' => exact hlt
  | slot a =>
    cases d with
    | slot s =>
      simp only [setDst, opd] at hlt ⊢
      have hUs := hd (s, n) (by simp [dstUse])
      obtain ⟨hba, hap⟩ := hS.2 a sz (hU a rfl)
      have hbs := hS.1 s n hUs
      rcases hap s n hUs with ho | hfar
      · simp [ho] at hcond
      · rw [rd_wr_far _ _ _ _ _ _ hba hbs hfar]
        exact hlt
    | tmp u => exact hlt
  | tmp t =>
    cases d with
    | slot s => exact hlt
    | tmp u =>
      simp only [setDst, opd] at hlt ⊢
      have hne : u ≠ t := by
        intro e
        subst e
        simp at hcond
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne, ← Array.getD_eq_getD_getElem?]
      exact hlt

theorem hold_noSlots (h : FactsHold c U fs st tmps) (st' : St) : FactsHold c U (noSlots fs) st' tmps := by
  intro o sz b hm
  simp only [noSlots, List.mem_filter] at hm
  obtain ⟨hm, hcond⟩ := hm
  obtain ⟨hlt, hU⟩ := h o sz b hm
  refine ⟨?_, hU⟩
  cases o with
  | const v' => exact hlt
  | slot a => simp at hcond
  | tmp t => exact hlt

/-- **An instruction that goes on leaves the facts `factsAfter` gives.** -/
theorem facts_step (h : FactsHold c U fs st tmps) (hS : SlotsOK c.layout U D) (ins : Instr)
    (hu : ∀ u, u ∈ brUses ins → U u) (hd : ∀ u, u ∈ dstUses ins → D u) :
    match step c st tmps ins with
    | .next st2 tmps2 => FactsHold c U (factsAfter fs ins) st2 tmps2
    | .call _ _ ret => ∀ r st2,
        FactsHold c U (factsAfter fs ins) (setRet c st2 tmps ret r).1 (setRet c st2 tmps ret r).2
    | _ => True := by
  cases ins with
  | mov n d src => exact hold_written h hS hd _
  | bin op n d a b => exact hold_written h hS hd _
  | shift left n d a m amt => exact hold_written h hS hd _
  | not n d a => exact hold_written h hS hd _
  | neg n d a => exact hold_written h hS hd _
  | ext n d m src => exact hold_written h hS hd _
  | cmp op n d a b => exact hold_written h hS hd _
  | br op n a b l =>
    by_cases hcmp : cmpOp op (opd c st tmps n a) (opd c st tmps n b) = true
    · simp only [step, hcmp, if_true]
    · simp only [step, hcmp, Bool.false_eq_true, if_false, factsAfter]
      split
      · exact h
      · rename_i x cst _
        intro o sz bb hm
        rcases List.mem_cons.mp hm with he | hm'
        · cases he
          refine ⟨?_, fun s hs => hu (s, n) (by subst hs; simp [brUses, opdUse])⟩
          have : opd c st tmps n a < modN n cst := by simpa [cmpOp, opd] using hcmp
          exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)
        · exact h o sz bb hm'
      · exact h
  | jmp l => trivial
  | label l =>
    intro o sz b hm
    simp [factsAfter] at hm
  | load n d p =>
    simp only [step]
    cases addr c st tmps p with
    | none => trivial
    | some a =>
      by_cases hin : inBound c st tmps p = true
      · simp only [hin, if_true]
        exact hold_written h hS hd _
      · simp only [hin, Bool.false_eq_true, if_false]
  | store n p src =>
    simp only [step]
    cases addr c st tmps p with
    | none => trivial
    | some a =>
      by_cases hin : inBound c st tmps p = true
      · simp only [hin, if_true]
        exact hold_noSlots h _
      · simp only [hin, Bool.false_eq_true, if_false]
  | lea d p =>
    simp only [step]
    cases addr c st tmps p with
    | none => trivial
    | some a =>
      by_cases hin : inBound c st tmps p = true
      · simp only [hin, if_true]
        exact hold_written h hS hd _
      · simp only [hin, Bool.false_eq_true, if_false]
  | zero s n => exact hold_noSlots h _
  | call g ret reg =>
    intro r st2
    cases ret with
    | none => exact hold_noSlots h st2
    | some x => exact hold_written (hold_noSlots h st2) hS hd _
  | eff e args ret =>
    cases ret with
    | none => exact hold_noSlots h _
    | some x => exact hold_written (hold_noSlots h _) hS hd _
  | ret v => trivial
  | trap => trivial

/-- A check a fact makes needless does not fail. -/
theorem known_addr (h : FactsHold c U fs st tmps) (p : Addr) :
    addr c st tmps (knownAddr fs p) = addr c st tmps p := by
  unfold knownAddr
  split
  · rename_i x hx
    split
    · rename_i n hn
      split
      · rename_i hany
        obtain ⟨⟨o, sz, b⟩, hm, hc⟩ := List.any_eq_true.mp hany
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, hbn⟩ := hc
        have hlt := (h _ _ _ hm).1
        simp only [addr, hx, hn]
        rw [if_pos (by omega)]
      · rfl
    · rfl
  · rfl

/-- The bound stays where the check goes. -/
theorem known_inBound (p : Addr) : inBound c st tmps (knownAddr fs p) = inBound c st tmps p := by
  unfold knownAddr
  split
  · rename_i x hx
    split
    · split
      · simp only [inBound, hx]
      · rfl
    · rfl
  · rfl

theorem known_step (h : FactsHold c U fs st tmps) (ins : Instr) :
    step c st tmps (knownInstr fs ins) = step c st tmps ins := by
  cases ins <;> first | rfl | simp only [knownInstr, step, known_addr h, known_inBound]

end

theorem isLabel_known (l : Nat) (fs : Facts) (ins : Instr) : isLabel l (knownInstr fs ins) = isLabel l ins := by
  cases ins <;> rfl

/-- The facts `dropFrom` has at the instruction `pc`. -/
def factsAt : Facts → List Instr → Nat → Facts
  | fs, _, 0 => fs
  | fs, [], _ + 1 => fs
  | fs, i :: r, pc + 1 => factsAt (factsAfter fs i) r pc

theorem drop_get : ∀ (fs : Facts) (b : List Instr) (pc : Nat),
    (dropFrom fs b)[pc]? = (b[pc]?).map (knownInstr (factsAt fs b pc))
  | fs, [], pc => by simp [dropFrom]
  | fs, i :: r, 0 => by simp [dropFrom, factsAt]
  | fs, i :: r, pc + 1 => by
    simp only [dropFrom, factsAt, List.getElem?_cons_succ]
    exact drop_get _ r pc

theorem factsAt_succ : ∀ (fs : Facts) (b : List Instr) (pc : Nat) (ins : Instr), b[pc]? = some ins →
    factsAt fs b (pc + 1) = factsAfter (factsAt fs b pc) ins
  | _, [], _, _, h => by simp at h
  | fs, i :: r, 0, ins, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [factsAt]
  | fs, i :: r, pc + 1, ins, h => by
    simp only [factsAt]
    exact factsAt_succ _ r pc ins (by simpa using h)

theorem drop_find (l : Nat) : ∀ (fs : Facts) (b : List Instr),
    (dropFrom fs b).findIdx? (isLabel l) = b.findIdx? (isLabel l)
  | _, [] => rfl
  | fs, i :: r => by simp only [dropFrom, List.findIdx?_cons, isLabel_known, drop_find l _ r]

theorem drop_sim (c : Ctx) (f : Fn) (U D : Slot × Nat → Prop) (hS : SlotsOK c.layout U D)
    (hU : ∀ ins, ins ∈ f.body.toList → ∀ u, u ∈ brUses ins → U u)
    (hD : ∀ ins, ins ∈ f.body.toList → ∀ u, u ∈ dstUses ins → D u) :
    Sim c f (withBody f (dropChecks f.body)) (fun pc pc' st tmps => pc' = pc ∧
      ((∃ l, f.body[pc]? = some (.label l)) ∨ FactsHold c U (factsAt [] f.body.toList pc) st tmps)) := by
  refine ⟨fun pc0 pc st tmps ins hR hb => ?_, fun pc0 pc st tmps hR hb => ?_⟩
  · obtain ⟨rfl, hR⟩ := hR
    have hb' : f.body.toList[pc]? = some ins := by simpa using hb
    have hget : (withBody f (dropChecks f.body)).body[pc]? =
        some (knownInstr (factsAt [] f.body.toList pc) ins) := by
      simp [withBody, dropChecks, drop_get, hb']
    have hsucc := factsAt_succ [] _ pc ins hb'
    have hstep : step c st tmps (knownInstr (factsAt [] f.body.toList pc) ins) = step c st tmps ins := by
      rcases hR with ⟨l, hl⟩ | hF
      · rw [hb] at hl
        cases hl
        rfl
      · exact known_step hF ins
    refine Or.inr (Or.inr ⟨_, hget, hstep, ?_⟩)
    have hfacts : (∃ l, ins = .label l) ∨ FactsHold c U (factsAt [] f.body.toList pc) st tmps := by
      rcases hR with ⟨l, hl⟩ | hF
      · rw [hb] at hl
        cases hl
        exact Or.inl ⟨l, rfl⟩
      · exact Or.inr hF
    cases hs : step c st tmps ins with
    | next st2 tmps2 =>
      refine ⟨rfl, Or.inr ?_⟩
      rw [hsucc]
      rcases hfacts with ⟨l, rfl⟩ | hF
      · intro o sz b hm
        simp [factsAfter] at hm
      · have := facts_step hF hS ins (hU ins (List.mem_of_getElem? hb')) (hD ins (List.mem_of_getElem? hb'))
        simp only [hs] at this
        exact this
    | goto l =>
      intro i hi
      refine ⟨i, ?_, rfl, Or.inl ⟨l, label_get hi⟩⟩
      rw [labelAt_list] at hi ⊢
      simp only [withBody, dropChecks]
      rw [drop_find]
      exact hi
    | call g st1 ret =>
      intro r st2
      refine ⟨rfl, Or.inr ?_⟩
      rw [hsucc]
      rcases hfacts with ⟨l, rfl⟩ | hF
      · simp [step] at hs
      · have := facts_step hF hS ins (hU ins (List.mem_of_getElem? hb')) (hD ins (List.mem_of_getElem? hb'))
        simp only [hs] at this
        exact this r st2
    | stop _ => trivial
  · obtain ⟨rfl, _⟩ := hR
    have hb' : f.body.toList[pc]? = none := by simpa using hb
    simp [withBody, dropChecks, drop_get, hb']

/-! ## `tidy` -/

/-- The slots a body compares in a branch, and those it writes. -/
def BrIn (b : Array Instr) (u : Slot × Nat) : Prop := ∃ ins, ins ∈ b.toList ∧ u ∈ brUses ins

def DstIn (b : Array Instr) (u : Slot × Nat) : Prop := ∃ ins, ins ∈ b.toList ∧ u ∈ dstUses ins

theorem tidy_fref (c : Ctx) (f : Fn) (hu : (labelsOf f.body).Nodup)
    (hS : SlotsOK c.layout (BrIn f.body) (DstIn f.body)) : FRef c c f (tidy f) := by
  refine (cleanupN_ref c (f.body.size + 1) f hu).trans ?_
  refine fref_of_sim (CtxEq.refl c)
    (drop_sim c (withBody f (cleanupN (f.body.size + 1) f.body)) (BrIn f.body) (DstIn f.body) hS
      (fun ins hi u hu' => ⟨ins, (cleanupN_sub _ _).subset hi, hu'⟩)
      (fun ins hi u hu' => ⟨ins, (cleanupN_sub _ _).subset hi, hu'⟩))
    (fun _ _ => ⟨rfl, Or.inr (fun o sz b hm => by simp [factsAt] at hm)⟩)

/-- The program with every body tidied: what `IR.lower` returns. -/
def tidyProg (q : IR.Prog) : IR.Prog := { q with fns := q.fns.map tidy }

theorem tidy_fn (q : IR.Prog) (g : String) : (tidyProg q).fn? g = (q.fn? g).map tidy := by
  simp only [tidyProg, IR.Prog.fn?, List.find?_map]
  rfl

/-- **A call in the tidied program ends as in the program as lowered.** -/
theorem tidy_ref {c : Ctx} (hu : ∀ g f, c.prog.fn? g = some f → (labelsOf f.body).Nodup)
    (hs : ∀ g f, c.prog.fn? g = some f → SlotsOK c.layout (BrIn f.body) (DstIn f.body)) (n : Nat) (g : String) (st : St)
    (r : Res) (he : callF n c g st = r) (hd : Done r) :
    ∃ n', callF n' { c with prog := tidyProg c.prog } g st = r := by
  have hc : CtxEq c { c with prog := tidyProg c.prog } :=
    ⟨rfl, rfl, rfl, fun g => by rw [tidy_fn]; cases c.prog.fn? g <;> rfl⟩
  refine callRef_all (c := c) (c' := { c with prog := tidyProg c.prog }) (fun g f hf => ?_) (n + 1) n
    (Nat.lt_succ_self n) g st r he hd
  refine ⟨tidy f, by rw [tidy_fn, hf]; rfl, rfl, (fref_refl hc f).trans ?_⟩
  exact tidy_fref _ f (hu g f hf) (hs g f hf)

end Ember.Proof.IRSim
