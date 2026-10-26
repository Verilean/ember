import Ember.Proof.IRSim

/-!
# Ember.Proof.IRProgram — the lowered program (plan M7.1)

* `lowered_of_raw`: the program `IR.lowerRaw` returns is the lowering of
  every function, with no label defined twice;
* `layOk_sound`: a layout the validator accepts, with every global
  placed, is what the simulation needs (`LayOK`);
* `entry_sim`, `iter_sim`: a call of the entry function, and call after
  call, in the IR as in `Lang.Sem`.

This is about the program as lowered (`IR.lowerRaw`); `IR.lower` then
tidies every body (`cleanup`, `dropChecks`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 FieldOK TyOK NoRef)

/-! ## `mapM` -/

theorem mapM_nil_ok {α β : Type} (f : α → Except String β) : ([] : List α).mapM f = .ok [] := rfl

theorem mapM_cons_ok {α β : Type} (f : α → Except String β) (a : α) (l : List α) (l' : List β)
    (h : (a :: l).mapM f = .ok l') : ∃ b bs, f a = .ok b ∧ l.mapM f = .ok bs ∧ l' = b :: bs := by
  rw [List.mapM_cons] at h
  cases hfa : f a with
  | error e => simp [hfa, bind, Except.bind] at h
  | ok b =>
    cases hl : l.mapM f with
    | error e => simp [hfa, hl, bind, Except.bind] at h
    | ok bs =>
      simp only [hfa, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨b, bs, rfl, rfl, h.symm⟩

/-- A function found by its name is mapped to one found by its name. -/
theorem mapM_find {α β : Type} (f : α → Except String β) (ka : α → String) (kb : β → String)
    (hk : ∀ a b, f a = .ok b → kb b = ka a) : ∀ (l : List α) (l' : List β), l.mapM f = .ok l' →
    ∀ g a, l.find? (fun x => ka x == g) = some a → ∃ b, l'.find? (fun x => kb x == g) = some b ∧ f a = .ok b
  | [], _, _, _, _, hf => by simp at hf
  | x :: l, l', h, g, a, hf => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok f x l l' h
    simp only [List.find?_cons] at hf ⊢
    rw [hk x b hb]
    cases hx : ka x == g with
    | true =>
      simp only [hx, Option.some.injEq] at hf
      subst hf
      exact ⟨b, rfl, hb⟩
    | false =>
      simp only [hx] at hf
      exact mapM_find f ka kb hk l bs hbs g a hf

theorem mapM_mem {α β : Type} (f : α → Except String β) : ∀ (l : List α) (l' : List β), l.mapM f = .ok l' →
    ∀ b, b ∈ l' → ∃ a, a ∈ l ∧ f a = .ok b
  | [], l', h, b, hb => by
    cases h
    simp at hb
  | x :: l, l', h, b, hb => by
    obtain ⟨b0, bs, hb0, hbs, rfl⟩ := mapM_cons_ok f x l l' h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨x, by simp, hb0⟩
    · obtain ⟨a, ha, hfa⟩ := mapM_mem f l bs hbs b hb'
      exact ⟨a, by simp [ha], hfa⟩

/-! ## The program -/

theorem lowerFnRaw_name {lp : Prog} {fd : Lang.Fn} {gf : IR.Fn} (h : lowerFnRaw lp fd = .ok gf) : gf.name = fd.name := by
  unfold lowerFnRaw at h
  split at h
  · cases h; rfl
  · cases h

theorem lowerFnChecked_ok {lp : Prog} {fd : Lang.Fn} {gf : IR.Fn} (h : lowerFnChecked lp fd = .ok gf) :
    lowerFnRaw lp fd = .ok gf ∧ (labelsOf gf.body).Nodup := by
  unfold lowerFnChecked at h
  split at h
  · rename_i r hr
    split at h
    · rename_i hn
      cases h
      exact ⟨hr, hn⟩
    · cases h
  · cases h

/-- **The program `lowerRaw` returns is the lowering of the Ember program.** -/
theorem lowered_of_raw {lp : Prog} {q : IR.Prog} (h : lowerRaw lp = .ok q) (c : Ctx) (hc : c.prog = q)
    (hd : c.dropReasons = lp.dropReasons) (hn : c.notes = lp.notes) : Lowered lp c := by
  unfold lowerRaw at h
  split at h
  · rename_i fns hfns
    cases h
    refine ⟨fun g fd hfd => ?_, fun g gf hgf => ?_, hd, hn⟩
    · obtain ⟨gf, hgf, hok⟩ := mapM_find (lowerFnChecked lp) (·.name) (·.name)
        (fun a b hab => lowerFnRaw_name (lowerFnChecked_ok hab).1) lp.fns fns hfns g fd hfd
      exact ⟨gf, by rw [hc]; exact hgf, (lowerFnChecked_ok hok).1⟩
    · rw [hc] at hgf
      obtain ⟨fd, _, hok⟩ := mapM_mem (lowerFnChecked lp) lp.fns fns hfns gf (List.mem_of_find?_eq_some hgf)
      exact (lowerFnChecked_ok hok).2
  · cases h

theorem lowerRaw_shape {lp : Prog} {q : IR.Prog} (h : lowerRaw lp = .ok q) :
    q.globals = lp.globals.map (lowerGlobal lp) ∧ q.entry = lp.entry := by
  unfold lowerRaw at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-! ## The layout -/

/-- The check of a layout for a program: the validator accepts it in
64 KB, every global is placed, no two globals have one name, and a
`bool` starts as 0 or 1. -/
def layOkB (lp : Prog) (q : IR.Prog) (l : Layout) : Bool :=
  valid q l (fun f => ((q.fn? f).map (·.frame)).getD 0) 0 65536 &&
  lp.globals.all (fun g => (l.globals.lookup g.name).isSome) &&
  decide (lp.globals.map (·.name)).Nodup &&
  lp.globals.all (fun g => match g.ty with | .bool => g.init.all (· ≤ 1) | _ => true)

theorem lowerGlobal_name (lp : Prog) (g : Global) : (lowerGlobal lp g).name = g.name := rfl

theorem lowerGlobal_size (lp : Prog) (g : Global) : (lowerGlobal lp g).size = sizeOf lp g.ty := rfl

theorem layOk_sound {lp : Prog} {q : IR.Prog} {l : Layout} (h : layOkB lp q l = true)
    (hq : q.globals = lp.globals.map (lowerGlobal lp)) (c : Ctx) (hc1 : c.prog = q) (hc2 : c.layout = l) :
    LayOK lp c := by
  simp only [layOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hpl⟩, hnd⟩, hbool⟩ := h
  have S := valid_sound hv
  have hga : ∀ g, g ∈ lp.globals → ∃ a, l.globals.lookup g.name = some a ∧ gaddr c g.name = a ∧
      (g.name, a, sizeOf lp g.ty) ∈ placed q l := by
    intro g hg
    have := hpl g hg
    cases ha : l.globals.lookup g.name with
    | none => rw [ha] at this; cases this
    | some a =>
      refine ⟨a, rfl, by simp [gaddr, Layout.addr, Layout.areaAddr, hc2, ha], ?_⟩
      simp only [placed, hq, List.mem_filterMap, List.mem_map]
      exact ⟨lowerGlobal lp g, ⟨g, hg, rfl⟩, by simp [lowerGlobal_name, ha, lowerGlobal_size]⟩
  have hfa : ∀ fn f, c.prog.fn? fn = some f → f ∈ q.fns ∧ f.name = fn ∧
      ((q.fn? fn).map (·.frame)).getD 0 = f.frame := by
    intro fn f hf
    rw [hc1] at hf
    have hmem := List.mem_of_find?_eq_some hf
    have hname : f.name = fn := by simpa using List.find?_some hf
    exact ⟨hmem, hname, by rw [hf]; rfl⟩
  have hfb : ∀ fn f, c.prog.fn? fn = some f → ∃ a, l.frames.lookup fn = some a ∧ fbase c fn = a := by
    intro fn f hf
    obtain ⟨hmem, hname, _⟩ := hfa fn f hf
    obtain ⟨a, ha, _⟩ := S.frames f hmem
    rw [hname] at ha
    exact ⟨a, ha, by simp [fbase, Layout.addr, Layout.areaAddr, hc2, ha]⟩
  refine ⟨hnd, fun g hg => ?_, fun g g' hg hg' hne => ?_, fun g hg hb v hv' => ?_, fun fn f hf => ?_,
    fun fn A hin hgl => ?_, fun fn g A hr hin hin' => ?_⟩
  · obtain ⟨a, _, ha, hp⟩ := hga g hg
    rw [ha]
    exact (S.globals_in _ hp).2
  · obtain ⟨a, _, ha, hp⟩ := hga g hg
    obtain ⟨b, _, hb, hp'⟩ := hga g' hg'
    have hd := S.globals_apart _ _ hp hp' hne
    rw [ha, hb]
    simp only [disjoint, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
    omega
  · have := hbool g hg
    rw [hb] at this
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this v hv'
  · obtain ⟨hmem, hname, hfs⟩ := hfa fn f hf
    obtain ⟨a, ha, hfa'⟩ := hfb fn f hf
    obtain ⟨a', ha', _, hhi, _⟩ := S.frames f hmem
    rw [hname, ha] at ha'
    cases ha'
    rw [hname, hfs] at hhi
    rw [hfa']
    exact hhi
  · obtain ⟨f, hf, h1, h2⟩ := hin
    obtain ⟨g, hg, h3, h4⟩ := hgl
    obtain ⟨hmem, hname, hfs⟩ := hfa fn f hf
    obtain ⟨a, ha, hfa'⟩ := hfb fn f hf
    obtain ⟨b, _, hb, hp⟩ := hga g hg
    obtain ⟨a', ha', _, _, hgd, _⟩ := S.frames f hmem
    rw [hname, ha] at ha'
    cases ha'
    have hd := hgd _ hp
    rw [hname, hfs] at hd
    have hd' : disjoint a f.frame b (sizeOf lp g.ty) = true := hd
    exact disjoint_spec hd' A (by omega) (by omega)
  · have hr' : IR.Reach q fn g := by rw [← hc1]; exact hr
    obtain ⟨f, hf, h1, h2⟩ := hin
    obtain ⟨gf, hgf, h3, h4⟩ := hin'
    obtain ⟨hmem, hname, hfs⟩ := hfa fn f hf
    obtain ⟨a, ha, hfa'⟩ := hfb fn f hf
    obtain ⟨b, hb, hfb'⟩ := hfb g gf hgf
    obtain ⟨_, _, hgs⟩ := hfa g gf hgf
    obtain ⟨a', ha', _, _, _, hrd⟩ := S.frames f hmem
    rw [hname, ha] at ha'
    cases ha'
    rw [hname] at hrd
    obtain ⟨_, b', hb', hd⟩ := hrd g hr'
    rw [hb] at hb'
    cases hb'
    rw [hfs, hgs] at hd
    exact disjoint_spec hd A (by omega) (by omega)

/-! ## The entry function, called again and again -/

/-- `j` calls of the entry function; `none` when one traps or runs out of fuel. -/
def callIter (fuel : Nat) (p : Prog) : Nat → Lang.Sem.St → Option Lang.Sem.St
  | 0, st => some st
  | j + 1, st =>
    match Lang.Sem.call fuel p st p.entry [] with
    | .ok _ st' => callIter fuel p j st'
    | _ => none

/-- The same on the IR, as `Ember.Z80.IR.Sem.run` calls it. -/
def irIter (m : Nat) (c : Ctx) : Nat → St → Option St
  | 0, st => some st
  | j + 1, st =>
    match callF m c c.prog.entry st with
    | .ok _ st' => irIter m c j st'
    | _ => none

theorem irIter_le {c : Ctx} {m m' : Nat} (hm : m ≤ m') : ∀ (j : Nat) (st st' : St),
    irIter m c j st = some st' → irIter m' c j st = some st'
  | 0, _, _, h => h
  | j + 1, st, st', h => by
    rw [irIter] at h ⊢
    cases hc : callF m c c.prog.entry st with
    | ok r st1 =>
      rw [hc] at h
      rw [callF_mono (by rw [hc]; simp) hm, hc]
      exact irIter_le hm j st1 st' h
    | trap _ => rw [hc] at h; cases h
    | fuel => rw [hc] at h; cases h
    | bad => rw [hc] at h; cases h

section
variable {c : Ctx} {lp : Prog}

/-- **A call of the entry function.** -/
theorem entry_sim (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) (fd : Lang.Fn)
    (hE : lp.fn? lp.entry = some fd) (hpar : fd.params = []) (k : Nat) (st : Lang.Sem.St) (ist : St)
    (hG : GS c lp st ist) :
    match Lang.Sem.call k lp st lp.entry [] with
    | .ok _ st' => ∃ m r ist', callF m c lp.entry ist = .ok r ist' ∧ GS c lp st' ist'
    | .trap st' => ∃ m ist', callF m c lp.entry ist = .trap ist' ∧ ist'.world = st'.world
    | .fuel => True := by
  have H := fn_sim L hlow hok k lp.entry fd st [] ist hE hG (by simp [paramSlots, paramSlotsFrom, hpar, ParamsAt])
  rw [call_eq lp k st lp.entry [] fd hE]
  cases hB : Lang.Sem.execB k lp st ((fd.params.map (·.name)).zip []) fd.body with
  | fuel => trivial
  | trap st' => simp only [hB] at H ⊢; exact H
  | ok st' env' o =>
    simp only [hB] at H ⊢
    obtain ⟨m, ist', hm, hgs, _⟩ := H
    exact ⟨m, _, ist', hm, hgs⟩

/-- **The program, call after call.**  If `j` calls of the entry
function end in Ember, they end in the IR, in a related state. -/
theorem iter_sim (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) (he : c.prog.entry = lp.entry)
    (fd : Lang.Fn) (hE : lp.fn? lp.entry = some fd) (hpar : fd.params = []) (k : Nat) :
    ∀ (j : Nat) (st st' : Lang.Sem.St) (ist : St), GS c lp st ist → callIter k lp j st = some st' →
    ∃ m ist', irIter m c j ist = some ist' ∧ GS c lp st' ist'
  | 0, st, st', ist, hG, hi => by
    simp only [callIter, Option.some.injEq] at hi
    subst hi
    exact ⟨0, ist, rfl, hG⟩
  | j + 1, st, st', ist, hG, hi => by
    rw [callIter] at hi
    have hs := entry_sim L hlow hok fd hE hpar k st ist hG
    cases hc : Lang.Sem.call k lp st lp.entry [] with
    | ok v st1 =>
      simp only [hc] at hi hs
      obtain ⟨m1, r, ist1, hm1, hG1⟩ := hs
      obtain ⟨m2, ist', hm2, hG'⟩ := iter_sim L hlow hok he fd hE hpar k j st1 st' ist1 hG1 hi
      refine ⟨max m1 m2, ist', ?_, hG'⟩
      rw [irIter, he, callF_mono (by rw [hm1]; simp) (Nat.le_max_left m1 m2), hm1]
      exact irIter_le (Nat.le_max_right m1 m2) j ist1 ist' hm2
    | trap _ => simp only [hc] at hi; cases hi
    | fuel => simp only [hc] at hi; cases hi

/-- … and if the next call traps in Ember, it traps in the IR, with the same events. -/
theorem iter_trap (L : LayOK lp c) (hlow : Lowered lp c) (hok : ProgOK lp) (he : c.prog.entry = lp.entry)
    (fd : Lang.Fn) (hE : lp.fn? lp.entry = some fd) (hpar : fd.params = []) (k j : Nat)
    (st st1 st2 : Lang.Sem.St) (ist : St) (hG : GS c lp st ist) (hi : callIter k lp j st = some st1)
    (ht : Lang.Sem.call k lp st1 lp.entry [] = .trap st2) :
    ∃ m ist1 ist2, irIter m c j ist = some ist1 ∧ callF m c c.prog.entry ist1 = .trap ist2 ∧
      ist2.world = st2.world := by
  obtain ⟨m1, ist1, hm1, hG1⟩ := iter_sim L hlow hok he fd hE hpar k j st st1 ist hG hi
  have hs := entry_sim L hlow hok fd hE hpar k st1 ist1 hG1
  rw [ht] at hs
  obtain ⟨m2, ist2, hm2, hw⟩ := hs
  refine ⟨max m1 m2, ist1, ist2, irIter_le (Nat.le_max_left m1 m2) j ist ist1 hm1, ?_, hw⟩
  rw [he, callF_mono (by rw [hm2]; simp) (Nat.le_max_right m1 m2), hm2]

end

end Ember.Proof.IRSim
