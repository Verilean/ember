import Ember.Proof.IRPass
import Ember.Proof.IRInit
import Ember.Proof.IRCheck

/-!
# Ember.Proof.IRLower — `IR.lower` as a whole (plan M7.1)

`IR.lower` is `IR.lowerRaw` with every body tidied (`lower_tidy`).  So
what `Ember/Proof/IRProgram.lean` says of the program as lowered holds
of the program `lower` returns (`Ember/Proof/IRPass.lean`):

* `lower_iter`: **from the initial state, if `j` calls of the entry
  function end in Ember, they end in the IR, with the same events**;
* `lower_trap`: and if the next call traps in Ember, it traps in the IR.

Both for a program and a layout two checkers accept: `progOkB`
(`Ember/Proof/IRCheck.lean`) for the program, `irOkB` for the layout —
the frame validator accepts it for the program as lowered, a slot a body
compares and one it writes are where it keeps them apart, and the
initial values fit their types.
-/

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (TyOK tyOkB tyOkB_sound)

/-! ## `lower` is `lowerRaw`, tidied -/

theorem mapM_cons_intro {α β : Type} (f : α → Except String β) (a : α) (l : List α) (b : β) (bs : List β)
    (ha : f a = .ok b) (hl : l.mapM f = .ok bs) : (a :: l).mapM f = .ok (b :: bs) := by
  rw [List.mapM_cons]
  simp [ha, hl, bind, Except.bind, pure, Except.pure]

theorem mapM_tidy (lp : Prog) : ∀ (l : List Lang.Fn) (fns' : List IR.Fn), l.mapM (lowerFn lp) = .ok fns' →
    ∃ fns, l.mapM (lowerFnChecked lp) = .ok fns ∧ fns' = fns.map tidy
  | [], fns', h => by
    cases h
    exact ⟨[], rfl, rfl⟩
  | x :: l, fns', h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok _ x l fns' h
    obtain ⟨fns, hfns, rfl⟩ := mapM_tidy lp l bs hbs
    unfold lowerFn at hb
    split at hb
    · rename_i r hr
      cases hb
      exact ⟨r :: fns, mapM_cons_intro _ x l r fns hr hfns, rfl⟩
    · cases hb

theorem lower_tidy {lp : Prog} {q' : IR.Prog} (h : lower lp = .ok q') :
    ∃ q, lowerRaw lp = .ok q ∧ q' = tidyProg q := by
  unfold lower at h
  cases hm : lp.fns.mapM (lowerFn lp) with
  | error e => simp [hm, bind, Except.bind] at h
  | ok fns' =>
    simp only [hm, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, if_false, Except.ok.injEq] at h
    obtain ⟨fns, hfns, rfl⟩ := mapM_tidy lp lp.fns fns' hm
    refine ⟨{ globals := lp.globals.map (lowerGlobal lp), fns, entry := lp.entry }, ?_, h.symm⟩
    unfold lowerRaw
    rw [hfns]

/-! ## The calls of the entry function, in the tidied program -/

theorem tidy_iter {c : Ctx} (hu : ∀ g f, c.prog.fn? g = some f → (labelsOf f.body).Nodup)
    (hs : ∀ g f, c.prog.fn? g = some f → SlotsOK c.layout (BrIn f.body) (DstIn f.body)) :
    ∀ (j m : Nat) (st st' : St), irIter m c j st = some st' →
      ∃ m', irIter m' { c with prog := tidyProg c.prog } j st = some st'
  | 0, _, _, _, h => ⟨0, h⟩
  | j + 1, m, st, st', h => by
    rw [irIter] at h
    cases hc : callF m c c.prog.entry st with
    | ok r st1 =>
      rw [hc] at h
      obtain ⟨n1, hn1⟩ := tidy_ref hu hs m _ st _ hc trivial
      obtain ⟨m2, hm2⟩ := tidy_iter hu hs j m st1 st' h
      refine ⟨max n1 m2, ?_⟩
      rw [irIter]
      have he : (tidyProg c.prog).entry = c.prog.entry := rfl
      simp only [he]
      rw [callF_mono (by rw [hn1]; simp) (Nat.le_max_left n1 m2), hn1]
      exact irIter_le (Nat.le_max_right n1 m2) j st1 st' hm2
    | trap _ => rw [hc] at h; cases h
    | fuel => rw [hc] at h; cases h
    | bad => rw [hc] at h; cases h

/-! ## The checker of the layout -/

/-- The initial value of a global fits its type. -/
def globalInitB (p : Prog) (g : Global) : Bool :=
  tyOkB p g.ty &&
    match g.ty with
    | .int _ => decide (g.init.length ≤ 1)
    | .bool => decide (g.init.length ≤ 1) && g.init.all (· ≤ 1)
    | .arr .bool _ => g.init.all (· ≤ 1)
    | .arr _ _ => true
    | .record _ => g.init.isEmpty

theorem globalInitB_sound {p : Prog} {g : Global} (h : globalInitB p g = true) : GlobalOK p g := by
  simp only [globalInitB, Bool.and_eq_true] at h
  refine ⟨tyOkB_sound _ _ h.1, ?_⟩
  have h2 := h.2
  cases hty : g.ty with
  | int w => simpa [hty] using h2
  | bool => simpa [hty] using h2
  | arr el n =>
    cases el <;> simp only [hty] at h2 ⊢
    · simpa using h2
  | record r => simpa [hty] using h2

/-- In every body, a slot it compares and one it writes are where the
layout keeps them apart. -/
def slotsOkB (l : Layout) (q : IR.Prog) : Bool :=
  q.fns.all fun f =>
    let us := f.body.toList.flatMap brUses
    let ds := f.body.toList.flatMap dstUses
    (ds.all fun v => decide (l.addr v.1 + v.2 ≤ 65536)) &&
      us.all fun u =>
        decide (l.addr u.1 + u.2 ≤ 65536) &&
          ds.all fun v =>
            slotsOverlap u.1 u.2 v.1 v.2 || decide (l.addr u.1 + u.2 ≤ l.addr v.1) ||
              decide (l.addr v.1 + v.2 ≤ l.addr u.1)

theorem slotsOkB_sound {l : Layout} {q : IR.Prog} (h : slotsOkB l q = true) (f : IR.Fn) (hf : f ∈ q.fns) :
    SlotsOK l (BrIn f.body) (DstIn f.body) := by
  simp only [slotsOkB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hd, hu⟩ := h f hf
  refine ⟨fun b bn ⟨i, hi, hb⟩ => hd (b, bn) (List.mem_flatMap.mpr ⟨i, hi, hb⟩), fun a an ⟨i1, hi1, hu1⟩ => ?_⟩
  have h1 := hu (a, an) (List.mem_flatMap.mpr ⟨i1, hi1, hu1⟩)
  refine ⟨h1.1, fun b bn ⟨i2, hi2, hu2⟩ => ?_⟩
  have h2 := h1.2 (b, bn) (List.mem_flatMap.mpr ⟨i2, hi2, hu2⟩)
  rcases h2 with (h2 | h2) | h2
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

/-- **The checker of a layout** for the program `IR.lower` returns. -/
def irOkB (lp : Prog) (l : Layout) : Bool :=
  match lowerRaw lp with
  | .ok q => layOkB lp q l && slotsOkB l q && lp.globals.all (globalInitB lp)
  | .error _ => false

/-! ## The program `lower` returns -/

/-- The IR's context and initial state, as `Ember.Z80.IR.Sem.run` makes them. -/
def irCtx (lp : Prog) (q : IR.Prog) (l : Layout) : Ctx :=
  { prog := q, layout := l, dropReasons := lp.dropReasons, notes := lp.notes }

def irInit (lp : Prog) (q : IR.Prog) (l : Layout) (inputs : Array Trace.Input) : St :=
  { mem := initMem l q.globals (ByteArray.mk (Array.replicate 65536 0)), world := { inputs, framed := lp.framed } }

theorem lower_rel {lp : Prog} {q' : IR.Prog} (hl : lower lp = .ok q') (l : Layout) (hok : progOkB lp = true)
    (hir : irOkB lp l = true) (inputs : Array Trace.Input) :
    ∃ q, q' = tidyProg q ∧ LayOK lp (irCtx lp q l) ∧ Lowered lp (irCtx lp q l) ∧ q.entry = lp.entry ∧
      (∀ f, f ∈ q.fns → SlotsOK l (BrIn f.body) (DstIn f.body)) ∧
      GS (irCtx lp q l) lp (Lang.Sem.initial lp inputs) (irInit lp q' l inputs) := by
  obtain ⟨q, hraw, rfl⟩ := lower_tidy hl
  unfold irOkB at hir
  simp only [hraw, Bool.and_eq_true, List.all_eq_true] at hir
  obtain ⟨⟨hlay, hslot⟩, hglob⟩ := hir
  obtain ⟨hq, he⟩ := lowerRaw_shape hraw
  have L := layOk_sound hlay hq (irCtx lp q l) rfl rfl
  exact ⟨q, rfl, L, lowered_of_raw hraw _ rfl rfl rfl, he, slotsOkB_sound hslot,
    init_rel hq (fun g hg => globalInitB_sound (hglob g hg)) _ L inputs⟩

/-- **The lowered program, call after call.**  From the initial state,
if `j` calls of the entry function end in Ember, they end in the IR
`lower` returns, with the same events. -/
theorem lower_iter {lp : Prog} {q' : IR.Prog} (hl : lower lp = .ok q') (l : Layout) (hok : progOkB lp = true)
    (hir : irOkB lp l = true) (inputs : Array Trace.Input) (k j : Nat) (st' : Lang.Sem.St)
    (hi : callIter k lp j (Lang.Sem.initial lp inputs) = some st') :
    ∃ m ist', irIter m (irCtx lp q' l) j (irInit lp q' l inputs) = some ist' ∧ ist'.world = st'.world := by
  obtain ⟨q, rfl, L, hlow, he, hslot, hG0⟩ := lower_rel hl l hok hir inputs
  obtain ⟨hPok, fd, hE, hpar⟩ := progOkB_sound hok
  obtain ⟨m, ist', hit, hG'⟩ := iter_sim L hlow hPok he fd hE hpar k j _ st' _ hG0 hi
  obtain ⟨m', hm'⟩ := tidy_iter (c := irCtx lp q l) hlow.uniq
    (fun g f hf => hslot f (List.mem_of_find?_eq_some hf)) j m _ _ hit
  exact ⟨m', ist', hm', hG'.2.1⟩

/-- … and if the next call traps in Ember, it traps in the IR, with the same events. -/
theorem lower_trap {lp : Prog} {q' : IR.Prog} (hl : lower lp = .ok q') (l : Layout) (hok : progOkB lp = true)
    (hir : irOkB lp l = true) (inputs : Array Trace.Input) (k j : Nat) (st1 st2 : Lang.Sem.St)
    (hi : callIter k lp j (Lang.Sem.initial lp inputs) = some st1)
    (ht : Lang.Sem.call k lp st1 lp.entry [] = .trap st2) :
    ∃ m ist1 ist2, irIter m (irCtx lp q' l) j (irInit lp q' l inputs) = some ist1 ∧
      callF m (irCtx lp q' l) q'.entry ist1 = .trap ist2 ∧ ist2.world = st2.world := by
  obtain ⟨q, rfl, L, hlow, he, hslot, hG0⟩ := lower_rel hl l hok hir inputs
  obtain ⟨hPok, fd, hE, hpar⟩ := progOkB_sound hok
  obtain ⟨m, ist1, ist2, hit, htr, hw⟩ := iter_trap L hlow hPok he fd hE hpar k j _ st1 st2 _ hG0 hi ht
  have hu := hlow.uniq
  have hs : ∀ g f, (irCtx lp q l).prog.fn? g = some f → SlotsOK (irCtx lp q l).layout (BrIn f.body) (DstIn f.body) :=
    fun g f hf => hslot f (List.mem_of_find?_eq_some hf)
  obtain ⟨m1, hm1⟩ := tidy_iter hu hs j m _ _ hit
  obtain ⟨m2, hm2⟩ := tidy_ref hu hs m _ ist1 _ htr trivial
  refine ⟨max m1 m2, ist1, ist2, irIter_le (Nat.le_max_left m1 m2) j _ _ hm1, ?_, hw⟩
  have hm2' : callF m2 (irCtx lp (tidyProg q) l) (tidyProg q).entry ist1 = .trap ist2 := hm2
  rw [callF_mono (by rw [hm2']; simp) (Nat.le_max_right m1 m2), hm2']

/-- info: 'Ember.Proof.IRSim.lower_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lower_iter

/-- info: 'Ember.Proof.IRSim.lower_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lower_trap

end Ember.Proof.IRSim
