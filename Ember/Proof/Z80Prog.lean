import Ember.Proof.Z80FnGen

/-!
# Ember.Proof.Z80Prog — the functions of a generated program (plan M7.3)

`Codegen.genProg` generates the functions one after the other, each in
two passes.  `genProg_spec`: every function with code has a run of
`genFnCode` (its second pass) that `jumpsOk` accepted, and the items of
that run are in the program's items at an offset.  `prog_gen`: so, in an
image that holds those items, every function has the `FnGen` that
`fn_ok` asks for — given `FnStatic` of each.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The environment of a function's generation. -/
def genEnv (f : IR.Fn) (spilled : Array Bool) (live : Option (Array Bool)) : GEnv :=
  { fn := f, spilled, tmpOff := (tmpLayout f spilled).1, live }

/-- The state a function's generation starts in. -/
def genStart (f : IR.Fn) (lits : Array (Nat × Nat)) : GS :=
  { missed := Array.replicate f.tmps.size false, lits, reads := Array.replicate f.frame false }

/-- A run of the generator for `f` that `jumpsOk` accepted, with the items `code`. -/
def GenRun (p : IR.Prog) (ann : Bool) (f : IR.Fn) (code : Array Item) : Prop :=
  ∃ spilled live lits st,
    genFnCode f (f.name == p.entry) ann (genEnv f spilled live) (genStart f lits) = .ok ((), st) ∧
      jumpsOk st = true ∧ st.out = code

theorem genFn_run {f : IR.Fn} {spilled : Array Bool} {lits : Array (Nat × Nat)} {isEntry : Bool}
    {live : Option (Array Bool)} {ann : Bool} {r : Array Item × Array Bool × Array (Nat × Nat) × Nat × Option (Array Bool)}
    (h : genFn f spilled lits isEntry live ann = .ok r) :
    ∃ st, genFnCode f isEntry ann (genEnv f spilled live) (genStart f lits) = .ok ((), st) ∧
      jumpsOk st = true ∧ st.out = r.1 := by
  unfold genFn at h
  have hrun : ((genFnCode f isEntry ann).run { fn := f, spilled, tmpOff := (tmpLayout f spilled).1, live }).run
      { missed := Array.replicate f.tmps.size false, lits, reads := Array.replicate f.frame false } =
      genFnCode f isEntry ann (genEnv f spilled live) (genStart f lits) := rfl
  rw [hrun] at h
  cases hm : genFnCode f isEntry ann (genEnv f spilled live) (genStart f lits) with
  | error e => rw [hm] at h; cases h
  | ok q =>
    obtain ⟨⟨⟩, st⟩ := q
    rw [hm] at h
    by_cases hj : jumpsOk st = true
    · simp only [hj, if_true] at h
      cases h
      exact ⟨st, rfl, hj, rfl⟩
    · simp only [hj, Bool.false_eq_true, if_false] at h
      cases h

theorem genOne_run {p : IR.Prog} {ann : Bool} {f : IR.Fn} {lits : Array (Nat × Nat)}
    {r : Array Item × Array (Nat × Nat) × Nat} (h : genOne p ann f lits = .ok r) : GenRun p ann f r.1 := by
  unfold genOne at h
  split at h
  · cases h
  · rename_i missed _ _ live _
    split at h
    · cases h
    · rename_i code missed2 lits2 size _ h2
      split at h
      · cases h
      · cases h
        obtain ⟨st, hst, hj, ho⟩ := genFn_run h2
        exact ⟨missed, live, lits, st, hst, hj, ho⟩

theorem getElem?_of_prefix {α : Type} {a b : Array α} (h : a.toList <+: b.toList) {j : Nat} {x : α}
    (hj : a[j]? = some x) : b[j]? = some x := by
  obtain ⟨t, ht⟩ := h
  have hlt : j < a.size := by
    rcases Nat.lt_or_ge j a.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hj; cases hj
  have : b.toList[j]? = some x := by
    rw [← ht, List.getElem?_append_left (by simpa using hlt)]
    simpa using hj
  simpa using this

/-- **The functions of the program**, in its items. -/
theorem genFns_spec (p : IR.Prog) (ann : Bool) :
    ∀ (fs : List IR.Fn) (acc acc' : Array Item × Array (String × Nat) × Array (Nat × Nat)),
      genFns p ann fs acc = .ok acc' →
      acc.1.toList <+: acc'.1.toList ∧
        ∀ f, f ∈ fs → f.dead = false →
          ∃ (base : Nat) (code : Array Item), GenRun p ann f code ∧ ∀ (j : Nat) it, code[j]? = some it → acc'.1[base + j]? = some it
  | [], acc, acc', h => by
    cases h
    exact ⟨List.prefix_refl _, fun f hf => by cases hf⟩
  | f :: r, (items, frames, lits), acc', h => by
    rw [genFns] at h
    by_cases hd : f.dead = true
    · rw [if_pos hd] at h
      obtain ⟨hp, hall⟩ := genFns_spec p ann r _ acc' h
      refine ⟨hp, fun g hg hgd => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg'
      · rw [hd] at hgd; cases hgd
      · exact hall g hg' hgd
    · rw [if_neg hd] at h
      cases hone : genOne p ann f lits with
      | error e => rw [hone] at h; cases h
      | ok q =>
        obtain ⟨code, lits2, size⟩ := q
        rw [hone] at h
        obtain ⟨hp, hall⟩ := genFns_spec p ann r _ acc' h
        have hp1 : (items ++ code).toList <+: acc'.1.toList := hp
        refine ⟨(by simp : items.toList <+: (items ++ code).toList).trans hp1, fun g hg hgd => ?_⟩
        rcases List.mem_cons.mp hg with rfl | hg'
        · refine ⟨items.size, code, genOne_run hone, fun j it hj => ?_⟩
          refine getElem?_of_prefix hp1 ?_
          rw [Array.getElem?_append_right (by omega)]
          simpa using hj
        · exact hall g hg' hgd

theorem genProg_spec {p : IR.Prog} {ann : Bool} {c : Compiled} (h : genProg p ann = .ok c) :
    ∀ f, f ∈ p.fns → f.dead = false →
      ∃ (base : Nat) (code : Array Item), GenRun p ann f code ∧ ∀ (j : Nat) it, code[j]? = some it → c.items[base + j]? = some it := by
  unfold genProg at h
  cases hf : genFns p ann p.fns (#[], #[], #[]) with
  | error e => rw [hf] at h; cases h
  | ok q =>
    obtain ⟨items, frames, lits⟩ := q
    rw [hf] at h
    cases h
    intro f hfm hd
    obtain ⟨base, code, hrun, hat⟩ := (genFns_spec p ann p.fns _ _ hf).2 f hfm hd
    exact ⟨base, code, hrun, fun j it hj => by simpa using hat j it hj⟩

/-- **Every function of a generated program has its `FnGen`**, in an
image that holds the program's items from `off` on. -/
theorem prog_gen {Z : ZCtx} (ok : Z.OK) (hrt : RtOK Z) {ann : Bool} {c : Compiled}
    (hgen : genProg Z.c.prog ann = .ok c) {off : Nat}
    (hitems : ∀ j it, c.items[j]? = some it → Z.items[off + j]? = some it)
    (hstatic : ∀ f, f ∈ Z.c.prog.fns → ∀ spilled live, FnStatic Z (genEnv f spilled live)) :
    ∀ g gf, Z.c.prog.fn? g = some gf → gf.dead = false → ∃ G : FnGen, G.OK Z gf := by
  intro g gf hgf hd
  have hmem : gf ∈ Z.c.prog.fns := List.mem_of_find?_eq_some hgf
  obtain ⟨base, code, ⟨spilled, live, lits, st, hrun, hj, ho⟩, hat⟩ := genProg_spec hgen gf hmem hd
  have F : GFinal Z (off + base) st := ⟨fun j it h => by
    rw [Nat.add_assoc]
    exact hitems _ it (hat j it (by rw [← ho]; exact h))⟩
  have h := genFn_ok (E := genEnv gf spilled live) ok hrt (hstatic gf hmem spilled live) F hj
    (gf.name == Z.c.prog.entry) ann (genStart gf lits) rfl rfl
  have hfn : (genEnv gf spilled live).fn = gf := rfl
  rw [hfn] at h
  unfold wpg at h
  rw [hrun] at h
  exact h rfl

/-- **The functions of a generated program do what the IR's functions
do**: in an image that holds the items `genProg` gives, a function
entered as `Entry` says returns as `IR.Sem.callF` does — the machine
standing for the world it leaves — or gets to `rt_trap`. -/
theorem prog_ok {Z : ZCtx} (ok : Z.OK) (hrt : RtOK Z) {ann : Bool} {c : Compiled}
    (hgen : genProg Z.c.prog ann = .ok c) {off : Nat}
    (hitems : ∀ j it, c.items[j]? = some it → Z.items[off + j]? = some it)
    (hstatic : ∀ f, f ∈ Z.c.prog.fns → ∀ spilled live, FnStatic Z (genEnv f spilled live)) :
    ∀ k g st1, Callee Z g st1 (IR.Sem.callF k Z.c g st1) :=
  fn_ok ok (prog_gen ok hrt hgen hitems hstatic)

/-- info: 'Ember.Proof.Z80Gen.prog_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_ok

end Ember.Proof.Z80Gen
