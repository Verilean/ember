import Ember.Proof.Z80Image

/-!
# Ember.Proof.Z80ImageParts — an image checked in parts (plan M7.3)

`ImgIn.check` asks the kernel to run the generator over a whole program
in one evaluation; for the stack that does not end (the kernel keeps
the generator's states as unevaluated terms: tens of gigabytes).  Here
the same facts are taken function by function.

`FnPart`: what the generator gives for one function — the temporaries
its first pass saw read from their slot, where it saw reads of the
frame start, the items, the literals so far, the bytes of temporaries.
`pass1B`/`pass2B` run one pass of `genFn` on one function and compare
(a theorem for each, by the kernel); `Gens` chains them along the
program, and gives `progEnvs` and `genProg` of it (`Gens.envs`,
`Gens.prog`).

`ImgIn.ok_partsOn`: with `Gens`, `okB` of the plan, `fnStaticB` of each
function and what `PartsOn` asks of the image the items assemble to
(labels, the literal pool, the symbols, the generated items in place,
the size), the conclusion of `ImgIn.ok`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

structure FnPart where
  f : IR.Fn
  /-- Temporaries the first pass saw read from their slot. -/
  missed : Array Bool
  /-- Where reads of the frame start (with the bytes other frames share). -/
  live : Option (Array Bool)
  code : List Item
  /-- The literals after the function. -/
  lits : Array (Nat × Nat)
  /-- Bytes of the slots of its temporaries. -/
  size : Nat

/-- The first pass of `g.f`, from the literals `lits`. -/
def pass1B (p : IR.Prog) (lits : Array (Nat × Nat)) (g : FnPart) : Bool :=
  match genFn g.f (Array.replicate g.f.tmps.size true) lits with
  | .error _ => false
  | .ok r => decide (r.2.1 = g.missed) && decide (keepShared (sharedBytes p g.f.name) r.2.2.2.2 = g.live)

/-- The second pass. -/
def pass2B (p : IR.Prog) (lits : Array (Nat × Nat)) (g : FnPart) : Bool :=
  !g.f.dead &&
  match genFn g.f g.missed lits (g.f.name == p.entry) g.live false with
  | .error _ => false
  | .ok r => decide (r.1.toList = g.code) && decide (r.2.2.1 = g.lits) && decide (r.2.2.2.1 = g.size) &&
      ((List.range g.f.tmps.size).find? fun t => r.2.1[t]! && !g.missed[t]!).isNone

section
variable {p : IR.Prog} {lits : Array (Nat × Nat)} {g : FnPart}

theorem genOne_of (h1 : pass1B p lits g = true) (h2 : pass2B p lits g = true) :
    g.f.dead = false ∧ ∃ code : Array Item, code.toList = g.code ∧
      genOne p false (sharedBytes p) g.f lits = .ok (code, g.lits, g.size) := by
  unfold pass1B at h1
  unfold pass2B at h2
  cases hg1 : genFn g.f (Array.replicate g.f.tmps.size true) lits with
  | error e => rw [hg1] at h1; cases h1
  | ok r1 =>
    obtain ⟨c1, m1, l1, s1, lv1⟩ := r1
    rw [hg1] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨e1, e2⟩ := h1
    cases hg2 : genFn g.f g.missed lits (g.f.name == p.entry) g.live false with
    | error e => rw [hg2] at h2; simp at h2
    | ok r2 =>
      obtain ⟨c2, m2, l2, s2, lv2⟩ := r2
      rw [hg2] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at h2
      obtain ⟨hd, ⟨⟨⟨e3, e4⟩, e5⟩, e6⟩⟩ := h2
      refine ⟨hd, c2, e3, ?_⟩
      unfold genOne
      simp only [hg1]
      rw [e1, e2, hg2]
      simp only [e6, e4, e5]

theorem envFns_cons_of (h1 : pass1B p lits g = true) (h2 : pass2B p lits g = true) (r : List IR.Fn) :
    envFns p false (sharedBytes p) (g.f :: r) lits =
      match envFns p false (sharedBytes p) r g.lits with
      | .error e => .error e
      | .ok es => .ok ((g.f, g.missed, g.live) :: es) := by
  unfold pass1B at h1
  unfold pass2B at h2
  cases hg1 : genFn g.f (Array.replicate g.f.tmps.size true) lits with
  | error e => rw [hg1] at h1; cases h1
  | ok r1 =>
    obtain ⟨c1, m1, l1, s1, lv1⟩ := r1
    rw [hg1] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨e1, e2⟩ := h1
    cases hg2 : genFn g.f g.missed lits (g.f.name == p.entry) g.live false with
    | error e => rw [hg2] at h2; simp at h2
    | ok r2 =>
      obtain ⟨c2, m2, l2, s2, lv2⟩ := r2
      rw [hg2] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at h2
      obtain ⟨hd, ⟨⟨⟨e3, e4⟩, e5⟩, e6⟩⟩ := h2
      rw [envFns]
      simp only [hd, Bool.false_eq_true, if_false, hg1]
      rw [e1, e2, hg2]
      simp only [e4]
      cases envFns p false (sharedBytes p) r g.lits <;> rfl

end

/-- The functions `gs`, generated one after the other from the literals `l`. -/
inductive Gens (p : IR.Prog) : Array (Nat × Nat) → List FnPart → Prop
  | nil (l : Array (Nat × Nat)) : Gens p l []
  | cons {l : Array (Nat × Nat)} {g : FnPart} {gs : List FnPart} :
      pass1B p l g = true → pass2B p l g = true → Gens p g.lits gs → Gens p l (g :: gs)

/-- The environments of the functions. -/
def envsOf (gs : List FnPart) : List (IR.Fn × Array Bool × Option (Array Bool)) :=
  gs.map fun g => (g.f, g.missed, g.live)

theorem Gens.envs {p : IR.Prog} {l : Array (Nat × Nat)} {gs : List FnPart} (h : Gens p l gs) :
    envFns p false (sharedBytes p) (gs.map (·.f)) l = .ok (envsOf gs) := by
  induction h with
  | nil l => rfl
  | cons h1 h2 _ ih =>
    rw [List.map_cons, envFns_cons_of h1 h2, ih]
    rfl

theorem Gens.gen {p : IR.Prog} {l : Array (Nat × Nat)} {gs : List FnPart} (h : Gens p l gs) :
    ∀ (items : Array Item) (frames : Array (String × Nat)), ∃ its fr l',
      genFns p false (sharedBytes p) (gs.map (·.f)) (items, frames, l) = .ok (its, fr, l') ∧
      its.toList = items.toList ++ gs.flatMap (·.code) := by
  induction h with
  | nil l => exact fun items frames => ⟨items, frames, l, rfl, by simp⟩
  | @cons l0 g gs0 h1 h2 _ ih =>
    intro items frames
    obtain ⟨hd, code, hc, hone⟩ := genOne_of h1 h2
    obtain ⟨its, fr, l', hgen, hits⟩ := ih (items ++ code) (frames.push (g.f.name, g.size))
    refine ⟨its, fr, l', ?_, ?_⟩
    · rw [List.map_cons, genFns]
      simp only [hd, Bool.false_eq_true, if_false, hone]
      exact hgen
    · rw [hits, List.flatMap_cons, Array.toList_append, hc, List.append_assoc]

/-- `progEnvs` and `genProg` of a program whose functions are `gs`. -/
theorem Gens.prog {p : IR.Prog} {gs : List FnPart} (h : Gens p #[] gs) (hfns : p.fns = gs.map (·.f)) :
    progEnvs p false (sharedBytes p) = .ok (envsOf gs) ∧
    ∃ c, genProg p false (sharedBytes p) = .ok c ∧ c.items = gs.flatMap (·.code) := by
  refine ⟨by unfold progEnvs; rw [hfns]; exact h.envs, ?_⟩
  obtain ⟨its, fr, l', hgen, hits⟩ := h.gen #[] #[]
  refine ⟨{ items := its.toList, tmps := fr.toList, lits := l' }, ?_, by simpa using hits⟩
  unfold genProg
  rw [hfns, hgen]

namespace ImgIn

/-- The plan of an image whose functions are generated as `gs` say: the
plan of their environments (so the kernel need not run the generator
over the program to know it). -/
theorem plan_parts (I : ImgIn) (gs : List FnPart) (hfns : I.ir.fns = gs.map (·.f)) (hgen : Gens I.ir #[] gs) :
    I.plan = mkPlan (I.planIn (envsOf gs)) := by
  have henvs : I.envs = envsOf gs := by unfold envs; rw [(hgen.prog hfns).1]
  unfold plan
  rw [henvs]

/-- What is computed of the image `a` the items assemble to, the
functions being `gs`: each a check of its own, so that the kernel takes
them one declaration at a time (in one evaluation it keeps what each
computes: the labels looked up by name are most of it). -/
structure PartsOn (I : ImgIn) (gs : List FnPart) (a : Assembled) : Prop where
  asm : assemble I.items = .ok a
  labels : ((mkPlan (I.planIn (envsOf gs))).labels.all fun l => I.items.any (isLab l)) = true
  lits : (mkPlan (I.planIn (envsOf gs))).lits.all (litB a I.ramStart) = true
  globals : (I.layout.globals.all fun e => a.labels.reverse.lookup (areaSym (.global e.1)) == some e.2) = true
  frames : (I.layout.frames.all fun e => a.labels.reverse.lookup (areaSym (.frame e.1)) == some e.2) = true
  code : decide ((I.items.drop I.genOff).take (gs.flatMap (·.code)).length = gs.flatMap (·.code)) = true
  acc : (I.items.all noAcc || a.labels.reverse.lookup "rt_acc" == some I.acc) = true
  size : decide (a.bytes.size < 65536) = true

/-- **An image checked in parts.** -/
theorem ok_partsOn (I : ImgIn) (gs : List FnPart) (a : Assembled) (hfns : I.ir.fns = gs.map (·.f))
    (hgen : Gens I.ir #[] gs)
    (hplan : okB (mkPlan (I.planIn (envsOf gs))) = true)
    (hstat : ∀ g, g ∈ gs → fnStaticB (mkPlan (I.planIn (envsOf gs))) (genEnv g.f g.missed g.live) = true)
    (h : PartsOn I gs a) :
    ∃ (a : Assembled) (addrs : List Nat), assemble I.items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ (W : Type) (bus : W → UInt16 → UInt8) (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop),
        (∀ w, dev w .none = w) →
        (I.plan.toZ (I.around a addrs W bus dev wrel)).OK ∧
        (RtOK (I.plan.toZ (I.around a addrs W bus dev wrel)) →
          ∀ k g st1, Callee (I.plan.toZ (I.around a addrs W bus dev wrel)) g st1 (IR.Sem.callF k I.ctx g st1)) := by
  obtain ⟨he, c, hg, hc⟩ := hgen.prog hfns
  obtain ⟨ha, hlab, hlits, hglob, hfr, hsub, hacc, hsize⟩ := h
  simp only [List.all_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hlab hlits hglob hfr hsub hacc hsize
  obtain ⟨addrs, hpl⟩ := placed_of_assemble ha
  refine ⟨a, addrs, ha, hsize, fun W bus dev wrel quiet => ?_⟩
  rw [I.plan_parts gs hfns hgen]
  have hpc : planCheck (I.planIn (envsOf gs)) = true := by
    unfold planCheck
    rw [hplan, Bool.true_and, List.all_eq_true]
    intro e hemem
    obtain ⟨g, hgm, rfl⟩ := List.mem_map.mp hemem
    exact hstat g hgm
  have hok : ((mkPlan (I.planIn (envsOf gs))).toZ (I.around a addrs W bus dev wrel)).OK := by
    refine plan_ok (planCheck_ok hpc) _ hpl quiet (fun ar ad har => ?_) (fun href => ?_)
    · cases ar with
      | global g => exact hglob (g, ad) (lookup_mem har)
      | frame f => exact hfr (f, ad) (lookup_mem har)
    · rcases hacc with hacc | hacc
      · obtain ⟨k, i, off, hk, hi⟩ := href
        have := hacc _ (List.mem_of_getElem? hk)
        simp [noAcc, hi] at this
      · exact hacc
  refine ⟨hok, fun hrt => ?_⟩
  have hitems : ∀ (j : Nat) it, c.items[j]? = some it → I.items[I.genOff + j]? = some it := by
    intro j it hj
    rw [hc] at hj
    have hlt : j < (gs.flatMap (·.code)).length := by
      rcases Nat.lt_or_ge j (gs.flatMap (·.code)).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hj; cases hj
    rw [← hsub, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
    exact hj
  have hram : (mkPlan (I.planIn (envsOf gs))).ramStart = I.ramStart := rfl
  have hLits : Lits (mkPlan (I.planIn (envsOf gs))) (I.around a addrs W bus dev wrel) := by
    intro n v hv
    have h1 : litB a I.ramStart (n, v) = true := hlits (n, v) hv
    exact litB_sound (mkPlan (I.planIn (envsOf gs))) (I.around a addrs W bus dev wrel) hram n v h1
  exact prog_ok (Z := (mkPlan (I.planIn (envsOf gs))).toZ (I.around a addrs W bus dev wrel)) hok hrt (ann := false)
    hg hitems he (planCheck_static hpc _ (fun l hl => mem_label (hlab l hl)) hLits)

end ImgIn

end Ember.Proof.Z80Gen
