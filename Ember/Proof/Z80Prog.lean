import Ember.Proof.Z80FnGen

/-!
# Ember.Proof.Z80Prog — the functions of a generated program (plan M7.3)

`Codegen.genProg` generates the functions one after the other, each in
two passes.  `genProg_spec`: every function with code has a run of
`genFnCode` (its second pass) that `jumpsOk` accepted, and the items of
that run are in the program's items at an offset.  `prog_gen`: so, in an
image that holds those items, every function has the `FnGen` that
`fn_ok` asks for — given `FnStatic` of each in the environment its
second pass ran in (`progEnvs`), and in no other.
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

/-- A run of the generator for `f` in the environment of `spilled` and
`live` that `jumpsOk` accepted, with the items `code`. -/
def GenRun (p : IR.Prog) (ann : Bool) (f : IR.Fn) (spilled : Array Bool) (live : Option (Array Bool))
    (code : Array Item) : Prop :=
  ∃ lits st,
    genFnCode f (f.name == p.entry) ann (genEnv f spilled live) (genStart f lits) = .ok ((), st) ∧
      jumpsOk st = true ∧ st.out = code

/-- The environments the functions with code are generated in (their
second pass): the temporaries the first pass saw read from their slot,
and where it saw reads of the frame start.  It follows `Codegen.genFns`. -/
def envFns (p : IR.Prog) (ann : Bool) :
    List IR.Fn → Array (Nat × Nat) → Except String (List (IR.Fn × Array Bool × Option (Array Bool)))
  | [], _ => .ok []
  | f :: r, lits =>
    if f.dead then envFns p ann r lits
    else
      match genFn f (Array.replicate f.tmps.size true) lits with
      | .error e => .error e
      | .ok (_, missed, _, _, live) =>
        match genFn f missed lits (f.name == p.entry) live ann with
        | .error e => .error e
        | .ok (_, _, lits2, _, _) =>
          match envFns p ann r lits2 with
          | .error e => .error e
          | .ok es => .ok ((f, missed, live) :: es)

def progEnvs (p : IR.Prog) (ann : Bool := false) : Except String (List (IR.Fn × Array Bool × Option (Array Bool))) :=
  envFns p ann p.fns #[]

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

/-- The two passes of `genOne`. -/
theorem genOne_inv {p : IR.Prog} {ann : Bool} {f : IR.Fn} {lits : Array (Nat × Nat)}
    {r : Array Item × Array (Nat × Nat) × Nat} (h : genOne p ann f lits = .ok r) :
    ∃ c1 missed l1 s1 live missed2 lv2,
      genFn f (Array.replicate f.tmps.size true) lits = .ok (c1, missed, l1, s1, live) ∧
      genFn f missed lits (f.name == p.entry) live ann = .ok (r.1, missed2, r.2.1, r.2.2, lv2) := by
  unfold genOne at h
  split at h
  · cases h
  · rename_i c1 missed l1 s1 live h1
    split at h
    · cases h
    · rename_i code missed2 lits2 size lv2 h2
      split at h
      · cases h
      · cases h
        exact ⟨c1, missed, l1, s1, live, missed2, lv2, h1, h2⟩

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

/-- **The functions of the program**, in its items, each generated in its environment. -/
theorem genFns_spec (p : IR.Prog) (ann : Bool) :
    ∀ (fs : List IR.Fn) (acc acc' : Array Item × Array (String × Nat) × Array (Nat × Nat)),
      genFns p ann fs acc = .ok acc' →
      acc.1.toList <+: acc'.1.toList ∧
        ∃ envs, envFns p ann fs acc.2.2 = .ok envs ∧
        ∀ f, f ∈ fs → f.dead = false →
          ∃ (base : Nat) (code : Array Item) (sp : Array Bool) (lv : Option (Array Bool)),
            (f, sp, lv) ∈ envs ∧ GenRun p ann f sp lv code ∧
              ∀ (j : Nat) it, code[j]? = some it → acc'.1[base + j]? = some it
  | [], acc, acc', h => by
    cases h
    exact ⟨List.prefix_refl _, [], rfl, fun f hf => by cases hf⟩
  | f :: r, (items, frames, lits), acc', h => by
    rw [genFns] at h
    by_cases hd : f.dead = true
    · rw [if_pos hd] at h
      obtain ⟨hp, envs, he, hall⟩ := genFns_spec p ann r _ acc' h
      refine ⟨hp, envs, by rw [envFns, if_pos hd]; exact he, fun g hg hgd => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg'
      · rw [hd] at hgd; cases hgd
      · exact hall g hg' hgd
    · rw [if_neg hd] at h
      cases hone : genOne p ann f lits with
      | error e => rw [hone] at h; cases h
      | ok q =>
        obtain ⟨code, lits2, size⟩ := q
        rw [hone] at h
        obtain ⟨hp, envs, he, hall⟩ := genFns_spec p ann r _ acc' h
        obtain ⟨c1, missed, l1, s1, live, missed2, lv2, h1, h2⟩ := genOne_inv hone
        have hp1 : (items ++ code).toList <+: acc'.1.toList := hp
        have he' : envFns p ann (f :: r) lits = .ok ((f, missed, live) :: envs) := by
          rw [envFns, if_neg hd]
          simp only [h1, h2]
          have he2 : envFns p ann r lits2 = .ok envs := he
          rw [he2]
        refine ⟨(by simp : items.toList <+: (items ++ code).toList).trans hp1, _, he', fun g hg hgd => ?_⟩
        rcases List.mem_cons.mp hg with rfl | hg'
        · obtain ⟨st, hst, hj, ho⟩ := genFn_run h2
          refine ⟨items.size, code, missed, live, List.mem_cons_self, ⟨lits, st, hst, hj, ho⟩, fun j it hj => ?_⟩
          refine getElem?_of_prefix hp1 ?_
          rw [Array.getElem?_append_right (by omega)]
          simpa using hj
        · obtain ⟨base, code', sp, lv, hm, hrun, hat⟩ := hall g hg' hgd
          exact ⟨base, code', sp, lv, List.mem_cons_of_mem _ hm, hrun, hat⟩

theorem genProg_spec {p : IR.Prog} {ann : Bool} {c : Compiled} (h : genProg p ann = .ok c) :
    ∃ envs, progEnvs p ann = .ok envs ∧
    ∀ f, f ∈ p.fns → f.dead = false →
      ∃ (base : Nat) (code : Array Item) (sp : Array Bool) (lv : Option (Array Bool)),
        (f, sp, lv) ∈ envs ∧ GenRun p ann f sp lv code ∧
          ∀ (j : Nat) it, code[j]? = some it → c.items[base + j]? = some it := by
  unfold genProg at h
  cases hf : genFns p ann p.fns (#[], #[], #[]) with
  | error e => rw [hf] at h; cases h
  | ok q =>
    obtain ⟨items, frames, lits⟩ := q
    rw [hf] at h
    cases h
    obtain ⟨_, envs, he, hall⟩ := genFns_spec p ann p.fns _ _ hf
    refine ⟨envs, he, fun f hfm hd => ?_⟩
    obtain ⟨base, code, sp, lv, hm, hrun, hat⟩ := hall f hfm hd
    exact ⟨base, code, sp, lv, hm, hrun, fun j it hj => by simpa using hat j it hj⟩

/-- **Every function of a generated program has its `FnGen`**, in an
image that holds the program's items from `off` on. -/
theorem prog_gen {Z : ZCtx} (ok : Z.OK) (hrt : RtOK Z) {ann : Bool} {c : Compiled}
    (hgen : genProg Z.c.prog ann = .ok c) {off : Nat}
    (hitems : ∀ j it, c.items[j]? = some it → Z.items[off + j]? = some it)
    {envs : List (IR.Fn × Array Bool × Option (Array Bool))} (henvs : progEnvs Z.c.prog ann = .ok envs)
    (hstatic : ∀ e, e ∈ envs → FnStatic Z (genEnv e.1 e.2.1 e.2.2)) :
    ∀ g gf, Z.c.prog.fn? g = some gf → gf.dead = false → ∃ G : FnGen, G.OK Z gf := by
  intro g gf hgf hd
  have hmem : gf ∈ Z.c.prog.fns := List.mem_of_find?_eq_some hgf
  obtain ⟨envs', he', hall⟩ := genProg_spec hgen
  rw [henvs] at he'
  cases he'
  obtain ⟨base, code, spilled, live, hm, ⟨lits, st, hrun, hj, ho⟩, hat⟩ := hall gf hmem hd
  have F : GFinal Z (off + base) st := ⟨fun j it h => by
    rw [Nat.add_assoc]
    exact hitems _ it (hat j it (by rw [← ho]; exact h))⟩
  have h := genFn_ok (E := genEnv gf spilled live) ok hrt (hstatic _ hm) F hj
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
    {envs : List (IR.Fn × Array Bool × Option (Array Bool))} (henvs : progEnvs Z.c.prog ann = .ok envs)
    (hstatic : ∀ e, e ∈ envs → FnStatic Z (genEnv e.1 e.2.1 e.2.2)) :
    ∀ k g st1, Callee Z g st1 (IR.Sem.callF k Z.c g st1) :=
  fn_ok ok (prog_gen ok hrt hgen hitems henvs hstatic)

/-- info: 'Ember.Proof.Z80Gen.prog_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_ok

end Ember.Proof.Z80Gen
