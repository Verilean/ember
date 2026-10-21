import Ember.Proof.Z80ImageParts
import Ember.Proof.Z80AsmChunks

/-!
# Ember.Proof.Z80GenChunks — one pass of the generator, a stretch of instructions at a time (plan M7.3)

`pass1B`/`pass2B` ask the kernel to run `genFn` over a whole function
in one evaluation; for the largest function of the stack (170
instructions) that takes about 11 GB, the kernel keeping what it
computed until the end.  Here a pass is cut into stretches: the state
of the generator at each cut is written out (`GS`), and the kernel
checks each stretch from the state before it to the state after it, a
theorem each (`runG … = .ok ((), s')`).  `genBody_append`: the body of a
function is generated stretch after stretch; `genFn_of`: from the
stretches, what `genFn` returns.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Codegen Ember.Z80.Asm

instance : DecidableEq Regs := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.hl = y.hl ∧ x.acc = y.acc) (by
    obtain ⟨a, h, c⟩ := x
    obtain ⟨a', h', c'⟩ := y
    simp)

instance : DecidableEq GS := fun x y =>
  decidable_of_iff (x.out = y.out ∧ x.regs = y.regs ∧ x.missed = y.missed ∧ x.lits = y.lits ∧
      x.labels = y.labels ∧ x.atLabel = y.atLabel ∧ x.dead = y.dead ∧ x.reads = y.reads ∧
      x.addrTaken = y.addrTaken ∧ x.jumps = y.jumps ∧ x.labelRegs = y.labelRegs) (by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := x
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := y
    simp)

/-- A generator run from a state. -/
def runG {α : Type} (m : GM α) (env : GEnv) (s : GS) : Except String (α × GS) := (m.run env).run s

theorem runG_bind {α β : Type} (m : GM α) (k : α → GM β) (env : GEnv) (s : GS) :
    runG (m >>= k) env s = match runG m env s with
      | .ok (a, s') => runG (k a) env s'
      | .error e => .error e := by
  unfold runG
  simp only [ReaderT.run_bind, StateT.run_bind]
  cases (m.run env).run s <;> rfl

theorem genBody_append (f : IR.Fn) (ann : Bool) : ∀ (k : Nat) (a b : List IR.Instr),
    genBody f ann k (a ++ b) = (genBody f ann k a >>= fun _ => genBody f ann (k + a.length) b)
  | k, [], b => by simp [genBody]
  | k, i :: r, b => by
    simp only [List.cons_append, genBody, List.length_cons]
    rw [genBody_append f ann (k + 1) r b, show k + 1 + r.length = k + (r.length + 1) by omega]
    cases ann <;> simp only [Bool.false_eq_true, if_false, if_true, bind_assoc]

/-- A stretch of `n` instructions from the `k`-th, then the rest. -/
theorem body_step (f : IR.Fn) (ann : Bool) (env : GEnv) (l : List IR.Instr) (k n : Nat) (s t u : GS)
    (hk : k + n ≤ l.length)
    (h1 : runG (genBody f ann k ((l.drop k).take n)) env s = .ok ((), t))
    (h2 : runG (genBody f ann (k + n) (l.drop (k + n))) env t = .ok ((), u)) :
    runG (genBody f ann k (l.drop k)) env s = .ok ((), u) := by
  rw [← List.take_append_drop n (l.drop k), genBody_append, runG_bind, h1]
  have hl : ((l.drop k).take n).length = n := by simp; omega
  simp only [hl, List.drop_drop]
  exact h2

theorem body_end (f : IR.Fn) (ann : Bool) (env : GEnv) (l : List IR.Instr) (k : Nat) (s : GS)
    (hk : l.length ≤ k) : runG (genBody f ann k (l.drop k)) env s = .ok ((), s) := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

/-- What a function's code does before its body: the labels, the register parameter stored. -/
def genPre (f : IR.Fn) (isEntry : Bool) : GM Unit := do
  if isEntry then modify fun s => { s with out := s.out.push (.label "f_entry") }
  modify fun s => { s with out := s.out.push (.label (fnLabel f.name)) }
  match f.regParam with
  | some (n, sl) => store n (.slot sl)
  | none => pure ()

theorem genFnCode_pre (f : IR.Fn) (isEntry ann : Bool) :
    genFnCode f isEntry ann = (genPre f isEntry >>= fun _ => genBody f ann 0 f.body.toList) := by
  unfold genFnCode genPre
  cases isEntry <;> cases f.regParam <;> simp only [Bool.false_eq_true, if_false, if_true, bind_assoc, pure_bind]

/-- The environment `genFn` generates a function in. -/
def fnEnv (f : IR.Fn) (spilled : Array Bool) (live : Option (Array Bool)) : GEnv :=
  { fn := f, spilled, tmpOff := (tmpLayout f spilled).1, live }

/-- The state `genFn` starts from. -/
def fnStart (f : IR.Fn) (lits : Array (Nat × Nat)) : GS :=
  { missed := Array.replicate f.tmps.size false, lits, reads := Array.replicate f.frame false }

/-- **A pass of the generator, from its stretches.** -/
theorem genFn_of (f : IR.Fn) (spilled : Array Bool) (lits : Array (Nat × Nat)) (isEntry : Bool)
    (live : Option (Array Bool)) (ann : Bool) (s0 s : GS)
    (hpre : runG (genPre f isEntry) (fnEnv f spilled live) (fnStart f lits) = .ok ((), s0))
    (hbody : runG (genBody f ann 0 (f.body.toList.drop 0)) (fnEnv f spilled live) s0 = .ok ((), s))
    (hj : jumpsOk s = true) :
    genFn f spilled lits isEntry live ann =
      .ok (s.out, s.missed, s.lits, (tmpLayout f spilled).2, if s.addrTaken then none else some s.reads) := by
  have h : runG (genFnCode f isEntry ann) (fnEnv f spilled live) (fnStart f lits) = .ok ((), s) := by
    rw [genFnCode_pre, runG_bind, hpre]
    simpa using hbody
  unfold genFn
  have h' : ((genFnCode f isEntry ann).run (fnEnv f spilled live)).run (fnStart f lits) = .ok ((), s) := h
  unfold fnEnv fnStart at h'
  rw [h']
  simp [hj]

/-- `pass1B` from what the pass gives. -/
theorem pass1B_of {p : IR.Prog} {lits : Array (Nat × Nat)} {g : FnPart}
    {r : Array Item × Array Bool × Array (Nat × Nat) × Nat × Option (Array Bool)}
    (h : genFn g.f (Array.replicate g.f.tmps.size true) lits = .ok r)
    (hc : (decide (r.2.1 = g.missed) && decide (keepShared (sharedBytes p g.f.name) r.2.2.2.2 = g.live)) = true) :
    pass1B p lits g = true := by
  unfold pass1B
  rw [h]
  exact hc

/-- `pass2B` from what the pass gives. -/
theorem pass2B_of {p : IR.Prog} {lits : Array (Nat × Nat)} {g : FnPart}
    {r : Array Item × Array Bool × Array (Nat × Nat) × Nat × Option (Array Bool)}
    (hd : g.f.dead = false) (h : genFn g.f g.missed lits (g.f.name == p.entry) g.live false = .ok r)
    (hc : (decide (r.1.toList = g.code) && decide (r.2.2.1 = g.lits) && decide (r.2.2.2.1 = g.size) &&
      ((List.range g.f.tmps.size).find? fun t => r.2.1[t]! && !g.missed[t]!).isNone) = true) :
    pass2B p lits g = true := by
  unfold pass2B
  rw [hd, h]
  exact hc

/-- `sharedBytes`, from the frames of the layout it computes. -/
def sharedOf (p : IR.Prog) (frames : List (String × Nat)) : String → Nat → Bool :=
  let frameSize (f : String) : Nat := ((p.fn? f).map (·.frame)).getD 0
  fun f k =>
    match frames.lookup f with
    | none => true
    | some a => frames.any fun (g, b) => g != f && decide (b ≤ a + k) && decide (a + k < b + frameSize g)

/-- With the frames of its layout known, `sharedBytes` of a program is
`sharedOf` of them: the kernel computes the layout once (`sharedBytes`
keeps it in a `let`, which the kernel computes again for every byte it
is asked about). -/
theorem sharedBytes_eq (p : IR.Prog) (frames : List (String × Nat))
    (h : (IR.layout p (fun f => ((p.fn? f).map (·.frame)).getD 0) 0).frames = frames) :
    sharedBytes p = sharedOf p frames := by
  unfold sharedBytes sharedOf
  simp only [h]
  funext f k
  cases List.lookup f frames <;> rfl

end Ember.Proof.Z80Gen
