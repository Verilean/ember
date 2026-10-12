import Ember.Proof.Z80LoopH

/-!
# Ember.Proof.Z80LoopHSpec — the loopback image for the harness, against the Ember semantics (plan M7.3)

`loopH_run` takes that the calls of `main` end in the IR's semantics,
each moving the position in the input while input remains.  They do:
the loopback never traps in the Ember semantics and takes an item of
input in every call (`loop_main_refines`, M5.5), and what ends there
ends in the IR with the same world (`lower_iter`, M7.1).  `loopH_spec`
composes the three: from reset, for any input and any number `j` of
calls, the machine holds the world `j` calls of `main` leave **in the
Ember semantics** — or it left the loop after `i ≤ j` calls and stopped
(`di; halt`) with the world of those, **the input used up**.

`LoopSrc p` is what is taken of the Ember program `p`: that it is the
checked loopback program, lowered to `Loop.ir`, accepted by the checkers
of M7.1 with this layout.  Each part that can be computed is a `#guard`
on `Net.Loop.prog.check` below (evaluation, not proof) — the kernel does
not run the type checker or the lowering.
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (callN LoopProg LoopInv loop_safe loop_initial)

theorem callN_eq (p : Lang.Prog) (he : p.entry = "main") (fuel : Nat) :
    ∀ (j : Nat) (st : Lang.Sem.St), callN fuel p "main" j st = callIter fuel p j st
  | 0, _ => rfl
  | j + 1, st => by
    rw [callN, callIter, he]
    cases Lang.Sem.call fuel p st "main" [] with
    | ok v st' => exact callN_eq p he fuel j st'
    | trap _ => rfl
    | fuel => rfl

/-- What is taken of the Ember program. -/
structure LoopSrc (p : Lang.Prog) : Prop where
  prog : LoopProg p
  entry : p.entry = "main"
  globals : p.globals = Net.Loop.prog.globals
  structs : p.structs = Net.Loop.prog.structs
  framed : p.framed = false
  lowered : IR.lower p = .ok Loop.ir
  okP : progOkB p = true
  okIR : irOkB p layout = true
  drops : p.dropReasons = ["oversize-frame"]
  notes : p.notes = []

-- the parts of `LoopSrc` that can be computed, of the checked loopback program
#guard (Net.Loop.prog.check.toOption.map fun q =>
  q.entry == "main" && q.globals == Net.Loop.prog.globals && q.structs == Net.Loop.prog.structs &&
    q.framed == false && progOkB q && irOkB q layout && q.dropReasons == ["oversize-frame"] && q.notes == []) ==
  some true

theorem callN_snoc (p : Lang.Prog) (fuel : Nat) : ∀ (i : Nat) (st sti sti' : Lang.Sem.St) (r : Option Lang.Val),
    callN fuel p "main" i st = some sti → Lang.Sem.call fuel p sti "main" [] = .ok r sti' →
    callN fuel p "main" (i + 1) st = some sti'
  | 0, st, sti, sti', r, h, hc => by
    cases h
    rw [callN, hc]
    rfl
  | i + 1, st, sti, sti', r, h, hc => by
    rw [callN] at h ⊢
    cases hc0 : Lang.Sem.call fuel p st "main" [] with
    | ok v st1 =>
      rw [hc0] at h
      exact callN_snoc p fuel i st1 sti sti' r h hc
    | trap _ => rw [hc0] at h; cases h
    | fuel => rw [hc0] at h; cases h

theorem irIter_snoc (m : Nat) (c : IR.Ctx) : ∀ (i : Nat) (st sti sti' : IR.Sem.St) (r : Option Nat),
    irIter m c i st = some sti → IR.Sem.callF m c c.prog.entry sti = .ok r sti' →
    irIter m c (i + 1) st = some sti'
  | 0, st, sti, sti', r, h, hc => by
    cases h
    rw [irIter, hc]
    rfl
  | i + 1, st, sti, sti', r, h, hc => by
    rw [irIter] at h ⊢
    cases hc0 : IR.Sem.callF m c c.prog.entry st with
    | ok v st1 =>
      rw [hc0] at h
      exact irIter_snoc m c i st1 sti sti' r h hc
    | trap _ => rw [hc0] at h; cases h
    | fuel => rw [hc0] at h; cases h
    | bad => rw [hc0] at h; cases h

theorem loopOut_pos (w : Lang.World) (r : Spec.Slip.Result) :
    (Ember.Proof.Refine.loopOut w r).pos = w.pos ∧ (Ember.Proof.Refine.loopOut w r).off = w.off ∧
      (Ember.Proof.Refine.loopOut w r).framed = w.framed ∧ (Ember.Proof.Refine.loopOut w r).inputs = w.inputs := by
  cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **One call of `main` in the Ember semantics**: it ends, the state
holds a decoder state again, and with input remaining the position in
the input has moved. -/
theorem lang_step (p : Lang.Prog) (hP : LoopProg p) (st : Lang.Sem.St) (d : Spec.Slip.Dec) (hinv : LoopInv st d 296)
    (hf : st.world.framed = false) :
    ∃ st' d', Lang.Sem.call 366 p st "main" [] = .ok none st' ∧ LoopInv st' d' 296 ∧ st'.world.framed = false ∧
      (st.world.next.1 ≠ 0xFFFF → (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off) ∧
        World.rem st'.world + 1 = World.rem st.world) := by
  obtain ⟨st', hc, hcase⟩ := Ember.Proof.Refine.loop_main_refines p hP st d 296 hinv 0
  have hc' : Lang.Sem.call 366 p st "main" [] = .ok none st' := hc
  have hmv := next_moves st.world hf
  have hfr := next_framed st.world hf
  split at hcase
  · obtain ⟨hI, hw⟩ := hcase
    obtain ⟨h1, h2, h3, h4⟩ := loopOut_pos st.world.next.2 (d.feed st.world.next.1.toUInt8 (296 : UInt16).toNat).2
    refine ⟨st', _, hc', hI, by rw [hw, h3]; exact hfr, fun hne => ⟨?_, ?_⟩⟩
    · rw [hw, h1, h2]
      exact hmv hne
    · rw [← rem_next st.world hf hne, hw]
      unfold World.rem
      rw [h1, h2, h4]
  · obtain ⟨hI, hw⟩ := hcase
    exact ⟨st', _, hc', hI, by rw [hw]; exact hfr, fun hne => ⟨by rw [hw]; exact hmv hne, by
      rw [hw]; exact rem_next st.world hf hne⟩⟩

/-- Any number of calls: they end, and every state on the way holds a decoder state. -/
theorem lang_run (p : Lang.Prog) (hP : LoopProg p) : ∀ (k : Nat) (st : Lang.Sem.St) (d : Spec.Slip.Dec),
    LoopInv st d 296 → st.world.framed = false →
    ∃ stk dk, callN 366 p "main" k st = some stk ∧ LoopInv stk dk 296 ∧ stk.world.framed = false
  | 0, st, d, h, hf => ⟨st, d, rfl, h, hf⟩
  | k + 1, st, d, h, hf => by
    obtain ⟨st1, d1, hc, h1, hf1, _⟩ := lang_step p hP st d h hf
    obtain ⟨stk, dk, hk, hk1, hk2⟩ := lang_run p hP k st1 d1 h1 hf1
    exact ⟨stk, dk, by rw [callN, hc]; exact hk, hk1, hk2⟩

/-- What the Ember semantics gives of the run, for the IR: after any
number of calls there is a state, the same whatever the fuel, with the
world the Ember semantics has; and a call with input remaining moves the
position in the input. -/
theorem src_facts (p : Lang.Prog) (S : LoopSrc p) (inputs : Array Ember.Trace.Input) :
    (∀ k, ∃ stk dk m istk, callN 366 p "main" k (Lang.Sem.initial p inputs) = some stk ∧
      LoopInv stk dk 296 ∧ stk.world.framed = false ∧
      irIter m img.ctx k (st0 inputs) = some istk ∧ istk.world = stk.world) ∧
    (∀ k m1 m2 x y, irIter m1 img.ctx k (st0 inputs) = some x → irIter m2 img.ctx k (st0 inputs) = some y → x = y) ∧
    ∀ m, Moves m (st0 inputs) := by
  have hinit : LoopInv (Lang.Sem.initial p inputs) {} 296 := by
    rw [Ember.Proof.CSim.initial_congr p Net.Loop.prog S.globals S.structs (by rw [S.framed]; rfl)]
    exact loop_initial inputs
  have hfr0 : (Lang.Sem.initial p inputs).world.framed = false := S.framed
  have hctx : irCtx p Loop.ir layout = img.ctx := by
    unfold irCtx
    rw [S.drops, S.notes]
    rfl
  have hst0 : irInit p Loop.ir layout inputs = st0 inputs := by
    unfold irInit
    rw [S.framed]
    rfl
  -- the calls end, in the Ember semantics and so in the IR's
  have lang : ∀ k, ∃ stk dk m istk, callN 366 p "main" k (Lang.Sem.initial p inputs) = some stk ∧
      LoopInv stk dk 296 ∧ stk.world.framed = false ∧
      irIter m img.ctx k (st0 inputs) = some istk ∧ istk.world = stk.world := by
    intro k
    obtain ⟨stk, dk, hk, hI, hf⟩ := lang_run p S.prog k _ _ hinit hfr0
    obtain ⟨m, istk, hit, hw⟩ := lower_iter S.lowered layout S.okP S.okIR inputs 366 k stk
      (by rw [← callN_eq p S.entry]; exact hk)
    rw [hctx, hst0] at hit
    exact ⟨stk, dk, m, istk, hk, hI, hf, hit, hw⟩
  -- the IR's state after `k` calls is one, whatever the fuel
  have det : ∀ k m1 m2 x y, irIter m1 img.ctx k (st0 inputs) = some x → irIter m2 img.ctx k (st0 inputs) = some y →
      x = y := by
    intro k m1 m2 x y h1 h2
    have e1 := irIter_le (c := img.ctx) (Nat.le_max_left m1 m2) k _ _ h1
    have e2 := irIter_le (c := img.ctx) (Nat.le_max_right m1 m2) k _ _ h2
    rw [e1] at e2
    exact Option.some.inj e2
  refine ⟨lang, det, fun m => ?_⟩
  -- a call with input remaining moves the position in the input
  intro i isti r isti' hiti hcall hne
  obtain ⟨sti, di, mi, isti0, hi, hIi, hfi, hiti0, hwi⟩ := lang i
  have e : isti = isti0 := det i _ _ _ _ hiti hiti0
  obtain ⟨sti', di', hc, _, _, hmoved⟩ := lang_step p S.prog sti di hIi hfi
  have hi' := callN_snoc p 366 i _ sti sti' none hi hc
  obtain ⟨sti1, _, mi1, isti1, hi1, _, _, hiti1, hwi1⟩ := lang (i + 1)
  rw [hi'] at hi1
  cases hi1
  have e' : isti' = isti1 := det (i + 1) _ _ _ _ (irIter_snoc m img.ctx i _ isti isti' r hiti hcall) hiti1
  rw [e', hwi1, e, hwi]
  exact (hmoved (by rw [← hwi, ← e]; exact hne)).1

/-- **The loopback image for the harness does what the Ember semantics
says**, from reset: `j` calls of `main` end there (it never traps), and
the machine holds their world at the head of its loop — or left the loop
after `i ≤ j` calls and stopped, holding the world of those, the input
used up. -/
theorem loopH_spec (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ j : Nat, ∃ st' : Lang.Sem.St, callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧
          ((∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0))) (s', w') ∧ At addrs 174 s' ∧
              s'.sp = 0 ∧ w'.1 = st'.world) ∨
           (∃ i sti s' w', i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
              WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0))) (s', w') ∧ s'.halted = true ∧
              s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF)) := by
  obtain ⟨a, addrs, ha, hrun⟩ := loopH_run
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j => ?_⟩
  obtain ⟨lang, det, hmv⟩ := src_facts p S inputs
  obtain ⟨stj, _, m, istj, hj, _, _, hitj, hwj⟩ := lang j
  refine ⟨stj, hj, ?_⟩
  rcases hrun inputs s hpc I hh hrs hsz j m istj (hmv m) hitj with ⟨s', w', stp, L⟩ |
    ⟨i, isti, s', w', hi, hiti, stp, hh', hi1', hw, hex⟩
  · exact Or.inl ⟨s', w', stp, L.at_, L.sp, by rw [L.world, hwj]⟩
  · obtain ⟨sti, _, m', isti', hi', _, _, hiti', hwi⟩ := lang i
    have e : isti = isti' := det i _ _ _ _ hiti hiti'
    exact Or.inr ⟨i, sti, s', w', hi, hi', stp, hh', hi1', by rw [hw, e, hwi], by rw [← hwi, ← e]; exact hex⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_spec

/-- **The input is used up after as many calls as it has items.** -/
theorem lang_exhaust (p : Lang.Prog) (hP : LoopProg p) : ∀ (n : Nat) (st : Lang.Sem.St) (d : Spec.Slip.Dec),
    LoopInv st d 296 → st.world.framed = false → World.rem st.world = n →
    ∃ stn, callN 366 p "main" n st = some stn ∧ stn.world.next.1 = 0xFFFF
  | 0, st, _, _, hf, hr => ⟨st, rfl, (rem_zero st.world hf).mpr hr⟩
  | n + 1, st, d, h, hf, hr => by
    have hne : st.world.next.1 ≠ 0xFFFF := fun e => by
      have := (rem_zero st.world hf).mp e
      omega
    obtain ⟨st1, d1, hc, h1, hf1, hmv⟩ := lang_step p hP st d h hf
    obtain ⟨stn, hn, hex⟩ := lang_exhaust p hP n st1 d1 h1 hf1 (by have := (hmv hne).2; omega)
    exact ⟨stn, by rw [callN, hc]; exact hn, hex⟩

/-- **The loopback image for the harness processes all its input and
stops**, from reset, for any input: some number `i` of calls of `main`
end in the Ember semantics leaving no input, and the machine is stopped
(`di; halt`) holding the world of those calls. -/
theorem loopH_spec_halt (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∃ i sti s' w', callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0))) (s', w') ∧ s'.halted = true ∧
          s'.iff1 = false ∧ w'.1 = sti.world := by
  obtain ⟨a, addrs, ha, hrun⟩ := loopH_run_halt
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz => ?_⟩
  obtain ⟨lang, det, hmv⟩ := src_facts p S inputs
  have hinit : LoopInv (Lang.Sem.initial p inputs) {} 296 := by
    rw [Ember.Proof.CSim.initial_congr p Net.Loop.prog S.globals S.structs (by rw [S.framed]; rfl)]
    exact loop_initial inputs
  obtain ⟨stn, hn, hexn⟩ := lang_exhaust p S.prog _ _ _ hinit S.framed rfl
  obtain ⟨stj, _, m, istj, hj, _, _, hitj, hwj⟩ := lang (World.rem (Lang.Sem.initial p inputs).world)
  rw [hn] at hj
  cases hj
  obtain ⟨i, isti, s', w', hi, hiti, stp, hh', hi1', hw, hex⟩ :=
    hrun inputs s hpc I hh hrs hsz _ m istj (hmv m) hitj (by rw [hwj]; exact hexn)
  obtain ⟨sti, _, m', isti', hi', _, _, hiti', hwi⟩ := lang i
  have e : isti = isti' := det i _ _ _ _ hiti hiti'
  exact ⟨i, sti, s', w', hi', by rw [← hwi, ← e]; exact hex, stp, hh', hi1', by rw [hw, e, hwi]⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_spec_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_spec_halt

end Ember.Proof.Z80Gen.LoopH
