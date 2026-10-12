import Ember.Proof.Z80LoopH

/-!
# Ember.Proof.Z80LoopHSpec — the loopback image for the harness, against the Ember semantics (plan M7.3)

`loopH_run` takes that the calls of `main` end in the IR's semantics.
They do: the loopback never traps in the Ember semantics (`loop_safe`,
M5.5), and what ends there ends in the IR with the same world
(`lower_iter`, M7.1).  `loopH_spec` composes the three: from reset, for
any input and any number `j` of calls, the machine holds the world `j`
calls of `main` leave **in the Ember semantics** — or it left the loop
after `i ≤ j` calls and stopped (`di; halt`) with the world of those:
the input used up, or by the loop's count of idle calls.

Still not said: that the second does not happen (the loopback consumes
an item of input in every call, so the count stays at zero — but the
count is in the runtime's own bytes, which the theorems about the
functions do not follow through a call), and so that all the input is
processed before the machine stops.

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

/-- **The loopback image for the harness does what the Ember semantics
says**, from reset: `j` calls of `main` end there (it never traps), and
the machine holds their world at the head of its loop — or left the loop
after `i ≤ j` calls, holding the world of those. -/
theorem loopH_spec (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ j : Nat, ∃ st' : Lang.Sem.St, callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧
          ((∃ s' w', WSteps (Zof a addrs) (s, ((st0 inputs).world, 0)) (s', w') ∧ At addrs 176 s' ∧
              s'.sp = 0 ∧ w'.1 = st'.world) ∨
           (∃ i sti s' w', i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
              WSteps (Zof a addrs) (s, ((st0 inputs).world, 0)) (s', w') ∧ s'.halted = true ∧ s'.iff1 = false ∧
              w'.1 = sti.world ∧ (sti.world.next.1 = 0xFFFF ∨ Idle sti.world))) := by
  obtain ⟨a, addrs, ha, hrun⟩ := loopH_run
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j => ?_⟩
  have hinit : LoopInv (Lang.Sem.initial p inputs) {} 296 := by
    rw [Ember.Proof.CSim.initial_congr p Net.Loop.prog S.globals S.structs (by rw [S.framed]; rfl)]
    exact loop_initial inputs
  have hctx : irCtx p Loop.ir layout = img.ctx := by
    unfold irCtx
    rw [S.drops, S.notes]
    rfl
  have hst0 : irInit p Loop.ir layout inputs = st0 inputs := by
    unfold irInit
    rw [S.framed]
    rfl
  -- the calls end, in the Ember semantics and so in the IR's
  have lang : ∀ k, ∃ stk m istk, callN 366 p "main" k (Lang.Sem.initial p inputs) = some stk ∧
      irIter m img.ctx k (st0 inputs) = some istk ∧ istk.world = stk.world := by
    intro k
    obtain ⟨stk, _, hk, _⟩ := loop_safe p S.prog 296 0 k _ _ hinit
    have hk' : callN 366 p "main" k (Lang.Sem.initial p inputs) = some stk := hk
    obtain ⟨m, istk, hit, hw⟩ := lower_iter S.lowered layout S.okP S.okIR inputs 366 k stk
      (by rw [← callN_eq p S.entry]; exact hk')
    rw [hctx, hst0] at hit
    exact ⟨stk, m, istk, hk', hit, hw⟩
  obtain ⟨stj, m, istj, hj, hitj, hwj⟩ := lang j
  refine ⟨stj, hj, ?_⟩
  rcases hrun inputs s hpc I hh hrs hsz j m istj hitj with ⟨s', w', stp, L, hw⟩ | ⟨i, isti, s', w', hi, hiti, stp, hh', hi1', hw, hwhy⟩
  · exact Or.inl ⟨s', w', stp, L.at_, L.sp, by rw [hw, hwj]⟩
  · obtain ⟨sti, m', isti', hi', hiti', hwi⟩ := lang i
    have e : isti = isti' := by
      have h1 := irIter_le (c := img.ctx) (Nat.le_max_left m m') i _ _ hiti
      have h2 := irIter_le (c := img.ctx) (Nat.le_max_right m m') i _ _ hiti'
      rw [h1] at h2
      exact Option.some.inj h2
    exact Or.inr ⟨i, sti, s', w', hi, hi', stp, hh', hi1', by rw [hw, e, hwi], by rw [← hwi, ← e]; exact hwhy⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_spec

end Ember.Proof.Z80Gen.LoopH
