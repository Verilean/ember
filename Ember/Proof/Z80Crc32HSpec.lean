import Ember.Proof.Z80Crc32HRun
import Ember.Proof.Z80WideHSpec

/-!
# Ember.Proof.Z80Crc32HSpec — `crc32`'s image, against the Ember semantics and on the machine the tests run (plan M7.3)

`crc32H_halts` takes runs of the IR.  Here it is composed with the
lowering (`lower_iter`, M7.1) and carried to `Ember.Z80.Machine`
(`step_sim`, through `LoopH.run_sim_of`), as `Z80WideHSpec` does for
`Ember.Z80.Wide`:

* `crc32H_spec_halt`, `crc32H_harness_halts`: **when `j` calls of
  `main` end in the Ember semantics (`callN k p "main" j` from
  `Lang.Sem.initial p inputs` is `some st'`) and leave no input**, the
  machine — the proofs' machine from reset, and `Machine.step` from the
  machine as the tests build it — halted (`di; halt`) after `i ≤ j`
  calls, standing for the world those `i` calls leave in the Ember
  semantics, with no input left.
* `crc32_lang_no_trap`: from a state that `j` calls of `main` reach in
  the Ember semantics, the next call does not trap (`main_no_trap`
  through `lower_trap`).  It says nothing of whether the call ends:
  it may run out of fuel; that the calls end is the hypothesis on
  `callN` of the theorems above.

What is taken: `Crc32Src p` of the Ember program — the checked
`Ember.Lang.Examples.Crc32.prog` is meant.  Of it, the parts of
`Crc32Src` are `#guard`s: its lowering is `Crc32.ir` (`irIsLowering`,
`Z80Crc32IR`), and entry, frame input, typing, the layout, drop reasons
and notes (`Z80Crc32HItems`) — evaluation when those files are built,
not proof: the checker is `partial`, so that `Crc32Src` holds of the
checked program is not a kernel theorem.  And the calls' ending as the
hypotheses say: nothing says that the program on a finite input ends in
the Ember semantics (for one input it is evaluated below, `#guard`).
The image is `Crc32H.items`, without the passes on the assembly.  Not
covered: the trace `runHarness` prints, the image as built by default,
real hardware.
-/

namespace Ember.Proof.Z80Gen.Crc32H
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (callN)
open Ember.Trace (Input)

/-- What is taken of the Ember program. -/
structure Crc32Src (p : Lang.Prog) : Prop where
  entry : p.entry = "main"
  framed : p.framed = false
  lowered : IR.lower p = .ok Crc32.ir
  okP : progOkB p = true
  okIR : irOkB p layout = true
  drops : p.dropReasons = []
  notes : p.notes = []

theorem ctx_eq (p : Lang.Prog) (S : Crc32Src p) : irCtx p Crc32.ir layout = img.ctx := by
  unfold irCtx
  rw [S.drops, S.notes]
  rfl

theorem init_eq (p : Lang.Prog) (S : Crc32Src p) (inputs : Array Input) :
    irInit p Crc32.ir layout inputs = st0 inputs := by
  unfold irInit
  rw [S.framed]
  rfl

theorem callN_pre (fuel : Nat) (p : Lang.Prog) (f : String) :
    ∀ (j i : Nat) (st st' : Lang.Sem.St), callN fuel p f j st = some st' → i ≤ j →
      ∃ sti, callN fuel p f i st = some sti
  | _, 0, st, _, _, _ => ⟨st, rfl⟩
  | 0, _ + 1, _, _, _, hij => absurd hij (by omega)
  | j + 1, i + 1, st, st', h, hij => by
    rw [callN] at h ⊢
    cases hc : Lang.Sem.call fuel p st f [] with
    | ok v st1 =>
      rw [hc] at h
      exact callN_pre fuel p f j i st1 st' h (by omega)
    | trap _ => rw [hc] at h; cases h
    | fuel => rw [hc] at h; cases h

theorem ir_det (k : Nat) (st : IR.Sem.St) (m1 m2 : Nat) (x y : IR.Sem.St) (h1 : irIter m1 img.ctx k st = some x)
    (h2 : irIter m2 img.ctx k st = some y) : x = y := by
  have e1 := irIter_le (c := img.ctx) (Nat.le_max_left m1 m2) k _ _ h1
  have e2 := irIter_le (c := img.ctx) (Nat.le_max_right m1 m2) k _ _ h2
  rw [e1] at e2
  exact Option.some.inj e2

/-- Calls that end in the Ember semantics end in the IR's, with the same world. -/
theorem lang_ir (p : Lang.Prog) (S : Crc32Src p) (inputs : Array Input) (k j : Nat) (st' : Lang.Sem.St)
    (h : callN k p "main" j (Lang.Sem.initial p inputs) = some st') :
    ∃ m ist', irIter m img.ctx j (st0 inputs) = some ist' ∧ ist'.world = st'.world := by
  obtain ⟨m, ist', hit, hw⟩ := lower_iter S.lowered layout S.okP S.okIR inputs k j st'
    (by rw [← LoopH.callN_eq p S.entry]; exact h)
  rw [ctx_eq p S, init_eq p S] at hit
  exact ⟨m, ist', hit, hw⟩

/-! ## The proofs' machine, from reset -/

/-- **Against the Ember semantics: halting.**  From reset, when `j` calls
of `main` end in the Ember semantics and leave no input, the machine
halted after `i ≤ j` of them, holding the world of those `i` calls. -/
theorem crc32H_spec_halt (p : Lang.Prog) (S : Crc32Src p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (k j : Nat) (st' : Lang.Sem.St), callN k p "main" j (Lang.Sem.initial p inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i sti s' w', i ≤ j ∧ callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hh⟩ := crc32H_halts
  refine ⟨a, addrs, ha, fun inputs s hpc I hhl hrs hsz k j st' hj hex => ?_⟩
  obtain ⟨m, ist', hit, hw⟩ := lang_ir p S inputs k j st' hj
  obtain ⟨i, sti_ir, s', w', hi, hiti, stp, hh1, hif, hw1, hex1⟩ :=
    hh inputs s hpc I hhl hrs hsz j m ist' hit (by rw [hw]; exact hex)
  obtain ⟨sti, hci⟩ := callN_pre k p "main" j i _ st' hj hi
  obtain ⟨m2, isti2, hit2, hw2⟩ := lang_ir p S inputs k i sti hci
  have e := ir_det i _ m m2 _ _ hiti hit2
  subst e
  exact ⟨i, sti, s', w', hi, hci, stp, hh1, hif, by rw [hw1, hw2], by rw [← hw2]; exact hex1⟩

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_spec_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_spec_halt

/-! ## The machine the tests run (`Z80Machine`: `step_sim`, `run_sim_of`) -/

theorem image_small : ∀ a, assemble items = .ok a → a.bytes.size ≤ 0x8000 := by
  intro a ha
  have h : (match assemble items with | .ok a => decide (a.bytes.size ≤ 0x8000) | .error _ => false) = true := by
    decide +kernel
  rw [ha] at h
  simpa using h

/-- A run of `Ember.Z80.Machine` is a run of the proofs' machine (`LoopH.run_sim_of`, for this image). -/
theorem run_sim (a : Assembled) (addrs : List Nat) (n : Nat) (m : Machine) (w : HW) (S : LoopH.Sim img.ctx m w) :
    (LoopH.mrun n m).cpu = (wrun (Zof a addrs (0, 0)) n (m.cpu, w)).1 ∧
      LoopH.Sim img.ctx (LoopH.mrun n m) (wrun (Zof a addrs (0, 0)) n (m.cpu, w)).2 :=
  LoopH.run_sim_of img a addrs n m w S

/-- The machine as the tests build it stands for the world the IR starts in. -/
theorem sim0 (a : Assembled) (inputs : Array Input) (hsz : a.bytes.size ≤ 0x8000) :
    LoopH.Sim img.ctx (LoopH.harnessMachine a inputs) ((st0 inputs).world, 0, (0, 0), (0, 0)) := by
  have R := LoopH.harness_reset a inputs hsz
  exact ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
    rw [R.events]
    rfl, R.nval, by rw [R.events]; show false = _; simp [LoopH.trapIn]⟩

/-- **On `Ember.Z80.Machine`, as the tests build it: halting.**  For any
input, when `j` calls of `main` end in the Ember semantics and leave no
input: after some number `n` of `Machine.step`s the CPU is halted and the
machine stands (`Sim`: input position, frame, events recorded) for the
world `i ≤ j` of those calls leave in the Ember semantics. -/
theorem crc32H_harness_halts (p : Lang.Prog) (S : Crc32Src p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ (inputs : Array Input) (k j : Nat) (st' : Lang.Sem.St),
        callN k p "main" j (Lang.Sem.initial p inputs) = some st' → st'.world.next.1 = 0xFFFF →
        ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW), i ≤ j ∧
          callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.halted = true ∧
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧ w'.1 = sti.world := by
  obtain ⟨a, addrs, ha, hspec⟩ := crc32H_spec_halt p S
  have hsz := image_small a ha
  refine ⟨a, ha, fun inputs k j st' hj hex => ?_⟩
  have R := LoopH.harness_reset a inputs hsz
  obtain ⟨i, sti, s', w', hi, hci, ⟨n, hn⟩, hh, _, hw, hex'⟩ :=
    hspec inputs _ R.pc R.img R.run R.rs R.msz k j st' hj hex
  obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
  rw [hn] at hc Sn
  exact ⟨i, sti, n, w', hi, hci, hex', by rw [hc]; exact hh, Sn, hw⟩

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_harness_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_harness_halts

/-! ## No trap in the Ember semantics -/

/-- **From a state the calls of `main` reach in the Ember semantics, the
next call does not trap**: a trap there would be a trap of the IR's
`main` (`lower_trap`), which has no instruction that can trap
(`main_no_trap`).  Not that the call ends: it may run out of fuel. -/
theorem crc32_lang_no_trap (p : Lang.Prog) (S : Crc32Src p) (inputs : Array Input) (k j : Nat)
    (st1 st2 : Lang.Sem.St) (hj : callN k p "main" j (Lang.Sem.initial p inputs) = some st1) :
    Lang.Sem.call k p st1 "main" [] ≠ .trap st2 := by
  intro htr
  obtain ⟨m, ist1, ist2, _, htrI, _⟩ := lower_trap S.lowered layout S.okP S.okIR inputs k j st1 st2
    (by rw [← LoopH.callN_eq p S.entry]; exact hj) (by rw [S.entry]; exact htr)
  rw [ctx_eq p S] at htrI
  exact main_no_trap m ist1 ist2 htrI

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32_lang_no_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32_lang_no_trap

/-! ## One input, in the Ember semantics (evaluated)

What `crc32H_harness_halts` takes of the Ember semantics, for one
input, evaluated (`#guard`: evaluation, not proof) on the checked
program: the nine bytes of `"123456789"` and a tick — ten calls end, no
input is left, and the frame sent is the CRC-32 of the bytes,
`0xCBF43926`, low byte first. -/

def inputsCheck : Array Input := #[.rx (ByteArray.mk "123456789".toUTF8.data), .tick]

#guard match Ember.Lang.Examples.Crc32.prog.check with
  | .ok q => match callN 1000 q "main" 10 (Lang.Sem.initial q inputsCheck) with
    | some st => st.world.next.1 == 0xFFFF && WideH.txs st.world == [[0x26, 0x39, 0xF4, 0xCB]]
    | none => false
  | .error _ => false

end Ember.Proof.Z80Gen.Crc32H
