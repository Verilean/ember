import Ember.Proof.Z80PassStack
import Ember.Proof.Z80StackHTrace

/-!
# Ember.Proof.Z80PassStackTrace — the trace the tests print of the stack's image as built by default (plan M7.3)

`stackD_trace`, `stackD_no_trap`, `stackD_trace_lines`: what
`stackH_trace`, `stackH_no_trap`, `stackH_trace_lines` say of the image
without the passes, of `StackD` — the image `build` makes by default,
loaded as `Tools.Z80.machineOf` loads it and run by `Target.runHarness`.

The proofs of those theorems use of the image only what `stackH_halts`
says of its run on each input (`HaltsAt`): they are written here for
any image with that (`trace_of`, `no_trap_of`, `trace_lines_of`), and
`stackD_halts` gives it of `StackD`.  That `StackD.items` are what
`build` gives by default, and its bytes what `build` gives, are
`#guard`s (`StackD.isBuilt`, `isLoadedD`).
-/

namespace Ember.Proof.PassSim.Stack
open Ember Ember.Z80 Ember.Z80.Asm
open Ember.Proof.Z80Gen
open Ember.Proof.Refine (kept specKept keep mainIter)
open Ember.Proof.Z80Gen.LoopH (Sim harnessMachine run_sim_of evOf evsOf trapIn)
open Ember.Proof.Z80Gen.StackH (loaded sim0 StackSrc)
open Ember.Trace (Input Line Event Trace)

/-- What `stackH_halts` says of an image's run on an input: some calls of `main` use the input up,
and after some steps the CPU is halted and the machine stands for the world they leave, whose kept
lines are the Spec's. -/
def HaltsAt (p : Lang.Prog) (a : Assembled) (inputs : Array Input) : Prop :=
  ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW),
    mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
    (LoopH.mrun n (harnessMachine a inputs)).cpu.halted = true ∧
    Sim StackH.img.ctx (LoopH.mrun n (harnessMachine a inputs)) w' ∧ w'.1 = sti.world ∧
    kept w'.1 = specKept inputs.toList 0 (Spec.State.init {})

/-- **The trace of an image that halts as `stackH_halts` says**: the transmissions and drops of the
Spec's trace, and the inputs as its input lines. -/
theorem trace_of (p : Lang.Prog) (S : StackSrc p) (a : Assembled) (hsz : a.bytes.size ≤ 0x8000)
    (hall : ∀ inputs, HaltsAt p a inputs) :
    ∀ (h : Trace.Header) (inputs : Array Input), ∃ N, ∀ maxSteps, N ≤ maxSteps → ∃ tr,
      Target.runHarness (loaded a) 0 h inputs p.dropReasons.toArray p.notes.toArray maxSteps = .ok tr ∧
      keptLines tr = keptLines (Spec.run {} inputs) ∧
      inputsOf tr = (List.range inputs.size).map fun i => (i, Target.inputEvent inputs[i]!) := by
  intro h inputs
  obtain ⟨_, _, n, w', _, _, hh, Sn, _, hk⟩ := hall inputs
  obtain ⟨n0, hle, hh0, hfirst⟩ := first_halt (harnessMachine a inputs) n hh
  refine ⟨n0, fun maxSteps hN => ?_⟩
  have hrun : Target.runToHalt maxSteps { loaded a with harness := true, inputs := inputs, program := UInt8.ofNat 0 } =
      .ok (LoopH.mrun n0 (harnessMachine a inputs)) :=
    runToHalt_of n0 maxSteps _ hN hfirst hh0
  obtain ⟨_, S0⟩ := run_sim_of StackH.img a [] n0 _ _ (sim0 a inputs hsz)
  have Sn' := (sim_halted_run (n - n0) _ _ S0 hh0).1
  rw [← Z80Gen.mrun_add, show n0 + (n - n0) = n by omega] at Sn'
  have hev : evsOf StackH.img.ctx (LoopH.mrun n0 (harnessMachine a inputs)).events = w'.1.events := by
    rw [S0.events, ← Sn'.events, Sn.events]
  have hkept : ((evsOf StackH.img.ctx (LoopH.mrun n0 (harnessMachine a inputs)).events).toList.filter fun x => keep x.2) =
      specKept inputs.toList 0 (Spec.State.init {}) := by
    rw [hev]; exact hk
  have hd : p.dropReasons.toArray = StackH.img.ctx.dropReasons.toArray := by rw [S.drops]; rfl
  have hn : p.notes.toArray = StackH.img.ctx.notes.toArray := by rw [S.notes]; rfl
  refine ⟨_, runHarness_lines _ h inputs _ _ maxSteps _ hrun, ?_, ?_⟩
  · rw [specRun_kept, hd, hn]
    unfold keptLines
    simp only [List.filterMap_append, List.filterMap_flatMap]
    have htrap : ∀ (c : Prop) [Decidable c],
        (if c then [(⟨(LoopH.mrun n0 (harnessMachine a inputs)).cur, .note "trap (z80)"⟩ : Line)] else []).filterMap
          (fun l => if keep l.ev then some (l.step, l.ev) else none) = [] := by
      intro c _; split <;> rfl
    rw [htrap, List.append_nil]
    have hblk := fun i => kept_inputLines StackH.img.ctx inputs (LoopH.mrun n0 (harnessMachine a inputs)).events.toList i
    simp only [Array.toArray_toList] at hblk
    simp only [hblk, hkept]
    rw [List.range_eq_range', show inputs.size = inputs.toList.length by simp]
    exact specKept_group inputs.toList 0 _
  · unfold inputsOf
    simp only [List.filterMap_append, List.filterMap_flatMap]
    have htrap : ∀ (c : Prop) [Decidable c],
        (if c then [(⟨(LoopH.mrun n0 (harnessMachine a inputs)).cur, .note "trap (z80)"⟩ : Line)] else []).filterMap
          inputOf = [] := by
      intro c _; split <;> rfl
    rw [htrap, List.append_nil]
    have hi := fun i => inputs_inputLines inputs (LoopH.mrun n0 (harnessMachine a inputs)).events.toList
      p.dropReasons.toArray p.notes.toArray i
    simp only [hi]
    simp only [List.flatMap]
    exact flatten_single _ _

/-- **No trap recorded** by the harness, for an image that halts as `stackH_halts` says. -/
theorem no_trap_of (p : Lang.Prog) (a : Assembled) (hsz : a.bytes.size ≤ 0x8000)
    (hall : ∀ inputs, HaltsAt p a inputs) :
    ∀ inputs : Array Input, ∃ n0,
      (∀ k, k < n0 → (LoopH.mrun k (harnessMachine a inputs)).cpu.halted = false) ∧
      (LoopH.mrun n0 (harnessMachine a inputs)).cpu.halted = true ∧
      (∀ x ∈ (LoopH.mrun n0 (harnessMachine a inputs)).events, x.2 ≠ .trap) ∧
      ∀ d, (LoopH.mrun (n0 + d) (harnessMachine a inputs)).cpu.halted = true ∧
        (LoopH.mrun (n0 + d) (harnessMachine a inputs)).events = (LoopH.mrun n0 (harnessMachine a inputs)).events := by
  intro inputs
  obtain ⟨i, sti, n, w', hi, _, hh, Sn, hw, _⟩ := hall inputs
  obtain ⟨n0, hle, hh0, hfirst⟩ := first_halt (harnessMachine a inputs) n hh
  obtain ⟨_, S0⟩ := run_sim_of StackH.img a [] n0 _ _ (sim0 a inputs hsz)
  have Sn' := (sim_halted_run (n - n0) _ _ S0 hh0).1
  rw [← Z80Gen.mrun_add, show n0 + (n - n0) = n by omega] at Sn'
  have htr : trapIn (LoopH.mrun n0 (harnessMachine a inputs)).events = false := by
    rw [← S0.trapped, Sn'.trapped, ← Sn.trapped, hw]
    exact mainIter_trapped 4716 p i _ sti (Lang.Sem.initial_trapped p inputs) hi
  refine ⟨n0, hfirst, hh0, not_trap_of htr, fun d => ⟨?_, ?_⟩⟩
  · rw [Z80Gen.mrun_add]; exact (sim_halted_run d _ _ S0 hh0).2
  · rw [Z80Gen.mrun_add]; exact halted_events_run d _ _ S0 hh0

/-- **The whole trace**, for an image that halts as `stackH_halts` says. -/
theorem trace_lines_of (p : Lang.Prog) (S : StackSrc p) (a : Assembled) (hsz : a.bytes.size ≤ 0x8000)
    (hall : ∀ inputs, HaltsAt p a inputs) :
    ∀ (h : Trace.Header) (inputs : Array Input), ∃ N, ∀ maxSteps, N ≤ maxSteps → ∃ tr,
      Target.runHarness (loaded a) 0 h inputs p.dropReasons.toArray p.notes.toArray maxSteps = .ok tr ∧
      tr.header = h ∧
      ∃ (i : Nat) (sti : Lang.Sem.St),
        mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
        tr.lines.toList = (List.range inputs.size).flatMap (fun j =>
            ⟨j, Target.inputEvent inputs[j]!⟩ ::
              (sti.world.events.toList.filter (·.1 == j)).map fun x => (⟨j, x.2⟩ : Line)) := by
  intro h inputs
  obtain ⟨i, sti, n, w', hi, hnext, hh, Sn, hw, _⟩ := hall inputs
  obtain ⟨n0, hle, hh0, hfirst⟩ := first_halt (harnessMachine a inputs) n hh
  refine ⟨n0, fun maxSteps hN => ?_⟩
  have hrun : Target.runToHalt maxSteps { loaded a with harness := true, inputs := inputs, program := UInt8.ofNat 0 } =
      .ok (LoopH.mrun n0 (harnessMachine a inputs)) :=
    runToHalt_of n0 maxSteps _ hN hfirst hh0
  obtain ⟨_, S0⟩ := run_sim_of StackH.img a [] n0 _ _ (sim0 a inputs hsz)
  have Sn' := (sim_halted_run (n - n0) _ _ S0 hh0).1
  rw [← Z80Gen.mrun_add, show n0 + (n - n0) = n by omega] at Sn'
  have hev : evsOf StackH.img.ctx (LoopH.mrun n0 (harnessMachine a inputs)).events = sti.world.events := by
    rw [S0.events, ← Sn'.events, Sn.events, hw]
  have htr : trapIn (LoopH.mrun n0 (harnessMachine a inputs)).events = false := by
    rw [← S0.trapped, Sn'.trapped, ← Sn.trapped, hw]
    exact mainIter_trapped 4716 p i _ sti (Lang.Sem.initial_trapped p inputs) hi
  have hd : p.dropReasons.toArray = StackH.img.ctx.dropReasons.toArray := by rw [S.drops]; rfl
  have hn : p.notes.toArray = StackH.img.ctx.notes.toArray := by rw [S.notes]; rfl
  refine ⟨_, runHarness_lines _ h inputs _ _ maxSteps _ hrun, rfl, i, sti, hi, hnext, ?_⟩
  dsimp only
  rw [List.toList_toArray, hd, hn]
  split
  · rename_i ht
    have h2 := trapIn_of_any (fun j e => by cases e <;> simp) ht
    rw [htr] at h2
    cases h2
  · rw [List.append_nil]
    apply flatMap_congr
    intro j _
    have := inputLines_evs StackH.img.ctx inputs (LoopH.mrun n0 (harnessMachine a inputs)).events.toList j
    simp only [Array.toArray_toList] at this
    rw [this, hev]

/-! ## The stack's image as built by default -/

/-- The image `build` makes of the stack by default (with the passes) is `StackD`'s, loaded at 0. -/
def isLoadedD : Bool :=
  match Codegen.build Stack.ir Runtime.harness, assemble StackD.items with
  | .ok img, .ok a => img.origin == 0 && img.bytes.data == a.bytes.data
  | _, _ => false

#guard isLoadedD

theorem romD_le : StackD.asm.bytes.size ≤ 0x8000 := by simpa using romD_size

theorem haltsD (p : Lang.Prog) (S : StackSrc p) : ∀ inputs, HaltsAt p StackD.asm inputs :=
  fun inputs => stackD_halts p S inputs

/-- **The trace the tests print of the stack's image as built by default**: loaded as
`Tools.Z80.machineOf` loads it and run by `Target.runHarness` with the names of the drops and notes of
the program, for any header and input, from some number of steps on the run does not fail, and the
trace has the transmissions and drops of the Spec's trace (`Spec.run`), each with the number of its
input, in order, and the inputs as its input lines. -/
theorem stackD_trace (p : Lang.Prog) (S : StackSrc p) :
    ∃ a : Assembled, assemble StackD.items = .ok a ∧
      ∀ (h : Trace.Header) (inputs : Array Input), ∃ N, ∀ maxSteps, N ≤ maxSteps → ∃ tr,
        Target.runHarness (loaded a) 0 h inputs p.dropReasons.toArray p.notes.toArray maxSteps = .ok tr ∧
        keptLines tr = keptLines (Spec.run {} inputs) ∧
        inputsOf tr = (List.range inputs.size).map fun i => (i, Target.inputEvent inputs[i]!) :=
  ⟨StackD.asm, StackD.assemble_items, trace_of p S StackD.asm romD_le (haltsD p S)⟩

/-- info: 'Ember.Proof.PassSim.Stack.stackD_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackD_trace

/-- **The harness records no trap** running the stack's image as built by default. -/
theorem stackD_no_trap (p : Lang.Prog) (S : StackSrc p) :
    ∃ a : Assembled, assemble StackD.items = .ok a ∧
      ∀ inputs : Array Input, ∃ n0,
        (∀ k, k < n0 → (LoopH.mrun k (harnessMachine a inputs)).cpu.halted = false) ∧
        (LoopH.mrun n0 (harnessMachine a inputs)).cpu.halted = true ∧
        (∀ x ∈ (LoopH.mrun n0 (harnessMachine a inputs)).events, x.2 ≠ .trap) ∧
        ∀ d, (LoopH.mrun (n0 + d) (harnessMachine a inputs)).cpu.halted = true ∧
          (LoopH.mrun (n0 + d) (harnessMachine a inputs)).events = (LoopH.mrun n0 (harnessMachine a inputs)).events :=
  ⟨StackD.asm, StackD.assemble_items, no_trap_of p StackD.asm romD_le (haltsD p S)⟩

/-- info: 'Ember.Proof.PassSim.Stack.stackD_no_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackD_no_trap

/-- **The whole trace the tests print of the stack's image as built by default**: for each input in
turn, its line, then that input's events in the world the Ember semantics leaves when the input is
used up — and nothing else. -/
theorem stackD_trace_lines (p : Lang.Prog) (S : StackSrc p) :
    ∃ a : Assembled, assemble StackD.items = .ok a ∧
      ∀ (h : Trace.Header) (inputs : Array Input), ∃ N, ∀ maxSteps, N ≤ maxSteps → ∃ tr,
        Target.runHarness (loaded a) 0 h inputs p.dropReasons.toArray p.notes.toArray maxSteps = .ok tr ∧
        tr.header = h ∧
        ∃ (i : Nat) (sti : Lang.Sem.St),
          mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          tr.lines.toList = (List.range inputs.size).flatMap (fun j =>
              ⟨j, Target.inputEvent inputs[j]!⟩ ::
                (sti.world.events.toList.filter (·.1 == j)).map fun x => (⟨j, x.2⟩ : Line)) :=
  ⟨StackD.asm, StackD.assemble_items, trace_lines_of p S StackD.asm romD_le (haltsD p S)⟩

/-- info: 'Ember.Proof.PassSim.Stack.stackD_trace_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackD_trace_lines

end Ember.Proof.PassSim.Stack
