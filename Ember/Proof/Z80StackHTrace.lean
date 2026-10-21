import Ember.Proof.Z80StackHMachine
import Ember.Z80.Target

/-!
# Ember.Proof.Z80StackHTrace — the trace the tests print of the stack's image (plan M7.3)

`Target.runHarness` is what the tests run: it steps the machine until
the CPU halts (`Target.runToHalt`, at most `maxSteps` steps) and prints
a trace — each input, then the events the harness recorded for it.

`stackH_trace`: for the image of the stack (`StackH.items` assembled,
loaded as `Tools.Z80.machineOf` loads it), any input and any header,
there is a number of steps from which on `runHarness` gives a trace —
it does not fail for want of steps — whose transmissions and drops,
each with the number of its input, are those of the Spec's trace
(`Spec.run`), and whose input lines are the inputs, in order.

Not in it: the notes of the trace (the harness writes them, the
comparison does not keep them), and the line a trap would add (a note:
that no trap is recorded is not proved).
-/

namespace Ember.Proof.Z80Gen
open Ember Ember.Z80 Ember.Z80.Asm
open Ember.Proof.Refine (kept specKept keep)
open Ember.Proof.Z80Gen.LoopH (Sim mrun harnessMachine step_sim evOf evsOf)
open Ember.Trace (Input Line Event Trace)

/-! ## Until the CPU halts -/

theorem mrun_add : ∀ (n d : Nat) (m : Machine), mrun (n + d) m = mrun d (mrun n m)
  | 0, d, m => by simp [mrun]
  | n + 1, d, m => by
    rw [show n + 1 + d = (n + d) + 1 by omega]
    exact mrun_add n d m.step

theorem runToHalt_of : ∀ (n fuel : Nat) (m : Machine), n ≤ fuel →
    (∀ k, k < n → (mrun k m).cpu.halted = false) → (mrun n m).cpu.halted = true →
    Target.runToHalt fuel m = .ok (mrun n m)
  | 0, fuel, m, _, _, hh => by
    unfold Target.runToHalt
    have hh' : m.cpu.halted = true := hh
    simp [hh', mrun]
  | n + 1, fuel, m, hle, hk, hh => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h0 : m.cpu.halted = false := hk 0 (by omega)
    unfold Target.runToHalt
    simp only [h0, Bool.false_eq_true, if_false]
    exact runToHalt_of n f m.step (by omega) (fun k hk' => hk (k + 1) (by omega)) hh

/-- The first time the CPU is halted. -/
theorem first_halt (m : Machine) : ∀ n, (mrun n m).cpu.halted = true →
    ∃ n0, n0 ≤ n ∧ (mrun n0 m).cpu.halted = true ∧ ∀ k, k < n0 → (mrun k m).cpu.halted = false := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hex : ∃ k, k < n ∧ (mrun k m).cpu.halted = true
    · obtain ⟨k, hk, hkh⟩ := hex
      obtain ⟨n0, h1, h2, h3⟩ := ih k hk hkh
      exact ⟨n0, by omega, h2, h3⟩
    · refine ⟨n, Nat.le_refl _, hn, fun k hk => ?_⟩
      cases h : (mrun k m).cpu.halted
      · rfl
      · exact absurd ⟨k, hk, h⟩ hex

theorem cpu_step_halted (s : Cpu) (inp : UInt16 → UInt8) (h : s.halted = true) :
    s.step inp = ({ s with io := .none, eiDelay := false }.bumpR).tick 4 := by
  unfold Cpu.step
  simp only [h, if_true]

/-- A halted CPU stays halted, and the machine stands for the same world. -/
theorem sim_halted {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) (h : m.cpu.halted = true) :
    Sim c m.step w ∧ m.step.cpu.halted = true := by
  obtain ⟨hc, S1⟩ := step_sim S
  rw [cpu_step_halted m.cpu (hbus w) h] at hc S1
  exact ⟨S1, by rw [hc]; exact h⟩

theorem sim_halted_run {c : IR.Ctx} : ∀ (d : Nat) (m : Machine) (w : HW), Sim c m w → m.cpu.halted = true →
    Sim c (mrun d m) w ∧ (mrun d m).cpu.halted = true
  | 0, _, _, S, h => ⟨S, h⟩
  | d + 1, m, w, S, h => by
    obtain ⟨S1, h1⟩ := sim_halted S h
    exact sim_halted_run d m.step w S1 h1

/-! ## The lines -/

/-- The transmissions and drops of a trace, each with the number of its input. -/
def keptLines (t : Trace) : List (Nat × Event) :=
  t.lines.toList.filterMap fun l => if keep l.ev then some (l.step, l.ev) else none

/-- An input line, with the number of its input. -/
def inputOf (l : Line) : Option (Nat × Event) :=
  match l.ev with
  | .rx b => some (l.step, .rx b)
  | .tick => some (l.step, .tick)
  | _ => none

/-- The input lines of a trace. -/
def inputsOf (t : Trace) : List (Nat × Event) := t.lines.toList.filterMap inputOf

theorem eventLine_evOf (c : IR.Ctx) (e : HEvent) :
    Target.eventLine c.dropReasons.toArray c.notes.toArray e = evOf c e := by
  cases e <;> simp [Target.eventLine, evOf]

/-- The kept lines of an input's lines: its kept events. -/
theorem keep_inputEvent (x : Input) : keep (Target.inputEvent x) = false := by cases x <;> rfl

theorem kept_inputLines (c : IR.Ctx) (inputs : Array Input) (evs : List (Nat × HEvent)) (i : Nat) :
    (Target.inputLines inputs evs c.dropReasons.toArray c.notes.toArray i).filterMap
        (fun l => if keep l.ev then some (l.step, l.ev) else none) =
      ((evsOf c evs.toArray).toList.filter fun x => keep x.2).filter (·.1 == i) := by
  unfold Target.inputLines evsOf
  rw [List.filterMap_cons]
  simp only [keep_inputEvent, Bool.false_eq_true, if_false, List.filterMap_toArray, List.toList_toArray,
    List.filter_filter, eventLine_evOf]
  induction evs with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨j, e⟩ := x
    simp only [beq_iff_eq] at ih ⊢
    by_cases hj : j = i
    · subst hj
      cases hv : evOf c e with
      | none => simp [hv, ih]
      | some v => cases hk : keep v <;> simp [hv, hk, ih]
    · cases hv : evOf c e with
      | none => simp [hv, ih]
      | some v => simp [hv, hj, ih]

theorem flatMap_congr {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ a, a ∈ l → f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: t, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), flatMap_congr fun x hx => h x (by simp [hx])]

theorem flatten_single {α β : Type} (f : α → β) : ∀ l : List α, (l.map fun a => [f a]).flatten = l.map f
  | [] => rfl
  | a :: t => by simp [flatten_single f t]

theorem specKept_ge : ∀ (xs : List Input) (j : Nat) (s : Spec.State) (x : Nat × Event),
    x ∈ specKept xs j s → j ≤ x.1 ∧ x.1 < j + xs.length
  | [], _, _, _, h => by simp [specKept] at h
  | y :: t, j, s, x, h => by
    simp only [specKept, List.mem_append, List.mem_map] at h
    rcases h with ⟨e, _, rfl⟩ | h
    · simp
    · have := specKept_ge t (j + 1) _ x h
      simp only [List.length_cons]
      omega

/-- Grouped by input, in order, the kept lines of the Spec are themselves. -/
theorem specKept_group : ∀ (xs : List Input) (j : Nat) (s : Spec.State),
    (List.range' j xs.length).flatMap (fun i => (specKept xs j s).filter (·.1 == i)) = specKept xs j s
  | [], _, _ => by simp [specKept]
  | y :: t, j, s => by
    rw [List.length_cons, List.range'_succ, List.flatMap_cons]
    have ih := specKept_group t (j + 1) (Spec.step s y).1
    simp only [specKept, List.filter_append]
    have hB : ∀ i, (((Spec.step s y).2.filter keep).map fun e => (j, e)).filter (·.1 == i) =
        if i = j then ((Spec.step s y).2.filter keep).map fun e => (j, e) else [] := by
      intro i
      by_cases hi : i = j
      · subst hi; simp [List.filter_map, Function.comp_def]
      · simp [List.filter_map, Function.comp_def, hi, Ne.symm hi]
    have hR : (specKept t (j + 1) (Spec.step s y).1).filter (·.1 == j) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := specKept_ge t (j + 1) _ x hx
      simp only [beq_iff_eq]
      omega
    rw [hB j, if_pos rfl, hR, List.append_nil]
    congr 1
    refine Eq.trans (flatMap_congr fun i hi => ?_) ih
    have hi' : j + 1 ≤ i := (List.mem_range'_1.mp hi).1
    rw [hB i, if_neg (by omega), List.nil_append]

/-! ## The Spec's trace -/

/-- The steps of `Spec.run`: each input and the events of its step. -/
def stepsFrom : List Input → Spec.State → List (Input × List Event)
  | [], _ => []
  | x :: t, s => (x, (Spec.step s x).2) :: stepsFrom t (Spec.step s x).1

theorem steps_foldl : ∀ (xs : List Input) (s : Spec.State) (acc : Array (Input × List Event)),
    (xs.foldl (fun b a => ((Spec.step b.fst a).fst, b.snd.push (a, (Spec.step b.fst a).snd))) (s, acc)).snd =
      acc ++ (stepsFrom xs s).toArray
  | [], _, acc => by simp [stepsFrom]
  | x :: t, s, acc => by
    rw [List.foldl_cons, steps_foldl t]
    simp [stepsFrom]

theorem flatMap_idx {α β : Type} [Inhabited α] (G : Nat → α → List β) : ∀ (l pre : List α),
    (List.range' pre.length l.length).flatMap (fun a => G a (pre ++ l).toArray[a]!) =
      (l.zipIdx pre.length).flatMap (fun p => G p.2 p.1)
  | [], _ => by simp
  | x :: t, pre => by
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.zipIdx_cons, List.flatMap_cons]
    have h1 : (pre ++ x :: t).toArray[pre.length]! = x := by
      simp
    rw [h1]
    congr 1
    have := flatMap_idx G t (pre ++ [x])
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    exact this

theorem specKept_zip : ∀ (xs : List Input) (j : Nat) (s : Spec.State),
    specKept xs j s = ((stepsFrom xs s).zipIdx j).flatMap (fun p => (p.1.2.filter keep).map fun e => (p.2, e))
  | [], _, _ => by simp [specKept, stepsFrom]
  | x :: t, j, s => by
    simp only [specKept, stepsFrom, List.zipIdx_cons, List.flatMap_cons]
    rw [specKept_zip t (j + 1)]

theorem length_stepsFrom : ∀ (xs : List Input) (s : Spec.State), (stepsFrom xs s).length = xs.length
  | [], _ => rfl
  | _ :: t, s => by simp [stepsFrom, length_stepsFrom t]

theorem filterMap_line (a : Nat) : ∀ (l : List Event),
    (l.map (Line.mk a)).filterMap (fun l => if keep l.ev = true then some (l.step, l.ev) else none) =
      (l.filter keep).map fun e => (a, e)
  | [] => rfl
  | e :: t => by
    cases hk : keep e <;> simp [hk, filterMap_line a t]

theorem foldl_app {β : Type} (f : Nat → List β) : ∀ (r : List Nat) (acc : Array β),
    r.foldl (fun b a => b ++ (f a).toArray) acc = acc ++ (r.flatMap f).toArray
  | [], acc => by simp
  | a :: t, acc => by rw [List.foldl_cons, foldl_app f t]; simp

/-- The kept lines of `Spec.run`. -/
theorem specRun_kept (inputs : Array Input) :
    keptLines (Spec.run {} inputs) =
      specKept inputs.toList 0 (Spec.State.init {}) := by
  simp only [keptLines, Spec.run, Trace.ofSteps, Id.run]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', ← Array.foldl_toList]
  simp only [steps_foldl, foldl_app, Array.empty_append, List.size_toArray]
  show List.filterMap _ (List.flatMap _ _) = _
  rw [List.filterMap_flatMap, specKept_zip]
  have := flatMap_idx (fun a (st : Input × List Event) => ((st.2.filter keep).map fun e => (a, e))) (stepsFrom inputs.toList (Spec.State.init {})) []
  simp only [List.nil_append, List.length_nil] at this
  rw [← this, length_stepsFrom]
  congr 1; funext a
  generalize (stepsFrom inputs.toList _).toArray[a]! = st
  obtain ⟨x, es⟩ := st
  cases x <;> simp only [List.filterMap_cons, keep, Bool.false_eq_true, if_false] <;> exact filterMap_line a es

/-! ## The trace `runHarness` prints -/

/-- The input lines of an input's lines: the input. -/
theorem inputOf_eventLine {dn nn : Array String} {e : HEvent} {v : Event} (i : Nat)
    (h : Target.eventLine dn nn e = some v) : inputOf ⟨i, v⟩ = none := by
  cases e <;> simp only [Target.eventLine, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem inputs_inputLines (inputs : Array Input) (evs : List (Nat × HEvent)) (dn nn : Array String) (i : Nat) :
    (Target.inputLines inputs evs dn nn i).filterMap inputOf = [(i, Target.inputEvent inputs[i]!)] := by
  unfold Target.inputLines
  rw [List.filterMap_cons]
  have h0 : inputOf ⟨i, Target.inputEvent inputs[i]!⟩ = some (i, Target.inputEvent inputs[i]!) := by
    cases inputs[i]! <;> rfl
  simp only [h0, List.cons.injEq, true_and]
  induction evs with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨j, e⟩ := x
    simp only [beq_iff_eq] at ih ⊢
    by_cases hj : j = i
    · subst hj
      cases hv : Target.eventLine dn nn e with
      | none => simp [hv, ih]
      | some v => simp [hv, ih, inputOf_eventLine j hv]
    · simp [hj, ih]

theorem runHarness_lines (m : Machine) (h : Trace.Header) (inputs : Array Input) (dn nn : Array String)
    (maxSteps : Nat) (m' : Machine)
    (hrun : Target.runToHalt maxSteps { m with harness := true, inputs := inputs, program := UInt8.ofNat 0 } = .ok m') :
    Target.runHarness m 0 h inputs dn nn maxSteps =
      .ok { header := h,
            lines := ((List.range inputs.size).flatMap (Target.inputLines inputs m'.events.toList dn nn) ++
              if m'.events.any (fun (j, e) => j < inputs.size && e matches .trap) then
                [(⟨m'.cur, .note "trap (z80)"⟩ : Line)] else []).toArray } := by
  unfold Target.runHarness
  rw [hrun]
  rfl

end Ember.Proof.Z80Gen

namespace Ember.Proof.Z80Gen.StackH
open Ember Ember.Z80 Ember.Z80.Asm
open Ember.Proof.Refine (kept specKept keep)
open Ember.Proof.Z80Gen.LoopH (Sim mrun harnessMachine run_sim_of harness_reset evOf evsOf)
open Ember.Trace (Input Line Event Trace)

/-- The machine `Tools.Z80.machineOf` makes of an image whose bytes are those of `a`. -/
def loaded (a : Assembled) : Machine := { cpu := { (({} : Cpu).load 0 a.bytes) with ramStart := 0x8000 } }

/-- The image `build` makes of the stack without the passes is this one, loaded at 0. -/
def isLoaded : Bool :=
  match Codegen.build Stack.ir Runtime.harness (passes := false), assemble items with
  | .ok img, .ok a => img.origin == 0 && img.bytes.data == a.bytes.data
  | _, _ => false

#guard isLoaded

theorem sim0 (a : Assembled) (inputs : Array Input) (hsz : a.bytes.size ≤ 0x8000) :
    Sim img.ctx (harnessMachine a inputs) ((st0 inputs).world, 0, (0, 0), (0, 0)) := by
  have R := harness_reset a inputs hsz
  exact ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
      rw [R.events]
      rfl, R.nval⟩

/-- **The trace the tests print of the image of the stack**: loaded as
`Tools.Z80.machineOf` loads it and run by `Target.runHarness` with the
names of the drops and notes of the program, for any header and input,
from some number of steps on the run does not fail, and the trace has
the transmissions and drops of the Spec's trace (`Spec.run`), each with
the number of its input, in order, and the inputs as its input lines. -/
theorem stackH_trace (p : Lang.Prog) (S : StackSrc p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ (h : Trace.Header) (inputs : Array Input), ∃ N, ∀ maxSteps, N ≤ maxSteps → ∃ tr,
        Target.runHarness (loaded a) 0 h inputs p.dropReasons.toArray p.notes.toArray maxSteps = .ok tr ∧
        keptLines tr = keptLines (Spec.run {} inputs) ∧
        inputsOf tr = (List.range inputs.size).map fun i => (i, Target.inputEvent inputs[i]!) := by
  obtain ⟨a, ha, hall⟩ := stackH_halts p S
  have hsz : a.bytes.size ≤ 0x8000 := by
    have h := assemble_items
    rw [ha] at h
    cases h
    simpa using rom_size
  refine ⟨a, ha, fun h inputs => ?_⟩
  obtain ⟨_, _, n, w', _, _, hh, Sn, _, hk⟩ := hall inputs
  obtain ⟨n0, hle, hh0, hfirst⟩ := first_halt (harnessMachine a inputs) n hh
  refine ⟨n0, fun maxSteps hN => ?_⟩
  have hrun : Target.runToHalt maxSteps { loaded a with harness := true, inputs := inputs, program := UInt8.ofNat 0 } =
      .ok (mrun n0 (harnessMachine a inputs)) :=
    runToHalt_of n0 maxSteps _ hN hfirst hh0
  -- the events at the first halt: those of the world at the end
  obtain ⟨_, S0⟩ := run_sim_of img a [] n0 _ _ (sim0 a inputs hsz)
  have Sn' := (sim_halted_run (n - n0) _ _ S0 hh0).1
  rw [← mrun_add, show n0 + (n - n0) = n by omega] at Sn'
  have hev : evsOf img.ctx (mrun n0 (harnessMachine a inputs)).events = w'.1.events := by
    rw [S0.events, ← Sn'.events, Sn.events]
  have hkept : ((evsOf img.ctx (mrun n0 (harnessMachine a inputs)).events).toList.filter fun x => keep x.2) =
      specKept inputs.toList 0 (Spec.State.init {}) := by
    rw [hev]; exact hk
  have hd : p.dropReasons.toArray = img.ctx.dropReasons.toArray := by rw [S.drops]; rfl
  have hn : p.notes.toArray = img.ctx.notes.toArray := by rw [S.notes]; rfl
  refine ⟨_, runHarness_lines _ h inputs _ _ maxSteps _ hrun, ?_, ?_⟩
  · rw [specRun_kept, hd, hn]
    unfold keptLines
    simp only [List.toList_toArray, List.filterMap_append, List.filterMap_flatMap]
    have htrap : (if (mrun n0 (harnessMachine a inputs)).events.any (fun (j, e) => j < inputs.size && e matches .trap)
        then [(⟨(mrun n0 (harnessMachine a inputs)).cur, .note "trap (z80)"⟩ : Line)] else []).filterMap
          (fun l => if keep l.ev then some (l.step, l.ev) else none) = [] := by
      split <;> rfl
    rw [htrap, List.append_nil]
    have hblk := fun i => kept_inputLines img.ctx inputs (mrun n0 (harnessMachine a inputs)).events.toList i
    simp only [Array.toArray_toList] at hblk
    simp only [hblk, hkept]
    rw [List.range_eq_range', show inputs.size = inputs.toList.length by simp]
    exact specKept_group inputs.toList 0 _
  · unfold inputsOf
    simp only [List.toList_toArray, List.filterMap_append, List.filterMap_flatMap]
    have htrap : (if (mrun n0 (harnessMachine a inputs)).events.any (fun (j, e) => j < inputs.size && e matches .trap)
        then [(⟨(mrun n0 (harnessMachine a inputs)).cur, .note "trap (z80)"⟩ : Line)] else []).filterMap
          inputOf = [] := by
      split <;> rfl
    rw [htrap, List.append_nil]
    have hi := fun i => inputs_inputLines inputs (mrun n0 (harnessMachine a inputs)).events.toList
      p.dropReasons.toArray p.notes.toArray i
    simp only [hi]
    simp only [List.flatMap]
    exact flatten_single _ _

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_trace

end Ember.Proof.Z80Gen.StackH
