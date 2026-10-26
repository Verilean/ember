import Ember.Proof.Z80StackHSpec
import Ember.Proof.Z80Machine

/-!
# Ember.Proof.Z80StackHMachine — the image of the stack on the machine the tests run (plan M7.3)

`stackH_halts`: the image the assembler makes of `StackH.items`, loaded
into `Ember.Z80.Machine` as the tests load it for the harness
(`harnessMachine`) and stepped by `Machine.step`, for any input: after
some number of steps the CPU is halted, and the machine stands for a
world (`Sim`: the input position, the frame, the events recorded — a
drop by the name of its reason, a note by its name and value) with no
input left, whose transmissions and drops are those of `Spec.step`,
input by input.

`stackH_spec_halt` (the proofs' machine against the Spec) and
`step_sim` (a step of `Machine` in harness mode is a step of the proofs'
machine).

What it is not: `Target.runHarness` — the loop of the tests until
`halted`, and the trace it prints from the machine's events — is not in
the theorem (it is in `stackH_trace`, `Z80StackHTrace`); nor is the
image as built by default (with the passes on the assembly), nor a board.
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (mainIter kept specKept)
open Ember.Proof.Z80Gen.LoopH (Sim mrun harnessMachine harness_reset run_sim_of)
open Ember.Trace (Input)

set_option maxRecDepth 100000

theorem rom_size : decide (asm.bytes.size ≤ 0x8000) = true := by decide +kernel

/-- **The image of the stack, loaded and run as the tests do, processes
all its input and stops, having transmitted and dropped what the Spec
does.**  For any input: after some number of `Machine.step`s the CPU is
halted (`di; halt`), and the machine stands for the world that some
number of calls of `main` leave in the Ember semantics, with no input
left; the kept lines of that world — transmissions and drops, each with
the number of its input — are those of `Spec.step`. -/
theorem stackH_halts (p : Lang.Prog) (S : StackSrc p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ inputs : Array Input, ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW),
        mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
        (mrun n (harnessMachine a inputs)).cpu.halted = true ∧
        Sim img.ctx (mrun n (harnessMachine a inputs)) w' ∧ w'.1 = sti.world ∧
        kept w'.1 = specKept inputs.toList 0 (Spec.State.init {}) := by
  obtain ⟨a, addrs, ha, hspec⟩ := stackH_spec_halt p S
  have hsz : a.bytes.size ≤ 0x8000 := by
    have h := assemble_items
    rw [ha] at h
    cases h
    simpa using rom_size
  refine ⟨a, ha, fun inputs => ?_⟩
  have R := harness_reset a inputs hsz
  have S0 : Sim img.ctx (harnessMachine a inputs) ((st0 inputs).world, 0, (0, 0), (0, 0)) :=
    ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
      rw [R.events]
      rfl, R.nval, by rw [R.events]; show false = _; simp [LoopH.trapIn]⟩
  obtain ⟨i, sti, s', w', hi, hex, ⟨n, hn⟩, hh, _, hw, hk⟩ := hspec inputs _ R.pc R.img R.run R.rs R.msz
  obtain ⟨hc, Sn⟩ := run_sim_of img a addrs n _ _ S0
  have hn' : wrun (img.ZH a addrs (0, 0)) n ((harnessMachine a inputs).cpu, ((st0 inputs).world, 0, (0, 0), (0, 0))) =
      (s', w') := hn
  rw [hn'] at hc Sn
  exact ⟨i, sti, n, w', hi, hex, by rw [hc]; exact hh, Sn, hw, hk⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_halts

end Ember.Proof.Z80Gen.StackH
