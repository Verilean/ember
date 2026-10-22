import Ember.Proof.Z80PassCertDOK
import Ember.Proof.Z80PassMaster
import Ember.Proof.Z80StackHMachine

/-!
# Ember.Proof.Z80PassStack — the stack's image as built by default, on the machine the tests run (plan M7.3)

`stackD_halts`: the image the assembler makes of `StackD.items` (the
stack as `build` makes it by default, with the passes on the assembly),
loaded into `Ember.Z80.Machine` as the tests load it for the harness and
stepped by `Machine.step`, for any input, **given `SafeA` of the image
without the passes** (`StackH`) on that input: after some number of
steps the CPU is halted and the machine stands for a world with no input
left whose transmissions and drops are those of `Spec.step` — what
`stackH_halts` says of `StackH`.

How: `StackH`'s run halts (`stackH_spec_halt`); the two images run side
by side in the harness's devices (`hD`) keep the relation of the
certificate (`certD_ok`, `passes_halt`), so `StackD`'s run halts with the
same devices; and `Machine.step` is that run (`run_sim_of`).

What is taken, not proved: `SafeA` (`Z80PassMaster`), a statement about
`StackH`'s run alone — the stack above `hi + 4`, the bytes read and
written through `HL`, `DE` in the RAM `[lo, hi)` — at every item of the
certificate's meeting points it reaches (not inside the routines of the
runtime and the copies of literals, which read the ROM).  The proofs of
`StackH` do not give it yet; `ember-passcert --safe` tries it on the
fixtures.
-/

namespace Ember.Proof.PassSim.Stack
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim Ember.Proof.PassSim Ember.Proof.Z80Gen
open Ember.Proof.Refine (mainIter kept specKept)
open Ember.Proof.Z80Gen.LoopH (Sim harnessMachine harness_reset run_sim_of)
open Ember.Trace (Input)

/-- The devices of the harness, as `Dev`. -/
def hD : Dev := ⟨HW, hbus, hdev StackH.img.ctx, fun _ => rfl⟩

/-- A run of the proofs' machine in the harness is a run in `hD`. -/
theorem wrun_hD (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) :
    ∀ (n : Nat) (x : Cpu × HW), wrun (StackH.img.ZH a addrs μ) n x = PassSim.mrun hD n x
  | 0, _ => rfl
  | n + 1, x => wrun_hD a addrs μ n _

/-- `StackH` as a `Code`. -/
noncomputable def codeH : Code :=
  ⟨StackH.items, StackH.asm, Classical.choose (placed_of_assemble StackH.assemble_items),
    Classical.choose_spec (placed_of_assemble StackH.assemble_items)⟩

/-- `StackD` as a `Code`. -/
noncomputable def codeD : Code :=
  ⟨StackD.items, StackD.asm, Classical.choose (placed_of_assemble StackD.assemble_items),
    Classical.choose_spec (placed_of_assemble StackD.assemble_items)⟩

theorem romD_size : decide (StackD.asm.bytes.size ≤ 0x8000) = true := by decide +kernel

/-- The world the harness starts in. -/
def w0 (inputs : Array Input) : HW := ((StackH.st0 inputs).world, 0, (0, 0), (0, 0))

/-- `StackH`'s run from the start, in the harness. -/
def x0 (inputs : Array Input) : Cpu × HW := ((harnessMachine StackH.asm inputs).cpu, w0 inputs)

/-- `StackD`'s run from the start, in the harness. -/
def y0 (inputs : Array Input) : Cpu × HW := ((harnessMachine StackD.asm inputs).cpu, w0 inputs)

/-! ## The two machines at the start -/

theorem load_zero (bytes m0 : ByteArray) (hz : ∀ x, m0.get! x = 0) :
    ∀ n x, n ≤ x → ((List.range n).foldl (fun m k => if 0 + k < 65536 then m.set! (0 + k) bytes[k]! else m) m0).get! x = 0
  | 0, x, _ => hz x
  | n + 1, x, h => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add]
    split
    · rw [getBang_set _ _ _ _ (by omega)]
      simpa using load_zero bytes m0 hz n x (by omega)
    · simpa using load_zero bytes m0 hz n x (by omega)

theorem zero_mem (x : Nat) : (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).get! x = 0 := by
  simp only [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  by_cases h : x < 65536
  · simp [h]
  · simp [h]; rfl

/-- The CPU at reset with an image of at most `0x8000` bytes: the RAM zero. -/
theorem reset_ram (a : Assembled) (inputs : Array Input) (hsz : a.bytes.size ≤ 0x8000) (x : Nat) (hx : 0x8000 ≤ x) :
    (harnessMachine a inputs).cpu.mem.get! x = 0 :=
  load_zero a.bytes _ zero_mem a.bytes.size x (by omega)

/-- **The two machines at the start, related**: at their first items, `H`, `L` the same, empty stacks. -/
theorem sync0 (inputs : Array Input) :
    Sync hD codeH codeD CertD.lo CertD.hi [] 0 0 false false (x0 inputs) (y0 inputs) := by
  have hszH : StackH.asm.bytes.size ≤ 0x8000 := by simpa using StackH.rom_size
  have hszD : StackD.asm.bytes.size ≤ 0x8000 := by simpa using romD_size
  have RH := harness_reset StackH.asm inputs hszH
  have RD := harness_reset StackD.asm inputs hszD
  have pH := codeH.placed
  have pD := codeD.placed
  refine ⟨⟨0, pH.1, RH.pc⟩, ⟨0, pD.1, RD.pc⟩, ⟨RH.img, RH.run⟩, ⟨RD.img, RD.run⟩, ?_, ?_, RH.msz, ?_, rfl⟩
  · apply EqvT.of_eqv
    refine ⟨rfl, fun x h1 _ => ?_, ?_⟩
    · have h1' : 0x8000 ≤ x := by simp [CertD.lo] at h1; omega
      show (harnessMachine StackH.asm inputs).cpu.mem.get! x = (harnessMachine StackD.asm inputs).cpu.mem.get! x
      rw [reset_ram _ _ hszH x h1', reset_ram _ _ hszD x h1']
    · show (harnessMachine StackH.asm inputs).cpu.mem.size = (harnessMachine StackD.asm inputs).cpu.mem.size
      rw [RH.msz, RD.msz]
  · show Stk codeH codeD CertD.hi [] (top (harnessMachine StackH.asm inputs).cpu.sp)
      (top (harnessMachine StackD.asm inputs).cpu.sp) _ _
    exact ⟨rfl, rfl⟩
  · show (harnessMachine StackH.asm inputs).cpu.ramStart.toNat ≤ CertD.lo
    rw [RH.rs]; decide

/-! ## The facts the theorem takes -/

theorem symVal_acc : symVal StackH.asm "rt_acc" = some 32768 ∧ symVal StackD.asm "rt_acc" = some 32768 := by
  constructor <;> decide +kernel

/-- **What the theorem takes, for the stack's images**, from `SafeA` of `StackH`'s run. -/
theorem glob (inputs : Array Input) (hs : SafeA hD codeH CertD.lo CertD.hi CertD.rows (x0 inputs)) :
    Glob hD codeH codeD CertD.lo CertD.hi CertD.rows CertD.tr (x0 inputs) where
  chk := CertD.certD_ok
  safe := hs
  hlo := by decide
  h1 := by decide
  hhi := by decide
  acc := by
    refine ⟨32768, fun pa => ?_, fun pb => ?_, by decide, by decide⟩
    · rw [val_sym _ _ 0 32768 (by rw [env_resolve]; exact symVal_acc.1)]; rfl
    · rw [val_sym _ _ 0 32768 (by rw [env_resolve]; exact symVal_acc.2)]; rfl

/-! ## The theorem -/

/-- **The stack's image as built by default, loaded and run as the tests do, processes all its input
and stops, having transmitted and dropped what the Spec does** — given `SafeA` of the image without
the passes on that input.  For any input with `SafeA`: after some number of `Machine.step`s the CPU of
`StackD`'s image is halted, and the machine stands for the world that some number of calls of `main`
leave in the Ember semantics, with no input left; its kept lines — transmissions and drops, each with
the number of its input — are those of `Spec.step`. -/
theorem stackD_halts (p : Lang.Prog) (S : StackH.StackSrc p) (inputs : Array Input)
    (hs : SafeA hD codeH CertD.lo CertD.hi CertD.rows (x0 inputs)) :
    ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW),
      mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
      (LoopH.mrun n (harnessMachine StackD.asm inputs)).cpu.halted = true ∧
      Sim StackH.img.ctx (LoopH.mrun n (harnessMachine StackD.asm inputs)) w' ∧ w'.1 = sti.world ∧
      kept w'.1 = specKept inputs.toList 0 (Spec.State.init {}) := by
  obtain ⟨a, addrs, ha, hspec⟩ := StackH.stackH_spec_halt p S
  have haH : a = StackH.asm := by
    have h := StackH.assemble_items
    rw [ha] at h; cases h; rfl
  subst haH
  have hszH : StackH.asm.bytes.size ≤ 0x8000 := by simpa using StackH.rom_size
  have hszD : StackD.asm.bytes.size ≤ 0x8000 := by simpa using romD_size
  have RH := harness_reset StackH.asm inputs hszH
  have RD := harness_reset StackD.asm inputs hszD
  obtain ⟨i, sti, s', w', hi, hex, ⟨n, hn⟩, hh, _, hw, hk⟩ := hspec inputs _ RH.pc RH.img RH.run RH.rs RH.msz
  -- `StackH`'s run halts after `n` steps, in `hD`
  have hnH : PassSim.mrun hD n (x0 inputs) = (s', w') := by
    rw [← wrun_hD StackH.asm addrs (0, 0)]; exact hn
  obtain ⟨M, hM, hMw⟩ := passes_halt (glob inputs hs) (sync0 inputs) n (by rw [hnH]; exact hh)
  rw [hnH] at hMw
  -- `StackD`'s machine is that run
  have S0 : Sim StackH.img.ctx (harnessMachine StackD.asm inputs) (w0 inputs) :=
    ⟨RD.harness, RD.noRx, RD.rdrf, RD.tick, RD.prog, RD.inputs, RD.pos, RD.off, RD.cur, RD.latch, RD.mark, RD.frame,
      rfl, by rw [RD.events]; rfl, RD.nval, by rw [RD.events]; show false = _; simp [LoopH.trapIn]⟩
  obtain ⟨hc, Sn⟩ := run_sim_of StackH.img StackH.asm addrs M _ _ S0
  have hy : wrun (StackH.img.ZH StackH.asm addrs (0, 0)) M ((harnessMachine StackD.asm inputs).cpu, w0 inputs) =
      PassSim.mrun hD M (y0 inputs) := wrun_hD StackH.asm addrs (0, 0) M _
  rw [hy] at hc Sn
  rw [hMw] at Sn
  exact ⟨i, sti, M, w', hi, hex, by rw [hc]; exact hM, Sn, hw, hk⟩

/-- info: 'Ember.Proof.PassSim.Stack.stackD_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackD_halts

end Ember.Proof.PassSim.Stack
