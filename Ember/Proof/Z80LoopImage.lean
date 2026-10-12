import Ember.Proof.Z80LoopItems

/-!
# Ember.Proof.Z80LoopImage — the loopback image: its functions do what the IR's do (plan M7.3)

`loop_image_ok`: in the image the assembler makes of `Loop.items` — the
loopback program for the board, without the passes on the assembly —
every function, entered as `Entry` says, returns as `IR.Sem.callF` does
with the machine standing for the world it leaves, or reaches `rt_trap`.

What `loop_ok` took of the image is computed here by the kernel
(`imageCheck`): the assembler accepts the items (so they are placed,
`assemble_ok`), the areas of the layout have their symbols, the items
`genProg` gives are in the image, `rt_trap` is there, and no instruction
names `rt_acc`.

What is still taken: of the machine around the CPU, that an instruction
without I/O leaves it alone; of the runtime, `RtOK` — the specifications
of the routines this image calls (`rt_bound` and the routines of the
effects).  And the theorem is of the functions: start-up, the interrupt
routine and the loop that calls `main` are not in it.
-/

namespace Ember.Proof.Z80Gen.Loop
open Ember.Z80 Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

/-- Where the generated items start in the image: after the names and the vectors. -/
def genOff : Nat := 26

/-- The instruction does not name the accumulator. -/
def noAcc : Item → Bool
  | .ins i =>
    (match i.immVal? with
     | some (.sym s _) => s != "rt_acc"
     | _ => true)
  | _ => true

def imageCheck : Bool :=
  match assemble items, genProg ir false (sharedBytes ir) with
  | .ok a, .ok c =>
    (layout.globals.all fun e => a.labels.reverse.lookup (areaSym (.global e.1)) == some e.2) &&
    (layout.frames.all fun e => a.labels.reverse.lookup (areaSym (.frame e.1)) == some e.2) &&
    decide ((items.drop genOff).take c.items.length = c.items) &&
    items.any (isLab "rt_trap") && items.all noAcc
  | _, _ => false

theorem imageCheck_true : imageCheck = true := by decide +kernel

/-- **The functions of the loopback image do what the IR's functions do.** -/
theorem loop_image_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (W : Type) (bus : W → UInt16 → UInt8) (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop),
        (∀ w, dev w .none = w) →
        RtOK (plan.toZ { items, a, addrs, W, bus, dev, wrel }) →
        ∀ k g st1, Callee (plan.toZ { items, a, addrs, W, bus, dev, wrel }) g st1 (IR.Sem.callF k ctx g st1) := by
  have h := imageCheck_true
  unfold imageCheck at h
  cases ha : assemble items with
  | error e => rw [ha] at h; cases h
  | ok a =>
    cases hg : genProg ir false (sharedBytes ir) with
    | error e => rw [ha, hg] at h; cases h
    | ok c =>
      rw [ha, hg] at h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hglob, hfr⟩, hsub⟩, htrap⟩, hnoacc⟩ := h
      obtain ⟨addrs, hpl⟩ := placed_of_assemble ha
      refine ⟨a, addrs, rfl, fun W bus dev wrel quiet hrt => ?_⟩
      have hitems : ∀ (j : Nat) it, c.items[j]? = some it → items[genOff + j]? = some it := by
        intro j it hj
        have hlt : j < c.items.length := by
          rcases Nat.lt_or_ge j c.items.length with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none h'] at hj; cases hj
        rw [← hsub, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
        exact hj
      refine loop_ok { items, a, addrs, W, bus, dev, wrel } hpl quiet (fun ar ad har => ?_) (fun href => ?_) hrt hg
        hitems ?_
      · cases ar with
        | global g => exact hglob (g, ad) (lookup_mem har)
        | frame f => exact hfr (f, ad) (lookup_mem har)
      · obtain ⟨k, i, off, hk, hi⟩ := href
        have := hnoacc _ (List.mem_of_getElem? hk)
        simp [noAcc, hi] at this
      · obtain ⟨it, hm, hi⟩ := List.any_eq_true.mp htrap
        obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hm
        cases it with
        | label x =>
          have : x = "rt_trap" := by simpa [isLab] using hi
          subst this
          exact ⟨j, by rw [List.getElem?_eq_getElem hj, hget]⟩
        | _ => cases hi

/-- info: 'Ember.Proof.Z80Gen.Loop.loop_image_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_image_ok

end Ember.Proof.Z80Gen.Loop
