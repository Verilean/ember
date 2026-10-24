import Ember.Proof.Z80WideH
import Ember.Proof.Z80Machine

/-!
# Ember.Proof.Z80WideHSpec — the image of `Ember.Z80.Wide`, against the Ember semantics and on the machine the tests run (plan M7.3)

`wideH_halts`/`wideH_traps` take runs of the IR.  Here they are composed
with the lowering (`lower_iter`, `lower_trap`, M7.1) and carried to
`Ember.Z80.Machine` (`step_sim`, as `Z80Machine` does for the loopback):

* `wideH_spec_halt`, `wideH_harness_halts`: **when `j` calls of `main`
  end in the Ember semantics (`callN k p "main" j` from
  `Lang.Sem.initial p inputs` is `some st'`) and leave no input**, the
  machine — the proofs' machine from reset, and `Machine.step` from the
  machine as the tests build it — halted (`di; halt`) after `i ≤ j`
  calls, standing for the world those `i` calls leave in the Ember
  semantics (the input position, the frame, the events recorded).
* `wideH_spec_trap`, `wideH_harness_trap`: **when `j` calls end and
  the next one, with input remaining, traps in the Ember semantics**,
  the machine gets to the label `rt_trap`, standing for the world of the
  trap — or it halted earlier, the input used up.
* `wideH_harness_trap_halt`: the same, and on from the label, whose
  items are `out (0xD7),a; di; halt; jr rt_trap_l` (`trap_tail`, from the
  image in ROM there, which `Trapped` carries): the trap port written —
  the harness records a trap among its events (`trapIn`), the world
  says so (`trapped`) —, interrupts off (`iff1 = false`), the CPU
  halted.  The machine of the harness has no maskable interrupt (no
  serial input, no tick); that the CPU stays halted is not stated.

What is taken: `WideSrc p` of the Ember program — its computable parts a
`#guard` on `Ember.Z80.Wide.prog.check`; and the calls' ending as the
hypotheses say.  Nothing says that a program on a finite input ends in
the Ember semantics: that is the hypothesis on `callN`.  For the two
inputs of the test it is evaluated below (`#guard`, not proof).  Not
covered: the image as built by default (with the passes on the
assembly), the board's runtime and interrupts, `input.frame`.
-/

namespace Ember.Proof.Z80Gen.WideH
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (callN)
open Ember.Trace (Input)

/-- What is taken of the Ember program. -/
structure WideSrc (p : Lang.Prog) : Prop where
  entry : p.entry = "main"
  framed : p.framed = false
  lowered : IR.lower p = .ok Wide.ir
  okP : progOkB p = true
  okIR : irOkB p layout = true
  drops : p.dropReasons = []
  notes : p.notes = []

-- the parts of `WideSrc` that can be computed, of the checked program (its lowering: `Wide.irIsLowering`)
#guard (Ember.Z80.Wide.prog.check.toOption.map fun q =>
  q.entry == "main" && q.framed == false && progOkB q && irOkB q layout && q.dropReasons == [] && q.notes == []) ==
  some true

theorem ctx_eq (p : Lang.Prog) (S : WideSrc p) : irCtx p Wide.ir layout = img.ctx := by
  unfold irCtx
  rw [S.drops, S.notes]
  rfl

theorem init_eq (p : Lang.Prog) (S : WideSrc p) (inputs : Array Input) :
    irInit p Wide.ir layout inputs = st0 inputs := by
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
theorem lang_ir (p : Lang.Prog) (S : WideSrc p) (inputs : Array Input) (k j : Nat) (st' : Lang.Sem.St)
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
theorem wideH_spec_halt (p : Lang.Prog) (S : WideSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (k j : Nat) (st' : Lang.Sem.St), callN k p "main" j (Lang.Sem.initial p inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i sti s' w', i ≤ j ∧ callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hh⟩ := wideH_halts
  refine ⟨a, addrs, ha, fun inputs s hpc I hhl hrs hsz k j st' hj hex => ?_⟩
  obtain ⟨m, ist', hit, hw⟩ := lang_ir p S inputs k j st' hj
  obtain ⟨i, sti_ir, s', w', hi, hiti, stp, hh1, hif, hw1, hex1⟩ :=
    hh inputs s hpc I hhl hrs hsz j m ist' hit (by rw [hw]; exact hex)
  obtain ⟨sti, hci⟩ := callN_pre k p "main" j i _ st' hj hi
  obtain ⟨m2, isti2, hit2, hw2⟩ := lang_ir p S inputs k i sti hci
  have e := ir_det i _ m m2 _ _ hiti hit2
  subst e
  exact ⟨i, sti, s', w', hi, hci, stp, hh1, hif, by rw [hw1, hw2], by rw [← hw2]; exact hex1⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_spec_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_spec_halt

/-- **Against the Ember semantics: a trap reaches the label `rt_trap`.**
From reset, when `j` calls of `main` end in the Ember semantics and the
next one, with input remaining, traps there, the machine gets to the
label `rt_trap` (`Trapped`: at the label, not halted, the shared bytes
as the IR's state of the trap), holding the world of the trap — or it
halted earlier, the input used up.  Nothing is said of the items after
the label. -/
theorem wideH_spec_trap (p : Lang.Prog) (S : WideSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      (∀ μ, (Zof a addrs μ).OK) ∧
      ∀ (inputs : Array Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (k j : Nat) (st1 st2 : Lang.Sem.St), callN k p "main" j (Lang.Sem.initial p inputs) = some st1 →
          st1.world.next.1 ≠ 0xFFFF → Lang.Sem.call k p st1 "main" [] = .trap st2 →
          (∃ s' w' ist2, WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            w'.1 = st2.world ∧ ist2.world = st2.world ∧ Trapped (Zof a addrs (0, 0)) ist2 s') ∨
          (∃ i sti s' w', i ≤ j ∧ callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hok, ht⟩ := wideH_traps
  refine ⟨a, addrs, ha, hok, fun inputs s hpc I hhl hrs hsz k j st1 st2 hj hne htr => ?_⟩
  obtain ⟨m, ist1, ist2, hit, htrI, hw2⟩ := lower_trap S.lowered layout S.okP S.okIR inputs k j st1 st2
    (by rw [← LoopH.callN_eq p S.entry]; exact hj) (by rw [S.entry]; exact htr)
  rw [ctx_eq p S, init_eq p S] at hit
  rw [ctx_eq p S] at htrI
  have htr' : IR.Sem.callF m img.ctx "main" ist1 = .trap ist2 := htrI
  obtain ⟨m', ist1', hit', hw1⟩ := lang_ir p S inputs k j st1 hj
  have e := ir_det j _ m m' _ _ hit hit'
  subst e
  rcases ht inputs s hpc I hhl hrs hsz j m ist1 ist2 hit (by rw [hw1]; exact hne) htr' with
    ⟨s', w', stp, hw, htp⟩ | ⟨i, sti_ir, s', w', hi, hiti, stp, hh1, hif, hwi, hexi⟩
  · exact Or.inl ⟨s', w', ist2, stp, by rw [hw, hw2], hw2, htp⟩
  · obtain ⟨sti, hci⟩ := callN_pre k p "main" j i _ st1 hj hi
    obtain ⟨m2, isti2, hit2, hw3⟩ := lang_ir p S inputs k i sti hci
    have e2 := ir_det i _ m m2 _ _ hiti hit2
    subst e2
    exact Or.inr ⟨i, sti, s', w', hi, hci, stp, hh1, hif, by rw [hwi, hw3], by rw [← hw3]; exact hexi⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_spec_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_spec_trap

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
theorem wideH_harness_halts (p : Lang.Prog) (S : WideSrc p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ (inputs : Array Input) (k j : Nat) (st' : Lang.Sem.St),
        callN k p "main" j (Lang.Sem.initial p inputs) = some st' → st'.world.next.1 = 0xFFFF →
        ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW), i ≤ j ∧
          callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.halted = true ∧
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧ w'.1 = sti.world := by
  obtain ⟨a, addrs, ha, hspec⟩ := wideH_spec_halt p S
  have hsz := image_small a ha
  refine ⟨a, ha, fun inputs k j st' hj hex => ?_⟩
  have R := LoopH.harness_reset a inputs hsz
  obtain ⟨i, sti, s', w', hi, hci, ⟨n, hn⟩, hh, _, hw, hex'⟩ :=
    hspec inputs _ R.pc R.img R.run R.rs R.msz k j st' hj hex
  obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
  rw [hn] at hc Sn
  exact ⟨i, sti, n, w', hi, hci, hex', by rw [hc]; exact hh, Sn, hw⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_harness_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_harness_halts

/-- **On `Ember.Z80.Machine`, as the tests build it: a trap reaches the
label `rt_trap`.**  When `j` calls of `main` end in the Ember semantics
and the next one, with input remaining, traps: after some number of
`Machine.step`s the CPU is at the label `rt_trap` (`Trapped`), the
machine standing for the world of the trap — or it halted earlier, the
input used up.  Not claimed here (see `wideH_harness_trap_halt`): the write to the trap port (`0xD7`) and the
halt that follow the label. -/
theorem wideH_harness_trap (p : Lang.Prog) (S : WideSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (k j : Nat) (st1 st2 : Lang.Sem.St),
        callN k p "main" j (Lang.Sem.initial p inputs) = some st1 → st1.world.next.1 ≠ 0xFFFF →
        Lang.Sem.call k p st1 "main" [] = .trap st2 →
        (∃ (n : Nat) (w' : HW) (ist2 : IR.Sem.St),
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧ w'.1 = st2.world ∧
          ist2.world = st2.world ∧ Trapped (Zof a addrs (0, 0)) ist2 (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu) ∨
        (∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW), i ≤ j ∧
          callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.halted = true ∧
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧ w'.1 = sti.world) := by
  obtain ⟨a, addrs, ha, _, hspec⟩ := wideH_spec_trap p S
  have hsz := image_small a ha
  refine ⟨a, addrs, ha, fun inputs k j st1 st2 hj hne htr => ?_⟩
  have R := LoopH.harness_reset a inputs hsz
  rcases hspec inputs _ R.pc R.img R.run R.rs R.msz k j st1 st2 hj hne htr with
    ⟨s', w', ist2, ⟨n, hn⟩, hw, hw2, htp⟩ | ⟨i, sti, s', w', hi, hci, ⟨n, hn⟩, hh, _, hw, hex⟩
  · obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
    rw [hn] at hc Sn
    exact Or.inl ⟨n, w', ist2, Sn, hw, hw2, by rw [hc]; exact htp⟩
  · obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
    rw [hn] at hc Sn
    exact Or.inr ⟨i, sti, n, w', hi, hci, hex, by rw [hc]; exact hh, Sn, hw⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_harness_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_harness_trap

/-! ## After the label: the trap port, `di`, `halt`

`rt_trap` is `out (0xD7),a; di; halt; jr rt_trap_l` in the harness's
runtime.  From the label (`Trapped`, the image in ROM there) the three
instructions run as their items say: the write to `0xD7` records the trap
in the world the machine stands for (`hdev`), `di` clears `iff1`, `halt`
halts.  The machine of the harness has no maskable interrupt (no serial
input, no tick, `Sim`), so nothing would take the CPU out of the halt;
that the CPU stays halted is not needed here and not stated. -/

theorem zh_dev (I : ImgIn) (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) (w : HW) (e : IoEvent) :
    (I.ZH a addrs μ).dev w e = hdev I.ctx w e := rfl

/-- The items at `rt_trap`, in the image. -/
def trapItems : List Item :=
  [.label "rt_trap", .ins ⟨.out, [.mem (.num 0xD7), .a]⟩, .label "rt_trap_l", .ins ⟨.di, []⟩, .ins ⟨.halt, []⟩]

theorem trapItems_at : (items.drop 235).take trapItems.length = trapItems := by decide +kernel

theorem trap_idx {j : Nat} (h : items[j]? = some (.label "rt_trap")) : j = 235 := by
  have hall : ∀ j, j < items.length → items[j]? = some (.label "rt_trap") → j = 235 := by decide +kernel
  have hlt : j < items.length := by
    rcases Nat.lt_or_ge j items.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  exact hall j hlt h

/-- **From the label `rt_trap`**: the trap port written (the world says
a trap was recorded), interrupts off, the CPU halted. -/
theorem trap_tail {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} (ok : (Zof a addrs μ).OK) {ist : IR.Sem.St}
    {s : Cpu} (T : Trapped (Zof a addrs μ) ist s) (w : HW) :
    ∃ s3, WSteps (Zof a addrs μ) (s, w) (s3, ({ w.1 with trapped := true }, w.2)) ∧ s3.halted = true ∧
      s3.iff1 = false := by
  obtain ⟨j, hj, hat, hh, _, I⟩ := T
  have hj' := trap_idx hj
  subst hj'
  have H : Has (Zof a addrs μ) 235 trapItems := has_of trapItems_at
  have M : Mach (Zof a addrs μ) s := ⟨I, hh⟩
  have at1 : At (Zof a addrs μ).addrs (235 + 1) s := at_label ok (H.get 0 rfl) hat
  obtain ⟨st1, at2⟩ := wstep_item ok (H.get 1 rfl) M at1 w
    (s' := (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a } : Cpu).tick 11)) (fun ad _ => rfl)
  have M1 : Mach (Zof a addrs μ) (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a } : Cpu).tick 11) :=
    M.sys (by simp only [Sys, skip, zsim, and_self])
  have hdev1 : (Zof a addrs μ).dev w (.write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a) =
      ({ w.1 with trapped := true }, w.2) := by
    have hb : byteOf (215 : Int) = (215 : UInt8) := rfl
    rw [show (Zof a addrs μ).dev w (.write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a) =
      hdev img.ctx w (.write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a) from zh_dev img a addrs μ w _]
    simp [hdev, lo_mk16, hb]
  rw [show (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a } : Cpu).tick 11).io =
      .write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a from rfl, hdev1] at st1
  have at3 := at_label ok (H.get 2 rfl) (at2 rfl)
  generalize hc1 : (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat 0xD7))) (op1 s).a } : Cpu).tick 11) = c1 at st1 M1 at3
  obtain ⟨st2, at4⟩ := wstep_item ok (H.get 3 rfl) M1 at3 ({ w.1 with trapped := true }, w.2)
    (s' := ({ op1 c1 with iff1 := false, iff2 := false } : Cpu).tick 4) (fun ad _ => rfl)
  have M2 : Mach (Zof a addrs μ) (({ op1 c1 with iff1 := false, iff2 := false } : Cpu).tick 4) :=
    M1.sys (by simp only [Sys, zsim, and_self])
  have hq : ∀ c : Cpu, c.io = .none → ∀ w' : HW, (Zof a addrs μ).dev w' c.io = w' := fun c h w' => by
    rw [h]; rfl
  rw [hq _ rfl] at st2
  obtain ⟨st3, _⟩ := wstep_item ok (H.get 4 rfl) M2 (at4 rfl) ({ w.1 with trapped := true }, w.2)
    (s' := ({ op1 (({ op1 c1 with iff1 := false, iff2 := false } : Cpu).tick 4) with halted := true } : Cpu).tick 4)
    (fun ad _ => rfl)
  rw [hq _ rfl] at st3
  exact ⟨_, st1.trans (st2.trans st3), rfl, rfl⟩

/-- **On `Ember.Z80.Machine`, as the tests build it: a trap halts the
machine with the trap recorded.**  When `j` calls of `main` end in the
Ember semantics and the next one, with input remaining, traps there:
after some number of `Machine.step`s the CPU is halted with interrupts
off (`rt_trap`: the write to `0xD7`, `di`, `halt`), the harness has
recorded a trap among its events (`trapIn`), and the machine stands for
the world of the trap with the trap recorded — or it halted earlier, the
input used up. -/
theorem wideH_harness_trap_halt (p : Lang.Prog) (S : WideSrc p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ (inputs : Array Input) (k j : Nat) (st1 st2 : Lang.Sem.St),
        callN k p "main" j (Lang.Sem.initial p inputs) = some st1 → st1.world.next.1 ≠ 0xFFFF →
        Lang.Sem.call k p st1 "main" [] = .trap st2 →
        (∃ (n : Nat) (w' : HW),
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.halted = true ∧
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.iff1 = false ∧
          LoopH.trapIn (LoopH.mrun n (LoopH.harnessMachine a inputs)).events = true ∧
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧
          w'.1 = { st2.world with trapped := true }) ∨
        (∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW), i ≤ j ∧
          callN k p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          (LoopH.mrun n (LoopH.harnessMachine a inputs)).cpu.halted = true ∧
          LoopH.Sim img.ctx (LoopH.mrun n (LoopH.harnessMachine a inputs)) w' ∧ w'.1 = sti.world) := by
  obtain ⟨a, addrs, ha, hok, hspec⟩ := wideH_spec_trap p S
  have hsz := image_small a ha
  refine ⟨a, ha, fun inputs k j st1 st2 hj hne htr => ?_⟩
  have R := LoopH.harness_reset a inputs hsz
  rcases hspec inputs _ R.pc R.img R.run R.rs R.msz k j st1 st2 hj hne htr with
    ⟨s', w', ist2, stp, hw, _, htp⟩ | ⟨i, sti, s', w', hi, hci, ⟨n, hn⟩, hh, _, hw, hex⟩
  · obtain ⟨s3, st3, hh3, hif3⟩ := trap_tail (hok (0, 0)) htp w'
    obtain ⟨n, hn⟩ := stp.trans st3
    obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
    rw [hn] at hc Sn
    refine Or.inl ⟨n, _, by rw [hc]; exact hh3, by rw [hc]; exact hif3, ?_, Sn, by rw [hw]⟩
    rw [← Sn.trapped]
  · obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ (sim0 a inputs hsz)
    rw [hn] at hc Sn
    exact Or.inr ⟨i, sti, n, w', hi, hci, hex, by rw [hc]; exact hh, Sn, hw⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_harness_trap_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_harness_trap_halt

/-! ## The two inputs of the test, in the Ember semantics (evaluated)

What the theorems take of the Ember semantics, for the two inputs of the
test, evaluated (`#guard`: evaluation, not proof) on the checked
program: indices in range — two calls end, no input left, the two frames
`78 79 70`, `78 7a 70` sent; one out of range — the first call ends, the
second, with input remaining, traps. -/

def langTxs (w : Ember.Lang.World) : List (List UInt8) := txs w

#guard match Ember.Z80.Wide.prog.check with
  | .ok q => match callN 1000 q "main" 2 (Lang.Sem.initial q inputsOk) with
    | some st => st.world.next.1 == 0xFFFF && langTxs st.world == [[0x78, 0x79, 0x70], [0x78, 0x7a, 0x70]]
    | none => false
  | .error _ => false

#guard match Ember.Z80.Wide.prog.check with
  | .ok q => match callN 1000 q "main" 1 (Lang.Sem.initial q inputsTrap) with
    | some st => st.world.next.1 != 0xFFFF && langTxs st.world == [[0x78, 0x7a, 0x70]] &&
        (match Lang.Sem.call 1000 q st "main" [] with
         | .trap _ => true
         | _ => false)
    | none => false
  | .error _ => false

end Ember.Proof.Z80Gen.WideH
