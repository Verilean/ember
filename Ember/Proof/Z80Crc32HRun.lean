import Ember.Proof.Z80Crc32H
import Ember.Proof.Z80WideH
import Ember.Proof.Z80BootInit

/-!
# Ember.Proof.Z80Crc32HRun — `crc32`'s image for the harness, from reset (plan M7.3)

`crc32H_run`: the CPU starts at address 0 with the image of
`Crc32H.items` in ROM.  Start-up — the stack pointer, the RAM cleared by
`rt_zero`, **the initial value of `crc` (`0xFFFFFFFF`) copied from the
ROM** — and the loop that calls `main` are the image's own items, proved
(`boot_zeroed`, `copy_ok`, `Z80Gen.loop_run`); the functions are
`crc32H_ok`'s.  For any number of calls of `main` that end in the IR's
semantics from its initial state (`st0`: the memory `IR.initMem`
gives), the machine is at the head of the loop with the world those
calls leave, or it left the loop earlier and stopped with the input used
up.  `crc32H_halts`: with no input left it has stopped.  `Moves` (a
call with input remaining moves the position in the input) is proved
for `main` (`moves`): its first instruction takes the input, the rest
take none, and the function it calls, `update`, does not touch the
input (`update_keep`).

There is no theorem on traps here: the IR of `crc32` has no instruction
that can trap (no `trap`, no `load`, `store` or `lea`), so a call of
`main` never traps in the IR's semantics (`main_no_trap`), and the image
has no `rt_trap`.

What the statements are about, and what they are not: the IR's runs of
`Crc32.ir` and the image `Crc32H.items` assembled, in the machine of the
proofs with the harness's ports — that the IR and items are
`IR.lower`'s and `build`'s is `#guard`.  Not composed with the Ember
semantics of `crc32`, not carried to `Ember.Z80.Machine`, not the image
as built by default.

`bootCheck`, by the kernel: where start-up, the copy, `rt_zero` and the
loop are in the image, the symbols, the bytes of the initial value in
the ROM, the plan's stack and shared bytes.
-/

namespace Ember.Proof.Z80Gen.Crc32H
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-! ## Start-up -/

/-- The IR's state the program starts in: the memory `Ember.Z80.IR`
starts with (zero but for the initial value of `crc`, at its address in
RAM), the input still to come. -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout Crc32.ir.globals (ByteArray.mk (Array.replicate 65536 0)),
    world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- `rt_init` of this image: the RAM cleared, the initial value of `crc` copied. -/
def initItems : List Item :=
  initHead ++ copyItems "init_crc" "g_crc" 4 ++ [.ins ⟨.ret, []⟩]

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 9).all isEqu && decide (items[9]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 106).take startItems.length = startItems) &&
  decide ((items.drop 97).take initItems.length = initItems) &&
  decide ((items.drop 275).take zeroItems.length = zeroItems) &&
  decide ((items.drop 110).take mainLoopItems.length = mainLoopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 29 &&
     a.labels.reverse.lookup "rt_idle" == some 32776 &&
     a.labels.reverse.lookup "init_crc" == some 483 && a.labels.reverse.lookup "g_crc" == some 32777 &&
     decide ((List.range 4).map (fun j => a.bytes.data[483 + j]?) = [some 255, some 255, some 255, some 255]) &&
     (match a.labels.reverse.lookup "f_entry" with
      | some e => a.labels.reverse.lookup (fnLabel "main") == some e && decide (e < 65536)
      | none => false)
   | .error _ => false) &&
  !img.plan.wrB "main" 32776 &&
  decide (img.plan.stackLo + img.plan.depthOf "main" ≤ 65534) && decide (img.plan.stackLo ≤ 65532) &&
  (img.plan.data.all fun iv => decide (32777 ≤ iv.1) && decide (iv.2 ≤ 32797))

theorem bootCheck_true : bootCheck = true := by decide +kernel

/-- What `bootCheck` computed, of the image `a`. -/
structure Facts (a : Assembled) : Prop where
  head : ∀ it, it ∈ items.take 9 → isEqu it = true
  jump : items[9]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : (items.drop 106).take startItems.length = startItems
  init : (items.drop 97).take initItems.length = initItems
  zero : (items.drop 275).take zeroItems.length = zeroItems
  loop : (items.drop 110).take mainLoopItems.length = mainLoopItems
  ram : a.labels.reverse.lookup "rt_ram" = some 32768
  ramSize : a.labels.reverse.lookup "rt_ram_size" = some 29
  idle : a.labels.reverse.lookup "rt_idle" = some 32776
  initCrc : a.labels.reverse.lookup "init_crc" = some 483
  gCrc : a.labels.reverse.lookup "g_crc" = some 32777
  /-- The initial value in the ROM. -/
  rom : (List.range 4).map (fun j => a.bytes.data[483 + j]?) = [some 255, some 255, some 255, some 255]
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel "main") = some e ∧
    e < 65536
  nowr : img.plan.wrB "main" 32776 = false
  room : img.plan.stackLo + img.plan.depthOf "main" ≤ 65534
  slo : img.plan.stackLo ≤ 65532
  data : ∀ iv, iv ∈ img.plan.data → 32777 ≤ iv.1 ∧ iv.2 ≤ 32797

theorem facts {a : Assembled} (ha : assemble items = .ok a) : Facts a := by
  have hbc := bootCheck_true
  unfold bootCheck at hbc
  rw [ha] at hbc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hbc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, hjump⟩, hstart⟩, hinit⟩, hzero⟩, hloop⟩, hlab⟩, hnowr⟩, hdep⟩, hslo⟩, hdata⟩ := hbc
  obtain ⟨⟨⟨⟨⟨⟨hram, hrsz⟩, hidle⟩, hiw⟩, hgw⟩, hrom⟩, hentry⟩ := hlab
  refine ⟨hhead, hjump, hstart, hinit, hzero, hloop, hram, hrsz, hidle, hiw, hgw, hrom, ?_, hnowr, hdep, hslo, hdata⟩
  cases he : a.labels.reverse.lookup "f_entry" with
  | none => rw [he] at hentry; cases hentry
  | some e =>
    rw [he] at hentry
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hentry
    exact ⟨e, rfl, hentry.1, hentry.2⟩

/-- What the loop needs of the image (`Z80HarnessLoop`). -/
theorem loopNeed {a : Assembled} (ha : assemble items = .ok a) :
    LoopNeed img a 110 32776 "main" Crc32.main := by
  have F := facts ha
  exact
    { loop := F.loop, idle := F.idle, entry := F.entry, nowr := F.nowr, room := F.room
      iaRam := ⟨by decide, by decide⟩
      ram := by decide
      stackHi := rfl
      data := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        omega
      fn := rfl, name := rfl, live := rfl, noreg := rfl, isEntry := rfl }

abbrev AtLoop (a : Assembled) (addrs : List Nat) (st : IR.Sem.St) (s : Cpu) (w : HW) : Prop :=
  Z80Gen.AtLoop img 110 32776 a addrs st s w

/-- A call of `main` with input remaining moves the position in the input. -/
abbrev Moves (m : Nat) (st : IR.Sem.St) : Prop := Z80Gen.Moves img "main" m st

theorem initMem_eq (m : ByteArray) :
    IR.initMem layout Crc32.ir.globals m =
      (((m.set! 32777 255).set! 32778 255).set! 32779 255).set! 32780 255 := rfl

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- The IR's initial memory, byte by byte: `crc` is `0xFFFFFFFF`, the rest zero. -/
def ival (x : Nat) : UInt8 :=
  if 32777 ≤ x ∧ x < 32781 then 255 else 0

theorem st0_get (inputs : Array Ember.Trace.Input) (x : Nat) (hx : x < 65536) :
    (st0 inputs).mem.get! x = ival x := by
  show (IR.initMem _ _ _).get! x = _
  rw [initMem_eq]
  have hsz : (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).size = 65536 := by simp [ByteArray.size]
  by_cases h3 : x = 32780
  · subst h3; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h2 : x = 32779
  · subst h2; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h1 : x = 32778
  · subst h1; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h0 : x = 32777
  · subst h0; rw [getBang_same _ _ _ (by omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega), zeros_get]
  simp only [ival]
  rw [if_neg (by omega)]

theorem st0_size (inputs : Array Ember.Trace.Input) : (st0 inputs).mem.size = 65536 := by
  show (IR.initMem _ _ _).size = _
  rw [initMem_eq, set_size, set_size, set_size, set_size]
  simp [ByteArray.size]

theorem has_drop {Z : ZCtx} {k : Nat} {l1 l2 : List Item} (h : Has Z k (l1 ++ l2)) : Has Z (k + l1.length) l2 :=
  fun j it hj => by
    have := h (l1.length + j) it (by rw [List.getElem?_append_right (by omega)]; simpa using hj)
    rw [show k + l1.length + j = k + (l1.length + j) by omega]
    exact this

/-- **Start-up**: from reset the CPU gets to the head of the loop, its
stack empty, the shared bytes as the IR's initial state has them. -/
theorem boot_loop {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (ok : (Zof a addrs (0, 0)).OK) (inputs : Array Ember.Trace.Input) (s : Cpu) (hpc : s.pc.toNat = 0)
    (I : Img a 0 s) (hh : s.halted = false) (hrs : s.ramStart.toNat = 0x8000) (hsz : s.mem.size = 65536) :
    ∃ s', Steps s s' ∧ AtLoop a addrs (st0 inputs) s' ((st0 inputs).world, 0, (0, 0), (0, 0)) := by
  have F := facts ha
  have hinit : Has (Zof a addrs (0, 0)) 97 initItems := has_of F.init
  have B : BootHead (Zof a addrs (0, 0)) 9 106 97 275 32768 29 :=
    { head := fun i hi => by
        have hlt : i < (items.take 9).length := by
          have : (items.take 9).length = 9 := by decide +kernel
          omega
        have hm := F.head _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 9)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 9)[i] = it at hm hget
        cases it with
        | equ n v => exact ⟨n, v, hget⟩
        | _ => cases hm
      jump := F.jump
      start := has_of F.start
      init := Has.pre (Has.pre hinit)
      zero := has_of F.zero
      ram := F.ram
      ramSize := F.ramSize
      n2 := by decide
      lo := Nat.le_refl _
      hi := by decide
      stackLo := F.slo
      stackHi := rfl
      size := hsize }
  obtain ⟨s7, c3, st7, at7, M7, hsp7, hrs7, hsz7, hzero, hkeep, hmem78, hback⟩ := boot_zeroed ok B hpc I hh hrs hsz
  -- the initial value of `crc`
  have hc1 : Has (Zof a addrs (0, 0)) (97 + 4) (copyItems "init_crc" "g_crc" (3 + 1)) :=
    has_drop (l1 := initHead) (Has.pre hinit)
  obtain ⟨s8, st8, at8, M8, hsp8, hrs8, hsz8, hcp8, hk8⟩ := copy_ok ok (m := 3) (S := 483) (D := 32777) hc1 F.initCrc
    F.gCrc (show (32768 : Nat) ≤ 32777 by decide) (by decide) (by decide) (by decide) M7 at7 hrs7 hsz7
  -- ret, to the head of the loop
  have hsp8' : s8.sp.toNat = 65534 := by rw [hsp8]; exact hsp7
  obtain ⟨s9, st9, hpc9, hsp9, hmem9, hh9, hrs9, _, _, _⟩ := ret_raw ok (hinit.get 8 rfl) M8 at8
  have hrom : ∀ j, j < 4 → ∀ b, a.bytes.data[483 + j]? = some b → s7.mem.get! (483 + j) = b := by
    intro j hj b hb
    rw [hkeep _ (Or.inl (by omega)) (by omega)]
    simpa using I.bytes (483 + j) b hb
  have hR := F.rom
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hR
  obtain ⟨r0, r1, r2, r3⟩ := hR
  -- the RAM after start-up
  have hram : ∀ x, 32768 ≤ x → x < 32797 → s8.mem.get! x = ival x := by
    intro x h1 h2
    by_cases hA : 32777 ≤ x ∧ x < 32781
    · obtain ⟨j, rfl⟩ : ∃ j, x = 32777 + j := ⟨x - 32777, by omega⟩
      rw [hcp8 j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rw [hrom 0 (by decide) 255 r0]; rfl
      · rw [hrom 1 (by decide) 255 r1]; rfl
      · rw [hrom 2 (by decide) 255 r2]; rfl
      · rw [hrom 3 (by decide) 255 r3]; rfl
    · rw [hk8 x (by omega), hzero x h1 (by omega)]
      simp only [ival]
      rw [if_neg (by omega)]
  refine ⟨s9, ((st7.trans st8).trans st9), ?_⟩
  exact
    { at_ := hback s9 (by
        rw [hpc9, cpu_rd16 _ _ (by rw [hsp8']; omega), hsp8']
        exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => by rw [hk8 x (by omega)]; exact hmem78 x h1))
      image := M8.1.congr hrs9 hmem9
      run := by rw [hh9]; exact M8.2
      rs := by rw [hrs9, hrs8]; exact hrs7
      msz := by rw [hmem9]; exact hsz8
      isz := st0_size inputs
      sp := by
        apply UInt16.toNat_inj.mp
        rw [hsp9, UInt16.toNat_add, hsp8']
        rfl
      mem := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        rw [hmem9, hram x (by omega) (by omega), st0_get inputs x (by omega)]
      idle := by rw [hmem9, hram 32776 (by decide) (by decide)]; rfl
      world := rfl
      mark := rfl
      nval := rfl }

/-- From reset to the head of the loop, and the loop. -/
theorem run_core {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (inputs : Array Ember.Trace.Input) (s : Cpu) (hpc : s.pc.toNat = 0) (I : Img a 0 s) (hh : s.halted = false)
    (hrs : s.ramStart.toNat = 0x8000) (hsz : s.mem.size = 65536) (j m : Nat) (st' : IR.Sem.St)
    (hmv : Moves m (st0 inputs)) (hit : irIter m img.ctx j (st0 inputs) = some st') :
    (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
      AtLoop a addrs st' s' w') ∨
    (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
      WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
      s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨ok, _⟩ := hset (0, 0)
  obtain ⟨s1, stb, L0⟩ := boot_loop ha hsize ok inputs s hpc I hh hrs hsz
  rcases Z80Gen.loop_run (loopNeed ha) hsize hset m j (st0 inputs) s1 _ L0 hmv st' hit with
    ⟨s2, w2, stp, L2⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, hh2, hi2, hw2, hex⟩
  · exact Or.inl ⟨s2, w2, (Steps.lift ok stb _).trans stp, L2⟩
  · exact Or.inr ⟨i, sti, s2, w2, hi, hiter, (Steps.lift ok stb _).trans stp, hh2, hi2, hw2, hex⟩

/-- **The image for the harness, from reset**, given `Moves`: for any
number `j` of calls of `main` that end in the IR's semantics from
its initial state, the machine gets to the head of the loop with the
world those calls leave, or it left the loop after `i ≤ j` of them and
stopped (`di; halt`) with the world `i` calls leave, the input used up. -/
theorem crc32H_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            AtLoop a addrs st' s' w') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := crc32H_setting
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit =>
    run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit⟩

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_run

/-- **With the input used up the machine stops** (given `Moves`). -/
theorem crc32H_run_halt :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := crc32H_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit hex => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases Z80Gen.loop_iter (loopNeed ha) hsize hset L m with ⟨_, s2, w2, st2, hh2, hi2, hw2⟩ | ⟨hnex, _⟩
    · exact ⟨j, st', s2, w2, Nat.le_refl _, hit, stp.trans st2, hh2, hi2, hw2, hex⟩
    · exact absurd hex hnex
  · exact hr

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_run_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_run_halt

/-! ## No traps: the IR of `crc32` has no instruction that can trap -/

/-- An instruction whose step cannot trap. -/
def safeI : IR.Instr → Bool
  | .load .. | .store .. | .lea .. | .trap => false
  | _ => true

theorem step_safe (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (i : IR.Instr) (h : safeI i = true)
    (st' : IR.Sem.St) : IR.Sem.step c st tmps i ≠ .stop (.trap st') := by
  intro hs
  cases i <;> simp only [safeI, Bool.false_eq_true] at h <;> simp only [IR.Sem.step, IR.Sem.Step.set] at hs <;>
    (try split at hs) <;> cases hs

/-- The function `g` of a step that calls is the one the instruction names. -/
theorem step_call (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (i : IR.Instr) {g : String} {st1 : IR.Sem.St}
    {ret : Option (Nat × IR.Dst)} (hs : IR.Sem.step c st tmps i = .call g st1 ret) :
    ∃ ret0 reg, i = IR.Instr.call g ret0 reg := by
  cases i with
  | call g0 ret0 reg0 =>
    simp only [IR.Sem.step, IR.Sem.Step.call.injEq] at hs
    exact ⟨ret0, reg0, by rw [hs.1]⟩
  | _ =>
    simp only [IR.Sem.step, IR.Sem.Step.set] at hs <;> (try split at hs) <;> (try split at hs) <;> cases hs

/-- A step that calls keeps the world (it passes the argument in memory). -/
theorem step_call_world (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (i : IR.Instr) {g : String}
    {st1 : IR.Sem.St} {ret : Option (Nat × IR.Dst)} (hs : IR.Sem.step c st tmps i = .call g st1 ret) :
    st1.world = st.world := by
  obtain ⟨ret0, reg, rfl⟩ := step_call c st tmps i hs
  simp only [IR.Sem.step, IR.Sem.Step.call.injEq] at hs
  rw [← hs.2.1]
  split
  · split <;> rfl
  · rfl

/-- **A function whose instructions cannot trap, and whose calls do not trap, does not trap.** -/
theorem exec_safe (c : IR.Ctx) (f : IR.Fn) (hall : ∀ (q : Nat) (i : IR.Instr), f.body[q]? = some i → safeI i = true)
    (hcall : ∀ (q : Nat) (g : String) (ret : Option (Nat × IR.Dst)) (reg : Option (Nat × IR.Opd)),
      f.body[q]? = some (IR.Instr.call g ret reg) → ∀ k st1 st2, IR.Sem.callF k c g st1 ≠ .trap st2) :
    ∀ (k pc : Nat) (tmps : Array Nat) (st st2 : IR.Sem.St), IR.Sem.exec k c f pc tmps st ≠ .trap st2
  | 0, _, _, _, _, h => by simp [IR.Sem.exec] at h
  | k + 1, pc, tmps, st, st2, h => by
    rw [IR.Sem.exec] at h
    cases hb : f.body[pc]? with
    | none => rw [hb] at h; cases h
    | some i =>
      rw [hb] at h
      simp only at h
      cases hs : IR.Sem.step c st tmps i with
      | next st1 tmps1 =>
        rw [hs] at h
        exact exec_safe c f hall hcall k (pc + 1) tmps1 st1 st2 h
      | goto l =>
        rw [hs] at h
        simp only at h
        cases hl : IR.Sem.labelAt f l with
        | none => rw [hl] at h; cases h
        | some q =>
          rw [hl] at h
          exact exec_safe c f hall hcall k q tmps st st2 h
      | call g st1 ret =>
        rw [hs] at h
        simp only at h
        obtain ⟨ret0, reg, hi⟩ := step_call c st tmps i hs
        subst hi
        cases hc : IR.Sem.callF k c g st1 with
        | ok r st3 =>
          rw [hc] at h
          simp only at h
          exact exec_safe c f hall hcall k (pc + 1) _ _ st2 h
        | trap st3 => exact hcall pc g ret0 reg hb k st1 st3 hc
        | fuel => rw [hc] at h; cases h
        | bad => rw [hc] at h; cases h
      | stop r =>
        rw [hs] at h
        simp only at h
        subst h
        exact step_safe c st tmps i (hall pc i hb) st2 hs

theorem update_safe : ∀ (q : Nat) (i : IR.Instr), Crc32.update.body[q]? = some i → safeI i = true ∧
    (∀ (g : String) (ret : Option (Nat × IR.Dst)) (reg : Option (Nat × IR.Opd)), i ≠ IR.Instr.call g ret reg) := by
  have h : ∀ q, q < Crc32.update.body.size → ∀ i, Crc32.update.body[q]? = some i →
      safeI i = true ∧ (match i with | .call .. => false | _ => true) = true := by decide +kernel
  intro q i hq
  have hlt : q < Crc32.update.body.size := by
    rcases Nat.lt_or_ge q Crc32.update.body.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hq; cases hq
  obtain ⟨h1, h2⟩ := h q hlt i hq
  exact ⟨h1, fun g ret reg he => by subst he; cases h2⟩

theorem main_safe : ∀ (q : Nat) (i : IR.Instr), Crc32.main.body[q]? = some i → safeI i = true ∧
    (∀ (g : String) (ret : Option (Nat × IR.Dst)) (reg : Option (Nat × IR.Opd)), i = IR.Instr.call g ret reg →
      g = "update") := by
  have h : ∀ q, q < Crc32.main.body.size → ∀ i, Crc32.main.body[q]? = some i →
      safeI i = true ∧ (match i with | .call g .. => g == "update" | _ => true) = true := by decide +kernel
  intro q i hq
  have hlt : q < Crc32.main.body.size := by
    rcases Nat.lt_or_ge q Crc32.main.body.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hq; cases hq
  obtain ⟨h1, h2⟩ := h q hlt i hq
  exact ⟨h1, fun g ret reg he => by subst he; simpa using h2⟩

theorem update_no_trap (k : Nat) (st st2 : IR.Sem.St) : IR.Sem.callF k img.ctx "update" st ≠ .trap st2 := by
  match k with
  | 0 => simp [IR.Sem.callF]
  | k1 + 1 =>
    have hfn : img.ctx.prog.fn? "update" = some Crc32.update := rfl
    simp only [IR.Sem.callF, hfn]
    exact exec_safe img.ctx Crc32.update (fun q i h => (update_safe q i h).1)
      (fun q g ret reg h => absurd rfl ((update_safe q _ h).2 g ret reg)) k1 0 _ st st2

/-- **A call of `main` never traps in the IR's semantics.** -/
theorem main_no_trap (k : Nat) (st st2 : IR.Sem.St) : IR.Sem.callF k img.ctx "main" st ≠ .trap st2 := by
  match k with
  | 0 => simp [IR.Sem.callF]
  | k1 + 1 =>
    have hfn : img.ctx.prog.fn? "main" = some Crc32.main := rfl
    simp only [IR.Sem.callF, hfn]
    exact exec_safe img.ctx Crc32.main (fun q i h => (main_safe q i h).1)
      (fun q g ret reg h k st1 st3 => by
        rw [(main_safe q _ h).2 g ret reg rfl]
        exact update_no_trap k st1 st3) k1 0 _ st st2

/-- info: 'Ember.Proof.Z80Gen.Crc32H.main_no_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms main_no_trap

/-! ## `Moves`, proved: a call of `main` with input remaining moves the position

`main` begins with `input.next`; no other instruction of it takes input,
and the one call it makes is of `update`, which takes no input and calls
nothing (`update_keep`).  So a call that ends normally has the world's
position where `input.next` left it — moved, when input remained. -/

/-- **`update` keeps the world's place in the input**, from any instruction. -/
theorem update_exec_keep (c : IR.Ctx) : ∀ (k pc : Nat) (tmps : Array Nat) (st : IR.Sem.St) (r : Option Nat)
    (st' : IR.Sem.St), IR.Sem.exec k c Crc32.update pc tmps st = .ok r st' → WideH.Keep st.world st'.world
  | 0, _, _, _, _, _, h => by simp [IR.Sem.exec] at h
  | k + 1, pc, tmps, st, r, st', h => by
    rw [IR.Sem.exec] at h
    cases hb : Crc32.update.body[pc]? with
    | none =>
      rw [hb] at h
      cases h
      exact WideH.Keep.refl _
    | some i =>
      rw [hb] at h
      simp only at h
      have hi : WideH.noIn i = true := by
        have hlt : pc < Crc32.update.body.size := by
          rcases Nat.lt_or_ge pc Crc32.update.body.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none h'] at hb; cases hb
        have hall : ∀ q, q < Crc32.update.body.size → ∀ i, Crc32.update.body[q]? = some i →
            WideH.noIn i = true := by
          decide +kernel
        exact hall pc hlt i hb
      obtain ⟨hn, hc, hst⟩ := WideH.step_keep c st tmps i hi
      cases hs : IR.Sem.step c st tmps i with
      | next st1 tmps1 =>
        rw [hs] at h
        exact (hn st1 tmps1 hs).trans (update_exec_keep c k (pc + 1) tmps1 st1 r st' h)
      | goto l =>
        rw [hs] at h
        simp only at h
        cases hl : IR.Sem.labelAt Crc32.update l with
        | none => rw [hl] at h; cases h
        | some q =>
          rw [hl] at h
          exact update_exec_keep c k q tmps st r st' h
      | call g st1 ret => exact absurd hs (hc g st1 ret)
      | stop r0 =>
        rw [hs] at h
        simp only at h
        subst h
        rw [hst r st' hs]
        exact WideH.Keep.refl _

theorem update_keep (k : Nat) (st : IR.Sem.St) (r : Option Nat) (st' : IR.Sem.St)
    (h : IR.Sem.callF k img.ctx "update" st = .ok r st') : WideH.Keep st.world st'.world := by
  match k, h with
  | 0, h => simp [IR.Sem.callF] at h
  | k1 + 1, h =>
    have hfn : img.ctx.prog.fn? "update" = some Crc32.update := rfl
    simp only [IR.Sem.callF, hfn] at h
    exact update_exec_keep img.ctx k1 0 _ _ r st' h

/-- An instruction of `main` past the first: it takes no input, or it calls `update`. -/
def okI : IR.Instr → Bool
  | .call g _ _ => g == "update"
  | i => WideH.noIn i

/-- **From the second instruction on, `main` keeps the world's place in the input.** -/
theorem exec_keep : ∀ (k pc : Nat) (tmps : Array Nat) (st : IR.Sem.St) (r : Option Nat)
    (st' : IR.Sem.St), 1 ≤ pc → IR.Sem.exec k img.ctx Crc32.main pc tmps st = .ok r st' →
      WideH.Keep st.world st'.world
  | 0, _, _, _, _, _, _, h => by simp [IR.Sem.exec] at h
  | k + 1, pc, tmps, st, r, st', hpc, h => by
    rw [IR.Sem.exec] at h
    cases hb : Crc32.main.body[pc]? with
    | none =>
      rw [hb] at h
      cases h
      exact WideH.Keep.refl _
    | some i =>
      rw [hb] at h
      simp only at h
      have hok : okI i = true := by
        have hlt : pc < Crc32.main.body.size := by
          rcases Nat.lt_or_ge pc Crc32.main.body.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none h'] at hb; cases hb
        have hall : ∀ q, q < Crc32.main.body.size → 1 ≤ q → ∀ i, Crc32.main.body[q]? = some i → okI i = true := by
          decide +kernel
        exact hall pc hlt hpc i hb
      by_cases hci : ∃ (g : String) (ret0 : Option (Nat × IR.Dst)) (reg : Option (Nat × IR.Opd)),
          i = IR.Instr.call g ret0 reg
      · obtain ⟨g, ret0, reg, rfl⟩ := hci
        have hg : g = "update" := by simpa [okI] using hok
        subst hg
        cases hs : IR.Sem.step img.ctx st tmps (IR.Instr.call "update" ret0 reg) with
        | call g' st1 ret =>
          have hw1 := step_call_world img.ctx st tmps _ hs
          have hg' : g' = "update" := by
            have hs' := hs
            simp only [IR.Sem.step, IR.Sem.Step.call.injEq] at hs'
            exact hs'.1.symm
          subst hg'
          rw [hs] at h
          simp only at h
          cases hc : IR.Sem.callF k img.ctx "update" st1 with
          | ok r2 st2 =>
            rw [hc] at h
            simp only at h
            have K1 := update_keep k st1 r2 st2 hc
            have K2 := exec_keep k (pc + 1) _ _ r st' (by omega) h
            rw [WideH.setRet_world] at K2
            rw [hw1] at K1
            exact K1.trans K2
          | trap st2 => rw [hc] at h; cases h
          | fuel => rw [hc] at h; cases h
          | bad => rw [hc] at h; cases h
        | _ => simp [IR.Sem.step] at hs
      · have hi : WideH.noIn i = true := by
          cases i with
          | call g ret0 reg => exact absurd ⟨g, ret0, reg, rfl⟩ hci
          | _ => simpa [okI] using hok
        obtain ⟨hn, hc, hst⟩ := WideH.step_keep img.ctx st tmps i hi
        cases hs : IR.Sem.step img.ctx st tmps i with
        | next st1 tmps1 =>
          rw [hs] at h
          exact (hn st1 tmps1 hs).trans (exec_keep k (pc + 1) tmps1 st1 r st' (by omega) h)
        | goto l =>
          rw [hs] at h
          simp only at h
          cases hl : IR.Sem.labelAt Crc32.main l with
          | none => rw [hl] at h; cases h
          | some q =>
            rw [hl] at h
            have hq := labelAt_spec hl
            have h1 : 1 ≤ q := by
              rcases Nat.eq_zero_or_pos q with h0 | h0
              · subst h0
                have : Crc32.main.body[0]? =
                    some (.eff .inputNext [] (some (2, .slot { area := .frame "main", off := 0 }))) := rfl
                rw [this] at hq
                cases hq
              · exact h0
            exact exec_keep k q tmps st r st' h1 h
        | call g st1 ret => exact absurd hs (hc g st1 ret)
        | stop r0 =>
          rw [hs] at h
          simp only at h
          subst h
          rw [hst r st' hs]
          exact WideH.Keep.refl _

/-- **A call of `main`**: it keeps the world reading byte by byte, and, with input remaining, moves its place. -/
theorem fn_call (k : Nat) (st : IR.Sem.St) (r : Option Nat) (st' : IR.Sem.St) (hf : st.world.framed = false)
    (h : IR.Sem.callF k img.ctx "main" st = .ok r st') :
    st'.world.framed = false ∧ (st.world.next.1 ≠ 0xFFFF → (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off)) := by
  match k, h with
  | k1 + 2, h =>
    have hfn : img.ctx.prog.fn? "main" = some Crc32.main := rfl
    simp only [IR.Sem.callF, hfn, IR.Sem.exec] at h
    have hb : Crc32.main.body[0]? =
        some (.eff .inputNext [] (some (2, .slot { area := .frame "main", off := 0 }))) := rfl
    rw [hb] at h
    simp only [IR.Sem.step, IR.Sem.Step.set] at h
    have K := exec_keep k1 1 _ _ r st' (Nat.le_refl _) h
    rw [WideH.setRet_world] at K
    obtain ⟨hp, ho, hfr⟩ := K
    refine ⟨by rw [hfr]; exact LoopH.next_framed _ hf, fun hne => ?_⟩
    rw [hp, ho]
    exact LoopH.next_moves _ hf hne
  | 0, h => simp [IR.Sem.callF] at h
  | 1, h =>
    have hfn : img.ctx.prog.fn? "main" = some Crc32.main := rfl
    simp [IR.Sem.callF, hfn, IR.Sem.exec] at h

theorem iter_framed (m : Nat) : ∀ (i : Nat) (st sti : IR.Sem.St), st.world.framed = false →
    irIter m img.ctx i st = some sti → sti.world.framed = false
  | 0, st, sti, hf, h => by cases h; exact hf
  | i + 1, st, sti, hf, h => by
    rw [irIter] at h
    cases hc : IR.Sem.callF m img.ctx img.ctx.prog.entry st with
    | ok r st1 =>
      rw [hc] at h
      exact iter_framed m i st1 sti (fn_call m st r st1 hf hc).1 h
    | _ => rw [hc] at h; cases h

/-- **`Moves`, for any input.** -/
theorem moves (inputs : Array Ember.Trace.Input) (m : Nat) : Moves m (st0 inputs) := by
  intro i sti r sti' hi hc hne
  exact (fn_call m sti r sti' (iter_framed m i (st0 inputs) sti rfl hi) hc).2 hne

/-- info: 'Ember.Proof.Z80Gen.Crc32H.moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms moves

/-! ## The image from reset, with nothing taken -/

/-- **The image for the harness halts when the IR's run ends with the
input used up**: from reset, for any input, when `j` calls of `main`
end in the IR's semantics and leave no input, the machine stopped (`di;
halt`) after `i ≤ j` of them, holding the world those `i` calls leave
with no input left. -/
theorem crc32H_halts :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' → st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, h⟩ := crc32H_run_halt
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hit hex =>
    h inputs s hpc I hh hrs hsz j m st' (moves inputs m) hit hex⟩

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_halts

end Ember.Proof.Z80Gen.Crc32H
