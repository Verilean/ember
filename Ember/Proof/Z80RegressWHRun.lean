import Ember.Proof.Z80RegressWH
import Ember.Proof.Z80WideH
import Ember.Proof.Z80BootInit

/-!
# Ember.Proof.Z80RegressWHRun — `regress_wide_store`'s image for the harness, from reset (plan M7.3)

`regressH_run`: the CPU starts at address 0 with the image of
`RegressWH.items` in ROM.  Start-up — the stack pointer, the RAM cleared
by `rt_zero`, **the initial value of `wv` copied from the ROM** — and the
loop that calls `wide_store` are the image's own items, proved
(`boot_zeroed`, `copy_ok`, `Z80Gen.loop_run`); the functions are
`regressH_ok`'s.  For any number of calls of `wide_store` that end in the
IR's semantics from its initial state (`st0`: the memory `IR.initMem`
gives), the machine is at the head of the loop with the world those
calls leave, or it left the loop earlier and stopped with the input used
up.  `regressH_halts`: with no input left it has stopped.
`regressH_traps`: when the next call traps in the IR's semantics, the
machine reaches the label `rt_trap` holding the world of the trap.
`Moves` (a call with input remaining moves the position in the input) is
proved for `wide_store` (`moves`).

What the statements are about, and what they are not: the IR's runs of
`RegressW.ir` and the image `RegressWH.items` assembled, in the machine
of the proofs with the harness's ports — that the IR and items are
`IR.lower`'s and `build`'s is `#guard`.  Not composed with the Ember
semantics of `Regress.p5`, not carried to `Ember.Z80.Machine`, nothing
of the items at `rt_trap` beyond the label, not the image as built by
default.

`bootCheck`, by the kernel: where start-up, the copy, `rt_zero` and the
loop are in the image, the symbols, the bytes of the initial value in
the ROM, the plan's stack and shared bytes.
-/

namespace Ember.Proof.Z80Gen.RegressWH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-! ## Start-up -/

/-- The IR's state the program starts in: the memory `Ember.Z80.IR`
starts with (zero but for the initial value of `wv`, at its address in
RAM), the input still to come. -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout RegressW.ir.globals (ByteArray.mk (Array.replicate 65536 0)),
    world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- `rt_init` of this image: the RAM cleared, the initial value of `wv` copied. -/
def initItems : List Item :=
  initHead ++ copyItems "init_wv" "g_wv" 4 ++ [.ins ⟨.ret, []⟩]

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 8).all isEqu && decide (items[8]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 125).take startItems.length = startItems) &&
  decide ((items.drop 116).take initItems.length = initItems) &&
  decide ((items.drop 226).take zeroItems.length = zeroItems) &&
  decide ((items.drop 129).take mainLoopItems.length = mainLoopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 33 &&
     a.labels.reverse.lookup "rt_idle" == some 32776 &&
     a.labels.reverse.lookup "init_wv" == some 430 && a.labels.reverse.lookup "g_wv" == some 32793 &&
     decide ((List.range 4).map (fun j => a.bytes.data[430 + j]?) = [some 120, some 86, some 52, some 18]) &&
     (match a.labels.reverse.lookup "f_entry" with
      | some e => a.labels.reverse.lookup (fnLabel "wide_store") == some e && decide (e < 65536)
      | none => false)
   | .error _ => false) &&
  !img.plan.wrB "wide_store" 32776 &&
  decide (img.plan.stackLo + img.plan.depthOf "wide_store" ≤ 65534) && decide (img.plan.stackLo ≤ 65532) &&
  (img.plan.data.all fun iv => decide (32777 ≤ iv.1) && decide (iv.2 ≤ 32801))

theorem bootCheck_true : bootCheck = true := by decide +kernel

/-- What `bootCheck` computed, of the image `a`. -/
structure Facts (a : Assembled) : Prop where
  head : ∀ it, it ∈ items.take 8 → isEqu it = true
  jump : items[8]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : (items.drop 125).take startItems.length = startItems
  init : (items.drop 116).take initItems.length = initItems
  zero : (items.drop 226).take zeroItems.length = zeroItems
  loop : (items.drop 129).take mainLoopItems.length = mainLoopItems
  ram : a.labels.reverse.lookup "rt_ram" = some 32768
  ramSize : a.labels.reverse.lookup "rt_ram_size" = some 33
  idle : a.labels.reverse.lookup "rt_idle" = some 32776
  initWv : a.labels.reverse.lookup "init_wv" = some 430
  gWv : a.labels.reverse.lookup "g_wv" = some 32793
  /-- The initial value in the ROM. -/
  rom : (List.range 4).map (fun j => a.bytes.data[430 + j]?) = [some 120, some 86, some 52, some 18]
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel "wide_store") = some e ∧
    e < 65536
  nowr : img.plan.wrB "wide_store" 32776 = false
  room : img.plan.stackLo + img.plan.depthOf "wide_store" ≤ 65534
  slo : img.plan.stackLo ≤ 65532
  data : ∀ iv, iv ∈ img.plan.data → 32777 ≤ iv.1 ∧ iv.2 ≤ 32801

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
    LoopNeed img a 129 32776 "wide_store" RegressW.wide_store := by
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
  Z80Gen.AtLoop img 129 32776 a addrs st s w

/-- A call of `wide_store` with input remaining moves the position in the input. -/
abbrev Moves (m : Nat) (st : IR.Sem.St) : Prop := Z80Gen.Moves img "wide_store" m st

theorem initMem_eq (m : ByteArray) :
    IR.initMem layout RegressW.ir.globals m =
      (((m.set! 32793 120).set! 32794 86).set! 32795 52).set! 32796 18 := rfl

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- The IR's initial memory, byte by byte: `wv` is `0x12345678`, the rest zero. -/
def ival (x : Nat) : UInt8 :=
  if x = 32793 then 120 else if x = 32794 then 86 else if x = 32795 then 52 else if x = 32796 then 18 else 0

theorem st0_get (inputs : Array Ember.Trace.Input) (x : Nat) (hx : x < 65536) :
    (st0 inputs).mem.get! x = ival x := by
  show (IR.initMem _ _ _).get! x = _
  rw [initMem_eq]
  have hsz : (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).size = 65536 := by simp [ByteArray.size]
  by_cases h3 : x = 32796
  · subst h3; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h2 : x = 32795
  · subst h2; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h1 : x = 32794
  · subst h1; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h0 : x = 32793
  · subst h0; rw [getBang_same _ _ _ (by omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega), zeros_get]
  simp [ival, h0, h1, h2, h3]

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
  have hinit : Has (Zof a addrs (0, 0)) 116 initItems := has_of F.init
  have B : BootHead (Zof a addrs (0, 0)) 8 125 116 226 32768 33 :=
    { head := fun i hi => by
        have hlt : i < (items.take 8).length := by
          have : (items.take 8).length = 8 := by decide +kernel
          omega
        have hm := F.head _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 8)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 8)[i] = it at hm hget
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
  -- the initial value of `wv`
  have hc1 : Has (Zof a addrs (0, 0)) (116 + 4) (copyItems "init_wv" "g_wv" (3 + 1)) :=
    has_drop (l1 := initHead) (Has.pre hinit)
  obtain ⟨s8, st8, at8, M8, hsp8, hrs8, hsz8, hcp8, hk8⟩ := copy_ok ok (m := 3) (S := 430) (D := 32793) hc1 F.initWv
    F.gWv (show (32768 : Nat) ≤ 32793 by decide) (by decide) (by decide) (by decide) M7 at7 hrs7 hsz7
  -- ret, to the head of the loop
  have hsp8' : s8.sp.toNat = 65534 := by rw [hsp8]; exact hsp7
  obtain ⟨s9, st9, hpc9, hsp9, hmem9, hh9, hrs9, _, _, _⟩ := ret_raw ok (hinit.get 8 rfl) M8 at8
  have hrom : ∀ j, j < 4 → ∀ b, a.bytes.data[430 + j]? = some b → s7.mem.get! (430 + j) = b := by
    intro j hj b hb
    rw [hkeep _ (Or.inl (by omega)) (by omega)]
    simpa using I.bytes (430 + j) b hb
  have hR := F.rom
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hR
  obtain ⟨r0, r1, r2, r3⟩ := hR
  -- the RAM after start-up
  have hram : ∀ x, 32768 ≤ x → x < 32801 → s8.mem.get! x = ival x := by
    intro x h1 h2
    by_cases hA : 32793 ≤ x ∧ x < 32797
    · obtain ⟨j, rfl⟩ : ∃ j, x = 32793 + j := ⟨x - 32793, by omega⟩
      rw [hcp8 j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rw [hrom 0 (by decide) 120 r0]; rfl
      · rw [hrom 1 (by decide) 86 r1]; rfl
      · rw [hrom 2 (by decide) 52 r2]; rfl
      · rw [hrom 3 (by decide) 18 r3]; rfl
    · rw [hk8 x (by omega), hzero x h1 (by omega)]
      simp [ival, show x ≠ 32793 by omega, show x ≠ 32794 by omega, show x ≠ 32795 by omega,
        show x ≠ 32796 by omega]
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
number `j` of calls of `wide_store` that end in the IR's semantics from
its initial state, the machine gets to the head of the loop with the
world those calls leave, or it left the loop after `i ≤ j` of them and
stopped (`di; halt`) with the world `i` calls leave, the input used up. -/
theorem regressH_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            AtLoop a addrs st' s' w') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := regressH_setting
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit =>
    run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit⟩

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_run

/-- **With the input used up the machine stops** (given `Moves`). -/
theorem regressH_run_halt :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := regressH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit hex => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases Z80Gen.loop_iter (loopNeed ha) hsize hset L m with ⟨_, s2, w2, st2, hh2, hi2, hw2⟩ | ⟨hnex, _⟩
    · exact ⟨j, st', s2, w2, Nat.le_refl _, hit, stp.trans st2, hh2, hi2, hw2, hex⟩
    · exact absurd hex hnex
  · exact hr

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_run_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_run_halt

/-- **A trap, from reset** (given `Moves`): when `j` calls of
`wide_store` end in the IR's semantics and the next one, with input
remaining, traps there, the machine gets to `rt_trap` holding the world
of the trap — or it left the loop earlier and stopped, the input used up. -/
theorem regressH_trap :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      (∀ μ, (Zof a addrs μ).OK) ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' st'' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 ≠ 0xFFFF → IR.Sem.callF m img.ctx "wide_store" st' = .trap st'' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            w'.1 = st''.world ∧ Trapped (Zof a addrs (0, 0)) st'' s') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := regressH_setting
  refine ⟨a, addrs, ha, fun μ => (hset μ).1, fun inputs s hpc I hh hrs hsz j m st' st'' hmv hit hne htr => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases Z80Gen.loop_iter (loopNeed ha) hsize hset L m with ⟨hex, _⟩ | ⟨_, hit2⟩
    · exact absurd hex hne
    · rw [htr] at hit2
      obtain ⟨s2, w2, st2, hw, htrp⟩ := hit2
      exact Or.inl ⟨s2, w2, stp.trans st2, hw, htrp⟩
  · exact Or.inr hr

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_trap

/-! ## `Moves`, proved: a call of `wide_store` with input remaining moves the position

`wide_store` begins with `input.next`; no other instruction of it takes
input or calls, and no label is its first instruction (as `main` of
`Ember.Z80.Wide`: the lemmas on single instructions are `WideH`'s). -/

/-- **From the second instruction on, `wide_store` keeps the world's place in the input.** -/
theorem exec_keep (c : IR.Ctx) : ∀ (k pc : Nat) (tmps : Array Nat) (st : IR.Sem.St) (r : Option Nat)
    (st' : IR.Sem.St), 1 ≤ pc → IR.Sem.exec k c RegressW.wide_store pc tmps st = .ok r st' →
      WideH.Keep st.world st'.world
  | 0, _, _, _, _, _, _, h => by simp [IR.Sem.exec] at h
  | k + 1, pc, tmps, st, r, st', hpc, h => by
    rw [IR.Sem.exec] at h
    cases hb : RegressW.wide_store.body[pc]? with
    | none =>
      rw [hb] at h
      cases h
      exact WideH.Keep.refl _
    | some i =>
      rw [hb] at h
      simp only at h
      have hi : WideH.noIn i = true := by
        have hlt : pc < RegressW.wide_store.body.size := by
          rcases Nat.lt_or_ge pc RegressW.wide_store.body.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none h'] at hb; cases hb
        have hall : ∀ q, q < RegressW.wide_store.body.size → 1 ≤ q → ∀ i, RegressW.wide_store.body[q]? = some i →
            WideH.noIn i = true := by
          decide +kernel
        exact hall pc hlt hpc i hb
      obtain ⟨hn, hc, hst⟩ := WideH.step_keep c st tmps i hi
      cases hs : IR.Sem.step c st tmps i with
      | next st1 tmps1 =>
        rw [hs] at h
        exact (hn st1 tmps1 hs).trans (exec_keep c k (pc + 1) tmps1 st1 r st' (by omega) h)
      | goto l =>
        rw [hs] at h
        simp only at h
        cases hl : IR.Sem.labelAt RegressW.wide_store l with
        | none => rw [hl] at h; cases h
        | some q =>
          rw [hl] at h
          have hq := labelAt_spec hl
          have h1 : 1 ≤ q := by
            rcases Nat.eq_zero_or_pos q with h0 | h0
            · subst h0
              have : RegressW.wide_store.body[0]? =
                  some (.eff .inputNext [] (some (2, .slot { area := .frame "wide_store", off := 0 }))) := rfl
              rw [this] at hq
              cases hq
            · exact h0
          exact exec_keep c k q tmps st r st' h1 h
      | call g st1 ret => exact absurd hs (hc g st1 ret)
      | stop r0 =>
        rw [hs] at h
        simp only at h
        subst h
        rw [hst r st' hs]
        exact WideH.Keep.refl _

/-- **A call of `wide_store`**: it keeps the world reading byte by byte, and, with input remaining, moves its place. -/
theorem fn_call (k : Nat) (st : IR.Sem.St) (r : Option Nat) (st' : IR.Sem.St) (hf : st.world.framed = false)
    (h : IR.Sem.callF k img.ctx "wide_store" st = .ok r st') :
    st'.world.framed = false ∧ (st.world.next.1 ≠ 0xFFFF → (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off)) := by
  match k, h with
  | k1 + 2, h =>
    have hfn : img.ctx.prog.fn? "wide_store" = some RegressW.wide_store := rfl
    simp only [IR.Sem.callF, hfn, IR.Sem.exec] at h
    have hb : RegressW.wide_store.body[0]? =
        some (.eff .inputNext [] (some (2, .slot { area := .frame "wide_store", off := 0 }))) := rfl
    rw [hb] at h
    simp only [IR.Sem.step, IR.Sem.Step.set] at h
    have K := exec_keep img.ctx k1 1 _ _ r st' (Nat.le_refl _) h
    rw [WideH.setRet_world] at K
    obtain ⟨hp, ho, hfr⟩ := K
    refine ⟨by rw [hfr]; exact LoopH.next_framed _ hf, fun hne => ?_⟩
    rw [hp, ho]
    exact LoopH.next_moves _ hf hne
  | 0, h => simp [IR.Sem.callF] at h
  | 1, h =>
    have hfn : img.ctx.prog.fn? "wide_store" = some RegressW.wide_store := rfl
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

/-- info: 'Ember.Proof.Z80Gen.RegressWH.moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms moves

/-! ## The image from reset, with nothing taken -/

/-- **The image for the harness halts when the IR's run ends with the
input used up**: from reset, for any input, when `j` calls of
`wide_store` end in the IR's semantics and leave no input, the machine
stopped (`di; halt`) after `i ≤ j` of them, holding the world those `i`
calls leave with no input left. -/
theorem regressH_halts :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' → st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, h⟩ := regressH_run_halt
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hit hex =>
    h inputs s hpc I hh hrs hsz j m st' (moves inputs m) hit hex⟩

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_halts

/-- **A trap of the IR's run reaches `rt_trap` in the image** — the
label only (`Trapped`: at the label, not halted, the shared bytes as the
IR's, the image in ROM); nothing of the items after it.  From reset,
when `j` calls of `wide_store` end in the IR's semantics and the next
one, with input remaining, traps, the machine gets to `rt_trap` holding
the world of the trap — or it stopped earlier, the input used up. -/
theorem regressH_traps :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      (∀ μ, (Zof a addrs μ).OK) ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' st'' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 ≠ 0xFFFF → IR.Sem.callF m img.ctx "wide_store" st' = .trap st'' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            w'.1 = st''.world ∧ Trapped (Zof a addrs (0, 0)) st'' s') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hok, h⟩ := regressH_trap
  exact ⟨a, addrs, ha, hok, fun inputs s hpc I hh hrs hsz j m st' st'' hit hne htr =>
    h inputs s hpc I hh hrs hsz j m st' st'' (moves inputs m) hit hne htr⟩

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_traps

/-! ## Two inputs, evaluated

What `regressH_halts` and `regressH_traps` take of the IR's run, for two
inputs, is evaluated here (`#guard`: evaluation, not proof). -/

/-- Each byte a call of `wide_store` that ends (the last store's index in range), then no input. -/
def inputsOk : Array Ember.Trace.Input := #[.rx (ByteArray.mk #[1, 2])]

/-- The second byte, 7, is out of range for the last store: the second call traps. -/
def inputsTrap : Array Ember.Trace.Input := #[.rx (ByteArray.mk #[2, 7])]

-- `inputsOk`: two calls end, no input is left, the two frames sent (`regressH_halts`)
#guard match irIter 100 img.ctx 2 (st0 inputsOk) with
  | some st => st.world.next.1 == 0xFFFF && WideH.txs st.world == [[0x78, 0x79, 0x70], [0x78, 0x7a, 0x70]]
  | none => false

-- `inputsTrap`: the first call ends, the second, with input remaining, traps (`regressH_traps`)
#guard match irIter 100 img.ctx 1 (st0 inputsTrap) with
  | some st => st.world.next.1 != 0xFFFF && WideH.txs st.world == [[0x78, 0x7a, 0x70]] &&
      (match IR.Sem.callF 100 img.ctx "wide_store" st with
       | .trap _ => true
       | _ => false)
  | none => false

end Ember.Proof.Z80Gen.RegressWH
