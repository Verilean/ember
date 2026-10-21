import Ember.Proof.Z80StackH
import Ember.Proof.Z80HarnessLoop
import Ember.Proof.Z80BootInit

/-!
# Ember.Proof.Z80StackHRun — the image of the stack for the harness, from reset (plan M7.3)

`stackH_run`: the CPU starts at address 0 with the image in ROM.
Start-up — the stack pointer, the RAM cleared by `rt_zero`, **the
initial values of `iss` and `ip_id` copied from the ROM** — and the
loop that calls `main` are the image's own items, proved (`boot_zeroed`,
`copy_ok`, `Z80Gen.loop_run`).  For any number of calls of `main` that
end in the IR's semantics from its initial state (`st0`: the memory
`IR.initMem` gives), the machine is at the head of the loop with the
world those calls leave, or it left the loop earlier and stopped with
the input used up.  `stackH_run_halt`: with no input left it has
stopped.

What is taken: `Moves` — a call of `main` with input remaining moves
the position in the input (so the loop is not left by its count of idle
calls).  It is a property of the program, not proved here.  And the
statement is about the IR's calls: that they end, and what they
transmit (the Spec, `stack_ir`), is not composed with it here; nor is
it carried to `Ember.Z80.Machine`, the machine the tests run.

`runCheck`, by the kernel: where start-up, the copies, `rt_zero` and
the loop are in the image, the symbols, the bytes of the initial values
in the ROM, the plan's stack and shared bytes, and which globals have
an initial value.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

/-! ## The initial memory of the IR -/

theorem storeBytes_size : ∀ (bs : List UInt8) (m : ByteArray) (a : Nat), (IR.storeBytes m a bs).size = m.size
  | [], _, _ => rfl
  | b :: bs, m, a => by rw [IR.storeBytes, storeBytes_size bs, set_size]

theorem storeBytes_far : ∀ (bs : List UInt8) (m : ByteArray) (a x : Nat), x < a ∨ a + bs.length ≤ x →
    (IR.storeBytes m a bs).get! x = m.get! x
  | [], _, _, _, _ => rfl
  | b :: bs, m, a, x, h => by
    rw [IR.storeBytes, storeBytes_far bs _ _ x (by simp only [List.length_cons] at h; omega),
      getBang_set _ _ _ _ (by simp only [List.length_cons] at h; omega)]

/-- The initial values, with their addresses. -/
def initsOf (l : IR.Layout) (gs : List IR.Global) : List (Nat × List UInt8) :=
  gs.filterMap fun g => g.init.map fun b => ((l.globals.lookup g.name).getD 0, b.data.toList)

def storeAll (ps : List (Nat × List UInt8)) (m : ByteArray) : ByteArray :=
  ps.foldl (fun m p => IR.storeBytes m p.1 p.2) m

theorem initMem_inits (l : IR.Layout) : ∀ (gs : List IR.Global) (m : ByteArray),
    IR.initMem l gs m = storeAll (initsOf l gs) m
  | [], _ => rfl
  | g :: gs, m => by
    unfold IR.initMem at *
    rw [List.foldl_cons]
    cases hg : g.init with
    | none =>
      have : initsOf l (g :: gs) = initsOf l gs := by simp [initsOf, hg]
      rw [this]
      exact initMem_inits l gs m
    | some b =>
      have : initsOf l (g :: gs) = ((l.globals.lookup g.name).getD 0, b.data.toList) :: initsOf l gs := by
        simp [initsOf, hg]
      rw [this, storeAll, List.foldl_cons]
      exact initMem_inits l gs _

theorem storeAll_size : ∀ (ps : List (Nat × List UInt8)) (m : ByteArray), (storeAll ps m).size = m.size
  | [], _ => rfl
  | p :: ps, m => by
    rw [storeAll, List.foldl_cons]
    exact (storeAll_size ps _).trans (storeBytes_size _ _ _)

theorem storeAll_append (p q : List (Nat × List UInt8)) (m : ByteArray) :
    storeAll (p ++ q) m = storeAll q (storeAll p m) := by
  simp [storeAll, List.foldl_append]

/-- Initial values that end at or below `x` leave the byte at `x`. -/
theorem storeAll_below : ∀ (ps : List (Nat × List UInt8)) (m : ByteArray) (x : Nat),
    (∀ p, p ∈ ps → p.1 + p.2.length ≤ x) → (storeAll ps m).get! x = m.get! x
  | [], _, _, _ => rfl
  | p :: ps, m, x, h => by
    rw [storeAll, List.foldl_cons]
    exact (storeAll_below ps _ x (fun q hq => h q (List.mem_cons_of_mem _ hq))).trans
      (storeBytes_far _ _ _ _ (Or.inr (h p List.mem_cons_self)))

theorem Has.drop {Z : ZCtx} {k : Nat} {l1 l2 : List Item} (h : Has Z k (l1 ++ l2)) : Has Z (k + l1.length) l2 :=
  fun j it hj => by
    have := h (l1.length + j) it (by rw [List.getElem?_append_right (by omega)]; simpa using hj)
    rw [show k + l1.length + j = k + (l1.length + j) by omega]
    exact this

namespace StackH

set_option maxRecDepth 100000

/-- The IR's state the program starts in: the memory `IR.initMem` gives
(zero but for the initial values: the constants at their addresses in
ROM, `iss` and `ip_id` in RAM), the input still to come. -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout Stack.ir.globals (ByteArray.mk (Array.replicate 65536 0)),
    world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- `rt_init` of this image: the RAM cleared, the two initial values copied. -/
def initItems : List Item :=
  initHead ++ copyItems "init_iss" "g_iss" 4 ++ copyItems "init_ip_id" "g_ip_id" 2 ++ [.ins ⟨.ret, []⟩]

/-- What start-up and the loop need of the image and of the plan, computed. -/
def runCheck : Bool :=
  (items.take 85).all isEqu && decide (items[85]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 2585).take startItems.length = startItems) &&
  decide ((items.drop 2572).take initItems.length = initItems) &&
  decide ((items.drop 2771).take zeroItems.length = zeroItems) &&
  decide ((items.drop 2589).take mainLoopItems.length = mainLoopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 797 &&
     a.labels.reverse.lookup "rt_idle" == some 32776 &&
     a.labels.reverse.lookup "init_iss" == some 6102 && a.labels.reverse.lookup "g_iss" == some 33068 &&
     a.labels.reverse.lookup "init_ip_id" == some 6106 && a.labels.reverse.lookup "g_ip_id" == some 33072 &&
     decide ((List.range 6).map (fun j => a.bytes.data[6102 + j]?) = [some 0, some 0, some 1, some 0, some 1, some 0]) &&
     (match a.labels.reverse.lookup "f_entry" with
      | some e => a.labels.reverse.lookup (fnLabel "main") == some e && decide (e < 65536)
      | none => false)
   | .error _ => false) &&
  !plan.wrB "main" 32776 &&
  decide (plan.stackLo + plan.depthOf "main" ≤ 65534) && decide (plan.stackLo ≤ 65532) &&
  (plan.data.all fun iv => decide (32777 ≤ iv.1) && decide (iv.2 ≤ 33565)) &&
  decide ((initsOf layout Stack.ir.globals).drop 61 = [(33068, [0, 0, 1, 0]), (33072, [1, 0])]) &&
  ((initsOf layout Stack.ir.globals).take 61).all fun p => decide (p.1 + p.2.length ≤ 32768)

theorem runCheck_true : runCheck = true := by decide +kernel

/-- What `runCheck` computed, of the image `a`. -/
structure Facts (a : Assembled) : Prop where
  head : ∀ it, it ∈ items.take 85 → isEqu it = true
  jump : items[85]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : (items.drop 2585).take startItems.length = startItems
  init : (items.drop 2572).take initItems.length = initItems
  zero : (items.drop 2771).take zeroItems.length = zeroItems
  loop : (items.drop 2589).take mainLoopItems.length = mainLoopItems
  ram : a.labels.reverse.lookup "rt_ram" = some 32768
  ramSize : a.labels.reverse.lookup "rt_ram_size" = some 797
  idle : a.labels.reverse.lookup "rt_idle" = some 32776
  initIss : a.labels.reverse.lookup "init_iss" = some 6102
  gIss : a.labels.reverse.lookup "g_iss" = some 33068
  initId : a.labels.reverse.lookup "init_ip_id" = some 6106
  gId : a.labels.reverse.lookup "g_ip_id" = some 33072
  /-- The initial values in the ROM. -/
  rom : (List.range 6).map (fun j => a.bytes.data[6102 + j]?) = [some 0, some 0, some 1, some 0, some 1, some 0]
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel "main") = some e ∧ e < 65536
  /-- `main` and what it calls do not write the loop's count. -/
  nowr : img.plan.wrB "main" 32776 = false
  room : img.plan.stackLo + img.plan.depthOf "main" ≤ 65534
  slo : img.plan.stackLo ≤ 65532
  data : ∀ iv, iv ∈ img.plan.data → 32777 ≤ iv.1 ∧ iv.2 ≤ 33565
  /-- The globals with an initial value: constants in ROM, then `iss` and `ip_id`. -/
  inits : (initsOf layout Stack.ir.globals).drop 61 = [(33068, [0, 0, 1, 0]), (33072, [1, 0])]
  consts : ∀ p, p ∈ (initsOf layout Stack.ir.globals).take 61 → p.1 + p.2.length ≤ 32768

theorem facts {a : Assembled} (ha : assemble items = .ok a) : Facts a := by
  have hbc := runCheck_true
  unfold runCheck at hbc
  rw [ha] at hbc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hbc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, hjump⟩, hstart⟩, hinit⟩, hzero⟩, hloop⟩, hlab⟩, hnowr⟩, hdep⟩, hslo⟩, hdata⟩, hinits⟩,
    hconsts⟩ := hbc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hram, hrsz⟩, hidle⟩, h1⟩, h2⟩, h3⟩, h4⟩, hrom⟩, hentry⟩ := hlab
  refine ⟨hhead, hjump, hstart, hinit, hzero, hloop, hram, hrsz, hidle, h1, h2, h3, h4, hrom, ?_,
    by rw [img_plan]; exact hnowr, by rw [img_plan]; exact hdep, by rw [img_plan]; exact hslo,
    by rw [img_plan]; exact hdata, hinits, hconsts⟩
  cases he : a.labels.reverse.lookup "f_entry" with
  | none => rw [he] at hentry; cases hentry
  | some e =>
    rw [he] at hentry
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hentry
    exact ⟨e, rfl, hentry.1, hentry.2⟩

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem st0_size (inputs : Array Ember.Trace.Input) : (st0 inputs).mem.size = 65536 := by
  show (IR.initMem _ _ _).size = _
  rw [initMem_inits, storeAll_size]
  simp [ByteArray.size]

/-- The IR's initial memory in RAM: `iss` is 65536, `ip_id` is 1, the rest zero. -/
theorem st0_ram {a : Assembled} (F : Facts a) (inputs : Array Ember.Trace.Input) (x : Nat) (hx : 32768 ≤ x)
    (hx2 : x < 65536) : (st0 inputs).mem.get! x = if x = 33070 ∨ x = 33072 then 1 else 0 := by
  show (IR.initMem _ _ _).get! x = _
  rw [initMem_inits, ← List.take_append_drop 61 (initsOf layout Stack.ir.globals), storeAll_append, F.inits]
  obtain ⟨M, hM⟩ : ∃ M, M = storeAll ((initsOf layout Stack.ir.globals).take 61) (ByteArray.mk (Array.replicate 65536 0)) :=
    ⟨_, rfl⟩
  have hMsz : M.size = 65536 := by rw [hM, storeAll_size]; simp [ByteArray.size]
  have hMx : ∀ y, 32768 ≤ y → M.get! y = 0 := by
    intro y hy
    rw [hM, storeAll_below _ _ y (fun p hp => by have := F.consts p hp; omega), zeros_get]
  rw [← hM]
  show ((((((M.set! 33068 0).set! 33069 0).set! 33070 1).set! 33071 0).set! 33072 1).set! 33073 0).get! x = _
  by_cases h5 : x = 33073
  · subst h5; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h4 : x = 33072
  · subst h4; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h3 : x = 33071
  · subst h3; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h2 : x = 33070
  · subst h2; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h1 : x = 33069
  · subst h1; rw [getBang_same _ _ _ (by simp only [set_size]; omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega)]
  by_cases h0 : x = 33068
  · subst h0; rw [getBang_same _ _ _ (by omega)]; rfl
  rw [getBang_set _ _ _ _ (by omega), hMx x hx, if_neg (by omega)]

/-- What the loop needs of the image (`Z80HarnessLoop`). -/
theorem loopNeed {a : Assembled} (ha : assemble items = .ok a) : LoopNeed img a 2589 32776 "main" Stack.fn_main := by
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

/-- **Start-up**: from reset the CPU gets to the head of the loop, its
stack empty, the shared bytes as the IR's initial state has them. -/
theorem boot_loop {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (ok : (Zof a addrs (0, 0)).OK) (inputs : Array Ember.Trace.Input) (s : Cpu) (hpc : s.pc.toNat = 0)
    (I : Img a 0 s) (hh : s.halted = false) (hrs : s.ramStart.toNat = 0x8000) (hsz : s.mem.size = 65536) :
    ∃ s', Steps s s' ∧ AtLoop img 2589 32776 a addrs (st0 inputs) s' ((st0 inputs).world, 0, (0, 0), (0, 0)) := by
  have F := facts ha
  have hinit : Has (Zof a addrs (0, 0)) 2572 initItems := has_of F.init
  have B : BootHead (Zof a addrs (0, 0)) 85 2585 2572 2771 32768 797 :=
    { head := fun i hi => by
        have hlt : i < (items.take 85).length := by
          have : (items.take 85).length = 85 := by decide +kernel
          omega
        have hm := F.head _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 85)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 85)[i] = it at hm hget
        cases it with
        | equ n v => exact ⟨n, v, hget⟩
        | _ => cases hm
      jump := F.jump
      start := has_of F.start
      init := Has.pre (Has.pre (Has.pre hinit))
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
  -- the initial value of `iss`
  have hc1 : Has (Zof a addrs (0, 0)) (2572 + 4) (copyItems "init_iss" "g_iss" (3 + 1)) :=
    Has.drop (l1 := initHead) (Has.pre (Has.pre hinit))
  obtain ⟨s8, st8, at8, M8, hsp8, hrs8, hsz8, hcp8, hk8⟩ := copy_ok ok (m := 3) (S := 6102) (D := 33068) hc1 F.initIss
    F.gIss (show (32768 : Nat) ≤ 33068 by decide) (by decide) (by decide) (by decide) M7 at7 hrs7 hsz7
  -- the initial value of `ip_id`
  have hc2 : Has (Zof a addrs (0, 0)) (2572 + 4 + 4) (copyItems "init_ip_id" "g_ip_id" (1 + 1)) :=
    Has.drop (l1 := initHead ++ copyItems "init_iss" "g_iss" 4) (Has.pre hinit)
  obtain ⟨s9, st9, at9, M9, hsp9, hrs9, hsz9, hcp9, hk9⟩ := copy_ok ok (m := 1) (S := 6106) (D := 33072) hc2 F.initId
    F.gId (show (32768 : Nat) ≤ 33072 by decide) (by decide) (by decide) (by decide) M8 at8 (by rw [hrs8]; exact hrs7) hsz8
  -- ret, to the head of the loop
  have hsp9' : s9.sp.toNat = 65534 := by rw [hsp9, hsp8]; exact hsp7
  obtain ⟨s10, st10, hpc10, hsp10, hmem10, hh10, hrs10, _, _, _⟩ := ret_raw ok (hinit.get 12 rfl) M9 at9
  have hm9 : ∀ x, x < 33068 ∨ 33074 ≤ x → s9.mem.get! x = s7.mem.get! x := by
    intro x hx
    rw [hk9 x (by omega), hk8 x (by omega)]
  have hrom : ∀ j, j < 6 → ∀ b, a.bytes.data[6102 + j]? = some b → s7.mem.get! (6102 + j) = b := by
    intro j hj b hb
    rw [hkeep _ (Or.inl (by omega)) (by omega)]
    simpa using I.bytes (6102 + j) b hb
  have hR := F.rom
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hR
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hR
  -- the RAM after start-up
  have hram : ∀ x, 32768 ≤ x → x < 33565 → s9.mem.get! x = if x = 33070 ∨ x = 33072 then 1 else 0 := by
    intro x h1 h2
    by_cases hA : 33068 ≤ x ∧ x < 33072
    · rw [hk9 x (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, x = 33068 + j := ⟨x - 33068, by omega⟩
      rw [hcp8 j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rw [hrom 0 (by decide) 0 r0]; rfl
      · rw [hrom 1 (by decide) 0 r1]; rfl
      · rw [hrom 2 (by decide) 1 r2]; rfl
      · rw [hrom 3 (by decide) 0 r3]; rfl
    · by_cases hB : 33072 ≤ x ∧ x < 33074
      · obtain ⟨j, rfl⟩ : ∃ j, x = 33072 + j := ⟨x - 33072, by omega⟩
        rw [hcp9 j (by omega), hk8 _ (by omega)]
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · rw [show 6106 + 0 = 6102 + 4 from rfl, hrom 4 (by decide) 1 r4]; rfl
        · rw [show 6106 + 1 = 6102 + 5 from rfl, hrom 5 (by decide) 0 r5]; rfl
      · rw [hm9 x (by omega), hzero x h1 (by omega), if_neg (by omega)]
  refine ⟨s10, (((st7.trans st8).trans st9).trans st10), ?_⟩
  exact
    { at_ := hback s10 (by
        rw [hpc10, cpu_rd16 _ _ (by rw [hsp9']; omega), hsp9']
        exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => by rw [hm9 x (by omega)]; exact hmem78 x h1))
      image := M9.1.congr hrs10 hmem10
      run := by rw [hh10]; exact M9.2
      rs := by rw [hrs10, hrs9, hrs8]; exact hrs7
      msz := by rw [hmem10]; exact hsz9
      isz := st0_size inputs
      sp := by
        apply UInt16.toNat_inj.mp
        rw [hsp10, UInt16.toNat_add, hsp9']
        rfl
      mem := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        rw [hmem10, hram x (by omega) (by omega), st0_ram F inputs x (by omega) (by omega)]
      idle := by rw [hmem10, hram 32776 (by decide) (by decide)]; rfl
      world := rfl
      mark := rfl
      nval := rfl }

/-- **The image of the stack for the harness, from reset.**  The CPU
starts at address 0 with the image in ROM; the machine holds the input.
For any number `j` of calls of `main` that end in the IR's semantics
from its initial state (each moving the position in the input while
input remains): the machine gets to the head of the loop with the world
those calls leave — the input consumed, the events emitted — or it left
the loop after `i ≤ j` of them and stopped (`di; halt`) with the world
`i` calls leave, **the input used up**.
Nothing is taken of the layout, the image or the runtime. -/
theorem stackH_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves img "main" m (st0 inputs) →
          irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            AtLoop img 2589 32776 a addrs st' s' w') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := stackH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit => ?_⟩
  obtain ⟨ok, _⟩ := hset (0, 0)
  obtain ⟨s1, stb, L0⟩ := boot_loop ha hsize ok inputs s hpc I hh hrs hsz
  rcases loop_run (loopNeed ha) hsize hset m j (st0 inputs) s1 _ L0 hmv st' hit with
    ⟨s2, w2, stp, L2⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, hh2, hi2, hw2, hex⟩
  · exact Or.inl ⟨s2, w2, (Steps.lift ok stb _).trans stp, L2⟩
  · exact Or.inr ⟨i, sti, s2, w2, hi, hiter, (Steps.lift ok stb _).trans stp, hh2, hi2, hw2, hex⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_run

/-- **With the input used up the machine stops**: from reset, when `j`
calls of `main` end in the IR's semantics and leave no input, the
machine stopped (`di; halt`) after `i ≤ j` of them, with the world `i`
calls leave and no input left. -/
theorem stackH_run_halt :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves img "main" m (st0 inputs) →
          irIter m img.ctx j (st0 inputs) = some st' → st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := stackH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit hex => ?_⟩
  obtain ⟨ok, _⟩ := hset (0, 0)
  obtain ⟨s1, stb, L0⟩ := boot_loop ha hsize ok inputs s hpc I hh hrs hsz
  rcases loop_run (loopNeed ha) hsize hset m j (st0 inputs) s1 _ L0 hmv st' hit with
    ⟨s2, w2, stp, L⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, hh2, hi2, hw2, hex2⟩
  · rcases loop_iter (loopNeed ha) hsize hset L m with ⟨_, s3, w3, st3, hh3, hi3, hw3⟩ | ⟨hnex, _⟩
    · exact ⟨j, st', s3, w3, Nat.le_refl _, hit, ((Steps.lift ok stb _).trans stp).trans st3, hh3, hi3, hw3, hex⟩
    · exact absurd hex hnex
  · exact ⟨i, sti, s2, w2, hi, hiter, (Steps.lift ok stb _).trans stp, hh2, hi2, hw2, hex2⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_run_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_run_halt

end StackH

end Ember.Proof.Z80Gen
