import Ember.Proof.Z80WideHItems
import Ember.Proof.Z80Boot
import Ember.Proof.Z80World
import Ember.Proof.Z80HarnessLoop
import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80WideH — the image of `Ember.Z80.Wide` for the test harness (plan M7.3)

`wideH_ok`: in the image the assembler makes of `WideH.items` — the
program `Ember.Z80.Wide` (four-byte loads and stores through addresses,
an index check that can trap) with the runtime of the test harness,
without the passes on the assembly — in the machine of the harness,
every function, entered as `Entry` says, returns as `IR.Sem.callF` does
with the machine holding the world it leaves, or reaches `rt_trap`.

Nothing is assumed of the program, the layout, the image or the runtime:
the routines the image calls — `rt_input`, `rt_ld32`, `rt_st32`,
`rt_add32`, `rt_acc_hl`, `rt_bound`, `rt_out_byte`, `rt_out_end` — are
proved from their items (`Z80Rt`, `Z80Wide`, `Z80Bytes`), and the image
calls no other routine of the runtime from its functions (`calls_eq`).

`wideH_run` goes from reset, as `LoopH.loopH_run` does for the loopback
image: start-up (the RAM cleared) and the loop that calls `main` are the
image's own items.  For any number of calls of `main` that end in the
IR's semantics, the machine is at the head of the loop with the world
those calls leave, or it left the loop earlier and stopped, the input
used up — given `Moves` (a call with input remaining moves the position
in the input), which is an assumption of these theorems.
`wideH_trap`: when the next call traps in the IR's semantics, the
machine gets to `rt_trap` holding the world of the trap.

What the statements are about, and what they are not: the image is
`WideH.items` assembled; that these are the items `build` gives without
the passes, the IR what `IR.lower` returns and the layout what `build`
computes are `#guard`s.  The machine is the CPU model with the harness's
ports (`hbus`, `hdev`).  Not the image as built by default (with the
passes on the assembly).  These theorems are about the IR's runs; against
the Ember semantics and on `Ember.Z80.Machine`: `Z80WideHSpec`.
-/

namespace Ember.Proof.Z80Gen.WideH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-- RAM from `0x8000`: the runtime's accumulator (eight bytes), the
loop's count of idle calls, the globals, the frames; the stack above.
A routine of the runtime needs two bytes of stack (`rtK`). -/
def img : ImgIn :=
  { ir := Wide.ir, layout, ramStart := 0x8000, stackLo := 32797, stackHi := 65536, acc := 32768, rtK := 2,
    rt := [], items, genOff := 8 }

theorem img_check : img.check = true := by decide +kernel

/-! ## The machine of the harness (`Z80HarnessW`) -/

def Zof (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : ZCtx := img.ZH a addrs μ

def harness (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : Harness (Zof a addrs μ) := img.harness a addrs μ

/-! ## The routines of the runtime in the image -/

/-- The routines the image calls. -/
def calls : List String :=
  (items.filterMap fun it =>
    match it with
    | .ins ⟨.call, [.imm (.sym n _)]⟩ => some n
    | _ => none).eraseDups

theorem calls_eq : calls = ["rt_input", "rt_ld32", "rt_bound", "rt_st32", "rt_acc_hl", "rt_add32", "rt_out_byte",
    "rt_out_end", "rt_zero", "rt_init", "f_entry"] := by decide +kernel

theorem uses_mem {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {name : String}
    (h : Uses (Zof a addrs μ) name) : name ∈ calls := by
  obtain ⟨k, hk⟩ := h
  have hm : Item.ins ⟨.call, [.imm (.sym name)]⟩ ∈ items := List.mem_of_getElem? hk
  unfold calls
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

theorem not_used {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {name : String}
    (h : name ∉ calls) : ¬ Uses (Zof a addrs μ) name := fun hu => h (uses_mem hu)

/-- Where the routines are. -/
def rtCheck : Bool :=
  decide ((items.drop 149).take inputItems.length = inputItems) &&
  decide ((items.drop 165).take ldItems.length = ldItems) &&
  decide ((items.drop 174).take boundItems.length = boundItems) &&
  decide ((items.drop 180).take stItems.length = stItems) &&
  decide ((items.drop 190).take accItems.length = accItems) &&
  decide ((items.drop 202).take (bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩).length =
    bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩) &&
  decide ((items.drop 218).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 221).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide (items[235]? = some (.label "rt_trap"))

theorem rtCheck_true : rtCheck = true := by decide +kernel

theorem has_of {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {k : Nat} {l : List Item}
    (h : (items.drop k).take l.length = l) : Has (Zof a addrs μ) k l := by
  intro j it hj
  have hlt : j < l.length := by
    rcases Nat.lt_or_ge j l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  rw [← h, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
  exact hj

/-- **The functions of the image for the harness do what the IR's
functions do**: nothing is taken of the runtime.  (For every place of
the mark: a function leaves it.) -/
theorem wideH_setting :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img.ok img_check
  refine ⟨a, addrs, ha, hsize, fun μ => ?_⟩
  obtain ⟨ok, hcallee⟩ := hall HW hbus (hdev img.ctx) (hrel μ) (fun _ => rfl)
  refine ⟨ok, hcallee ?_⟩
  have hrc := rtCheck_true
  unfold rtCheck at hrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hin, hld⟩, hbd⟩, hst⟩, hacc⟩, hadd⟩, hob⟩, hoe⟩, htrap⟩ := hrc
  have H := harness a addrs μ
  have pure : ∀ (name : String) (rel : Cpu → Cpu → Prop), name ∉ calls → RtPure (Zof a addrs μ) name rel :=
    fun name rel h hu => absurd hu (not_used h)
  have acc : ∀ (name : String) (pre : Cpu → Prop) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtAcc (Zof a addrs μ) name pre rel := fun name pre rel h hu => absurd hu (not_used h)
  exact
    { bound := rt_bound_ok ok hsize (has_of hbd) htrap
      wide :=
        { ld := rt_ld32_ok ok hsize (has_of hld)
          st := rt_st32_ok ok hsize (has_of hst)
          bin := fun op => by
            cases op
            case add => exact rt_add32_ok ok hsize (has_of hadd)
            all_goals exact acc _ _ _ (by rw [calls_eq]; decide +kernel)
          cmp := fun hu => absurd hu (not_used (by rw [calls_eq]; decide +kernel)) }
      accA := acc _ _ _ (by rw [calls_eq]; decide)
      accHL := rt_acc_hl_ok ok hsize (has_of hacc)
      eff := fun e he => by
        cases e with
        | inputNext => exact harness_input ok H hsize (has_of hin) _ (Or.inl rfl)
        | ringPop => exact harness_input ok H hsize (has_of hin) _ (Or.inr rfl)
        | outByte => exact harness_out_byte ok H hsize (has_of hob)
        | outEnd => exact harness_out_end ok H hsize (has_of hoe)
        | drop => exact fun hu => absurd hu (not_used (by rw [calls_eq]; decide))
        | note => exact fun hu => absurd hu (not_used (by rw [calls_eq]; decide))
        | _ => cases he
      shl8 := pure _ _ (by rw [calls_eq]; decide)
      shr8 := pure _ _ (by rw [calls_eq]; decide)
      shl16 := pure _ _ (by rw [calls_eq]; decide)
      shr16 := pure _ _ (by rw [calls_eq]; decide)
      mul8 := pure _ _ (by rw [calls_eq]; decide)
      div8 := pure _ _ (by rw [calls_eq]; decide)
      mod8 := pure _ _ (by rw [calls_eq]; decide)
      not16 := pure _ _ (by rw [calls_eq]; decide)
      neg16 := pure _ _ (by rw [calls_eq]; decide)
      mul16 := pure _ _ (by rw [calls_eq]; decide)
      div16 := pure _ _ (by rw [calls_eq]; decide)
      mod16 := pure _ _ (by rw [calls_eq]; decide) }

theorem wideH_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ μ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, h⟩ := wideH_setting
  exact ⟨a, addrs, ha, fun μ => (h μ).2⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_ok

/-! ## From reset: start-up and the loop -/

/-- The IR's state the program starts in: the memory `Ember.Z80.IR`
starts with (zero but for the initial value of the constant `WV`, at its
address in ROM), the input still to come. -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout Wide.ir.globals (ByteArray.mk (Array.replicate 65536 0)), world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 7).all isEqu && decide (items[7]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 123).take startItems.length = startItems) &&
  decide ((items.drop 118).take initItems.length = initItems) &&
  decide ((items.drop 224).take zeroItems.length = zeroItems) &&
  decide ((items.drop 127).take mainLoopItems.length = mainLoopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 29 &&
     a.labels.reverse.lookup "rt_idle" == some 32776 &&
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
  head : ∀ it, it ∈ items.take 7 → isEqu it = true
  jump : items[7]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : (items.drop 123).take startItems.length = startItems
  init : (items.drop 118).take initItems.length = initItems
  zero : (items.drop 224).take zeroItems.length = zeroItems
  loop : (items.drop 127).take mainLoopItems.length = mainLoopItems
  ram : a.labels.reverse.lookup "rt_ram" = some 32768
  ramSize : a.labels.reverse.lookup "rt_ram_size" = some 29
  idle : a.labels.reverse.lookup "rt_idle" = some 32776
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel "main") = some e ∧ e < 65536
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
  obtain ⟨⟨⟨hram, hrsz⟩, hidle⟩, hentry⟩ := hlab
  refine ⟨hhead, hjump, hstart, hinit, hzero, hloop, hram, hrsz, hidle, ?_, hnowr, hdep, hslo, hdata⟩
  cases he : a.labels.reverse.lookup "f_entry" with
  | none => rw [he] at hentry; cases hentry
  | some e =>
    rw [he] at hentry
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hentry
    exact ⟨e, rfl, hentry.1, hentry.2⟩

/-- What the loop needs of the image (`Z80HarnessLoop`). -/
theorem loopNeed {a : Assembled} (ha : assemble items = .ok a) : LoopNeed img a 127 32776 "main" Wide.main := by
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
  Z80Gen.AtLoop img 127 32776 a addrs st s w

/-- A call of `main` with input remaining moves the position in the input. -/
abbrev Moves (m : Nat) (st : IR.Sem.St) : Prop := Z80Gen.Moves img "main" m st

theorem initMem_eq (m : ByteArray) :
    IR.initMem layout Wide.ir.globals m = (((m.set! 426 120).set! 427 86).set! 428 52).set! 429 18 := rfl

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

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
  have F := facts ha
  obtain ⟨ok, _⟩ := hset (0, 0)
  have B : BootNeed (Zof a addrs (0, 0)) 7 123 118 224 32768 29 :=
    { head := fun i hi => by
        have hlt : i < (items.take 7).length := by
          have : (items.take 7).length = 7 := by decide +kernel
          omega
        have hm := F.head _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 7)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 7)[i] = it at hm hget
        cases it with
        | equ n v => exact ⟨n, v, hget⟩
        | _ => cases hm
      jump := F.jump
      start := has_of F.start
      init := has_of F.init
      zero := has_of F.zero
      ram := F.ram
      ramSize := F.ramSize
      n2 := by decide
      lo := Nat.le_refl _
      hi := by decide
      stackLo := F.slo
      stackHi := rfl
      size := hsize }
  obtain ⟨s1, stb, at1, I1, hh1, hrs1, hsz1, hsp1, hzeroed⟩ := boot_ok ok B hpc I hh hrs hsz
  have L0 : AtLoop a addrs (st0 inputs) s1 ((st0 inputs).world, 0, (0, 0), (0, 0)) :=
    { at_ := at1, image := I1, run := hh1, rs := hrs1, msz := hsz1,
      isz := by
        show (IR.initMem _ _ _).size = _
        rw [initMem_eq, set_size, set_size, set_size, set_size]
        simp [ByteArray.size]
      sp := hsp1
      mem := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        rw [hzeroed x (by omega) (by omega)]
        show _ = (IR.initMem _ _ _).get! x
        rw [initMem_eq, getBang_set _ _ _ _ (by omega), getBang_set _ _ _ _ (by omega),
          getBang_set _ _ _ _ (by omega), getBang_set _ _ _ _ (by omega), zeros_get]
      idle := hzeroed 32776 (by decide) (by decide)
      world := rfl
      mark := rfl
      nval := rfl }
  rcases Z80Gen.loop_run (loopNeed ha) hsize hset m j (st0 inputs) s1 _ L0 hmv st' hit with
    ⟨s2, w2, stp, L2⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, hh2, hi2, hw2, hex⟩
  · exact Or.inl ⟨s2, w2, (Steps.lift ok stb _).trans stp, L2⟩
  · exact Or.inr ⟨i, sti, s2, w2, hi, hiter, (Steps.lift ok stb _).trans stp, hh2, hi2, hw2, hex⟩

/-- **The image for the harness, from reset**, given `Moves`: for any
number `j` of calls of `main` that end in the IR's semantics from its
initial state, the machine gets to the head of the loop with the world
those calls leave, or it left the loop after `i ≤ j` of them and stopped
(`di; halt`) with the world `i` calls leave, the input used up. -/
theorem wideH_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            AtLoop a addrs st' s' w') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := wideH_setting
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit =>
    run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_run

/-- **With the input used up the machine stops** (given `Moves`). -/
theorem wideH_run_halt :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := wideH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit hex => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases Z80Gen.loop_iter (loopNeed ha) hsize hset L m with ⟨_, s2, w2, st2, hh2, hi2, hw2⟩ | ⟨hnex, _⟩
    · exact ⟨j, st', s2, w2, Nat.le_refl _, hit, stp.trans st2, hh2, hi2, hw2, hex⟩
    · exact absurd hex hnex
  · exact hr

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_run_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_run_halt

/-- **A trap, from reset** (given `Moves`): when `j` calls of `main` end
in the IR's semantics and the next one, with input remaining, traps
there, the machine gets to `rt_trap` holding the world of the trap — or
it left the loop earlier and stopped, the input used up. -/
theorem wideH_trap :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      (∀ μ, (Zof a addrs μ).OK) ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' st'' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 ≠ 0xFFFF → IR.Sem.callF m img.ctx "main" st' = .trap st'' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            w'.1 = st''.world ∧ Trapped (Zof a addrs (0, 0)) st'' s') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := wideH_setting
  refine ⟨a, addrs, ha, fun μ => (hset μ).1, fun inputs s hpc I hh hrs hsz j m st' st'' hmv hit hne htr => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases Z80Gen.loop_iter (loopNeed ha) hsize hset L m with ⟨hex, _⟩ | ⟨_, hit2⟩
    · exact absurd hex hne
    · rw [htr] at hit2
      obtain ⟨s2, w2, st2, hw, htrp⟩ := hit2
      exact Or.inl ⟨s2, w2, stp.trans st2, hw, htrp⟩
  · exact Or.inr hr

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_trap

/-! ## `Moves`, proved: a call of `main` with input remaining moves the position

`main` begins with `input.next`; no other instruction of it takes input
or calls, and no label is its first instruction.  So a call that ends
normally has the world's position where `input.next` left it — moved,
when input remained (`LoopH.next_moves`). -/

/-- The world's place in the input, and whether it reads by frames, kept. -/
def Keep (w w' : World) : Prop := w'.pos = w.pos ∧ w'.off = w.off ∧ w'.framed = w.framed

theorem Keep.refl (w : World) : Keep w w := ⟨rfl, rfl, rfl⟩

theorem Keep.trans {w1 w2 w3 : World} (h1 : Keep w1 w2) (h2 : Keep w2 w3) : Keep w1 w3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- An instruction that takes no input and calls nothing. -/
def noIn : IR.Instr → Bool
  | .eff .inputNext _ _ | .eff .ringPop _ _ | .eff .inputFrame _ _ => false
  | .call _ _ _ => false
  | _ => true

theorem setDst_world (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (n : Nat) (d : IR.Dst) (v : Nat) :
    (IR.Sem.setDst c st tmps n d v).1.world = st.world := by
  cases d <;> rfl

theorem setRet_world (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (ret : Option (Nat × IR.Dst))
    (r : Option Nat) : (IR.Sem.setRet c st tmps ret r).1.world = st.world := by
  cases ret with
  | none => rfl
  | some p => exact setDst_world c st tmps p.1 p.2 _

theorem effect_keep (c : IR.Ctx) (w : World) (e : Effect) (vs : List Nat)
    (h : e ≠ .inputNext ∧ e ≠ .ringPop ∧ e ≠ .inputFrame) : Keep w (IR.Sem.effect c w e vs).2 := by
  cases e <;> first | exact absurd rfl h.1 | exact absurd rfl h.2.1 | exact absurd rfl h.2.2 | exact ⟨rfl, rfl, rfl⟩

/-- What one instruction that takes no input and calls nothing does to the world's place in the input. -/
theorem step_keep (c : IR.Ctx) (st : IR.Sem.St) (tmps : Array Nat) (i : IR.Instr) (h : noIn i = true) :
    (∀ st' tmps', IR.Sem.step c st tmps i = .next st' tmps' → Keep st.world st'.world) ∧
    (∀ g st1 ret, IR.Sem.step c st tmps i ≠ .call g st1 ret) ∧
    (∀ r st', IR.Sem.step c st tmps i = .stop (.ok r st') → st' = st) := by
  cases i with
  | call g ret reg => cases h
  | eff e args ret =>
    have he : e ≠ .inputNext ∧ e ≠ .ringPop ∧ e ≠ .inputFrame := by
      refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> (subst h'; cases h)
    refine ⟨fun st' tmps' hs => ?_, fun g st1 r hs => ?_, fun r st' hs => ?_⟩
    · simp only [IR.Sem.step, IR.Sem.Step.set, IR.Sem.Step.next.injEq] at hs
      rw [← hs.1, setRet_world]
      exact effect_keep c st.world e _ he
    · simp [IR.Sem.step, IR.Sem.Step.set] at hs
    · simp [IR.Sem.step, IR.Sem.Step.set] at hs
  | ret v =>
    refine ⟨fun st' tmps' hs => ?_, fun g st1 r hs => ?_, fun r st' hs => ?_⟩
    · simp [IR.Sem.step] at hs
    · simp [IR.Sem.step] at hs
    · simp only [IR.Sem.step, IR.Sem.Step.stop.injEq, IR.Sem.Res.ok.injEq] at hs
      exact hs.2.symm
  | _ =>
    refine ⟨fun st' tmps' hs => ?_, fun g st1 r hs => ?_, fun r st' hs => ?_⟩ <;>
      simp only [IR.Sem.step, IR.Sem.Step.set] at hs <;>
      (try split at hs) <;> (try split at hs) <;>
      first
        | (cases hs; done)
        | (simp only [IR.Sem.Step.next.injEq] at hs; rw [← hs.1]; first | exact Keep.refl _ | (rw [setDst_world]; exact Keep.refl _))
        | simp at hs

/-- **From the second instruction on, `main` keeps the world's place in the input.** -/
theorem exec_keep (c : IR.Ctx) : ∀ (k pc : Nat) (tmps : Array Nat) (st : IR.Sem.St) (r : Option Nat)
    (st' : IR.Sem.St), 1 ≤ pc → IR.Sem.exec k c Wide.main pc tmps st = .ok r st' → Keep st.world st'.world
  | 0, _, _, _, _, _, _, h => by simp [IR.Sem.exec] at h
  | k + 1, pc, tmps, st, r, st', hpc, h => by
    rw [IR.Sem.exec] at h
    cases hb : Wide.main.body[pc]? with
    | none =>
      rw [hb] at h
      cases h
      exact Keep.refl _
    | some i =>
      rw [hb] at h
      simp only at h
      have hi : noIn i = true := by
        have hlt : pc < Wide.main.body.size := by
          rcases Nat.lt_or_ge pc Wide.main.body.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none h'] at hb; cases hb
        have hall : ∀ q, q < Wide.main.body.size → 1 ≤ q → ∀ i, Wide.main.body[q]? = some i → noIn i = true := by
          decide +kernel
        exact hall pc hlt hpc i hb
      obtain ⟨hn, hc, hst⟩ := step_keep c st tmps i hi
      cases hs : IR.Sem.step c st tmps i with
      | next st1 tmps1 =>
        rw [hs] at h
        exact (hn st1 tmps1 hs).trans (exec_keep c k (pc + 1) tmps1 st1 r st' (by omega) h)
      | goto l =>
        rw [hs] at h
        simp only at h
        cases hl : IR.Sem.labelAt Wide.main l with
        | none => rw [hl] at h; cases h
        | some q =>
          rw [hl] at h
          have hq := labelAt_spec hl
          have h1 : 1 ≤ q := by
            rcases Nat.eq_zero_or_pos q with h0 | h0
            · subst h0
              have : Wide.main.body[0]? = some (.eff .inputNext [] (some (2, .slot { area := .frame "main", off := 0 }))) :=
                rfl
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
        exact Keep.refl _

/-- **A call of `main`**: it keeps the world reading byte by byte, and, with input remaining, moves its place. -/
theorem main_call (k : Nat) (st : IR.Sem.St) (r : Option Nat) (st' : IR.Sem.St) (hf : st.world.framed = false)
    (h : IR.Sem.callF k img.ctx "main" st = .ok r st') :
    st'.world.framed = false ∧ (st.world.next.1 ≠ 0xFFFF → (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off)) := by
  match k, h with
  | k1 + 2, h =>
    have hfn : img.ctx.prog.fn? "main" = some Wide.main := rfl
    simp only [IR.Sem.callF, hfn, IR.Sem.exec] at h
    have hb : Wide.main.body[0]? = some (.eff .inputNext [] (some (2, .slot { area := .frame "main", off := 0 }))) := rfl
    rw [hb] at h
    simp only [IR.Sem.step, IR.Sem.Step.set] at h
    have K := exec_keep img.ctx k1 1 _ _ r st' (Nat.le_refl _) h
    rw [setRet_world] at K
    obtain ⟨hp, ho, hfr⟩ := K
    refine ⟨by rw [hfr]; exact LoopH.next_framed _ hf, fun hne => ?_⟩
    rw [hp, ho]
    exact LoopH.next_moves _ hf hne
  | 0, h => simp [IR.Sem.callF] at h
  | 1, h =>
    have hfn : img.ctx.prog.fn? "main" = some Wide.main := rfl
    simp [IR.Sem.callF, hfn, IR.Sem.exec] at h

theorem iter_framed (m : Nat) : ∀ (i : Nat) (st sti : IR.Sem.St), st.world.framed = false →
    irIter m img.ctx i st = some sti → sti.world.framed = false
  | 0, st, sti, hf, h => by cases h; exact hf
  | i + 1, st, sti, hf, h => by
    rw [irIter] at h
    cases hc : IR.Sem.callF m img.ctx img.ctx.prog.entry st with
    | ok r st1 =>
      rw [hc] at h
      exact iter_framed m i st1 sti (main_call m st r st1 hf hc).1 h
    | _ => rw [hc] at h; cases h

/-- **`Moves`, for any input.** -/
theorem moves (inputs : Array Ember.Trace.Input) (m : Nat) : Moves m (st0 inputs) := by
  intro i sti r sti' hi hc hne
  exact (main_call m sti r sti' (iter_framed m i (st0 inputs) sti rfl hi) hc).2 hne

/-- info: 'Ember.Proof.Z80Gen.WideH.moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms moves

/-! ## The image from reset, with nothing taken -/

/-- **The image for the harness halts when the IR's run ends with the
input used up**: from reset, for any input, when `j` calls of `main` end
in the IR's semantics and leave no input, the machine stopped (`di;
halt`) after `i ≤ j` of them, holding the world those `i` calls leave
(its events: the trace's transmissions and drops) with no input left. -/
theorem wideH_halts :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' → st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, h⟩ := wideH_run_halt
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hit hex =>
    h inputs s hpc I hh hrs hsz j m st' (moves inputs m) hit hex⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_halts

/-- **A trap of the IR's run reaches `rt_trap` in the image** — the
label: its items are `out (0xD7),a; di; halt; jr rt_trap_l`, and this
theorem claims nothing of them (`Trapped`: at the label, not halted, the
shared bytes as the IR's, the image in ROM; on from the label:
`wideH_harness_trap_halt`): from reset, when `j`
calls of `main` end in the IR's semantics and the next one, with input
remaining, traps, the machine gets to `rt_trap` holding the world of the
trap — or it stopped earlier, the input used up. -/
theorem wideH_traps :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      (∀ μ, (Zof a addrs μ).OK) ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' st'' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 ≠ 0xFFFF → IR.Sem.callF m img.ctx "main" st' = .trap st'' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            w'.1 = st''.world ∧ Trapped (Zof a addrs (0, 0)) st'' s') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hok, h⟩ := wideH_trap
  exact ⟨a, addrs, ha, hok, fun inputs s hpc I hh hrs hsz j m st' st'' hit hne htr =>
    h inputs s hpc I hh hrs hsz j m st' st'' (moves inputs m) hit hne htr⟩

/-- info: 'Ember.Proof.Z80Gen.WideH.wideH_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideH_traps

/-! ## Two inputs, evaluated

What `wideH_halts` and `wideH_traps` take of the IR's run, for two
inputs, is evaluated here (`#guard`: evaluation, not proof).  That the
interpreter, the IR's semantics and the generated code (with and without
the passes on the assembly) give the same trace on them is a test
(`Tests/Ember/Z80Tests.lean`, `ownExamples`). -/

/-- Indices in range: each byte a call of `main` that ends, then no input. -/
def inputsOk : Array Ember.Trace.Input := #[.rx (ByteArray.mk #[1, 2])]

/-- The second byte, 7, is out of range: the second call traps. -/
def inputsTrap : Array Ember.Trace.Input := #[.rx (ByteArray.mk #[2, 7])]

def txs (w : World) : List (List UInt8) :=
  w.events.toList.map fun e => match e.2 with
    | .tx b => b.toList
    | _ => []

-- `inputsOk`: two calls end, no input is left, the two frames sent (`wideH_halts`)
#guard match irIter 100 img.ctx 2 (st0 inputsOk) with
  | some st => st.world.next.1 == 0xFFFF && txs st.world == [[0x78, 0x79, 0x70], [0x78, 0x7a, 0x70]]
  | none => false

-- `inputsTrap`: the first call ends, the second, with input remaining, traps (`wideH_traps`)
#guard match irIter 100 img.ctx 1 (st0 inputsTrap) with
  | some st => st.world.next.1 != 0xFFFF && txs st.world == [[0x78, 0x7a, 0x70]] &&
      (match IR.Sem.callF 100 img.ctx "main" st with
       | .trap _ => true
       | _ => false)
  | none => false

end Ember.Proof.Z80Gen.WideH
