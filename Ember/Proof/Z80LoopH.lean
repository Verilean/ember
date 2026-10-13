import Ember.Proof.Z80LoopHItems
import Ember.Proof.Z80Boot
import Ember.Proof.Z80World
import Ember.Proof.Z80HarnessLoop

/-!
# Ember.Proof.Z80LoopH — the loopback image for the test harness: nothing taken of the runtime (plan M7.3)

`loopH_ok`: in the image the assembler makes of `LoopH.items` — the
loopback program with the runtime of the test harness, without the
passes on the assembly — in the machine of the harness (`hbus`, `hdev`:
the world behind ports), every function, entered as `Entry` says,
returns as `IR.Sem.callF` does with the machine holding the world it
leaves, or reaches `rt_trap`.

Nothing is assumed of the program, the layout, the image or the runtime:
the routines the image calls — `rt_input`, `rt_out_byte`, `rt_out_end`,
`rt_drop` — are proved (`Z80Rt`), and the image calls no other routine
of the runtime from its functions (`calls_eq`).  None of them uses the
stack, so the plan has `rtK = 0`: a function needs two bytes of stack
for each call below it, and no more.

`loopH_run` goes from reset: start-up (the stack pointer, the RAM
cleared by `rt_zero`'s `ldir`) and the loop that calls `main` are the
image's own items, proved (`Z80Boot`, `loop_iter`).  For any number of
calls of `main` that end in the IR's semantics from its initial state,
the machine is at the head of the loop with the world those calls leave,
or it left the loop earlier and stopped with the world of the calls made
till then — **the input used up**: the loop's count of idle calls stays
at zero, because a call with input remaining moves the position in the
input (`Moves`, taken here, proved of the program in `Z80LoopHSpec`).
`loopH_run_halt`: so with no input left the machine has stopped.

The harness asks the machine whether a call moved the position in the
input (port `0xD9`), as the interpreter's driver compares the position
before and after; the mark it compares with is part of the machine's
state, and the functions leave it — said by taking it into what the
machine stands for (`hrel μ`): the functions are proved for every `μ`.

What the statements are about, and what they are not:

* the image is `LoopH.items` assembled; that these are the items
  `build` gives without the passes, the IR what `IR.lower` returns and
  the layout what `build` computes are `#guard`s (evaluation, not proof).
  What the kernel computes: the generator's environments, the checks of
  the plan, the assembly, where the routines are, the symbols;
* the machine is the CPU model with `hbus`/`hdev`: the world behind the
  harness's ports.  That `Ember.Z80.Machine`, which the tests run, steps
  as this machine does is `Z80Machine` (`step_sim`, `loopH_halts`);
* that the calls of `main` do end — the loopback never traps
  (`loop_safe`, M5) — is composed with this in `Z80LoopHSpec`;
* not the image as built by default (with the passes on the assembly).
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-- RAM from `0x8000`: the one cell of the harness's runtime (its count
of idle calls — the loop's own, no routine writes it), the globals, the
frames; eight bytes for the accumulator (which this image does not
have); the stack up to the top.  A routine of the runtime needs no
stack and writes no memory. -/
def img : ImgIn :=
  { ir := Loop.ir, layout, dropReasons := ["oversize-frame"], ramStart := 0x8000, stackLo := 33087,
    stackHi := 65536, acc := 33079, rtK := 0, rt := [], items, genOff := 16 }

theorem img_check : img.check = true := by decide +kernel

/-! ## The machine of the harness (`Z80HarnessW`) -/

/-- The setting: the plan of the image, the image, the harness.  `μ` is
where the mark is — the functions leave it (only the loop reads `0xD9`),
which is said by taking it into what the machine stands for. -/
def Zof (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : ZCtx := img.ZH a addrs μ

def harness (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : Harness (Zof a addrs μ) := img.harness a addrs μ

/-- The machine runs the same whatever the mark is taken to be. -/
theorem wrun_mark (a : Assembled) (addrs : List Nat) (μ μ' : Nat × Nat) (n : Nat) (x : Cpu × HW) :
    wrun (Zof a addrs μ) n x = wrun (Zof a addrs μ') n x := img.wrun_mark a addrs μ μ' n x

theorem wsteps_mark {a : Assembled} {addrs : List Nat} {μ μ' : Nat × Nat} {x y : Cpu × HW}
    (h : WSteps (Zof a addrs μ) x y) : WSteps (Zof a addrs μ') x y := ImgIn.wsteps_mark h

/-! ## The routines of the runtime in the image -/

/-- The routines the image calls. -/
def calls : List String :=
  (items.filterMap fun it =>
    match it with
    | .ins ⟨.call, [.imm (.sym n _)]⟩ => some n
    | _ => none).eraseDups

theorem calls_eq : calls = ["rt_out_byte", "rt_out_end", "rt_drop", "f_slip_send", "f_slip_store", "rt_input",
    "f_loop_rx", "rt_zero", "rt_init", "f_entry"] := by decide +kernel

theorem uses_mem {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {name : String}
    (h : Uses (Zof a addrs μ) name) : name ∈ calls := by
  obtain ⟨k, hk⟩ := h
  have hm : Item.ins ⟨.call, [.imm (.sym name)]⟩ ∈ items := List.mem_of_getElem? hk
  unfold calls
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- Where the routines are. -/
def rtCheck : Bool :=
  decide ((items.drop 196).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 205).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 208).take 3 = [.label "rt_drop", .ins ⟨.out, [.mem (.num 0xD5), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 211).take inputItems.length = inputItems)

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

/-- **The functions of the loopback image for the harness do what the
IR's functions do**: nothing is taken of the runtime.  (For every place
of the mark: a function leaves it.) -/
theorem loopH_setting :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img.ok img_check
  refine ⟨a, addrs, ha, hsize, fun μ => ?_⟩
  obtain ⟨ok, hcallee⟩ := hall HW hbus (hdev img.ctx) (hrel μ) (fun _ => rfl)
  refine ⟨ok, hcallee ?_⟩
  have hrc := rtCheck_true
  unfold rtCheck at hrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hrc
  have H := harness a addrs μ
  have no : ∀ name, name ∉ calls → ¬ Uses (Zof a addrs μ) name := fun name h hu => h (uses_mem hu)
  have pure : ∀ (name : String) (rel : Cpu → Cpu → Prop), name ∉ calls → RtPure (Zof a addrs μ) name rel :=
    fun name rel h hu => absurd hu (no name h)
  have acc : ∀ (name : String) (pre : Cpu → Prop) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtAcc (Zof a addrs μ) name pre rel := fun name pre rel h hu => absurd hu (no name h)
  exact
    { bound := fun hu => absurd hu (no _ (by rw [calls_eq]; decide))
      wide :=
        { ld := acc _ _ _ (by rw [calls_eq]; decide +kernel)
          st := fun hu => absurd hu (no _ (by rw [calls_eq]; decide +kernel))
          bin := fun op => acc _ _ _ (by rw [calls_eq]; cases op <;> decide +kernel)
          cmp := fun hu => absurd hu (no _ (by rw [calls_eq]; decide +kernel)) }
      accA := acc _ _ _ (by rw [calls_eq]; decide)
      accHL := acc _ _ _ (by rw [calls_eq]; decide)
      eff := fun e he => by
        cases e with
        | inputNext => exact harness_input ok H hsize (has_of h4) _ (Or.inl rfl)
        | ringPop => exact harness_input ok H hsize (has_of h4) _ (Or.inr rfl)
        | outByte => exact harness_out_byte ok H hsize (has_of h1)
        | outEnd => exact harness_out_end ok H hsize (has_of h2)
        | drop => exact harness_drop ok H hsize (has_of h3)
        | note => exact fun hu => absurd hu (no _ (by rw [calls_eq]; decide))
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

theorem loopH_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ μ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, h⟩ := loopH_setting
  exact ⟨a, addrs, ha, fun μ => (h μ).2⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_ok

/-! ## From reset: start-up and the loop -/

/-- The IR's state the program starts in: the memory `Ember.Z80.IR`
starts with (`initMem`: zero but for the initial values — here the
constant `MTU`, at its address in ROM), the input still to come.  (This
is `irInit` of `Ember.Proof.IRLower` for the loopback program and this
layout.) -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout Loop.ir.globals (ByteArray.mk (Array.replicate 65536 0)), world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 15).all isEqu && decide (items[15]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 170).take startItems.length = startItems) &&
  decide ((items.drop 165).take initItems.length = initItems) &&
  decide ((items.drop 227).take zeroItems.length = zeroItems) &&
  decide ((items.drop 174).take mainLoopItems.length = mainLoopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 311 &&
     a.labels.reverse.lookup "rt_idle" == some 32768 &&
     (match a.labels.reverse.lookup "f_entry" with
      | some e => a.labels.reverse.lookup (fnLabel "main") == some e && decide (e < 65536)
      | none => false)
   | .error _ => false) &&
  !img.plan.wrB "main" 32768 &&
  decide (img.plan.stackLo + img.plan.depthOf "main" ≤ 65534) && decide (img.plan.stackLo ≤ 65532) &&
  (img.plan.data.all fun iv => decide (32769 ≤ iv.1) && decide (iv.2 ≤ 33079))

theorem bootCheck_true : bootCheck = true := by decide +kernel

/-- What `bootCheck` computed, of the image `a`. -/
structure Facts (a : Assembled) : Prop where
  head : ∀ it, it ∈ items.take 15 → isEqu it = true
  jump : items[15]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : (items.drop 170).take startItems.length = startItems
  init : (items.drop 165).take initItems.length = initItems
  zero : (items.drop 227).take zeroItems.length = zeroItems
  loop : (items.drop 174).take mainLoopItems.length = mainLoopItems
  ram : a.labels.reverse.lookup "rt_ram" = some 32768
  ramSize : a.labels.reverse.lookup "rt_ram_size" = some 311
  idle : a.labels.reverse.lookup "rt_idle" = some 32768
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel "main") = some e ∧ e < 65536
  /-- `main` and what it calls do not write the loop's count. -/
  nowr : img.plan.wrB "main" 32768 = false
  room : img.plan.stackLo + img.plan.depthOf "main" ≤ 65534
  slo : img.plan.stackLo ≤ 65532
  data : ∀ iv, iv ∈ img.plan.data → 32769 ≤ iv.1 ∧ iv.2 ≤ 33079

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
theorem loopNeed {a : Assembled} (ha : assemble items = .ok a) : LoopNeed img a 174 32768 "main" Loop.main := by
  have F := facts ha
  exact
    { loop := F.loop, idle := F.idle, entry := F.entry, nowr := F.nowr, room := F.room
      iaRam := ⟨Nat.le_refl _, by decide⟩
      ram := by decide
      stackHi := rfl
      data := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        omega
      fn := rfl, name := rfl, live := rfl, noreg := rfl, isEntry := rfl }

/-- **At the head of the loop**: the CPU there with its stack empty, the
shared bytes as the IR's state `st` has them, the loop's count of idle
calls at zero, and the machine holding `st`'s world with its mark at the
world's position in the input. -/
abbrev AtLoop (a : Assembled) (addrs : List Nat) (st : IR.Sem.St) (s : Cpu) (w : HW) : Prop :=
  Z80Gen.AtLoop img 174 32768 a addrs st s w

/-- **One turn of the loop** (`Z80Gen.loop_iter`, for this image). -/
theorem loop_iter {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    {st : IR.Sem.St} {s : Cpu} {w : HW} (L : AtLoop a addrs st s w) (m : Nat) :
    (st.world.next.1 = 0xFFFF ∧ ∃ s' w', WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧ s'.halted = true ∧
        s'.iff1 = false ∧ w'.1 = st.world) ∨
    (st.world.next.1 ≠ 0xFFFF ∧
      match IR.Sem.callF m img.ctx "main" st with
      | .ok _ st' => (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off) →
          ∃ s' w', WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧ AtLoop a addrs st' s' w'
      | .trap st' => ∃ s' w', WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧ w'.1 = st'.world ∧
          Trapped (Zof a addrs (0, 0)) st' s'
      | _ => True) :=
  Z80Gen.loop_iter (loopNeed ha) hsize hset L m

/-- A call of `main` with input remaining moves the position in the
input — along the run from `st`: what is taken of the program for the
loop not to be left before the input is used up. -/
abbrev Moves (m : Nat) (st : IR.Sem.St) : Prop := Z80Gen.Moves img "main" m st

/-- **The loop against `irIter`** (`Z80Gen.loop_run`, for this image). -/
theorem loop_run {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (m : Nat) :
    ∀ (j : Nat) (st : IR.Sem.St) (s : Cpu) (w : HW), AtLoop a addrs st s w → Moves m st →
      ∀ st', irIter m img.ctx j st = some st' →
        (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧ AtLoop a addrs st' s' w') ∨
        (∃ i sti s' w', i ≤ j ∧ irIter m img.ctx i st = some sti ∧ WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧
          s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF) :=
  Z80Gen.loop_run (loopNeed ha) hsize hset m

theorem initMem_eq (m : ByteArray) : IR.initMem layout Loop.ir.globals m = (m.set! 398 40).set! 399 1 := rfl

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- From reset to the head of the loop, and the loop (for the image `a` with its addresses). -/
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
  have B : BootNeed (Zof a addrs (0, 0)) 15 170 165 227 32768 311 :=
    { head := fun i hi => by
        have hlt : i < (items.take 15).length := by
          have : (items.take 15).length = 15 := by decide +kernel
          omega
        have hm := F.head _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 15)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 15)[i] = it at hm hget
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
      isz := by show (IR.initMem _ _ _).size = _; rw [initMem_eq, set_size, set_size]; simp [ByteArray.size]
      sp := hsp1
      mem := fun x hx => by
        obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
        have := F.data iv hm
        rw [hzeroed x (by omega) (by omega)]
        show _ = (IR.initMem _ _ _).get! x
        rw [initMem_eq, getBang_set _ _ _ _ (by omega), getBang_set _ _ _ _ (by omega), zeros_get]
      idle := hzeroed 32768 (Nat.le_refl _) (by decide)
      world := rfl
      mark := rfl
      nval := rfl }
  rcases loop_run ha hsize hset m j (st0 inputs) s1 _ L0 hmv st' hit with
    ⟨s2, w2, stp, L2⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, hh2, hi2, hw2, hex⟩
  · exact Or.inl ⟨s2, w2, (Steps.lift ok stb _).trans stp, L2⟩
  · exact Or.inr ⟨i, sti, s2, w2, hi, hiter, (Steps.lift ok stb _).trans stp, hh2, hi2, hw2, hex⟩

/-- **The loopback image for the harness, from reset.**  The CPU starts
at address 0 with the image in ROM; the machine holds the input.  For
any number `j` of calls of `main` that end in the IR's semantics from
its initial state (each moving the position in the input while input
remains): the machine gets to the head of the loop with the world those
calls leave — the input consumed, the events emitted — or it left the
loop after `i ≤ j` of them and stopped (`di; halt`) with the world `i`
calls leave, **the input used up**.
Nothing is taken of the layout, the image or the runtime. -/
theorem loopH_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            AtLoop a addrs st' s' w') ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := loopH_setting
  exact ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit =>
    run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_run

/-- **With the input used up the machine stops**: from reset, when
`j` calls of `main` end in the IR's semantics and leave no input, the
machine stopped (`di; halt`) after `i ≤ j` of them, with the world `i`
calls leave and no input left. -/
theorem loopH_run_halt :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), Moves m (st0 inputs) → irIter m img.ctx j (st0 inputs) = some st' →
          st'.world.next.1 = 0xFFFF →
          ∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧ st_i.world.next.1 = 0xFFFF := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := loopH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hmv hit hex => ?_⟩
  rcases run_core ha hsize hset inputs s hpc I hh hrs hsz j m st' hmv hit with ⟨s1, w1, stp, L⟩ | hr
  · rcases loop_iter ha hsize hset L m with ⟨_, s2, w2, st2, hh2, hi2, hw2⟩ | ⟨hnex, _⟩
    · exact ⟨j, st', s2, w2, Nat.le_refl _, hit, stp.trans st2, hh2, hi2, hw2, hex⟩
    · exact absurd hex hnex
  · exact hr

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_run_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_run_halt

end Ember.Proof.Z80Gen.LoopH
