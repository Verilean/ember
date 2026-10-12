import Ember.Proof.Z80LoopHItems
import Ember.Proof.Z80Boot

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
image's own items, proved (`Z80Boot`).  For any number of calls of
`main` that end in the IR's semantics from its initial state, the
machine is at the head of the loop with the world those calls leave, or
it left the loop earlier with the world of the calls made till then.

What the statements are about, and what they are not:

* the image is `LoopH.items` assembled; that these are the items
  `build` gives without the passes, the IR what `IR.lower` returns and
  the layout what `build` computes are `#guard`s (evaluation, not proof).
  What the kernel computes: the generator's environments, the checks of
  the plan, the assembly, where the routines are, the symbols;
* the machine is the CPU model with `hbus`/`hdev`: the world behind the
  harness's ports.  `Ember.Z80.Machine`, which the tests run, does the
  same at these ports by reading it (it records a drop by its code where
  the IR's world has the reason's name); that is not proved — its
  `normalize` is a `while` loop, opaque to the kernel;
* when the loop is left is not said (the IR's own driver, `Sem.run`, is
  a `partial` loop without a theorem); and that the calls of `main` do
  end — the loopback never traps (`loop_safe`, M5) — is a theorem about
  the Ember semantics not composed with this one yet;
* not the image as built by default (with the passes on the assembly).
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-- RAM from `0x8000`: the three cells of the harness's runtime, the
globals, the frames; eight bytes for the accumulator (which this image
does not have); the stack up to the top.  A routine of the runtime needs
no stack. -/
def img : ImgIn :=
  { ir := Loop.ir, layout, dropReasons := ["oversize-frame"], ramStart := 0x8000, stackLo := 33089,
    stackHi := 65536, acc := 33081, rtK := 0, rt := [(32768, 32771)], items, genOff := 18 }

theorem img_check : img.check = true := by decide +kernel

/-! ## The machine of the harness -/

def hbus (w : World × UInt8) (p : UInt16) : UInt8 :=
  if lo p = 0xD1 then kindOf w.1 else if lo p = 0xD2 then w.2
  else if lo p = 0xD0 then (if kindOf w.1 = 2 then 0 else 1) else 0xFF

def hdev (c : IR.Ctx) (w : World × UInt8) : IoEvent → World × UInt8
  | .none => w
  | .read p => if lo p = 0xD1 then (w.1.next.2, lo w.1.next.1) else w
  | .write p v =>
    if lo p = 0xD3 then ((IR.Sem.effect c w.1 .outByte [v.toNat]).2, w.2)
    else if lo p = 0xD4 then ((IR.Sem.effect c w.1 .outEnd []).2, w.2)
    else if lo p = 0xD5 then ((IR.Sem.effect c w.1 .drop [v.toNat]).2, w.2)
    else w

/-- The setting: the plan of the image, the image, the harness. -/
def Zof (a : Assembled) (addrs : List Nat) : ZCtx :=
  img.plan.toZ (img.around a addrs (World × UInt8) hbus (hdev img.ctx) (fun wd w => w.1 = wd))

def harness (a : Assembled) (addrs : List Nat) : Harness (Zof a addrs) where
  view := fun w => w
  wrel := fun _ _ => Iff.rfl
  busKind := fun w p h => by show hbus w p = _; simp [hbus, h]
  busByte := fun w p h => by show hbus w p = _; simp [hbus, h]
  rdNext := fun w p h => by show hdev img.ctx w (.read p) = _; simp [hdev, h]
  rdByte := fun w p h => by show (hdev img.ctx w (.read p)).1 = _; simp [hdev, h]
  rdMore := fun w p h => by show (hdev img.ctx w (.read p)).1 = _; simp [hdev, h]
  busMore := fun w p h => by show hbus w p = _; simp [hbus, h]
  wrByte := fun w p v h => by show (hdev img.ctx w (.write p v)).1 = _; simp [hdev, h]; rfl
  wrEnd := fun w p v h => by show (hdev img.ctx w (.write p v)).1 = _; simp [hdev, h]; rfl
  wrDrop := fun w p v h => by show (hdev img.ctx w (.write p v)).1 = _; simp [hdev, h]; rfl

/-! ## The routines of the runtime in the image -/

/-- The routines the image calls. -/
def calls : List String :=
  (items.filterMap fun it =>
    match it with
    | .ins ⟨.call, [.imm (.sym n _)]⟩ => some n
    | _ => none).eraseDups

theorem calls_eq : calls = ["rt_out_byte", "rt_out_end", "rt_drop", "f_slip_send", "f_slip_store", "rt_input",
    "f_loop_rx", "rt_zero", "rt_init", "f_entry"] := by decide +kernel

theorem uses_mem {a : Assembled} {addrs : List Nat} {name : String} (h : Uses (Zof a addrs) name) :
    name ∈ calls := by
  obtain ⟨k, hk⟩ := h
  have hm : Item.ins ⟨.call, [.imm (.sym name)]⟩ ∈ items := List.mem_of_getElem? hk
  unfold calls
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- Where the routines are. -/
def rtCheck : Bool :=
  decide ((items.drop 201).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 210).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 213).take 3 = [.label "rt_drop", .ins ⟨.out, [.mem (.num 0xD5), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 216).take inputItems.length = inputItems) &&
  (match assemble items with
   | .ok a => a.labels.reverse.lookup "rt_consumed" == some 32768
   | .error _ => false)

theorem rtCheck_true : rtCheck = true := by decide +kernel

theorem has_of {a : Assembled} {addrs : List Nat} {k : Nat} {l : List Item}
    (h : (items.drop k).take l.length = l) : Has (Zof a addrs) k l := by
  intro j it hj
  have hlt : j < l.length := by
    rcases Nat.lt_or_ge j l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  rw [← h, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
  exact hj

/-- **The functions of the loopback image for the harness do what the
IR's functions do**: nothing is taken of the runtime. -/
theorem loopH_setting :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧ a.bytes.size < 65536 ∧ (Zof a addrs).OK ∧
      ∀ k g st1, Callee (Zof a addrs) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img.ok img_check
  obtain ⟨ok, hcallee⟩ := hall (World × UInt8) hbus (hdev img.ctx) (fun wd w => w.1 = wd) (fun _ => rfl)
  refine ⟨a, addrs, ha, hsize, ok, hcallee ?_⟩
  have hrc := rtCheck_true
  unfold rtCheck at hrc
  have ha' : assemble items = .ok a := ha
  rw [ha'] at hrc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hrc
  have H := harness a addrs
  have no : ∀ name, name ∉ calls → ¬ Uses (Zof a addrs) name := fun name h hu => h (uses_mem hu)
  have pure : ∀ (name : String) (rel : Cpu → Cpu → Prop), name ∉ calls → RtPure (Zof a addrs) name rel :=
    fun name rel h hu => absurd hu (no name h)
  have acc : ∀ (name : String) (pre : Cpu → Prop) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtAcc (Zof a addrs) name pre rel := fun name pre rel h hu => absurd hu (no name h)
  have hrt0 : inIv img.plan.rt 32768 = true := by decide +kernel
  have hrt : (Zof a addrs).rt 32768 := hrt0
  exact
    { bound := fun hu => absurd hu (no _ (by rw [calls_eq]; decide))
      wide :=
        { ld := acc _ _ _ (by rw [calls_eq]; decide +kernel)
          st := fun hu => absurd hu (no _ (by rw [calls_eq]; decide +kernel))
          bin := fun op => acc _ _ _ (by rw [calls_eq]; cases op <;> decide +kernel)
          cmp := pure _ _ (by rw [calls_eq]; decide +kernel) }
      accA := acc _ _ _ (by rw [calls_eq]; decide)
      accHL := acc _ _ _ (by rw [calls_eq]; decide)
      eff := fun e he => by
        cases e with
        | inputNext => exact harness_input ok H hsize (has_of h4) h5 hrt (by decide) _ (Or.inl rfl)
        | ringPop => exact harness_input ok H hsize (has_of h4) h5 hrt (by decide) _ (Or.inr rfl)
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
      ∀ k g st1, Callee (Zof a addrs) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, _, h⟩ := loopH_setting
  exact ⟨a, addrs, ha, h⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_ok

/-! ## From reset: start-up and the loop -/

/-- The IR's state the program starts in: the memory `Ember.Z80.IR`
starts with (`initMem`: zero but for the initial values — here the
constant `MTU`, at its address in ROM), the input still
to come.  (This is `irInit` of `Ember.Proof.IRLower` for the loopback
program and this layout.) -/
def st0 (inputs : Array Ember.Trace.Input) : IR.Sem.St :=
  { mem := IR.initMem layout Loop.ir.globals (ByteArray.mk (Array.replicate 65536 0)), world := { inputs, framed := false } }

def isEqu : Item → Bool
  | .equ _ _ => true
  | _ => false

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 17).all isEqu && decide (items[17]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 172).take startItems.length = startItems) &&
  decide ((items.drop 167).take initItems.length = initItems) &&
  decide ((items.drop 234).take zeroItems.length = zeroItems) &&
  decide ((items.drop 176).take loopItems.length = loopItems) &&
  (match assemble items with
   | .ok a =>
     a.labels.reverse.lookup "rt_ram" == some 32768 && a.labels.reverse.lookup "rt_ram_size" == some 313 &&
     a.labels.reverse.lookup "rt_idle" == some 32770 && a.labels.reverse.lookup "rt_before" == some 32769 &&
     (match a.labels.reverse.lookup "f_entry" with
      | some e => a.labels.reverse.lookup (fnLabel "main") == some e && decide (e < 65536)
      | none => false)
   | .error _ => false) &&
  inIv img.plan.rt 32770 && inIv img.plan.rt 32769 &&
  decide (img.plan.stackLo + img.plan.depthOf "main" ≤ 65534) && decide (img.plan.stackLo ≤ 65532) &&
  (img.plan.data.all fun iv => decide (32768 ≤ iv.1) && decide (iv.2 ≤ 33081))

theorem bootCheck_true : bootCheck = true := by decide +kernel

theorem initMem_eq (m : ByteArray) : IR.initMem layout Loop.ir.globals m = (m.set! 412 40).set! 413 1 := rfl

theorem zeros_get (x : Nat) : (ByteArray.mk (Array.replicate 65536 0)).get! x = 0 := by
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- **The loopback image for the harness, from reset.**  The CPU starts
at address 0 with the image in ROM; the machine holds the input.  For
any number `j` of calls of `main` that end in the IR's semantics from
its initial state: the machine gets to the head of the loop with the
world those calls leave — the input consumed, the events emitted — or
it left the loop after `i ≤ j` of them and stopped (`di; halt`), with
the world `i` calls leave: the input used up, or — input remaining — by
the loop's count of calls that consumed nothing (`Idle`; that this does
not happen is not proved).
Nothing is taken of the program, the layout, the image or the runtime. -/
theorem loopH_run :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∀ (j m : Nat) (st' : IR.Sem.St), irIter m img.ctx j (st0 inputs) = some st' →
          (∃ s' w', WSteps (Zof a addrs) (s, ((st0 inputs).world, 0)) (s', w') ∧
            AtLoop (Zof a addrs) 176 st' s' ∧ w'.1 = st'.world) ∨
          (∃ i st_i s' w', i ≤ j ∧ irIter m img.ctx i (st0 inputs) = some st_i ∧
            WSteps (Zof a addrs) (s, ((st0 inputs).world, 0)) (s', w') ∧
            s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = st_i.world ∧
            (st_i.world.next.1 = 0xFFFF ∨ Idle st_i.world)) := by
  obtain ⟨a, addrs, ha, hsize, ok, hcal⟩ := loopH_setting
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz j m st' hit => ?_⟩
  have hbc := bootCheck_true
  unfold bootCheck at hbc
  have ha' : assemble items = .ok a := ha
  rw [ha'] at hbc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hbc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, hjump⟩, hstart⟩, hinit⟩, hzero⟩, hloop⟩, hlab⟩, hrtI⟩, hrtB⟩, hdep⟩, hslo⟩, hdata⟩ := hbc
  obtain ⟨⟨⟨⟨hram, hrsz⟩, hidle⟩, hbefore⟩, hentry⟩ := hlab
  have H := harness a addrs
  have B : BootNeed (Zof a addrs) 17 172 167 234 32768 313 :=
    { head := fun i hi => by
        have hlt : i < (items.take 17).length := by
          have : (items.take 17).length = 17 := by decide +kernel
          omega
        have hm := hhead _ (List.getElem_mem hlt)
        have hget : items[i]? = some ((items.take 17)[i]) := by
          rw [List.getElem_take]
          exact List.getElem?_eq_getElem _
        generalize (items.take 17)[i] = it at hm hget
        cases it with
        | equ n v => exact ⟨n, v, hget⟩
        | _ => cases hm
      jump := hjump
      start := has_of hstart
      init := has_of hinit
      zero := has_of hzero
      ram := hram
      ramSize := hrsz
      n2 := by decide
      lo := Nat.le_refl _
      hi := by decide
      stackLo := hslo
      stackHi := rfl
      size := hsize }
  obtain ⟨s1, stb, at1, I1, hh1, hrs1, hsz1, hsp1, hzeroed⟩ := boot_ok ok B hpc I hh hrs hsz
  -- the IR's initial state and the CPU's memory agree on the shared bytes: both are zero there
  have hdat : ∀ x, (Zof a addrs).data x → 32768 ≤ x ∧ x < 33081 := by
    intro x hx
    obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
    have := hdata iv hm
    omega
  have L0 : AtLoop (Zof a addrs) 176 (st0 inputs) s1 :=
    { at_ := at1, img := I1, run := hh1, rs := hrs1, msz := hsz1,
      isz := by show (IR.initMem _ _ _).size = _; rw [initMem_eq, set_size, set_size]; simp [ByteArray.size]
      sp := hsp1
      mem := fun x hx => by
        obtain ⟨h1, h2⟩ := hdat x hx
        rw [hzeroed x h1 (by omega)]
        show _ = (IR.initMem _ _ _).get! x
        rw [initMem_eq, getBang_set _ _ _ _ (by omega), getBang_set _ _ _ _ (by omega), zeros_get] }
  have N : LoopNeed (Zof a addrs) 176 Loop.main :=
    { has := has_of hloop
      fn := rfl
      live := rfl
      noArg := rfl
      entry := by
        cases he : a.labels.reverse.lookup "f_entry" with
        | none => rw [he] at hentry; cases hentry
        | some e =>
          rw [he] at hentry
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hentry
          exact ⟨e, he, hentry.1, hentry.2⟩
      room := hdep
      top := rfl
      size := hsize
      idle := ⟨32770, hidle, hrtI, by decide⟩
      before := ⟨32769, hbefore, hrtB, by decide⟩ }
  have hcal' : ∀ m st1, Callee (Zof a addrs) (Zof a addrs).c.prog.entry st1
      (IR.Sem.callF m (Zof a addrs).c (Zof a addrs).c.prog.entry st1) := fun m st1 => hcal m _ st1
  rcases loop_run ok H N hcal' m j (st0 inputs) s1 ((st0 inputs).world, 0) L0 rfl st' hit with
    ⟨s2, w2, stp, L2, hw2⟩ | ⟨i, sti, s2, w2, hi, hiter, stp, at2, M2, hw2, hwhy⟩
  · exact Or.inl ⟨s2, w2, (Steps.lift ok stb _).trans stp, L2, hw2⟩
  · obtain ⟨s3, st3, hh3, hi3, _⟩ := done_halts ok N.has M2 at2
    exact Or.inr ⟨i, sti, s3, w2, hi, hiter, ((Steps.lift ok stb _).trans stp).trans (Steps.lift ok st3 _), hh3, hi3,
      hw2, hwhy⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_run

end Ember.Proof.Z80Gen.LoopH
