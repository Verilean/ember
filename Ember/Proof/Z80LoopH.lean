import Ember.Proof.Z80LoopHItems

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

What the statement is about: the functions, in the model of the CPU and
of the harness's ports as written here (`hdev`; `Ember.Z80.Machine` does
the same at these ports, by reading).  Not: start-up and the loop that
calls `main`; the image as built by default (with the passes).
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
  if lo p = 0xD1 then kindOf w.1 else if lo p = 0xD2 then w.2 else 0xFF

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
theorem loopH_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ k g st1, Callee (Zof a addrs) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img.ok img_check
  obtain ⟨ok, hcallee⟩ := hall (World × UInt8) hbus (hdev img.ctx) (fun wd w => w.1 = wd) (fun _ => rfl)
  refine ⟨a, addrs, ha, hcallee ?_⟩
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

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_ok

end Ember.Proof.Z80Gen.LoopH
