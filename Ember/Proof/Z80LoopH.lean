import Ember.Proof.Z80LoopHItems
import Ember.Proof.Z80Boot
import Ember.Proof.Z80World

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

/-! ## The machine of the harness -/

/-- The machine's state: the world, the byte latched by the last read
of `0xD1` that took one, and the position in the input when `0xD9` was
last read, and the value of the note to come (what has been written
of it to `0xDA`, and how many bytes). -/
abbrev HW := World × UInt8 × (Nat × Nat) × (Nat × Nat)

def hbus (w : HW) (p : UInt16) : UInt8 :=
  if lo p = 0xD0 then (if kindOf w.1 = 2 then 0 else 1)
  else if lo p = 0xD1 then kindOf w.1
  else if lo p = 0xD2 then w.2.1
  else if lo p = 0xD8 then 0      -- which program of the image: the first
  else if lo p = 0xD9 then (if (w.1.pos, w.1.off) ≠ w.2.2.1 then 1 else 0)
  else 0xFF

def hdev (c : IR.Ctx) (w : HW) : IoEvent → HW
  | .none => w
  | .read p =>
    if lo p = 0xD1 then (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2.1, w.2.2)
    else if lo p = 0xD9 then (w.1, w.2.1, (w.1.pos, w.1.off), w.2.2.2)
    else w
  | .write p v =>
    if lo p = 0xD3 then ((IR.Sem.effect c w.1 .outByte [v.toNat]).2, w.2)
    else if lo p = 0xD4 then ((IR.Sem.effect c w.1 .outEnd []).2, w.2)
    else if lo p = 0xD5 then ((IR.Sem.effect c w.1 .drop [v.toNat]).2, w.2)
    else if lo p = 0xDA then (w.1, w.2.1, w.2.2.1, (w.2.2.2.1 + v.toNat * 2 ^ (8 * w.2.2.2.2), w.2.2.2.2 + 1))
    else if lo p = 0xD6 then ((IR.Sem.effect c w.1 .note [v.toNat, w.2.2.2.1]).2, w.2.1, w.2.2.1, (0, 0))
    else w

/-- The machine stands for the world `wd`, its mark at `μ`, no byte of
a note's value pending. -/
def hrel (μ : Nat × Nat) (wd : World) (w : HW) : Prop := w.1 = wd ∧ w.2.2.1 = μ ∧ w.2.2.2 = (0, 0)

/-- The setting: the plan of the image, the image, the harness.  `μ` is
where the mark is — the functions leave it (only the loop reads `0xD9`),
which is said by taking it into what the machine stands for. -/
def Zof (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : ZCtx :=
  img.plan.toZ (img.around a addrs HW hbus (hdev img.ctx) (hrel μ))

def harness (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : Harness (Zof a addrs μ) where
  view := fun w => (w.1, w.2.1)
  wrelView := fun _ _ h => h.1
  busKind := fun w p h => by show hbus w p = _; simp [hbus, h]
  busByte := fun w p h => by show hbus w p = _; simp [hbus, h]
  rdNext := fun wd w p h hw => by
    show hrel μ _ (hdev img.ctx w (.read p))
    obtain ⟨h1, h2⟩ := hw
    simp only [hdev, h, if_true]
    exact ⟨by rw [h1], h2⟩
  rdLatch := fun w p h hn => by show (hdev img.ctx w (.read p)).2.1 = _; simp [hdev, h, hn]
  rdByte := fun wd w p h hw => by
    show hrel μ _ (hdev img.ctx w (.read p))
    have : hdev img.ctx w (.read p) = w := by simp [hdev, h]
    rw [this]
    exact hw
  wrByte := fun wd w p v h hw => by
    show hrel μ _ (hdev img.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    simp only [hdev, h, if_true]
    exact ⟨by rw [h1]; rfl, h2⟩
  wrEnd := fun wd w p v h hw => by
    show hrel μ _ (hdev img.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    have : hdev img.ctx w (.write p v) = ((IR.Sem.effect img.ctx w.1 .outEnd []).2, w.2) := by simp [hdev, h]
    rw [this]
    exact ⟨by rw [h1]; rfl, h2⟩
  wrNote := fun wd w p0 p1 p2 p3 p b0 b1 b2 b3 k h0 h1 h2 h3 h hw => by
    show hrel μ _ (hdev img.ctx (hdev img.ctx (hdev img.ctx (hdev img.ctx (hdev img.ctx w (.write p0 b0))
      (.write p1 b1)) (.write p2 b2)) (.write p3 b3)) (.write p k))
    obtain ⟨e1, e2, e3⟩ := hw
    simp only [hdev, h0, h1, h2, h3, h, e3, show ¬ ((0xDA : UInt8) = 0xD3) by decide, show ¬ ((0xDA : UInt8) = 0xD4) by decide,
      show ¬ ((0xDA : UInt8) = 0xD5) by decide, show ¬ ((0xD6 : UInt8) = 0xD3) by decide,
      show ¬ ((0xD6 : UInt8) = 0xD4) by decide, show ¬ ((0xD6 : UInt8) = 0xD5) by decide,
      show ¬ ((0xD6 : UInt8) = 0xDA) by decide, if_true, if_false]
    refine ⟨?_, e2, rfl⟩
    rw [e1]
    have hv : 0 + b0.toNat * 2 ^ (8 * 0) + b1.toNat * 2 ^ (8 * (0 + 1)) + b2.toNat * 2 ^ (8 * (0 + 1 + 1)) +
        b3.toNat * 2 ^ (8 * (0 + 1 + 1 + 1)) =
        b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * 0))) := by
      rw [show (2 : Nat) ^ (8 * 0) = 1 from rfl, show (2 : Nat) ^ (8 * (0 + 1)) = 256 from rfl,
        show (2 : Nat) ^ (8 * (0 + 1 + 1)) = 65536 from rfl, show (2 : Nat) ^ (8 * (0 + 1 + 1 + 1)) = 16777216 from rfl]
      omega
    rw [hv]
    rfl
  wrDrop := fun wd w p v h hw => by
    show hrel μ _ (hdev img.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    have : hdev img.ctx w (.write p v) = ((IR.Sem.effect img.ctx w.1 .drop [v.toNat]).2, w.2) := by simp [hdev, h]
    rw [this]
    exact ⟨by rw [h1]; rfl, h2⟩

/-- The machine runs the same whatever the mark is taken to be. -/
theorem wrun_mark (a : Assembled) (addrs : List Nat) (μ μ' : Nat × Nat) : ∀ (n : Nat) (x : Cpu × HW),
    wrun (Zof a addrs μ) n x = wrun (Zof a addrs μ') n x
  | 0, _ => rfl
  | n + 1, x => by
    show wrun (Zof a addrs μ) n (wstep (Zof a addrs μ) x) = wrun (Zof a addrs μ') n (wstep (Zof a addrs μ') x)
    rw [wrun_mark a addrs μ μ' n]
    rfl

theorem wsteps_mark {a : Assembled} {addrs : List Nat} {μ μ' : Nat × Nat} {x y : Cpu × HW}
    (h : WSteps (Zof a addrs μ) x y) : WSteps (Zof a addrs μ') x y := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← wrun_mark a addrs μ μ' n]; exact hn⟩

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

/-- The harness's loop: call the entry while input remains and until
three calls in a row have not moved the position in the input. -/
def loopItems : List Item :=
  [.label "rt_main",
   .ins ⟨.in, [.a, .mem (.num 0xD0)]⟩, .ins ⟨.or, [.a]⟩, .ins ⟨.jr, [.z, .imm (.sym "rt_done")]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_idle")]⟩, .ins ⟨.cp, [.imm (.num 3)]⟩, .ins ⟨.jr, [.nc, .imm (.sym "rt_done")]⟩,
   .ins ⟨.call, [.imm (.sym "f_entry")]⟩,
   .ins ⟨.in, [.a, .mem (.num 0xD9)]⟩, .ins ⟨.or, [.a]⟩, .ins ⟨.jr, [.nz, .imm (.sym "rt_main_r")]⟩,
   .ins ⟨.ld, [.hl, .imm (.sym "rt_idle")]⟩, .ins ⟨.inc, [.mhl]⟩, .ins ⟨.jr, [.imm (.sym "rt_main")]⟩,
   .label "rt_main_r", .ins ⟨.xor, [.a]⟩, .ins ⟨.ld, [.mem (.sym "rt_idle"), .a]⟩, .ins ⟨.jr, [.imm (.sym "rt_main")]⟩,
   .label "rt_done", .ins ⟨.di, []⟩, .ins ⟨.halt, []⟩, .ins ⟨.jr, [.imm (.sym "rt_done")]⟩]

/-- What start-up and the loop need of the image and of the plan, computed. -/
def bootCheck : Bool :=
  (items.take 15).all isEqu && decide (items[15]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)) &&
  decide ((items.drop 170).take startItems.length = startItems) &&
  decide ((items.drop 165).take initItems.length = initItems) &&
  decide ((items.drop 227).take zeroItems.length = zeroItems) &&
  decide ((items.drop 174).take loopItems.length = loopItems) &&
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
  loop : (items.drop 174).take loopItems.length = loopItems
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

/-- **At the head of the loop**: the CPU there with its stack empty, the
shared bytes as the IR's state `st` has them, the loop's count of idle
calls at zero, and the machine holding `st`'s world with its mark at the
world's position in the input. -/
structure AtLoop (a : Assembled) (addrs : List Nat) (st : IR.Sem.St) (s : Cpu) (w : HW) : Prop where
  at_ : At addrs 174 s
  image : Img a 0 s
  run : s.halted = false
  rs : s.ramStart.toNat = 0x8000
  msz : s.mem.size = 65536
  isz : st.mem.size = 65536
  sp : s.sp = 0
  mem : ∀ x, inIv LoopH.img.plan.data x = true → s.mem.get! x = st.mem.get! x
  idle : s.mem.get! 32768 = 0
  world : w.1 = st.world
  mark : w.2.2.1 = (st.world.pos, st.world.off)
  nval : w.2.2.2 = (0, 0)

theorem orA_cond_z (s : Cpu) : (orA s).cond 1 = (s.a.toNat == 0) := orA_z s

theorem sp_wrap {x : UInt16} (h : x.toNat = 65534) : x + 2 = 0 := by
  have : x = 65534 := UInt16.toNat_inj.mp h
  rw [this]
  rfl

/-- **One turn of the loop.**  From its head: when the input is used up
the loop is left and the CPU stops (`di; halt`); else the entry is
called, and — as `IR.Sem.callF` says — the CPU is back at the head with
the machine holding the world the call left (given that the call moved
the position in the input: then the count of idle calls is set to zero
again), or it is at `rt_trap`.  The count of idle calls is zero at the
head, so the loop is never left by it. -/
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
      | _ => True) := by
  have F := facts ha
  obtain ⟨E, hEsym, hMsym, hElt⟩ := F.entry
  obtain ⟨ok, hcal⟩ := hset w.2.2.1
  have hl : Has (Zof a addrs w.2.2.1) 174 loopItems := has_of F.loop
  have hdat : ∀ x, inIv img.plan.data x = true → 32769 ≤ x ∧ x < 33079 := by
    intro x hx
    obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
    have := F.data iv hm
    omega
  have M : Mach (Zof a addrs w.2.2.1) s := ⟨L.image, L.run⟩
  have at1 := at_label ok (hl.get 0 rfl) L.at_
  -- does input remain?
  obtain ⟨c1, p, hp, st1, at2, M1, hS1, ha1⟩ := in_step ok (n := 0xD0) (by decide) (hl.get 1 rfl) M at1 w
  have hp' : lo p = 0xD0 := hp
  have hdev1 : (Zof a addrs w.2.2.1).dev w (.read p) = w := by
    show hdev img.ctx w (.read p) = w
    simp [hdev, hp']
  rw [hdev1] at st1
  have ha1' : c1.a = if kindOf st.world = 2 then 0 else 1 := by
    rw [ha1, ← L.world]
    show hbus w p = _
    simp [hbus, hp']
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_or_a (hl.get 2 rfl) M1 at2
  obtain ⟨c3, st3, M3, hS3, _, hbr3⟩ := jr_cond_step ok (cA := .z) (y := 1) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (hl.get 3 rfl) (hl.get 18 rfl) M2 at3
  have hz3 : (orA c1).cond 1 = decide (st.world.next.1 = 0xFFFF) := by
    rw [orA_cond_z, ha1']
    unfold kindOf
    by_cases h1 : st.world.next.1 = 0xFFFF
    · simp [h1]
    · by_cases h2 : st.world.next.1 = 0x0100 <;> simp [h1, h2]
  rw [hz3] at hbr3
  have st03 : WSteps (Zof a addrs w.2.2.1) (s, w) (c3, w) := st1.trans (Steps.lift ok (st2.trans st3) _)
  have hS03 : Sys s c3 := (hS1.trans hS2).trans hS3
  by_cases hex : st.world.next.1 = 0xFFFF
  · -- the input is used up: out of the loop, and stop
    rw [decide_eq_true hex, if_pos rfl] at hbr3
    have at19 := at_label ok (hl.get 18 rfl) hbr3
    obtain ⟨s4, st4, hh4, hi4, _⟩ := di_halt ok (hl.get 19 rfl) (hl.get 20 rfl) M3 at19
    exact Or.inl ⟨hex, s4, w, wsteps_mark (st03.trans (Steps.lift ok st4 _)), hh4, hi4, L.world⟩
  refine Or.inr ⟨hex, ?_⟩
  rw [decide_eq_false hex] at hbr3
  simp only [Bool.false_eq_true, if_false] at hbr3
  -- the count of idle calls is zero: not three
  obtain ⟨c4, st4, at5, M4, hS4, ha4⟩ := ld_a_cell ok (hl.get 4 rfl) F.idle (by decide) M3 hbr3
  have ha4' : c4.a = 0 := by rw [ha4, hS03.1]; exact L.idle
  obtain ⟨st5, at6, M5, hS5⟩ := does_raw ok (does_cp_n 3) (hl.get 5 rfl) M4 at5
  obtain ⟨c6, st6, M6, hS6, _, hbr6⟩ := jr_cond_step ok (cA := .nc) (y := 2) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (hl.get 6 rfl) (hl.get 18 rfl) M5 at6
  have hnc : (cpN 3 c4).cond 2 = false := by
    show (!(cpN 3 c4).flag FC) = false
    rw [cpN_c 3 (by decide), ha4']
    rfl
  rw [hnc] at hbr6
  simp only [Bool.false_eq_true, if_false] at hbr6
  have hS06 : Sys s c6 := ((hS03.trans hS4).trans hS5).trans hS6
  have st06 : WSteps (Zof a addrs w.2.2.1) (s, w) (c6, w) :=
    st03.trans (Steps.lift ok ((st4.trans st5).trans st6) _)
  -- call the entry
  obtain ⟨c7, st7, hsp7, hpc7, I7, hh7, hrs7, hsz7, hmem7, hback⟩ := call_top ok (hl.get 7 rfl) hEsym hElt hbr6
    M6.1 M6.2 (by rw [hS06.2.1]; exact L.rs) (by rw [hS06.1]; exact L.msz) (by rw [hS06.2.2.2]; exact L.sp)
    (show (32768 : Nat) ≤ 65534 by decide)
  have st07 : WSteps (Zof a addrs w.2.2.1) (s, w) (c7, w) := st06.trans (Steps.lift ok st7 _)
  have hroom := F.room
  have ent : Entry (Zof a addrs w.2.2.1) Loop.main st 0 c7 :=
    ⟨⟨E, hMsym, hpc7⟩, I7, hh7, by rw [hrs7, hS06.2.1]; exact L.rs, hsz7, L.isz, fun x hx => by
        have := hdat x hx
        rw [hmem7 x (by omega), hS06.1]
        exact L.mem x hx,
      ⟨by rw [hsp7]; exact hroom, by rw [hsp7]; exact Nat.le_refl _⟩, fun n sl h => by cases h⟩
  have hout := hcal m "main" st Loop.main st 0 c7 w rfl rfl rfl ent ⟨L.world, rfl, L.nval⟩
  cases hres : IR.Sem.callF m img.ctx "main" st with
  | fuel => trivial
  | bad => trivial
  | trap st' =>
    rw [hres] at hout
    obtain ⟨s', w', stt, hwt, htr⟩ := hout
    exact ⟨s', w', wsteps_mark (st07.trans stt), hwt.1, htr⟩
  | ok r st' =>
    rw [hres] at hout
    intro hmoved
    obtain ⟨s2, w2, v, stc, hw2, _, hret⟩ := hout
    have hsp2 : s2.sp = 0 := by rw [hret.sp]; exact sp_wrap hsp7
    have at8 : At addrs (174 + 8) s2 := hback s2 (by rw [hret.pc]; show IR.Sem.rd c7.mem c7.sp.toNat 2 = _; rw [hsp7])
    have M8 : Mach (Zof a addrs w.2.2.1) s2 := ⟨hret.img, hret.run⟩
    have hidle2 : s2.mem.get! 32768 = 0 := by
      rw [hret.out 32768 (fun h => by
        have h' : img.plan.wrB "main" 32768 = true := h
        rw [F.nowr] at h'
        cases h')]
      show c7.mem.get! 32768 = 0
      rw [hmem7 _ (by decide), hS06.1]
      exact L.idle
    -- has the position in the input moved?
    obtain ⟨c9, p9, hp9, st9, at10, M9, hS9, ha9⟩ := in_step ok (n := 0xD9) (by decide) (hl.get 8 rfl) M8 at8 w2
    have hp9' : lo p9 = 0xD9 := hp9
    have hdev9 : (Zof a addrs w.2.2.1).dev w2 (.read p9) = (w2.1, w2.2.1, (w2.1.pos, w2.1.off), w2.2.2.2) := by
      show hdev img.ctx w2 (.read p9) = _
      simp [hdev, hp9']
    rw [hdev9] at st9
    have ha9' : c9.a = 1 := by
      rw [ha9]
      show hbus w2 p9 = 1
      have hne : (w2.1.pos, w2.1.off) ≠ w2.2.2.1 := by
        rw [hw2.1, hw2.2.1, L.mark]
        exact hmoved
      simp [hbus, hp9', hne]
    obtain ⟨st10, at11, M10, hS10⟩ := does_raw ok does_or_a (hl.get 9 rfl) M9 at10
    obtain ⟨c11, st11, M11, hS11, _, hbr11⟩ := jr_cond_step ok (cA := .nz) (y := 0) (Or.inl ⟨rfl, rfl⟩)
      (hl.get 10 rfl) (hl.get 14 rfl) M10 at11
    have hnz : (orA c9).cond 0 = true := by
      show (!(orA c9).flag FZ) = true
      rw [orA_z, ha9']
      rfl
    rw [hnz, if_pos rfl] at hbr11
    -- it has: the count of idle calls starts again
    have at15 := at_label ok (hl.get 14 rfl) hbr11
    obtain ⟨st12, at16, M12, hS12⟩ := does_raw ok does_xor_a (hl.get 15 rfl) M11 at15
    have hS212 : Sys s2 (xorA c11) := ((hS9.trans hS10).trans hS11).trans hS12
    obtain ⟨c13, st13, at17, M13, hmem13, hrs13, hh13, hsp13⟩ := ld_cell_a ok (hl.get 16 rfl) F.idle (Nat.le_refl _)
      (by decide) M12 (by rw [hS212.2.1]; exact hret.rs) at16
    rw [xorA_a, hS212.1] at hmem13
    obtain ⟨c14, st14, M14, hS14, _, at0⟩ := jr_step ok (hl.get 17 rfl) (hl.get 0 rfl) M13 at17
    refine ⟨c14, (w2.1, w2.2.1, (w2.1.pos, w2.1.off), w2.2.2.2), ?_, ?_⟩
    · exact wsteps_mark (((st07.trans stc).trans st9).trans
        (Steps.lift ok ((((st10.trans st11).trans st12).trans st13).trans st14) _))
    · refine ⟨at0, M14.1, M14.2, ?_, ?_, hret.isz, ?_, fun x hx => ?_, ?_, hw2.1, ?_, hw2.2.2⟩
      · rw [hS14.2.1, hrs13, hS212.2.1]
        exact hret.rs
      · rw [hS14.1, hmem13, set_size]
        exact hret.msz
      · rw [hS14.2.2.2, hsp13, hS212.2.2.2]
        exact hsp2
      · have := hdat x hx
        rw [hS14.1, hmem13, getBang_set _ _ _ _ (by omega)]
        exact hret.mem x hx
      · rw [hS14.1, hmem13]
        exact getBang_same _ _ _ (by rw [hret.msz]; decide)
      · show (w2.1.pos, w2.1.off) = _
        rw [hw2.1]

/-- A call of `main` with input remaining moves the position in the
input — along the run from `st`: what is taken of the program for the
loop not to be left before the input is used up. -/
def Moves (m : Nat) (st : IR.Sem.St) : Prop :=
  ∀ i sti r sti', irIter m img.ctx i st = some sti → IR.Sem.callF m img.ctx "main" sti = .ok r sti' →
    sti.world.next.1 ≠ 0xFFFF → (sti'.world.pos, sti'.world.off) ≠ (sti.world.pos, sti.world.off)

/-- **The loop against `irIter`**: when `j` calls of `main` end in the
IR's semantics, the machine is back at the head of the loop with the
world those calls leave — or it left the loop after `i ≤ j` of them and
stopped, the world being the one `i` calls leave **and the input used
up**. -/
theorem loop_run {a : Assembled} {addrs : List Nat} (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (m : Nat) :
    ∀ (j : Nat) (st : IR.Sem.St) (s : Cpu) (w : HW), AtLoop a addrs st s w → Moves m st →
      ∀ st', irIter m img.ctx j st = some st' →
        (∃ s' w', WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧ AtLoop a addrs st' s' w') ∨
        (∃ i sti s' w', i ≤ j ∧ irIter m img.ctx i st = some sti ∧ WSteps (Zof a addrs (0, 0)) (s, w) (s', w') ∧
          s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF)
  | 0, st, s, w, L, _, st', h => by
    cases h
    exact Or.inl ⟨s, w, WSteps.refl _ _, L⟩
  | j + 1, st, s, w, L, hmv, st', h => by
    rw [irIter] at h
    have he : img.ctx.prog.entry = "main" := rfl
    rw [he] at h
    rcases loop_iter ha hsize hset L m with ⟨hex, s1, w1, st1, hh, hi, hw⟩ | ⟨hnex, hit⟩
    · exact Or.inr ⟨0, st, s1, w1, Nat.zero_le _, rfl, st1, hh, hi, hw, hex⟩
    · cases hc : IR.Sem.callF m img.ctx "main" st with
      | ok r st1 =>
        rw [hc] at h hit
        obtain ⟨s1, w1, stp, L1⟩ := hit (hmv 0 st r st1 rfl hc hnex)
        have hmv1 : Moves m st1 := fun i sti r' sti' hi hcall hne =>
          hmv (i + 1) sti r' sti' (by rw [irIter, he, hc]; exact hi) hcall hne
        rcases loop_run ha hsize hset m j st1 s1 w1 L1 hmv1 st' h with ⟨s2, w2, stp2, L2⟩ |
          ⟨i, sti, s2, w2, hi, hiter, stp2, hh, hif, hw, hex⟩
        · exact Or.inl ⟨s2, w2, stp.trans stp2, L2⟩
        · refine Or.inr ⟨i + 1, sti, s2, w2, by omega, ?_, stp.trans stp2, hh, hif, hw, hex⟩
          rw [irIter, he, hc]
          exact hiter
      | trap st1 => rw [hc] at h; cases h
      | fuel => rw [hc] at h; cases h
      | bad => rw [hc] at h; cases h

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
