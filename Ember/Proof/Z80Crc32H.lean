import Ember.Proof.Z80Crc32HItems
import Ember.Proof.Z80HarnessW
import Ember.Proof.Z80Rt
import Ember.Proof.Z80Not
import Ember.Proof.Z80ShrW
import Ember.Proof.Z80AndXor

/-!
# Ember.Proof.Z80Crc32H — the functions of `crc32`'s image for the test harness (plan M7.3)

`crc32H_ok`: in the image the assembler makes of `Crc32H.items` —
`Crc32.ir`, the IR of the example `crc32` (`update`: eight shifts right
of four bytes by one, each with an `xor` by the polynomial when the low
bit is set; `main`: a byte of input into `crc`, or on `0x0100` the
complement of `crc` sent and `crc` reset) with the runtime of the test
harness, without the passes on the assembly — in the machine of the
harness, every function, entered as `Entry` says, returns as
`IR.Sem.callF` does with the machine holding the world it leaves.

Nothing is assumed of the program, the layout, the image or the runtime:
the routines the image calls from its functions — `rt_input`, `rt_ld32`,
`rt_st32`, `rt_acc_a`, `rt_xor32`, `rt_and32`, `rt_cmp32`, `rt_shr32`,
`rt_not32`, `rt_out_byte`, `rt_out_end` — are proved from their items
(`Z80Rt`, `Z80Wide`, `Z80Bytes`, `Z80Not`, `Z80ShrW`, `Z80AndXor`), and
the image calls no other routine of the runtime from its functions
(`calls_eq`).  The program has no index checks and no traps, and the
image has no `rt_trap` (the runtime leaves it out when nothing jumps
there): the plan is checked without the label (`labels := []`).

What the statement is about, and what it is not: the image is
`Crc32H.items` assembled; that these are the items `build` gives
without the passes, the IR what `IR.lower` returns for
`Ember.Lang.Examples.Crc32.prog` and the layout what `build` computes
are `#guard`s (`Z80Crc32IR`, `Z80Crc32HItems`), evaluated when those
files are built, not proved.  The machine is the CPU model with the
harness's ports (`hbus`, `hdev`).  Not here: start-up, reset, the loop,
the Ember semantics, or `Ember.Z80.Machine`.
-/

namespace Ember.Proof.Z80Gen.Crc32H
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

/-- RAM from `0x8000`: the runtime's accumulator (eight bytes), the
loop's count of idle calls, the global, the frames; the stack above.
A routine of the runtime needs two bytes of stack (`rtK`).  No label
`rt_trap`: nothing in the program traps. -/
def img : ImgIn :=
  { ir := Crc32.ir, layout, ramStart := 0x8000, stackLo := 32797, stackHi := 65536, acc := 32768, rtK := 2,
    rt := [], items, genOff := 10, labels := [] }

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

theorem calls_eq : calls = ["rt_acc_a", "rt_xor32", "rt_st32", "rt_ld32", "rt_and32", "rt_cmp32", "rt_shr32",
    "rt_input", "rt_not32", "rt_out_byte", "rt_out_end", "f_update", "rt_zero", "rt_init", "f_entry"] := by
  decide +kernel

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
  decide ((items.drop 239).take inputItems.length = inputItems) &&
  decide ((items.drop 169).take ldItems.length = ldItems) &&
  decide ((items.drop 159).take stItems.length = stItems) &&
  decide ((items.drop 132).take accItems.length = accItems) &&
  decide ((items.drop 144).take (bytewiseItems "xor" [] ⟨.xor, [.mhl]⟩).length =
    bytewiseItems "xor" [] ⟨.xor, [.mhl]⟩) &&
  decide ((items.drop 178).take (bytewiseItems "and" [] ⟨.and, [.mhl]⟩).length =
    bytewiseItems "and" [] ⟨.and, [.mhl]⟩) &&
  decide ((items.drop 193).take cmpItems.length = cmpItems) &&
  decide ((items.drop 215).take shrWItems.length = shrWItems) &&
  decide ((items.drop 255).take notWItems.length = notWItems) &&
  decide ((items.drop 269).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 272).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩])

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
theorem crc32H_setting :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img.ok img_check
  refine ⟨a, addrs, ha, hsize, fun μ => ?_⟩
  obtain ⟨ok, hcallee⟩ := hall HW hbus (hdev img.ctx) (hrel μ) (fun _ => rfl)
  refine ⟨ok, hcallee ?_⟩
  have hrc := rtCheck_true
  unfold rtCheck at hrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hin, hld⟩, hst⟩, hacc⟩, hxor⟩, hand⟩, hcmp⟩, hshr⟩, hnot⟩, hob⟩, hoe⟩ := hrc
  have H := harness a addrs μ
  have hK : 2 ≤ (Zof a addrs μ).rtK := Nat.le_refl 2
  have pure : ∀ (name : String) (rel : Cpu → Cpu → Prop), name ∉ calls → RtPure (Zof a addrs μ) name rel :=
    fun name rel h hu => absurd hu (not_used h)
  have acc : ∀ (name : String) (pre : Cpu → Prop) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtAcc (Zof a addrs μ) name pre rel := fun name pre rel h hu => absurd hu (not_used h)
  exact
    { bound := fun hu => absurd hu (not_used (by rw [calls_eq]; decide))
      wide :=
        { ld := rt_ld32_ok ok hsize (has_of hld)
          st := rt_st32_ok ok hsize (has_of hst)
          bin := fun op => by
            cases op
            case and => exact rt_and32_ok ok hsize (has_of hand)
            case xor => exact rt_xor32_ok ok hsize (has_of hxor)
            all_goals exact acc _ _ _ (by rw [calls_eq]; decide +kernel)
          cmp := rt_cmp32_ok ok hsize hK (has_of hcmp) }
      accA := rt_acc_a_ok ok hsize (has_of hacc)
      accHL := rt_acc_hl_ok ok hsize (has_of hacc)
      not32 := rt_not32_ok ok hsize (has_of hnot)
      shr32 := rt_shr32_ok ok hsize hK (has_of hshr)
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

theorem crc32H_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ μ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, h⟩ := crc32H_setting
  exact ⟨a, addrs, ha, fun μ => (h μ).2⟩

/-- info: 'Ember.Proof.Z80Gen.Crc32H.crc32H_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32H_ok

end Ember.Proof.Z80Gen.Crc32H
