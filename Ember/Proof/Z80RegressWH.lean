import Ember.Proof.Z80RegressWHItems
import Ember.Proof.Z80HarnessW
import Ember.Proof.Z80Rt
import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80RegressWH — the functions of `regress_wide_store`'s image for the test harness (plan M7.3)

`regressH_ok`: in the image the assembler makes of `RegressWH.items` —
`RegressW.ir`, the IR of the Lang program `regress_wide_store` (four-byte
stores through addresses, from a global with an initial value; an index
check that can trap; a narrowing to one byte) with the runtime of the
test harness, without the passes on the assembly — in the machine of the
harness, every function, entered as `Entry` says, returns as
`IR.Sem.callF` does with the machine holding the world it leaves, or
reaches `rt_trap`.

Nothing is assumed of the program, the layout, the image or the runtime:
the routines the image calls from its functions — `rt_input`, `rt_ld32`,
`rt_st32`, `rt_add32`, `rt_acc_hl`, `rt_bound`, `rt_out_byte`,
`rt_out_end` — are proved from their items (`Z80Rt`, `Z80Wide`,
`Z80Bytes`), and the image calls no other routine of the runtime from
its functions (`calls_eq`).

What the statement is about, and what it is not: the image is
`RegressWH.items` assembled; that these are the items `build` gives
without the passes, the IR what `IR.lower` returns for `Regress.p5` and
the layout what `build` computes are `#guard`s (`Z80RegressWHItems`,
`Tests.Ember.Z80RegressW`), evaluated when those files are built, not
proved.  The machine is the CPU model with the harness's ports (`hbus`,
`hdev`).  Not here: start-up (the RAM cleared, the initial value of `wv`
copied), reset, the loop, traps from reset, the Ember semantics, or
`Ember.Z80.Machine`.
-/

namespace Ember.Proof.Z80Gen.RegressWH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

/-- RAM from `0x8000`: the runtime's accumulator (eight bytes), the
loop's count of idle calls, the globals, the frames; the stack above.
A routine of the runtime needs two bytes of stack (`rtK`). -/
def img : ImgIn :=
  { ir := RegressW.ir, layout, ramStart := 0x8000, stackLo := 32801, stackHi := 65536, acc := 32768, rtK := 2,
    rt := [], items, genOff := 9 }

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
  decide ((items.drop 151).take inputItems.length = inputItems) &&
  decide ((items.drop 167).take ldItems.length = ldItems) &&
  decide ((items.drop 176).take boundItems.length = boundItems) &&
  decide ((items.drop 182).take stItems.length = stItems) &&
  decide ((items.drop 192).take accItems.length = accItems) &&
  decide ((items.drop 204).take (bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩).length =
    bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩) &&
  decide ((items.drop 220).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 223).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide (items[237]? = some (.label "rt_trap"))

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
theorem regressH_setting :
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
      not32 := acc _ _ _ (by rw [calls_eq]; decide)
      shr32 := acc _ _ _ (by rw [calls_eq]; decide)
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

theorem regressH_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ μ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, h⟩ := regressH_setting
  exact ⟨a, addrs, ha, fun μ => (h μ).2⟩

/-- info: 'Ember.Proof.Z80Gen.RegressWH.regressH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regressH_ok

end Ember.Proof.Z80Gen.RegressWH
