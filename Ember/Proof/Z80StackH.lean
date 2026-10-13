import Ember.Proof.Z80StackHPlan
import Ember.Proof.Z80HarnessW
import Ember.Proof.Z80Note
import Ember.Proof.Z80Wide
import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80StackH — the image of the stack for the test harness: nothing taken of the runtime (plan M7.3)

`stackH_ok`: in the image the assembler makes of `StackH.items` — the
SLIP build of the stack with the runtime of the test harness, without
the passes on the assembly — in the machine of the harness (`hbus`,
`hdev`: the world behind ports), every function, entered as `Entry`
says, returns as `IR.Sem.callF` does with the machine holding the world
it leaves, or reaches `rt_trap`.

Nothing is assumed of the program, the layout, the image or the
runtime: the routines the functions call (`calls_eq`) — `rt_ld32`,
`rt_st32`, `rt_acc_a`, `rt_acc_hl`, `rt_add32`, `rt_sub32`, `rt_or32`,
`rt_cmp32`, `rt_shr8`, `rt_not16`, and the effects `rt_input`,
`rt_out_byte`, `rt_out_end`, `rt_drop`, `rt_note` — are proved from
their items, which `rtCheck` finds in the image.  `rt_cmp32` keeps `AF`
on the stack: the plan has `rtK = 2`.

What the statement is not: it is of the functions.  Start-up (with the
copy of the initial values of the variables), the loop that calls
`main`, and the composition with the theorems about the stack's IR and
the Spec are not here — the image is not yet run from reset in a
theorem, as the loopback image is (`loopH_halts`).  That the items are
those `build` gives, the IR what `IR.lower` returns and the layout what
`build` computes are `#guard`s (evaluation, not proof).  Not the image
as built by default (with the passes on the assembly).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

set_option maxRecDepth 100000

/-- The setting: the plan of the image, the image, the harness (the mark at `μ`). -/
def Zof (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : ZCtx := img.ZH a addrs μ

/-- The routines the image calls. -/
def calls : List String :=
  (items.filterMap fun it =>
    match it with
    | .ins ⟨.call, [.imm (.sym n _)]⟩ => some n
    | _ => none).eraseDups

theorem calls_eq : calls =
    ["f_get16", "rt_acc_hl", "rt_st32", "rt_or32", "f_set16", "f_add16", "rt_ld32", "rt_not16", "rt_out_byte",
    "rt_out_end", "f_set32", "f_csum", "f_slip_send", "rt_drop", "f_verifies", "f_csum_update", "f_ip_send",
    "f_pseudo", "rt_shr8", "f_get32", "rt_cmp32", "f_icmp_input", "f_udp_input", "f_tcp_input", "f_ip_input",
    "f_slip_store", "f_cap", "rt_add32", "f_wnd", "f_tcp_emit", "f_send_seg", "f_seg_len", "rt_acc_a",
    "f_send_syn_ack", "rt_sub32", "f_send_reset", "f_tcb_reset", "f_listen_input", "f_acceptable", "rt_note",
    "f_ack_input", "f_output", "f_parse_mss", "f_tcp_segment", "f_rto", "f_rexmit", "rt_input", "f_tcp_tick",
    "f_slip_rx", "rt_zero", "rt_init", "f_entry"] := by decide +kernel

theorem uses_mem {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {name : String}
    (h : Uses (Zof a addrs μ) name) : name ∈ calls := by
  obtain ⟨k, hk⟩ := h
  have hm : Item.ins ⟨.call, [.imm (.sym name)]⟩ ∈ items := List.mem_of_getElem? hk
  unfold calls
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- A routine that the image does not call. -/
theorem not_used {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {name : String}
    (h : name ∉ calls) : ¬ Uses (Zof a addrs μ) name := fun hu => h (uses_mem hu)

/-- Where the routines are. -/
def rtCheck : Bool :=
  decide ((items.drop 2617).take accItems.length = accItems) &&
  decide ((items.drop 2629).take stItems.length = stItems) &&
  decide ((items.drop 2639).take (bytewiseItems "or" [] ⟨.or, [.mhl]⟩).length = bytewiseItems "or" [] ⟨.or, [.mhl]⟩) &&
  decide ((items.drop 2654).take ldItems.length = ldItems) &&
  decide ((items.drop 2663).take not16Items.length = not16Items) &&
  decide ((items.drop 2671).take 3 = [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 2674).take 3 = [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 2677).take 3 = [.label "rt_drop", .ins ⟨.out, [.mem (.num 0xD5), .a]⟩, .ins ⟨.ret, []⟩]) &&
  decide ((items.drop 2680).take shrItems.length = shrItems) &&
  decide ((items.drop 2688).take cmpItems.length = cmpItems) &&
  decide ((items.drop 2710).take (bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩).length =
    bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩) &&
  decide ((items.drop 2726).take (bytewiseItems "sub" [.ins ⟨.or, [.a]⟩] ⟨.sbc, [.a, .mhl]⟩).length =
    bytewiseItems "sub" [.ins ⟨.or, [.a]⟩] ⟨.sbc, [.a, .mhl]⟩) &&
  decide ((items.drop 2742).take noteItems.length = noteItems) &&
  decide ((items.drop 2755).take inputItems.length = inputItems)

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

/-- **The functions of the image of the stack for the harness do what
the IR's functions do**: nothing is taken of the runtime.  (For every
place of the mark: a function leaves it.) -/
theorem stackH_setting :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, hsize, hall⟩ := img_ok
  refine ⟨a, addrs, ha, hsize, fun μ => ?_⟩
  obtain ⟨ok, hcallee⟩ := hall HW hbus (hdev img.ctx) (hrel μ) (fun _ => rfl)
  refine ⟨ok, hcallee ?_⟩
  have hrc := rtCheck_true
  unfold rtCheck at hrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hacc, hst⟩, hor⟩, hld⟩, hnot⟩, hob⟩, hoe⟩, hdr⟩, hshr⟩, hcmp⟩, hadd⟩, hsub⟩, hnote⟩, hin⟩ := hrc
  have H : Harness (Zof a addrs μ) := img.harness a addrs μ
  have hK : 2 ≤ (Zof a addrs μ).rtK := Nat.le_refl 2
  have pure : ∀ (name : String) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtPure (Zof a addrs μ) name rel := fun name rel h hu => absurd hu (not_used h)
  have acc : ∀ (name : String) (pre : Cpu → Prop) (rel : Cpu → Cpu → Prop), name ∉ calls →
      RtAcc (Zof a addrs μ) name pre rel := fun name pre rel h hu => absurd hu (not_used h)
  exact
    { bound := fun hu => absurd hu (not_used (by rw [calls_eq]; decide))
      wide :=
        { ld := rt_ld32_ok ok hsize (has_of hld)
          st := rt_st32_ok ok hsize (has_of hst)
          bin := fun op => by
            cases op
            case add => exact rt_add32_ok ok hsize (has_of hadd)
            case sub => exact rt_sub32_ok ok hsize (has_of hsub)
            case or => exact rt_or32_ok ok hsize (has_of hor)
            all_goals exact acc _ _ _ (by rw [calls_eq]; decide +kernel)
          cmp := rt_cmp32_ok ok hsize hK (has_of hcmp) }
      accA := rt_acc_a_ok ok hsize (has_of hacc)
      accHL := rt_acc_hl_ok ok hsize (has_of hacc)
      eff := fun e he => by
        cases e with
        | inputNext => exact harness_input ok H hsize (has_of hin) _ (Or.inl rfl)
        | ringPop => exact harness_input ok H hsize (has_of hin) _ (Or.inr rfl)
        | outByte => exact harness_out_byte ok H hsize (has_of hob)
        | outEnd => exact harness_out_end ok H hsize (has_of hoe)
        | drop => exact harness_drop ok H hsize (has_of hdr)
        | note => exact harness_note ok H hsize (has_of hnote)
        | _ => cases he
      shl8 := pure _ _ (by rw [calls_eq]; decide)
      shr8 := rt_shr8_ok ok hsize (has_of hshr)
      shl16 := pure _ _ (by rw [calls_eq]; decide)
      shr16 := pure _ _ (by rw [calls_eq]; decide)
      mul8 := pure _ _ (by rw [calls_eq]; decide)
      div8 := pure _ _ (by rw [calls_eq]; decide)
      mod8 := pure _ _ (by rw [calls_eq]; decide)
      not16 := rt_not16_ok ok hsize (has_of hnot)
      neg16 := pure _ _ (by rw [calls_eq]; decide)
      mul16 := pure _ _ (by rw [calls_eq]; decide)
      div16 := pure _ _ (by rw [calls_eq]; decide)
      mod16 := pure _ _ (by rw [calls_eq]; decide) }

/-- **The image of the stack for the harness**: every function does
what the IR's function does. -/
theorem stackH_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ μ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1) := by
  obtain ⟨a, addrs, ha, _, h⟩ := stackH_setting
  exact ⟨a, addrs, ha, fun μ => (h μ).2⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_ok

end Ember.Proof.Z80Gen.StackH
