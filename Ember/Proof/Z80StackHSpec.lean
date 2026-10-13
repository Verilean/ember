import Ember.Proof.Z80StackHRun
import Ember.Proof.Z80LoopHSpec
import Ember.Proof.IRNet

/-!
# Ember.Proof.Z80StackHSpec — the image of the stack for the harness, against the Spec (plan M7.3)

`stackH_run` takes that the calls of `main` end in the IR's semantics,
each moving the position in the input while input remains (`Moves`).
They do: in the Ember semantics a call of `main` never traps and reads
one item of the input (`main_step`, M5.6), and what ends there ends in
the IR with the same world (`lower_iter`, M7.1).

`stackH_spec_halt` composes them with `main_run_all`: **from reset, for
any input, the machine of the harness running the image of the stack
stops (`di; halt`) with the input used up, and the transmissions and
drops of the world it holds — each with the number of its input — are
those of `Spec.step`, input by input.**

`StackSrc p` is what is taken of the Ember program `p`: that it is the
checked SLIP build (its functions, `TcpAll`, `TcpReasons`, `main_fn`),
lowered to `Stack.ir`, accepted by the checkers of M7.1 with this
layout.  Each part that can be computed is a `#guard` on
`Net.prog.check` below (evaluation, not proof) — the kernel does not
run the type checker or the lowering.

The machine is the CPU model with the harness's ports as a function of
the world (`hbus`, `hdev`).  That `Ember.Z80.Machine`, which the tests
run, steps as it does is proved for the loopback image (`Z80Machine`),
not yet for this one.  Not the image as built by default (with the
passes on the assembly).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (mainIter kept specKept witems later laterL itemsAt itemsOf main_fn TcpAll TcpReasons MainInv
  main_step main_run_all boot_call boot_inv bootSt itemM keep next_spec foldl_emit kept_emit kept_congr witems_emit)
open Ember.Lang (World)

/-- What is taken of the Ember program. -/
structure StackSrc (p : Lang.Prog) : Prop where
  all : TcpAll p
  reasons : TcpReasons p
  main : p.fn? "main" = some main_fn
  entry : p.entry = "main"
  globals : p.globals = Net.prog.globals
  structs : p.structs = Net.prog.structs
  framed : p.framed = false
  lowered : IR.lower p = .ok Stack.ir
  okP : progOkB p = true
  okIR : irOkB p layout = true
  drops : p.dropReasons = img.dropReasons
  notes : p.notes = img.notes

-- the parts of `StackSrc` that can be computed, of the checked SLIP build
#guard (Net.prog.check.toOption.map fun q =>
  q.fn? "main" == some main_fn && q.entry == "main" && q.globals == Net.prog.globals &&
    q.structs == Net.prog.structs && q.framed == false && progOkB q && irOkB q layout &&
    q.dropReasons == img.dropReasons && q.notes == img.notes) == some true

/-! ## The items of the input -/

theorem laterL_ne : ∀ (l : List Trace.Input) (j : Nat) (q : Nat × UInt16), q ∈ laterL l j → q.2 ≠ 0xFFFF
  | [], _, _, h => by cases h
  | x :: t, j, q, h => by
    rw [laterL, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      cases x with
      | tick =>
        have : k = 0x0100 := by simpa [itemsOf] using hk
        rw [this]
        show (0x0100 : UInt16) ≠ 0xFFFF
        decide
      | rx b =>
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hk
        intro e
        have := congrArg UInt16.toNat e
        have hc := c.toNat_lt
        simp at this
        omega
    · exact laterL_ne t (j + 1) q h

/-- No item is `0xFFFF` (which `input.next` gives when nothing is left). -/
theorem witems_ne (w : World) (q : Nat × UInt16) (h : q ∈ witems w) : q.2 ≠ 0xFFFF := by
  unfold witems at h
  split at h
  · rw [List.mem_append] at h
    rcases h with h | h
    · split at h
      · have : q = (w.pos, 0x0100) := by simpa using h
        rw [this]
        show (0x0100 : UInt16) ≠ 0xFFFF
        decide
      · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
        intro e
        have := congrArg UInt16.toNat e
        have hc := c.toNat_lt
        simp at this
        omega
    · exact laterL_ne _ _ q h
  · cases h

/-- With nothing left, no item is left — before the call of `input.next` and after. -/
theorem exhausted_witems (w : World) (hf : w.framed = false) (h : w.next.1 = 0xFFFF) :
    witems w = [] ∧ witems w.next.2 = [] := by
  obtain ⟨_, _, hcase⟩ := next_spec w hf
  rcases hcase with ⟨h0, _, h0'⟩ | ⟨i, k, hi, hk, _⟩
  · exact ⟨h0, h0'⟩
  · exact absurd (hk ▸ h) (witems_ne w (i, k) (by rw [hi]; exact List.mem_cons_self))

/-! ## The calls of `main` in the Ember semantics -/

/-- A state from which `main` runs as from a state under `MainInv` with
the same world (the initial state is one: its first call boots). -/
def Good (p : Lang.Prog) (st : Lang.Sem.St) : Prop :=
  ∃ (sm : Lang.Sem.St) (s : Spec.State) (w : Ember.Proof.Refine.TW),
    MainInv sm s w 296 Spec.ourIpDefault 296 ∧ sm.world = st.world ∧ st.world.framed = false ∧
    Lang.Sem.call 4716 p st "main" [] = Lang.Sem.call 4716 p sm "main" []

/-- **One call of `main` in the Ember semantics**: it ends, in a state
that is good again; with input remaining the position in the input has
moved (one item less is left); with none the kept lines stay. -/
theorem good_step (p : Lang.Prog) (S : StackSrc p) (st : Lang.Sem.St) (h : Good p st) :
    ∃ st', Lang.Sem.call 4716 p st "main" [] = .ok none st' ∧ Good p st' ∧
      witems st'.world = witems st.world.next.2 ∧
      (st.world.next.1 ≠ 0xFFFF → (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off) ∧
        LoopH.World.rem st'.world + 1 = LoopH.World.rem st.world) ∧
      (st.world.next.1 = 0xFFFF → kept st'.world = kept st.world) := by
  obtain ⟨sm, s, w, hinv, hw, hf, hc⟩ := h
  obtain ⟨st1, w1, X, hcall, hinv1, hw1, htr⟩ := main_step p S.all S.reasons S.main sm s w 296 Spec.ourIpDefault 296
    hinv #[] 0
  have hcall' : Lang.Sem.call 4716 p sm "main" [] = .ok none st1 := hcall
  rw [hw] at hw1 htr
  obtain ⟨hev, hfr, _⟩ := next_spec st.world hf
  have hpos : st1.world.pos = st.world.next.2.pos ∧ st1.world.off = st.world.next.2.off ∧
      st1.world.framed = st.world.next.2.framed ∧ st1.world.inputs = st.world.next.2.inputs := by
    rw [hw1, foldl_emit]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨st1, by rw [hc]; exact hcall', ⟨st1, _, w1, hinv1, rfl, by rw [hpos.2.2.1]; exact hfr, rfl⟩,
    by rw [hw1, witems_emit], fun hne => ⟨?_, ?_⟩, fun hex => ?_⟩
  · rw [hpos.1, hpos.2.1]
    exact LoopH.next_moves st.world hf hne
  · rw [← LoopH.rem_next st.world hf hne]
    unfold LoopH.World.rem
    rw [hpos.1, hpos.2.1, hpos.2.2.2]
  · rw [hex, show itemM 0xFFFF = pure () from if_pos rfl] at htr
    have hX : X.filter keep = [] := by
      have : ([] : List Trace.Event) = [] ++ X.filter keep := htr
      simpa using this.symm
    rw [hw1, kept_emit, hX, List.map_nil, List.append_nil]
    exact kept_congr hev

theorem initial_good (p : Lang.Prog) (S : StackSrc p) (inputs : Array Trace.Input) :
    Good p (Lang.Sem.initial p inputs) := by
  obtain ⟨w, hinv⟩ := boot_inv inputs
  have hi : Lang.Sem.initial p inputs = Lang.Sem.initial Net.prog inputs :=
    Ember.Proof.CSim.initial_congr p Net.prog S.globals S.structs (by rw [S.framed]; rfl) inputs
  rw [hi]
  exact ⟨bootSt inputs, _, w, hinv, rfl, rfl, boot_call p S.all S.main inputs 4676⟩

theorem mainIter_snoc (p : Lang.Prog) (fuel : Nat) : ∀ (i : Nat) (st sti sti' : Lang.Sem.St) (r : Option Lang.Val),
    mainIter fuel p i st = some sti → Lang.Sem.call fuel p sti "main" [] = .ok r sti' →
    mainIter fuel p (i + 1) st = some sti'
  | 0, st, sti, sti', r, h, hc => by
    cases h
    rw [mainIter, hc]
    rfl
  | i + 1, st, sti, sti', r, h, hc => by
    rw [mainIter] at h ⊢
    cases hc0 : Lang.Sem.call fuel p st "main" [] with
    | ok v st1 =>
      rw [hc0] at h
      exact mainIter_snoc p fuel i st1 sti sti' r h hc
    | trap _ => rw [hc0] at h; cases h
    | fuel => rw [hc0] at h; cases h

/-- Any number of calls: they end, in a good state. -/
theorem good_run (p : Lang.Prog) (S : StackSrc p) : ∀ (k : Nat) (st : Lang.Sem.St), Good p st →
    ∃ stk, mainIter 4716 p k st = some stk ∧ Good p stk
  | 0, st, h => ⟨st, rfl, h⟩
  | k + 1, st, h => by
    obtain ⟨st1, hc, h1, _⟩ := good_step p S st h
    obtain ⟨stk, hk, hg⟩ := good_run p S k st1 h1
    exact ⟨stk, by rw [mainIter, hc]; exact hk, hg⟩

/-- **The input is used up after as many calls as it has items.** -/
theorem good_exhaust (p : Lang.Prog) (S : StackSrc p) : ∀ (n : Nat) (st : Lang.Sem.St), Good p st →
    LoopH.World.rem st.world = n → ∃ stn, mainIter 4716 p n st = some stn ∧ stn.world.next.1 = 0xFFFF
  | 0, st, h, hr => ⟨st, rfl, (LoopH.rem_zero st.world h.choose_spec.choose_spec.choose_spec.2.2.1).mpr hr⟩
  | n + 1, st, h, hr => by
    have hf := h.choose_spec.choose_spec.choose_spec.2.2.1
    have hne : st.world.next.1 ≠ 0xFFFF := fun e => by
      have := (LoopH.rem_zero st.world hf).mp e
      omega
    obtain ⟨st1, hc, h1, _, hmv, _⟩ := good_step p S st h
    obtain ⟨stn, hn, hex⟩ := good_exhaust p S n st1 h1 (by have := (hmv hne).2; omega)
    exact ⟨stn, by rw [mainIter, hc]; exact hn, hex⟩

/-- What the Ember semantics gives of the run, for the IR: after any
number of calls there is a state, the same whatever the fuel, with the
world the Ember semantics has; and a call with input remaining moves the
position in the input. -/
theorem src_facts (p : Lang.Prog) (S : StackSrc p) (inputs : Array Trace.Input) :
    (∀ k, ∃ stk m istk, mainIter 4716 p k (Lang.Sem.initial p inputs) = some stk ∧ Good p stk ∧
      irIter m img.ctx k (st0 inputs) = some istk ∧ istk.world = stk.world) ∧
    (∀ k m1 m2 x y, irIter m1 img.ctx k (st0 inputs) = some x → irIter m2 img.ctx k (st0 inputs) = some y → x = y) ∧
    ∀ m, Moves img "main" m (st0 inputs) := by
  have hctx : irCtx p Stack.ir layout = img.ctx := by
    unfold irCtx
    rw [S.drops, S.notes]
    rfl
  have hst0 : irInit p Stack.ir layout inputs = st0 inputs := by
    unfold irInit
    rw [S.framed]
    rfl
  have lang : ∀ k, ∃ stk m istk, mainIter 4716 p k (Lang.Sem.initial p inputs) = some stk ∧ Good p stk ∧
      irIter m img.ctx k (st0 inputs) = some istk ∧ istk.world = stk.world := by
    intro k
    obtain ⟨stk, hk, hg⟩ := good_run p S k _ (initial_good p S inputs)
    obtain ⟨m, istk, hit, hw⟩ := lower_iter S.lowered layout S.okP S.okIR inputs 4716 k stk
      (by rw [← mainIter_eq p S.entry]; exact hk)
    rw [hctx, hst0] at hit
    exact ⟨stk, m, istk, hk, hg, hit, hw⟩
  have det : ∀ k m1 m2 x y, irIter m1 img.ctx k (st0 inputs) = some x → irIter m2 img.ctx k (st0 inputs) = some y →
      x = y := by
    intro k m1 m2 x y h1 h2
    have e1 := irIter_le (c := img.ctx) (Nat.le_max_left m1 m2) k _ _ h1
    have e2 := irIter_le (c := img.ctx) (Nat.le_max_right m1 m2) k _ _ h2
    rw [e1] at e2
    exact Option.some.inj e2
  refine ⟨lang, det, fun m => ?_⟩
  intro i isti r isti' hiti hcall hne
  obtain ⟨sti, mi, isti0, hi, hgi, hiti0, hwi⟩ := lang i
  have e : isti = isti0 := det i _ _ _ _ hiti hiti0
  obtain ⟨sti', hc, _, _, hmoved, _⟩ := good_step p S sti hgi
  have hi' := mainIter_snoc p 4716 i _ sti sti' none hi hc
  obtain ⟨sti1, mi1, isti1, hi1, _, hiti1, hwi1⟩ := lang (i + 1)
  rw [hi'] at hi1
  cases hi1
  have e' : isti' = isti1 := det (i + 1) _ _ _ _ (LoopH.irIter_snoc m img.ctx i _ isti isti' r hiti hcall) hiti1
  rw [e', hwi1, e, hwi]
  exact (hmoved (by rw [← hwi, ← e]; exact hne)).1

/-- **The image of the stack for the harness transmits and drops what
the Spec does**, from reset, for any input: the machine stops
(`di; halt`) holding the world of `i` calls of `main` in the Ember
semantics, which leave no input; the kept lines of that world's trace —
transmissions and drops, each with the number of its input — are those
of `Spec.step`, input by input. -/
theorem stackH_spec_halt (p : Lang.Prog) (S : StackSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Ember.Trace.Input) (s : Cpu), s.pc.toNat = 0 → Img a 0 s → s.halted = false →
        s.ramStart.toNat = 0x8000 → s.mem.size = 65536 →
        ∃ i sti s' w', mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
          WSteps (Zof a addrs (0, 0)) (s, ((st0 inputs).world, 0, (0, 0), (0, 0))) (s', w') ∧ s'.halted = true ∧
          s'.iff1 = false ∧ w'.1 = sti.world ∧
          kept w'.1 = specKept inputs.toList 0 (Spec.State.init {}) := by
  obtain ⟨a, addrs, ha, hrun⟩ := stackH_run_halt
  refine ⟨a, addrs, ha, fun inputs s hpc I hh hrs hsz => ?_⟩
  obtain ⟨lang, det, hmv⟩ := src_facts p S inputs
  obtain ⟨stn, hn, hexn⟩ := good_exhaust p S _ _ (initial_good p S inputs) rfl
  obtain ⟨stj, m, istj, hj, _, hitj, hwj⟩ := lang (LoopH.World.rem (Lang.Sem.initial p inputs).world)
  rw [hn] at hj
  cases hj
  obtain ⟨i, isti, s', w', hi, hiti, stp, hh', hi1', hw, hex⟩ :=
    hrun inputs s hpc I hh hrs hsz _ m istj (hmv m) hitj (by rw [hwj]; exact hexn)
  obtain ⟨sti, m', isti', hi', hgi, hiti', hwi⟩ := lang i
  have e : isti = isti' := det i _ _ _ _ hiti hiti'
  have hexi : sti.world.next.1 = 0xFFFF := by rw [← hwi, ← e]; exact hex
  refine ⟨i, sti, s', w', hi', hexi, stp, hh', hi1', by rw [hw, e, hwi], ?_⟩
  rw [hw, e, hwi]
  -- one more call: it keeps the kept lines, and `main_run_all` speaks of the state after it
  have hfi := hgi.choose_spec.choose_spec.choose_spec.2.2.1
  obtain ⟨sti1, hc, _, hwit, _, hkeep⟩ := good_step p S sti hgi
  have hit1 := mainIter_snoc p 4716 i _ sti sti1 none hi' hc
  have hinit : Lang.Sem.initial p inputs = Lang.Sem.initial Net.prog inputs :=
    Ember.Proof.CSim.initial_congr p Net.prog S.globals S.structs (by rw [S.framed]; rfl) inputs
  rw [hinit] at hit1
  obtain ⟨st2, w2, hit2, _, _, hwi2⟩ := Ember.Proof.Refine.main_run p S.all S.reasons S.main inputs 0 i
  have hit2' : mainIter 4716 p (i + 1) (Lang.Sem.initial Net.prog inputs) = some st2 := hit2
  rw [hit1] at hit2'
  cases hit2'
  have hlen : (later inputs 0).length ≤ i + 1 := by
    have h0 : witems sti1.world = [] := by rw [hwit]; exact (exhausted_witems sti.world hfi hexi).2
    rw [h0] at hwi2
    exact List.drop_eq_nil_iff.mp hwi2.symm
  obtain ⟨st3, w3, hit3, _, hk3, _⟩ := main_run_all p S.all S.reasons S.main inputs 0 i hlen
  have hit3' : mainIter 4716 p (i + 1) (Lang.Sem.initial Net.prog inputs) = some st3 := hit3
  rw [hit1] at hit3'
  cases hit3'
  rw [← hkeep hexi]
  exact hk3

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_spec_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_spec_halt

end Ember.Proof.Z80Gen.StackH
