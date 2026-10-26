import Ember.Proof.Z80StackHTcb
import Ember.Proof.Z80StackHTrace
import Ember.Z80.TcbObs

/-!
# Ember.Proof.Z80StackHTcbObs — the observer's `tcb` lines of the stack's image (plan M7.3)

`Ember.Z80.TcbObs.run` takes the machine at every head of the harness's
loop (the CPU at `rt_main`, its stack empty, not halted), leaves out the
first, checks that it saw one more than there are input items, and
writes for each of the others a `tcb` line from the record `t` in the
RAM.  `stackH_tcb_obs`: for the image of the stack, when the observer
gives lines, they are **one per input item, in order, each at the number
of the input of its item, saying what `Tcb.describe` says of the Spec's
control block after that item**.

How: the run of the machine passes the head of the loop after `j` calls
of `main` for every `j` up to the number of items `K`, at steps that
increase with `j` (`chk_chain`: from one head the next call ends at the
next head, `loop_iter`), each before the first halt; so those `K + 1`
steps are among the observer's.  That they are all of them — that the
code of `main` does not pass `rt_main` with its stack empty — is not
proved: the observer checks it, by counting, and gives no lines when it
fails.  At each of those steps the RAM holds the record of
`stackH_tcb_ir` (the shared bytes, `AtLoop.mem`), and `describeAt`
reads from it what `RawTcb.describe` writes (`describeAt_of`).

Not the Spec's `tcb` lines: the Spec writes its lines inside an item,
for some items none, for some two (`TcbCheckpoint`); the observer's line
is the state after the item.
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu
open Ember.Proof.IRSim Ember.Proof.Z80Enc
open Ember.Proof.Refine (mainIter later witems TcbRel RawTcb RawTcb.describe specAfter next_spec main_step foldl_emit
  witems_start)
open Ember.Proof.Z80Gen.LoopH (Sim mrun harnessMachine harness_reset run_sim_of)
open Ember.Lang.Sem (bufVal)
open Ember.Proof.CSim (TyOK HasTy)

/-! ## Lists -/

theorem sublist_of_sorted : ∀ (l l' : List Nat), l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (∀ x ∈ l, x ∈ l') → l.Sublist l'
  | [], _, _, _, _ => List.nil_sublist _
  | x :: _, [], _, _, h => absurd (h x List.mem_cons_self) List.not_mem_nil
  | x :: xs, y :: ys, hl, hl', h => by
    have hx := h x List.mem_cons_self
    have hl1 := List.pairwise_cons.mp hl
    have hl2 := List.pairwise_cons.mp hl'
    rcases List.mem_cons.mp hx with e | hx'
    · subst e
      apply List.Sublist.cons_cons
      apply sublist_of_sorted xs ys hl1.2 hl2.2
      intro z hz
      rcases List.mem_cons.mp (h z (List.mem_cons_of_mem _ hz)) with e | hz'
      · have := hl1.1 z hz
        omega
      · exact hz'
    · apply List.Sublist.cons
      apply sublist_of_sorted (x :: xs) ys hl hl2.2
      intro z hz
      rcases List.mem_cons.mp (h z hz) with e | hz'
      · have hyx := hl2.1 x hx'
        rcases List.mem_cons.mp hz with e2 | hz2
        · omega
        · have := hl1.1 z hz2
          omega
      · exact hz'

/-- A list of increasing numbers below `n` that all satisfy `P`, as long
as the numbers below `n` that satisfy it, is them. -/
theorem filter_range_eq {P : Nat → Bool} {n : Nat} {ns : List Nat} (hs : ns.Pairwise (· < ·))
    (hlt : ∀ x ∈ ns, x < n) (hP : ∀ x ∈ ns, P x = true) (hlen : ((List.range n).filter P).length = ns.length) :
    (List.range n).filter P = ns := by
  have hsub : ns.Sublist ((List.range n).filter P) :=
    sublist_of_sorted _ _ hs (List.pairwise_lt_range.filter _)
      (fun x hx => List.mem_filter.mpr ⟨List.mem_range.mpr (hlt x hx), hP x hx⟩)
  exact (hsub.eq_of_length hlen.symm).symm

/-! ## The observer -/

theorem obsList_of (lh : Nat) : ∀ (n fuel : Nat) (m : Machine), n ≤ fuel →
    (∀ k, k < n → (mrun k m).cpu.halted = false) → (mrun n m).cpu.halted = true →
    TcbObs.obsList lh fuel m = .ok (((List.range n).filter fun k => TcbObs.obsAt lh (mrun k m)).map fun k => mrun k m)
  | 0, fuel, m, _, _, hh => by
    have hh' : m.cpu.halted = true := hh
    unfold TcbObs.obsList
    simp [hh']
  | n + 1, fuel, m, hle, hk, hh => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h0 : m.cpu.halted = false := hk 0 (by omega)
    rw [TcbObs.obsList]
    simp only [h0, Bool.false_eq_true, if_false]
    rw [obsList_of lh n f m.step (by omega) (fun k hk' => hk (k + 1) (by omega)) hh]
    show Except.ok _ = Except.ok _
    congr 1
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have hs : ∀ k, mrun (k + 1) m = mrun k m.step := fun _ => rfl
    have h0' : mrun 0 m = m := rfl
    by_cases ho : TcbObs.obsAt lh m = true
    · simp only [h0', ho, if_true, List.map_cons, List.map_map, Function.comp_def, Nat.succ_eq_add_one, hs]
    · simp only [h0', ho, if_false, Bool.false_eq_true, List.map_map, Function.comp_def, Nat.succ_eq_add_one, hs]

/-- The observer as it runs (`TcbObs.scan`) keeps the lines of the
machines `obsList` gives, last first, and stops where it stops. -/
theorem scan_eq (lh t : Nat) : ∀ (f : Nat) (m : Machine) (acc : List Trace.Line),
    TcbObs.scan lh t f m acc = (TcbObs.obsList lh f m).map fun l => (l.map (TcbObs.lineAt t)).reverse ++ acc
  | 0, m, acc => by
    rw [TcbObs.scan, TcbObs.obsList]
    cases m.cpu.halted <;> rfl
  | f + 1, m, acc => by
    rw [TcbObs.scan, TcbObs.obsList]
    cases hh : m.cpu.halted
    · simp only [Bool.false_eq_true, if_false]
      rw [scan_eq lh t f m.step]
      cases TcbObs.obsList lh f m.step <;> by_cases ho : TcbObs.obsAt lh m = true <;> simp [ho, Except.map]
    · rfl

/-- `TcbObs.run` (`scan`) gives what `TcbObs.runList` (`obsList`) gives. -/
theorem run_eq (m : Machine) (k : Nat) (inputs : Array Trace.Input) (t lh n : Nat) :
    TcbObs.run m k inputs t lh n = TcbObs.runList m k inputs t lh n := by
  unfold TcbObs.run TcbObs.runList
  rw [scan_eq]
  cases TcbObs.obsList lh n _ <;> simp [Except.map] <;> rfl

theorem itemCount_eq (inputs : Array Trace.Input) : TcbObs.itemCount inputs = (later inputs 0).length := by
  unfold TcbObs.itemCount later
  simp only [List.drop_zero]
  generalize inputs.toList = l
  suffices h : ∀ j, (l.map fun x => match x with | .rx b => b.size | .tick => 1).sum =
      (Ember.Proof.Refine.laterL l j).length from h 0
  induction l with
  | nil => intro j; rfl
  | cons x t ih =>
    intro j
    rw [List.map_cons, List.sum_cons, Ember.Proof.Refine.laterL, List.length_append, ← ih (j + 1)]
    congr 1
    cases x with
    | tick => rfl
    | rx b =>
      show b.size = ((b.toList.map (·.toUInt16)).map fun k => (j, k)).length
      rw [List.length_map, List.length_map, Ember.Proof.Refine.toList_length]

/-! ## Reading the record -/

theorem ty_t (p : Lang.Prog) (S : StackSrc p) {g : Lang.Global} (h : p.global? "t" = some g) :
    g.ty = .record "Tcb" := by
  have h' : Net.prog.global? "t" = some g := by
    rw [← h]; unfold Lang.Prog.global?; rw [S.globals]
  obtain rfl : g = (Net.prog.global? "t").get! := by rw [h']; rfl
  rfl

theorem struct_tcb (p : Lang.Prog) (S : StackSrc p) : p.struct? "Tcb" = some Net.Tcb := by
  unfold Lang.Prog.struct?
  rw [S.structs]
  rfl

/-- **The observer reads what the record says**: `describeAt` of the
bytes that hold a connection record is what `RawTcb.describe` writes. -/
theorem describeAt_of (p : Lang.Prog) (S : StackSrc p) {mem : ByteArray} {g : Lang.Global} {r : RawTcb}
    (hg : p.global? "t" = some g) (h : Holds p mem 32777 g.ty r.val) :
    TcbObs.describeAt mem 32777 = r.describe := by
  rw [ty_t p S hg] at h
  obtain ⟨sd, hsd, hf⟩ := h
  rw [struct_tcb p S] at hsd
  cases hsd
  have e0 : IR.Sem.rd mem 32777 1 = (Lang.Sem.u8 r.st).toNat := hf 0 (by simp) (by decide)
  have e3 : IR.Sem.rd mem (32777 + 7) 4 = (Lang.Sem.u32 r.snd_una).toNat := hf 3 (by simp) (by decide)
  have e4 : IR.Sem.rd mem (32777 + 11) 4 = (Lang.Sem.u32 r.snd_nxt).toNat := hf 4 (by simp) (by decide)
  have e5 : IR.Sem.rd mem (32777 + 15) 4 = (Lang.Sem.u32 r.rcv_nxt).toNat := hf 5 (by simp) (by decide)
  have e6 : IR.Sem.rd mem (32777 + 19) 2 = (Lang.Sem.u16 r.pend_len).toNat := hf 6 (by simp) (by decide)
  have e7 : IR.Sem.rd mem (32777 + 21) 2 = (Lang.Sem.u16 r.sent).toNat := hf 7 (by simp) (by decide)
  have e12 : IR.Sem.rd mem (32777 + 30) 1 = (Lang.Sem.u8 r.rt_timer).toNat := hf 12 (by simp) (by decide)
  have e13 : IR.Sem.rd mem (32777 + 31) 1 = (Lang.Sem.u8 r.retries).toNat := hf 13 (by simp) (by decide)
  unfold TcbObs.describeAt RawTcb.describe
  have e0' : IR.Sem.rd mem 32777 1 = r.st.toNat := by rw [e0]; simp [Lang.Val.toNat]
  rw [e0', e3, e4, e5, e6, e7, e12, e13]
  simp [Lang.Val.toNat]

/-! ## The calls of `main`, item by item -/

/-- After a call of `main` the world's step is that of the item it read. -/
theorem cur_of_call (p : Lang.Prog) (S : StackSrc p) {st st' : Lang.Sem.St} (h : Good p st)
    (hc : Lang.Sem.call 4716 p st "main" [] = .ok none st') : st'.world.cur = st.world.next.2.cur := by
  obtain ⟨sm, s, w, hinv, hw, _, hcs⟩ := h
  obtain ⟨st1, w1, X, hcall, _, hw1, _⟩ :=
    main_step p S.all S.reasons S.main sm s w 296 Spec.ourIpDefault 296 hinv #[] 0
  have hcall' : Lang.Sem.call 4716 p sm "main" [] = .ok none st1 := hcall
  rw [hcs, hcall'] at hc
  injection hc with _ h2
  subst h2
  rw [hw1, foldl_emit, hw]

/-- The Ember semantics, call by call: after `j` calls the items left
are those after the first `j`, and the `j`-th call left the world at the
step of the `j`-th item. -/
theorem lang_chain (p : Lang.Prog) (S : StackSrc p) (inputs : Array Trace.Input) : ∀ j, j ≤ (later inputs 0).length →
    ∃ stj, mainIter 4716 p j (Lang.Sem.initial p inputs) = some stj ∧ Good p stj ∧
      witems stj.world = (later inputs 0).drop j ∧ ∀ i, j = i + 1 → stj.world.cur = ((later inputs 0)[i]!).1
  | 0, _ => ⟨_, rfl, initial_good p S inputs, by
      rw [List.drop_zero]; exact witems_start inputs 0 _ rfl rfl rfl, fun i h => absurd h (by omega)⟩
  | j + 1, hj => by
    obtain ⟨stj, hit, hg, hw, _⟩ := lang_chain p S inputs j (by omega)
    obtain ⟨st', hc, hg', hwi, _, _⟩ := good_step p S stj hg
    have hf : stj.world.framed = false := by obtain ⟨_, _, _, _, _, hf, _⟩ := hg; exact hf
    obtain ⟨_, _, hcase⟩ := next_spec stj.world hf
    rcases hcase with ⟨h0, _, _⟩ | ⟨i, k, hik, _, hcur⟩
    · rw [hw] at h0
      have := congrArg List.length h0
      simp only [List.length_drop, List.length_nil] at this
      omega
    · have hd : (later inputs 0).drop j = (later inputs 0)[j] :: (later inputs 0).drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      rw [hw, hd] at hik
      injection hik with h1 h2
      refine ⟨st', mainIter_snoc p 4716 j _ stj st' none hit hc, hg', by rw [hwi, ← h2], fun i' hi' => ?_⟩
      obtain rfl : i' = j := by omega
      rw [cur_of_call p S hg hc, hcur, getElem!_pos (later inputs 0) i' (by omega)]
      exact (congrArg Prod.fst h1).symm

theorem irIter_split (m : Nat) (c : IR.Ctx) : ∀ (j : Nat) (st y : IR.Sem.St), irIter m c (j + 1) st = some y →
    ∃ x r, irIter m c j st = some x ∧ IR.Sem.callF m c c.prog.entry x = .ok r y
  | 0, st, y, h => by
    rw [irIter] at h
    split at h
    · rename_i r st1 hc
      cases h
      exact ⟨st, r, rfl, hc⟩
    · cases h
  | j + 1, st, y, h => by
    rw [irIter] at h
    split at h
    · rename_i r st1 hc
      obtain ⟨x, r', hx, hcx⟩ := irIter_split m c j st1 y h
      refine ⟨x, r', ?_, hcx⟩
      rw [irIter, hc]
      exact hx
    · cases h

/-! ## The heads of the loop on the machine the tests run -/

/-- The machine at step `n` is at the head of the loop after `j` calls
of `main`, the RAM's shared bytes those of the IR's state. -/
def Chk (a : Assembled) (addrs : List Nat) (inputs : Array Trace.Input) (j n : Nat) : Prop :=
  ∃ m ist w, irIter m img.ctx j (st0 inputs) = some ist ∧ Sim img.ctx (mrun n (harnessMachine a inputs)) w ∧
    AtLoop img 2589 32776 a addrs ist (mrun n (harnessMachine a inputs)).cpu w

section
variable {a : Assembled} {addrs : List Nat}

theorem chk0 (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (inputs : Array Trace.Input) (hsz : a.bytes.size ≤ 0x8000) : ∃ n, Chk a addrs inputs 0 n := by
  obtain ⟨ok, _⟩ := hset (0, 0)
  have R := harness_reset a inputs hsz
  obtain ⟨s1, stb, L0⟩ := boot_loop ha hsize ok inputs _ R.pc R.img R.run R.rs R.msz
  obtain ⟨d, hd⟩ := Steps.lift ok stb ((st0 inputs).world, 0, (0, 0), (0, 0))
  obtain ⟨hc, Sd⟩ := run_sim_of img a addrs d _ _ (sim0 a inputs hsz)
  have hd' : wrun (img.ZH a addrs (0, 0)) d ((harnessMachine a inputs).cpu, ((st0 inputs).world, 0, (0, 0), (0, 0))) =
      (s1, ((st0 inputs).world, 0, (0, 0), (0, 0))) := hd
  rw [hd'] at hc Sd
  exact ⟨d, 0, st0 inputs, _, rfl, Sd, by rw [hc]; exact L0⟩

theorem next_ne (p : Lang.Prog) (S : StackSrc p) (inputs : Array Trace.Input) {m j : Nat} {ist : IR.Sem.St}
    (hj : j < (later inputs 0).length) (hit : irIter m img.ctx j (st0 inputs) = some ist) :
    ist.world.next.1 ≠ 0xFFFF := by
  obtain ⟨lang, det, _⟩ := src_facts p S inputs
  obtain ⟨stj, hmj, hg, hwj, _⟩ := lang_chain p S inputs j (by omega)
  obtain ⟨stj', m', istj, hmj', _, hitj, hwij⟩ := lang j
  rw [hmj] at hmj'
  cases hmj'
  rw [det j _ _ _ _ hit hitj, hwij]
  intro hx
  have hf : stj.world.framed = false := by obtain ⟨_, _, _, _, _, hf, _⟩ := hg; exact hf
  obtain ⟨h0, _⟩ := exhausted_witems stj.world hf hx
  rw [hwj] at h0
  have := congrArg List.length h0
  simp only [List.length_drop, List.length_nil] at this
  omega

theorem chk_succ (p : Lang.Prog) (S : StackSrc p) (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (inputs : Array Trace.Input) (j n : Nat) (hj : j < (later inputs 0).length) (C : Chk a addrs inputs j n) :
    ∃ d, 0 < d ∧ Chk a addrs inputs (j + 1) (n + d) := by
  obtain ⟨m, ist, w, hit, Sn, L⟩ := C
  obtain ⟨lang, det, hmv⟩ := src_facts p S inputs
  have hne := next_ne p S inputs hj hit
  obtain ⟨_, m1, y, _, _, hity, _⟩ := lang (j + 1)
  obtain ⟨x, r, hx, hcx⟩ := irIter_split m1 img.ctx j _ _ hity
  have e2 : x = ist := det j _ _ _ _ hx hit
  subst e2
  have hentry : img.ctx.prog.entry = "main" := (loopNeed ha).isEntry
  rw [hentry] at hcx
  rcases loop_iter (loopNeed ha) hsize hset L m1 with ⟨hx', _⟩ | ⟨_, hcall⟩
  · exact absurd hx' hne
  · rw [hcx] at hcall
    dsimp only at hcall
    have hmoved := hmv m1 j x r y hx hcx hne
    obtain ⟨s', w', ⟨d, hd⟩, L'⟩ := hcall hmoved
    obtain ⟨hc, Sd⟩ := run_sim_of img a addrs d _ _ Sn
    have hd' : wrun (img.ZH a addrs (0, 0)) d ((mrun n (harnessMachine a inputs)).cpu, w) = (s', w') := hd
    rw [hd'] at hc Sd
    have hpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        have hw : w = w' := congrArg Prod.snd hd'
        exact absurd (by rw [← L'.world, ← L.world, hw]) hmoved
      · exact h0
    refine ⟨d, hpos, m1, y, w', hity, ?_, ?_⟩
    · rw [mrun_add]; exact Sd
    · rw [mrun_add, hc]; exact L'

theorem chk_last (p : Lang.Prog) (S : StackSrc p) (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (inputs : Array Trace.Input) (n : Nat) (C : Chk a addrs inputs (later inputs 0).length n) :
    ∃ d, (mrun (n + d) (harnessMachine a inputs)).cpu.halted = true := by
  obtain ⟨m, ist, w, hit, Sn, L⟩ := C
  obtain ⟨lang, det, _⟩ := src_facts p S inputs
  obtain ⟨stj, hmj, hg, hwj, _⟩ := lang_chain p S inputs _ (Nat.le_refl _)
  obtain ⟨stj', m', istj, hmj', _, hitj, hwij⟩ := lang (later inputs 0).length
  rw [hmj] at hmj'
  cases hmj'
  have e := det _ _ _ _ _ hit hitj
  have hf : stj.world.framed = false := by obtain ⟨_, _, _, _, _, hf, _⟩ := hg; exact hf
  have hex : ist.world.next.1 = 0xFFFF := by
    rw [e, hwij]
    obtain ⟨_, _, hcase⟩ := next_spec stj.world hf
    rcases hcase with ⟨_, h1, _⟩ | ⟨i, k, hik, _, _⟩
    · exact h1
    · rw [hwj, List.drop_length] at hik
      cases hik
  rcases loop_iter (loopNeed ha) hsize hset L m with ⟨_, s', w', ⟨d, hd⟩, hh, _⟩ | ⟨hne, _⟩
  · obtain ⟨hc, _⟩ := run_sim_of img a addrs d _ _ Sn
    have hd' : wrun (img.ZH a addrs (0, 0)) d ((mrun n (harnessMachine a inputs)).cpu, w) = (s', w') := hd
    rw [hd'] at hc
    exact ⟨d, by rw [mrun_add, hc]; exact hh⟩
  · exact absurd hex hne

theorem chk_chain (p : Lang.Prog) (S : StackSrc p) (ha : assemble items = .ok a) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (Zof a addrs μ).OK ∧ ∀ k g st1, Callee (Zof a addrs μ) g st1 (IR.Sem.callF k img.ctx g st1))
    (inputs : Array Trace.Input) (hsz : a.bytes.size ≤ 0x8000) : ∀ j, j ≤ (later inputs 0).length →
    ∃ ns : List Nat, ns.length = j + 1 ∧ ns.Pairwise (· < ·) ∧ ∀ i (h : i < ns.length), Chk a addrs inputs i ns[i]
  | 0, _ => by
    obtain ⟨n, C⟩ := chk0 ha hsize hset inputs hsz
    exact ⟨[n], rfl, List.pairwise_singleton _ _, fun i h => by
      obtain rfl : i = 0 := by simp at h; omega
      exact C⟩
  | j + 1, hj => by
    obtain ⟨ns, hlen, hs, hc⟩ := chk_chain p S ha hsize hset inputs hsz j (by omega)
    obtain ⟨d, hd, C⟩ := chk_succ p S ha hsize hset inputs j ns[j] (by omega) (hc j (by omega))
    refine ⟨ns ++ [ns[j] + d], by simp [hlen], ?_, fun i h => ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rcases Nat.lt_or_ge i j with hij | hij
      · have := List.pairwise_iff_getElem.mp hs i j hi (by omega) hij
        omega
      · obtain rfl : i = j := by omega
        omega
    · rcases Nat.lt_or_ge i ns.length with hi | hi
      · rw [List.getElem_append_left hi]
        exact hc i hi
      · have hi' : i = ns.length := by simp at h; omega
        subst hi'
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        generalize ns[j] + d = x at C ⊢
        rw [hlen]
        exact C

end

/-! ## The observer's lines -/

/-- **The observer's `tcb` lines of the image of the stack.**  For the
image (loaded as `Tools.Z80.machineOf` loads it; the head of its loop at
`lh`, the label `rt_main`) and any input, from some number of steps on:
when `TcbObs.run` gives lines — it saw one head of the loop more than
there are items — they are one per input item, in order: the `j`-th at
the number of the input of the `j`-th item, saying what `Tcb.describe`
says of the Spec's control block after the first `j + 1` items. -/
theorem stackH_tcb_obs (p : Lang.Prog) (S : StackSrc p) :
    ∃ (a : Assembled) (lh : Nat), assemble items = .ok a ∧ a.labels.reverse.lookup "rt_main" = some lh ∧
      ∀ inputs : Array Trace.Input, ∃ N, ∀ maxSteps, N ≤ maxSteps → ∀ lines,
        TcbObs.run (loaded a) 0 inputs 32777 lh maxSteps = .ok lines →
        lines = (List.range (later inputs 0).length).map fun j =>
          (⟨((later inputs 0)[j]!).1, .tcb (specAfter inputs (j + 1)).tcb.describe⟩ : Trace.Line) := by
  obtain ⟨a, addrs, ha, hsize, hset⟩ := stackH_setting
  have hsz8 : a.bytes.size ≤ 0x8000 := by
    have h := assemble_items
    rw [ha] at h
    cases h
    simpa using rom_size
  obtain ⟨ok, _⟩ := hset (0, 0)
  have hhas : Has (Zof a addrs (0, 0)) 2589 mainLoopItems := img.has_of (loopNeed ha).loop
  obtain ⟨T, hT, hsym, _⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨a, T, ha, hsym, fun inputs => ?_⟩
  obtain ⟨ns, hlen, hs, hc⟩ := chk_chain p S ha hsize hset inputs hsz8 _ (Nat.le_refl _)
  obtain ⟨d, hhalt⟩ := chk_last p S ha hsize hset inputs ns[(later inputs 0).length]
    (hc _ (by omega))
  obtain ⟨N0, _, hh0, hfirst⟩ := first_halt (harnessMachine a inputs) _ hhalt
  refine ⟨N0, fun maxSteps hN lines hrun => ?_⟩
  have hobs : TcbObs.obsList T maxSteps { loaded a with harness := true, inputs := inputs, program := UInt8.ofNat 0 } =
      .ok (((List.range N0).filter fun k => TcbObs.obsAt T (mrun k (harnessMachine a inputs))).map
        fun k => mrun k (harnessMachine a inputs)) :=
    obsList_of T N0 maxSteps _ hN hfirst hh0
  have hall : ∀ x ∈ ns, x < N0 ∧ TcbObs.obsAt T (mrun x (harnessMachine a inputs)) = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨_, _, _, _, _, L⟩ := hc i hi
    refine ⟨Nat.lt_of_not_le fun hge => ?_, ?_⟩
    · obtain ⟨_, SN⟩ := run_sim_of img a addrs N0 _ _ (sim0 a inputs hsz8)
      have h1 := (sim_halted_run (ns[i] - N0) _ _ SN hh0).2
      rw [← mrun_add, show N0 + (ns[i] - N0) = ns[i] by omega, L.run] at h1
      cases h1
    · obtain ⟨ad, had, hpc⟩ := L.at_
      have e : ad = T := Option.some.inj (had.symm.trans hT)
      subst e
      unfold TcbObs.obsAt
      simp [hpc, L.sp, L.run]
  rw [run_eq] at hrun
  unfold TcbObs.runList at hrun
  rw [hobs] at hrun
  dsimp only at hrun
  split at hrun
  · rename_i hlen'
    replace hrun := Except.ok.inj hrun
    rw [List.length_map, itemCount_eq] at hlen'
    have hfil := filter_range_eq hs (fun x hx => (hall x hx).1) (fun x hx => (hall x hx).2) (by rw [hlen', hlen])
    rw [hfil] at hrun
    rw [← hrun]
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      have hj : j < (later inputs 0).length := by simpa using h2
      simp only [List.getElem_map, List.getElem_drop, List.getElem_range]
      obtain ⟨m, ist, w, hit, Sx, L⟩ := hc (1 + j) (by omega)
      obtain ⟨lang, det, _⟩ := src_facts p S inputs
      obtain ⟨stj, hmj, _, _, hcur⟩ := lang_chain p S inputs (j + 1) (by omega)
      obtain ⟨stj', m', istj, hmj', _, hitj, hwij⟩ := lang (j + 1)
      rw [hmj] at hmj'
      cases hmj'
      rw [Nat.add_comm 1 j] at hit
      have e := det _ _ _ _ _ hit hitj
      obtain ⟨_, m2, ist', r, pd, gt, gp, _, hit2, _, hgt, hHt, _, _, _, hdesc, hTt, hVt, _, _⟩ :=
        stackH_tcb_ir p S inputs j
      have e2 := det _ _ _ _ _ hit hit2
      have hcur' : (mrun ns[1 + j] (harnessMachine a inputs)).cur = ((later inputs 0)[j]!).1 := by
        rw [Sx.cur, L.world, e, hwij, hcur j rfl]
      have st := size_t p S hgt
      rw [gaddr_t, ← e2] at hHt
      have hram : Holds p (mrun ns[1 + j] (harnessMachine a inputs)).cpu.mem 32777 gt.ty r.val :=
        Holds.frame hTt hVt (by rw [st]; decide) hHt
          (fun x h1 h2 => L.mem x (inIv_tcb x h1 (by rw [st] at h2; omega)))
      rw [describeAt_of p S hgt hram, hdesc, hcur']
  · cases hrun

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_tcb_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_tcb_obs

/-- The addresses the observer takes from the image `build` makes of
the stack without the passes (`TcbObs.addrsOf`, which checks the record)
are the ones of `stackH_tcb_obs`: `t` at 32777, the head of the loop at
`rt_main` of the assembled items. -/
def addrsAgree : Bool :=
  match Codegen.build Stack.ir Runtime.harness (passes := false), assemble items, Net.prog.check with
  | .ok img, .ok a, .ok q =>
    match TcbObs.addrsOf q img, a.labels.reverse.lookup "rt_main" with
    | .ok (t, lh), some lh' => t == 32777 && lh == lh'
    | _, _ => false
  | _, _, _ => false

#guard addrsAgree

end Ember.Proof.Z80Gen.StackH
