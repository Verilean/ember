import Ember.Proof.Z80PassMeet
import Ember.Proof.Z80PassStackTrace
import Ember.Proof.Z80StackHTcbObs

/-!
# Ember.Proof.Z80PassStackTcb — the observer's `tcb` lines of the stack's image as built by default (plan M7.3)

`stackD_tcb_obs`: what `stackH_tcb_obs` says of `StackH`, of `StackD` —
the image `build` makes by default, loaded as `Tools.Z80.machineOf`
loads it: when the observer (`TcbObs.run`) gives lines, they are one per
input item, in order, each saying what `Tcb.describe` says of the Spec's
control block after that item.

How: the steps of `StackH`'s run at the head of its loop (`chk_chain`)
are steps where its stack is empty and it is not halted; every such step
is where the two runs meet (`Z80PassMeet.meet`), at a row with no frames;
the item of `A` there is `rt_main`'s (its address), so `B`'s is too
(`rows_main`): `B` is at the head of its loop, its stack empty, not
halted, with the same RAM kept equal (where the record `t` is) and the
same world (the same input).  Those steps of `B` go up with `A`'s.

Like `stackH_tcb_obs`, it says what the lines are when the observer gives
them: that the observer saw no other head of the loop is its own count,
not proved (soundness, not totality).
-/

namespace Ember.Proof.PassSim.Stack
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim Ember.Proof.PassSim Ember.Proof.Z80Gen

/-! ## Addresses -/

/-- Addresses go up with the items. -/
theorem placed_mono {items : List Item} {o : Nat} {a : Assembled} {addrs : List Nat} (P : Placed items o a addrs) :
    ∀ d i ai aj, i + d ≤ items.length → addrs[i]? = some ai → addrs[i + d]? = some aj → ai ≤ aj
  | 0, i, ai, aj, _, h1, h2 => by rw [Nat.add_zero, h1] at h2; cases h2; exact Nat.le_refl _
  | d + 1, i, ai, aj, hd, h1, h2 => by
    obtain ⟨it, hit⟩ : ∃ it, items[i + d]? = some it := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ad, bs, e1, _, e2, _⟩ := P.2 (i + d) it hit
    have := placed_mono P d i ai ad (by omega) h1 e1
    rw [show i + (d + 1) = i + d + 1 by omega, e2] at h2
    cases h2
    omega

theorem items_H : StackH.items[2588]? = some (.ins ⟨.call, [.imm (.sym "rt_init" 0)]⟩) ∧
    StackH.items[2589]? = some (.label "rt_main") ∧ StackH.items[2590]? = some (.ins ⟨.in, [.a, .mem (.num 208)]⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem items_D : StackD.items[2490]? = some (.label "rt_main") := by decide +kernel

theorem rows_main : (rowAt CertD.rows 2589).kb = 2490 ∧ (rowAt CertD.rows 2590).kb = 2491 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem in_len {env : Env} {bs : List UInt8} (h : Item.encode (.ins ⟨.in, [.a, .mem (.num 208)]⟩) env = .ok bs) :
    bs.length = 2 := by
  have h' : Asm.encode ⟨.in, [.a, .mem (.num 208)]⟩ env = .ok bs := h
  have h'' := encode_run h'
  have he' : ((imm8 (.num 208)).run env).bind (fun l => .ok ([0xDB] ++ l)) = Except.ok bs := h''
  obtain ⟨l, hl, hb⟩ := bind_ok he'
  obtain rfl := imm8_bytes hl
  cases hb
  rfl

/-- A label's address, in an image. -/
theorem label_addr' {C : Code} {j : Nat} {l : String} (hj : C.items[j]? = some (.label l)) :
    ∃ T, C.addrs[j]? = some T ∧ C.a.labels.reverse.lookup l = some T := by
  obtain ⟨ad, bs, h1, _, _, _, _, _, h6⟩ := C.placed.2 j _ hj
  exact ⟨ad, h1, h6 l rfl⟩

/-- **The items of `StackH` at `rt_main`'s address**: the label and the instruction after it. -/
theorem row_main {k T : Nat} (hk : k < StackH.items.length) (hT : codeH.addrs[2589]? = some T)
    (hkT : codeH.addrs[k]? = some T) : k = 2589 ∨ k = 2590 := by
  obtain ⟨i88, i89, i90⟩ := items_H
  have P := codeH.placed
  obtain ⟨a88, bs88, e88, enc88, n88, _⟩ := P.2 2588 _ i88
  have l88 : bs88.length = 3 := call_len (show Asm.encode ⟨.call, [.imm (.sym "rt_init" 0)]⟩ (codeH.a.env a88) = .ok bs88 from enc88)
  obtain ⟨a89, bs89, e89, enc89, n89, _⟩ := P.2 2589 _ i89
  have l89 : bs89 = [] := by cases enc89; rfl
  obtain ⟨a90, bs90, e90, enc90, n90, _⟩ := P.2 2590 _ i90
  have l90 : bs90.length = 2 := in_len enc90
  have hlen : 2590 < codeH.items.length := (List.getElem?_eq_some_iff.mp i90).1
  have hk' : k < codeH.items.length := hk
  rw [n88, l88] at e89; cases e89
  rw [n88, l88] at hT; cases hT
  rw [n89, l89] at e90; cases e90
  simp only [List.length_nil, Nat.add_zero] at n90
  rw [l90] at n90
  rcases Nat.lt_or_ge k 2589 with h | h
  · exfalso
    have := placed_mono P (2588 - k) k (a88 + 3) a88 (by omega) hkT
      (by rw [show k + (2588 - k) = 2588 by omega]; exact e88)
    omega
  · rcases Nat.lt_or_ge k 2591 with h' | h'
    · omega
    · exfalso
      have := placed_mono P (k - 2591) 2591 (a88 + 3 + 2) (a88 + 3) (by omega) n90
        (by rw [show 2591 + (k - 2591) = k by omega]; exact hkT)
      omega

/-! ## The machines the tests run, as the runs of the proofs -/

open Ember.Proof.Z80Gen.LoopH (Sim harnessMachine harness_reset run_sim_of)
open Ember.Proof.Refine (later specAfter)
open Ember.Trace (Input)

theorem runA (inputs : Array Input) (n : Nat) :
    (PassSim.mrun hD n (x0 inputs)).1 = (LoopH.mrun n (harnessMachine StackH.asm inputs)).cpu ∧
      Sim StackH.img.ctx (LoopH.mrun n (harnessMachine StackH.asm inputs)) (PassSim.mrun hD n (x0 inputs)).2 := by
  have hsz : StackH.asm.bytes.size ≤ 0x8000 := by simpa using StackH.rom_size
  obtain ⟨hc, Sn⟩ := run_sim_of StackH.img StackH.asm [] n _ _ (StackH.sim0 StackH.asm inputs hsz)
  rw [wrun_hD] at hc Sn
  exact ⟨hc.symm, Sn⟩

theorem runB (inputs : Array Input) (n : Nat) :
    (PassSim.mrun hD n (y0 inputs)).1 = (LoopH.mrun n (harnessMachine StackD.asm inputs)).cpu ∧
      Sim StackH.img.ctx (LoopH.mrun n (harnessMachine StackD.asm inputs)) (PassSim.mrun hD n (y0 inputs)).2 := by
  obtain ⟨hc, Sn⟩ := run_sim_of StackH.img StackD.asm [] n _ _ (StackH.sim0 StackD.asm inputs romD_le)
  rw [wrun_hD] at hc Sn
  exact ⟨hc.symm, Sn⟩

/-- The address of `rt_main` in `StackH`, from any placing of its items. -/
theorem addr_mainH {addrs : List Nat} (P : Placed StackH.items 0 StackH.asm addrs) {T : Nat}
    (h : addrs[2589]? = some T) : codeH.addrs[2589]? = some T := by
  obtain ⟨_, i89, _⟩ := items_H
  obtain ⟨ad, _, h1, _, _, _, _, _, h6⟩ := P.2 2589 _ i89
  obtain ⟨ad', _, h1', _, _, _, _, _, h6'⟩ := codeH.placed.2 2589 _ i89
  rw [h] at h1; cases h1
  have e := (h6 _ rfl).symm.trans (h6' _ rfl)
  cases e
  exact h1'

/-- `StackD` at `rt_main`'s row of the certificate (the label or the instruction after it): at the
address of `rt_main`. -/
theorem atB_main {k : Nat} (hk : k = 2589 ∨ k = 2590) {TD : Nat} (hTD : codeD.addrs[2490]? = some TD)
    {s : Cpu} (h : At codeD.addrs (rowAt CertD.rows k).kb s) : s.pc.toNat = TD := by
  obtain ⟨r1, r2⟩ := rows_main
  have hTD' : codeD.addrs[2491]? = some TD := label_next (C := codeD) items_D hTD
  obtain ⟨ad, had, hpc⟩ := h
  rcases hk with rfl | rfl
  · rw [r1, hTD] at had; cases had; exact hpc
  · rw [r2, hTD'] at had; cases had; exact hpc

theorem top_zero {sp : UInt16} (h : top sp = 65536) : sp = 0 := by
  unfold top at h
  split at h
  · assumption
  · have := sp.toNat_lt; omega

/-! ## The observer's lines -/

theorem mask_mem' (th tl : Bool) (s t : Cpu) : (mask th tl s t).mem = t.mem := by cases t; rfl

/-- The RAM kept equal, in two related machines. -/
theorem EqvT.mem' {lo hi : Nat} {th tl : Bool} {s t : Cpu} (E : EqvT lo hi th tl s t) {x : Nat} (h1 : lo ≤ x)
    (h2 : x < hi) : t.mem.get! x = s.mem.get! x := by
  have := E.mem x h1 h2
  rw [mask_mem'] at this
  exact this.symm

/-- **The observer's `tcb` lines of the stack's image as built by default.**  For the image (`StackD`,
loaded as `Tools.Z80.machineOf` loads it; the head of its loop at `lh`, the label `rt_main`) and any
input, from some number of steps on: when `TcbObs.run` gives lines — it saw one head of the loop more
than there are items — they are one per input item, in order: the `j`-th at the number of the input
of the `j`-th item, saying what `Tcb.describe` says of the Spec's control block after the first
`j + 1` items.  (That the observer gives lines is its own count: not proved.) -/
theorem stackD_tcb_obs (p : Lang.Prog) (S : StackH.StackSrc p) :
    ∃ (a : Assembled) (lh : Nat), assemble StackD.items = .ok a ∧ a.labels.reverse.lookup "rt_main" = some lh ∧
      ∀ inputs : Array Trace.Input, ∃ N, ∀ maxSteps, N ≤ maxSteps → ∀ lines,
        TcbObs.run (StackH.loaded a) 0 inputs 32777 lh maxSteps = .ok lines →
        lines = (List.range (later inputs 0).length).map fun j =>
          (⟨((later inputs 0)[j]!).1, .tcb (specAfter inputs (j + 1)).tcb.describe⟩ : Trace.Line) := by
  obtain ⟨TD, hTD, hsymD⟩ := label_addr' (C := codeD) items_D
  refine ⟨StackD.asm, TD, StackD.assemble_items, hsymD, fun inputs => ?_⟩
  -- `StackH`'s heads of the loop
  obtain ⟨a, addrs, ha, hsize, hset⟩ := StackH.stackH_setting
  have haH : a = StackH.asm := by have h := StackH.assemble_items; rw [ha] at h; cases h; rfl
  subst haH
  have hsz8 : StackH.asm.bytes.size ≤ 0x8000 := by simpa using StackH.rom_size
  obtain ⟨ok, _⟩ := hset (0, 0)
  obtain ⟨ns, hlen, hs, hc⟩ := StackH.chk_chain p S ha hsize hset inputs hsz8 _ (Nat.le_refl _)
  -- `StackD`'s run halts: its first halt
  obtain ⟨_, _, M, _, _, _, hhM, _⟩ := stackD_halts p S inputs
  obtain ⟨N0, _, hh0, hfirst⟩ := first_halt (harnessMachine StackD.asm inputs) M hhM
  refine ⟨N0, fun maxSteps hN lines hrun => ?_⟩
  -- the two runs side by side, their meeting points
  have Gl := glob inputs
  have hI0 := inv0 Gl (sync0 inputs)
  -- `A`'s address of `rt_main`
  have hTA : ∃ T, codeH.addrs[2589]? = some T ∧ ∀ i (h : i < ns.length),
      (PassSim.mrun hD ns[i] (x0 inputs)).1.pc.toNat = T := by
    obtain ⟨_, _, _, _, _, L0⟩ := hc 0 (by omega)
    obtain ⟨T, hT, _⟩ := L0.at_
    refine ⟨T, addr_mainH ok.placed hT, fun i hi => ?_⟩
    obtain ⟨_, _, _, _, _, L⟩ := hc i hi
    obtain ⟨T', hT', hpc⟩ := L.at_
    rw [hT] at hT'; cases hT'
    rw [(runA inputs ns[i]).1]; exact hpc
  obtain ⟨T, hT, hpcA⟩ := hTA
  -- each head of `A`'s loop: where the runs meet, `B` at the head of its loop
  have good : ∀ i (h : i < ns.length), (PassSim.mrun hD ns[i] (x0 inputs)).1.halted = false ∧
      (PassSim.mrun hD ns[i] (x0 inputs)).1.sp = 0 := by
    intro i hi
    obtain ⟨_, _, _, _, _, L⟩ := hc i hi
    rw [(runA inputs ns[i]).1]; exact ⟨L.run, L.sp⟩
  let ix : Nat → Nat := fun n => Classical.epsilon fun j => (seq Gl (y0 inputs) j).1 = n
  have hix : ∀ i (h : i < ns.length), (seq Gl (y0 inputs) (ix ns[i])).1 = ns[i] := by
    intro i hi
    exact Classical.epsilon_spec (cover Gl hI0 (good i hi).1 (good i hi).2)
  let ms := ns.map fun n => (seq Gl (y0 inputs) (ix n)).2
  have hmsl : ms.length = ns.length := by simp [ms]
  have hmeet : ∀ i (h : i < ns.length), ∃ k, (k = 2589 ∨ k = 2590) ∧
      Sync hD codeH codeD CertD.lo CertD.hi [] k (rowAt CertD.rows k).kb (rowAt CertD.rows k).th (rowAt CertD.rows k).tl
        (PassSim.mrun hD ns[i] (x0 inputs)) (PassSim.mrun hD (seq Gl (y0 inputs) (ix ns[i])).2 (y0 inputs)) := by
    intro i hi
    have e := hix i hi
    obtain ⟨k, ht, S'⟩ := meet Gl hI0 (i := ix ns[i]) (by rw [e]; exact (good i hi).1) (by rw [e]; exact (good i hi).2)
    rw [e] at S'
    refine ⟨k, ?_, S'⟩
    have hk : k < StackH.items.length := by
      have := rowAt_some ht
      have h2 := (List.getElem?_eq_some_iff.mp this).1
      rw [CertD.certD_ok.1] at h2; exact h2
    obtain ⟨ad, had, hpc⟩ := S'.atA
    have : ad = T := by rw [← hpc]; exact hpcA i hi
    subst this
    exact row_main hk hT had
  have hB : ∀ i (h : i < ns.length), (seq Gl (y0 inputs) (ix ns[i])).2 < N0 ∧
      TcbObs.obsAt TD (LoopH.mrun (seq Gl (y0 inputs) (ix ns[i])).2 (harnessMachine StackD.asm inputs)) = true := by
    intro i hi
    obtain ⟨k, hk, S'⟩ := hmeet i hi
    have hcB := (runB inputs (seq Gl (y0 inputs) (ix ns[i])).2).1
    have hrun : (LoopH.mrun (seq Gl (y0 inputs) (ix ns[i])).2 (harnessMachine StackD.asm inputs)).cpu.halted = false := by
      rw [← hcB]; exact S'.LB.2
    refine ⟨Nat.lt_of_not_le fun hge => ?_, ?_⟩
    · obtain ⟨_, SN⟩ := run_sim_of StackH.img StackD.asm [] N0 _ _ (StackH.sim0 StackD.asm inputs romD_le)
      have h1 := (sim_halted_run ((seq Gl (y0 inputs) (ix ns[i])).2 - N0) _ _ SN hh0).2
      rw [← Z80Gen.mrun_add, show N0 + ((seq Gl (y0 inputs) (ix ns[i])).2 - N0) = (seq Gl (y0 inputs) (ix ns[i])).2 by
        omega, hrun] at h1
      cases h1
    · have hpc := atB_main hk hTD S'.atB
      have hsp : (PassSim.mrun hD (seq Gl (y0 inputs) (ix ns[i])).2 (y0 inputs)).1.sp = 0 := top_zero S'.stk.2
      unfold TcbObs.obsAt
      rw [← hcB]
      simp [hpc, hsp, S'.LB.2]
  have hms_sorted : ms.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [ms, List.getElem_map]
    have hi' : i < ns.length := by simpa [ms] using hi
    have hj' : j < ns.length := by simpa [ms] using hj
    have h1 := List.pairwise_iff_getElem.mp hs i j hi' hj' hij
    refine seq_lt Gl hI0 (by rw [hix i hi', hix j hj']; exact h1) (by rw [hix j hj']; exact (good j hj').1)
  have hobs : TcbObs.obsList TD maxSteps
      { StackH.loaded StackD.asm with harness := true, inputs := inputs, program := UInt8.ofNat 0 } =
      .ok (((List.range N0).filter fun k => TcbObs.obsAt TD (LoopH.mrun k (harnessMachine StackD.asm inputs))).map
        fun k => LoopH.mrun k (harnessMachine StackD.asm inputs)) :=
    StackH.obsList_of TD N0 maxSteps _ hN hfirst hh0
  have hall : ∀ x ∈ ms, x < N0 ∧ TcbObs.obsAt TD (LoopH.mrun x (harnessMachine StackD.asm inputs)) = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < ns.length := by simpa [ms] using hi
    simp only [ms, List.getElem_map]
    exact hB i hi'
  rw [StackH.run_eq] at hrun
  unfold TcbObs.runList at hrun
  rw [hobs] at hrun
  dsimp only at hrun
  split at hrun
  · rename_i hlen'
    replace hrun := Except.ok.inj hrun
    rw [List.length_map, StackH.itemCount_eq] at hlen'
    have hfil := StackH.filter_range_eq hms_sorted (fun x hx => (hall x hx).1) (fun x hx => (hall x hx).2)
      (by rw [hlen', hmsl, hlen])
    rw [hfil] at hrun
    rw [← hrun]
    apply List.ext_getElem
    · simp [hmsl, hlen]
    · intro j h1 h2
      have hj : j < (later inputs 0).length := by simpa using h2
      have hi : 1 + j < ns.length := by omega
      simp only [List.getElem_map, List.getElem_drop, List.getElem_range, ms]
      obtain ⟨m, ist, w, hit, Sx, L⟩ := hc (1 + j) hi
      obtain ⟨k, _, S'⟩ := hmeet (1 + j) hi
      obtain ⟨hcA, SA⟩ := runA inputs ns[1 + j]
      obtain ⟨hcB, SB⟩ := runB inputs (seq Gl (y0 inputs) (ix ns[1 + j])).2
      obtain ⟨lang, det, _⟩ := StackH.src_facts p S inputs
      obtain ⟨stj, hmj, _, _, hcur⟩ := StackH.lang_chain p S inputs (j + 1) (by omega)
      obtain ⟨stj', m', istj, hmj', _, hitj, hwij⟩ := lang (j + 1)
      rw [hmj] at hmj'
      cases hmj'
      rw [Nat.add_comm 1 j] at hit
      have e := det _ _ _ _ _ hit hitj
      obtain ⟨_, m2, ist', r, pd, gt, gp, _, hit2, _, hgt, hHt, _, _, _, hdesc, hTt, hVt, _, _⟩ :=
        StackH.stackH_tcb_ir p S inputs j
      have e2 := det _ _ _ _ _ hit hit2
      -- `B`'s world is `A`'s: the same input
      have hcurA : (LoopH.mrun ns[1 + j] (harnessMachine StackH.asm inputs)).cur = ((later inputs 0)[j]!).1 := by
        rw [Sx.cur, L.world, e, hwij, hcur j rfl]
      have hcurB : (LoopH.mrun (seq Gl (y0 inputs) (ix ns[1 + j])).2 (harnessMachine StackD.asm inputs)).cur =
          ((later inputs 0)[j]!).1 := by
        rw [SB.cur, S'.w, ← SA.cur, hcurA]
      have st := StackH.size_t p S hgt
      rw [StackH.gaddr_t, ← e2] at hHt
      -- `B`'s RAM where the record is: `A`'s
      have hram : Holds p (LoopH.mrun (seq Gl (y0 inputs) (ix ns[1 + j])).2 (harnessMachine StackD.asm inputs)).cpu.mem
          32777 gt.ty r.val := by
        refine Holds.frame hTt hVt (by rw [st]; decide) hHt (fun x h1 h2 => ?_)
        rw [← hcB, EqvT.mem' S'.E (by simp [CertD.lo]; omega) (by rw [st] at h2; simp [CertD.hi]; omega), hcA]
        exact L.mem x (StackH.inIv_tcb x h1 (by rw [st] at h2; omega))
      rw [StackH.describeAt_of p S hgt hram, hdesc, hcurB]
  · cases hrun

/-- info: 'Ember.Proof.PassSim.Stack.stackD_tcb_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackD_tcb_obs

/-- The addresses the observer takes from the image `build` makes of the stack by default
(`TcbObs.addrsOf`, which checks the record) are the ones of `stackD_tcb_obs`: `t` at 32777, the head of
the loop at `rt_main` of `StackD`'s items assembled. -/
def addrsAgreeD : Bool :=
  match Codegen.build Stack.ir Runtime.harness, assemble StackD.items, Net.prog.check with
  | .ok img, .ok a, .ok q =>
    match TcbObs.addrsOf q img, a.labels.reverse.lookup "rt_main" with
    | .ok (t, lh), some lh' => t == 32777 && lh == lh'
    | _, _ => false
  | _, _, _ => false

#guard addrsAgreeD

end Ember.Proof.PassSim.Stack
