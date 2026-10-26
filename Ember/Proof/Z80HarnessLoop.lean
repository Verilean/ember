import Ember.Proof.Z80HarnessW
import Ember.Proof.Z80Boot

/-!
# Ember.Proof.Z80HarnessLoop — the harness's loop, for any image (plan M7.3)

The loop of `Runtime.harness` that calls the entry while input remains
(`mainLoopItems`), from its items: one turn (`loop_iter`) and any number of
them against the IR's `irIter` (`loop_run`), for an image `I` in the
machine of the harness — given what `LoopNeed` asks of the image (where
the loop is, the count of idle calls, the entry) and that every
function does what the IR's does.  Used for the loopback image
(`Z80LoopH`) and for the image of the stack.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-- The harness's loop: call the entry while input remains and until
three calls in a row have not moved the position in the input. -/
def mainLoopItems : List Item :=
  [.label "rt_main",
   .ins ⟨.in, [.a, .mem (.num 0xD0)]⟩, .ins ⟨.or, [.a]⟩, .ins ⟨.jr, [.z, .imm (.sym "rt_done")]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_idle")]⟩, .ins ⟨.cp, [.imm (.num 3)]⟩, .ins ⟨.jr, [.nc, .imm (.sym "rt_done")]⟩,
   .ins ⟨.call, [.imm (.sym "f_entry")]⟩,
   .ins ⟨.in, [.a, .mem (.num 0xD9)]⟩, .ins ⟨.or, [.a]⟩, .ins ⟨.jr, [.nz, .imm (.sym "rt_main_r")]⟩,
   .ins ⟨.ld, [.hl, .imm (.sym "rt_idle")]⟩, .ins ⟨.inc, [.mhl]⟩, .ins ⟨.jr, [.imm (.sym "rt_main")]⟩,
   .label "rt_main_r", .ins ⟨.xor, [.a]⟩, .ins ⟨.ld, [.mem (.sym "rt_idle"), .a]⟩, .ins ⟨.jr, [.imm (.sym "rt_main")]⟩,
   .label "rt_done", .ins ⟨.di, []⟩, .ins ⟨.halt, []⟩, .ins ⟨.jr, [.imm (.sym "rt_done")]⟩]

theorem ImgIn.has_of (I : ImgIn) {a : Assembled} {addrs : List Nat} {μ : Nat × Nat} {k : Nat} {l : List Item}
    (h : (I.items.drop k).take l.length = l) : Has (I.ZH a addrs μ) k l := by
  intro j it hj
  have hlt : j < l.length := by
    rcases Nat.lt_or_ge j l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  rw [← h, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
  exact hj

/-- What the loop needs of the image `a` of `I`: the loop at `kL`, its
count of idle calls at `ia`, the entry `en` (the function `mf`). -/
structure LoopNeed (I : ImgIn) (a : Assembled) (kL ia : Nat) (en : String) (mf : IR.Fn) : Prop where
  loop : (I.items.drop kL).take mainLoopItems.length = mainLoopItems
  idle : a.labels.reverse.lookup "rt_idle" = some ia
  entry : ∃ e, a.labels.reverse.lookup "f_entry" = some e ∧ a.labels.reverse.lookup (fnLabel en) = some e ∧ e < 65536
  /-- The entry and what it calls do not write the loop's count. -/
  nowr : I.plan.wrB en ia = false
  room : I.plan.stackLo + I.plan.depthOf en ≤ 65534
  /-- The count is in RAM, below the stack's last two bytes, and no shared byte. -/
  iaRam : I.ramStart ≤ ia ∧ ia < 65534
  ram : I.ramStart ≤ 65534
  stackHi : I.stackHi = 65536
  data : ∀ x, inIv I.plan.data x = true → x ≠ ia ∧ x < 65534
  fn : I.ir.fn? en = some mf
  name : mf.name = en
  live : mf.dead = false
  noreg : mf.regParam = none
  isEntry : I.ir.entry = en

section
variable {I : ImgIn} {kL ia : Nat} {en : String} {mf : IR.Fn}

/-- **At the head of the loop**: the CPU there with its stack empty, the
shared bytes as the IR's state `st` has them, the loop's count of idle
calls at zero, and the machine holding `st`'s world with its mark at the
world's position in the input. -/
structure AtLoop (I : ImgIn) (kL ia : Nat) (a : Assembled) (addrs : List Nat) (st : IR.Sem.St) (s : Cpu) (w : HW) :
    Prop where
  at_ : At addrs kL s
  image : Img a 0 s
  run : s.halted = false
  rs : s.ramStart.toNat = I.ramStart
  msz : s.mem.size = 65536
  isz : st.mem.size = 65536
  sp : s.sp = 0
  mem : ∀ x, inIv I.plan.data x = true → s.mem.get! x = st.mem.get! x
  idle : s.mem.get! ia = 0
  world : w.1 = st.world
  mark : w.2.2.1 = (st.world.pos, st.world.off)
  nval : w.2.2.2 = (0, 0)

end

theorem orA_cond_z (s : Cpu) : (orA s).cond 1 = (s.a.toNat == 0) := orA_z s

theorem sp_wrap {x : UInt16} (h : x.toNat = 65534) : x + 2 = 0 := by
  have : x = 65534 := UInt16.toNat_inj.mp h
  rw [this]
  rfl

section
variable {I : ImgIn} {kL ia : Nat} {en : String} {mf : IR.Fn}

/-- **One turn of the loop.**  From its head: when the input is used up
the loop is left and the CPU stops (`di; halt`); else the entry is
called, and — as `IR.Sem.callF` says — the CPU is back at the head with
the machine holding the world the call left (given that the call moved
the position in the input: then the count of idle calls is set to zero
again), or it is at `rt_trap`.  The count of idle calls is zero at the
head, so the loop is never left by it. -/
theorem loop_iter {a : Assembled} {addrs : List Nat} (N : LoopNeed I a kL ia en mf) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (I.ZH a addrs μ).OK ∧ ∀ k g st1, Callee (I.ZH a addrs μ) g st1 (IR.Sem.callF k I.ctx g st1))
    {st : IR.Sem.St} {s : Cpu} {w : HW} (L : AtLoop I kL ia a addrs st s w) (m : Nat) :
    (st.world.next.1 = 0xFFFF ∧ ∃ s' w', WSteps (I.ZH a addrs (0, 0)) (s, w) (s', w') ∧ s'.halted = true ∧
        s'.iff1 = false ∧ w'.1 = st.world) ∨
    (st.world.next.1 ≠ 0xFFFF ∧
      match IR.Sem.callF m I.ctx en st with
      | .ok _ st' => (st'.world.pos, st'.world.off) ≠ (st.world.pos, st.world.off) →
          ∃ s' w', WSteps (I.ZH a addrs (0, 0)) (s, w) (s', w') ∧ AtLoop I kL ia a addrs st' s' w'
      | .trap st' => ∃ s' w', WSteps (I.ZH a addrs (0, 0)) (s, w) (s', w') ∧ w'.1 = st'.world ∧
          Trapped (I.ZH a addrs (0, 0)) st' s'
      | _ => True) := by
  have F := N
  obtain ⟨E, hEsym, hMsym, hElt⟩ := F.entry
  obtain ⟨ok, hcal⟩ := hset w.2.2.1
  have hl : Has (I.ZH a addrs w.2.2.1) kL mainLoopItems := I.has_of F.loop
  have hdat := F.data
  have hia := F.iaRam
  have M : Mach (I.ZH a addrs w.2.2.1) s := ⟨L.image, L.run⟩
  have at1 := at_label ok (hl.get 0 rfl) L.at_
  -- does input remain?
  obtain ⟨c1, p, hp, st1, at2, M1, hS1, ha1⟩ := in_step ok (n := 0xD0) (by decide) (hl.get 1 rfl) M at1 w
  have hp' : lo p = 0xD0 := hp
  have hdev1 : (I.ZH a addrs w.2.2.1).dev w (.read p) = w := by
    show hdev I.ctx w (.read p) = w
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
  have st03 : WSteps (I.ZH a addrs w.2.2.1) (s, w) (c3, w) := st1.trans (Steps.lift ok (st2.trans st3) _)
  have hS03 : Sys s c3 := (hS1.trans hS2).trans hS3
  by_cases hex : st.world.next.1 = 0xFFFF
  · -- the input is used up: out of the loop, and stop
    rw [decide_eq_true hex, if_pos rfl] at hbr3
    have at19 := at_label ok (hl.get 18 rfl) hbr3
    obtain ⟨s4, st4, hh4, hi4, _⟩ := di_halt ok (hl.get 19 rfl) (hl.get 20 rfl) M3 at19
    exact Or.inl ⟨hex, s4, w, ImgIn.wsteps_mark (st03.trans (Steps.lift ok st4 _)), hh4, hi4, L.world⟩
  refine Or.inr ⟨hex, ?_⟩
  rw [decide_eq_false hex] at hbr3
  simp only [Bool.false_eq_true, if_false] at hbr3
  -- the count of idle calls is zero: not three
  obtain ⟨c4, st4, at5, M4, hS4, ha4⟩ := ld_a_cell ok (hl.get 4 rfl) F.idle (by omega) M3 hbr3
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
  have st06 : WSteps (I.ZH a addrs w.2.2.1) (s, w) (c6, w) :=
    st03.trans (Steps.lift ok ((st4.trans st5).trans st6) _)
  -- call the entry
  obtain ⟨c7, st7, hsp7, hpc7, I7, hh7, hrs7, hsz7, hmem7, hback⟩ := call_top ok (hl.get 7 rfl) hEsym hElt hbr6
    M6.1 M6.2 (by rw [hS06.2.1]; exact L.rs) (by rw [hS06.1]; exact L.msz) (by rw [hS06.2.2.2]; exact L.sp)
    F.ram
  have st07 : WSteps (I.ZH a addrs w.2.2.1) (s, w) (c7, w) := st06.trans (Steps.lift ok st7 _)
  have hroom := F.room
  have ent : Entry (I.ZH a addrs w.2.2.1) mf st 0 c7 :=
    ⟨⟨E, by rw [F.name]; exact hMsym, hpc7⟩, I7, hh7, by rw [hrs7, hS06.2.1]; exact L.rs, hsz7, L.isz, fun x hx => by
        have := hdat x hx
        rw [hmem7 x (by omega), hS06.1]
        exact L.mem x hx,
      ⟨by rw [hsp7, F.name]; exact hroom, by rw [hsp7]; exact Nat.le_of_eq F.stackHi.symm⟩,
      fun n sl h => by rw [F.noreg] at h; cases h⟩
  have hout := hcal m en st mf st 0 c7 w F.fn F.live (by unfold stArg; rw [F.noreg]) ent ⟨L.world, rfl, L.nval⟩
  cases hres : IR.Sem.callF m I.ctx en st with
  | fuel => trivial
  | bad => trivial
  | trap st' =>
    rw [hres] at hout
    obtain ⟨s', w', stt, hwt, htr⟩ := hout
    exact ⟨s', w', ImgIn.wsteps_mark (st07.trans stt), hwt.1, htr⟩
  | ok r st' =>
    rw [hres] at hout
    intro hmoved
    obtain ⟨s2, w2, v, stc, hw2, _, hret⟩ := hout
    have hsp2 : s2.sp = 0 := by rw [hret.sp]; exact sp_wrap hsp7
    have at8 : At addrs (kL + 8) s2 := hback s2 (by rw [hret.pc]; show IR.Sem.rd c7.mem c7.sp.toNat 2 = _; rw [hsp7])
    have M8 : Mach (I.ZH a addrs w.2.2.1) s2 := ⟨hret.img, hret.run⟩
    have hidle2 : s2.mem.get! ia = 0 := by
      rw [hret.out ia (fun h => by
        have h' : I.plan.wrB en ia = true := by rw [← F.name]; exact h
        rw [F.nowr] at h'
        cases h')]
      show c7.mem.get! ia = 0
      rw [hmem7 _ (by omega), hS06.1]
      exact L.idle
    -- has the position in the input moved?
    obtain ⟨c9, p9, hp9, st9, at10, M9, hS9, ha9⟩ := in_step ok (n := 0xD9) (by decide) (hl.get 8 rfl) M8 at8 w2
    have hp9' : lo p9 = 0xD9 := hp9
    have hdev9 : (I.ZH a addrs w.2.2.1).dev w2 (.read p9) = (w2.1, w2.2.1, (w2.1.pos, w2.1.off), w2.2.2.2) := by
      show hdev I.ctx w2 (.read p9) = _
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
    obtain ⟨c13, st13, at17, M13, hmem13, hrs13, hh13, hsp13⟩ := ld_cell_a ok (hl.get 16 rfl) F.idle hia.1
      (by omega) M12 (by rw [hS212.2.1]; exact hret.rs) at16
    rw [xorA_a, hS212.1] at hmem13
    obtain ⟨c14, st14, M14, hS14, _, at0⟩ := jr_step ok (hl.get 17 rfl) (hl.get 0 rfl) M13 at17
    refine ⟨c14, (w2.1, w2.2.1, (w2.1.pos, w2.1.off), w2.2.2.2), ?_, ?_⟩
    · exact ImgIn.wsteps_mark (((st07.trans stc).trans st9).trans
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
        exact getBang_same _ _ _ (by rw [hret.msz]; omega)
      · show (w2.1.pos, w2.1.off) = _
        rw [hw2.1]

/-- A call of `main` with input remaining moves the position in the
input — along the run from `st`: what is taken of the program for the
loop not to be left before the input is used up. -/
def Moves (I : ImgIn) (en : String) (m : Nat) (st : IR.Sem.St) : Prop :=
  ∀ i sti r sti', irIter m I.ctx i st = some sti → IR.Sem.callF m I.ctx en sti = .ok r sti' →
    sti.world.next.1 ≠ 0xFFFF → (sti'.world.pos, sti'.world.off) ≠ (sti.world.pos, sti.world.off)

/-- **The loop against `irIter`**: when `j` calls of `main` end in the
IR's semantics, the machine is back at the head of the loop with the
world those calls leave — or it left the loop after `i ≤ j` of them and
stopped, the world being the one `i` calls leave **and the input used
up**. -/
theorem loop_run {a : Assembled} {addrs : List Nat} (N : LoopNeed I a kL ia en mf) (hsize : a.bytes.size < 65536)
    (hset : ∀ μ, (I.ZH a addrs μ).OK ∧ ∀ k g st1, Callee (I.ZH a addrs μ) g st1 (IR.Sem.callF k I.ctx g st1))
    (m : Nat) :
    ∀ (j : Nat) (st : IR.Sem.St) (s : Cpu) (w : HW), AtLoop I kL ia a addrs st s w → Moves I en m st →
      ∀ st', irIter m I.ctx j st = some st' →
        (∃ s' w', WSteps (I.ZH a addrs (0, 0)) (s, w) (s', w') ∧ AtLoop I kL ia a addrs st' s' w') ∨
        (∃ i sti s' w', i ≤ j ∧ irIter m I.ctx i st = some sti ∧ WSteps (I.ZH a addrs (0, 0)) (s, w) (s', w') ∧
          s'.halted = true ∧ s'.iff1 = false ∧ w'.1 = sti.world ∧ sti.world.next.1 = 0xFFFF)
  | 0, st, s, w, L, _, st', h => by
    cases h
    exact Or.inl ⟨s, w, WSteps.refl _ _, L⟩
  | j + 1, st, s, w, L, hmv, st', h => by
    rw [irIter] at h
    have he : I.ctx.prog.entry = en := N.isEntry
    rw [he] at h
    rcases loop_iter N hsize hset L m with ⟨hex, s1, w1, st1, hh, hi, hw⟩ | ⟨hnex, hit⟩
    · exact Or.inr ⟨0, st, s1, w1, Nat.zero_le _, rfl, st1, hh, hi, hw, hex⟩
    · cases hc : IR.Sem.callF m I.ctx en st with
      | ok r st1 =>
        rw [hc] at h hit
        obtain ⟨s1, w1, stp, L1⟩ := hit (hmv 0 st r st1 rfl hc hnex)
        have hmv1 : Moves I en m st1 := fun i sti r' sti' hi hcall hne =>
          hmv (i + 1) sti r' sti' (by rw [irIter, he, hc]; exact hi) hcall hne
        rcases loop_run N hsize hset m j st1 s1 w1 L1 hmv1 st' h with ⟨s2, w2, stp2, L2⟩ |
          ⟨i, sti, s2, w2, hi, hiter, stp2, hh, hif, hw, hex⟩
        · exact Or.inl ⟨s2, w2, stp.trans stp2, L2⟩
        · refine Or.inr ⟨i + 1, sti, s2, w2, by omega, ?_, stp.trans stp2, hh, hif, hw, hex⟩
          rw [irIter, he, hc]
          exact hiter
      | trap st1 => rw [hc] at h; cases h
      | fuel => rw [hc] at h; cases h
      | bad => rw [hc] at h; cases h

end

end Ember.Proof.Z80Gen
