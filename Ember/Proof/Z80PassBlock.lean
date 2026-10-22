import Ember.Proof.Z80PassSeg
import Ember.Proof.Z80Wide

/-!
# Ember.Proof.Z80PassBlock — a call of a routine of the runtime that works through `HL`, in both machines (plan M7.3)

The routines of the runtime that read or write the bytes at `HL`
(`rt_ld32`, …) are run, in the two machines, as one segment each: from
the call to the item after it.  Inside, the bytes they touch are those
of the call's operand, which the caller gives: in the RAM kept equal
(a hypothesis about the address, as for an ordinary instruction), or a
literal of each image's ROM (`ld hl,lit` just before the call; the two
literals the same bytes).

`blk_ld32`: `rt_ld32`, the four bytes at `HL` into the accumulator.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

/-- A label is where the item after it is. -/
theorem Sync.skip {D : Dev} {A B : Code} {lo hi : Nat} {G : List Frame} {kA kB : Nat} {th tl : Bool}
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) {lA lB : String}
    (hA : A.items[kA]? = some (.label lA)) (hB : B.items[kB]? = some (.label lB)) :
    Sync D A B lo hi G (kA + 1) (kB + 1) th tl x y :=
  { S with
    atA := at_skip A.placed hA (fun _ => rfl) S.atA
    atB := at_skip B.placed hB (fun _ => rfl) S.atB }

/-- The machine's step, from what the instruction does: no I/O, the devices as they were. -/
theorem mstep_exec (D : Dev) {C : Code} {k : Nat} {i : Instr} (hk : C.items[k]? = some (.ins i))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) {s' : Cpu}
    (hx : ∀ pa inp, exec (C.a.env pa) i s inp = some s') (hio : s'.io = .none) :
    mstep D (s, w) = (s', w) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have st := step_item C.placed L.1 hk had hpc L.2 (hx ad (D.bus w))
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [st.1, hio, D.quiet]

/-- Two segments, one after the other. -/
def Reach (D : Dev) (A B : Code) (lo hi : Nat) (x y : Cpu × D.W) (G : List Frame) (kA kB : Nat) (th tl : Bool) :
    Prop :=
  ∃ nA nB, 0 < nA ∧ Sync D A B lo hi G kA kB th tl (mrun D nA x) (mrun D nB y)

/-- An operand that both images resolve alike gives the same immediate bytes (not a relative jump). -/
theorem imm_same {A B : Code} (i : Instr) (v : Val) (hi : i.immVal? = some v) (hop : i.op ≠ .jr ∧ i.op ≠ .djnz)
    (hv : ∀ pa pb, (A.a.env pa).val v = (B.a.env pb).val v) :
    ∀ pa pb, i.immB (A.a.env pa) = i.immB (B.a.env pb) ∧ i.immW (A.a.env pa) = i.immW (B.a.env pb) := by
  intro pa pb
  have e : i.immInt (A.a.env pa) = i.immInt (B.a.env pb) := by simp only [Instr.immInt, hi, hv pa pb]
  refine ⟨?_, ?_⟩
  · simp only [Instr.immB, e]
    have : (i.op == .jr || i.op == .djnz) = false := by
      obtain ⟨h1, h2⟩ := hop
      revert h1 h2
      cases i.op <;> decide
    simp only [this]; rfl
  · simp only [Instr.immW, e]

/-- A number is resolved alike by both images. -/
theorem val_num {A B : Code} (n : Int) : ∀ pa pb, (A.a.env pa).val (.num n) = (B.a.env pb).val (.num n) :=
  fun _ _ => rfl

/-- The state after `ld rr,nn`. -/
def ldRP (s : Cpu) (p : UInt8) (n : UInt16) : Cpu := ((skip (op1 s) 2).setRp .hl p n).tick 10

theorem exec_ld_rp (env : Env) (x : Arg) (p : UInt8) (hx : rr? x = some p) (hp : p ≠ 3) (v : Val) (s : Cpu)
    (inp : UInt16 → UInt8) :
    exec env ⟨.ld, [x, .imm v]⟩ s inp = some (ldRP s p (Instr.immW env ⟨.ld, [x, .imm v]⟩)) := by
  cases x <;> simp only [rr?, reduceCtorEq, Option.some.injEq] at hx <;> subst hx <;>
    first | rfl | exact absurd rfl hp

/-! ## What the steps leave in the registers of one machine -/

theorem called_regs (s : Cpu) (n : UInt16) :
    (called s n).hl = s.hl ∧ (called s n).de = s.de ∧ (called s n).bc = s.bc := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> rfl

theorem ldRP_bc (s : Cpu) (n : UInt16) : (ldRP s 0 n).bc = n ∧ (ldRP s 0 n).hl = s.hl ∧ (ldRP s 0 n).de = s.de := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ldRP, Cpu.setRp, Cpu.setBC, Cpu.bc, Cpu.hl, Cpu.de, Cpu.tick, skip, op1, Cpu.bumpR,
      Ember.Proof.Z80Gen.mk16_hi_lo]

theorem ldRP_de (s : Cpu) (n : UInt16) : (ldRP s 1 n).de = n ∧ (ldRP s 1 n).hl = s.hl ∧ (ldRP s 1 n).bc = s.bc := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ldRP, Cpu.setRp, Cpu.setDE, Cpu.bc, Cpu.hl, Cpu.de, Cpu.tick, skip, op1, Cpu.bumpR,
      Ember.Proof.Z80Gen.mk16_hi_lo]

theorem ldirS_regs (s : Cpu) : (ldirS s).hl = s.hl + 1 ∧ (ldirS s).de = s.de + 1 ∧ (ldirS s).bc = s.bc - 1 := by
  simp only [ldirS, ldirG]
  split <;> refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Cpu.hl, Cpu.de, Cpu.bc, op2, op1, skip, Cpu.bumpR, Ember.Proof.Z80Gen.mk16_hi_lo]

theorem ldRP_falls (x : Arg) (v : Val) : (⟨.ld, [x, .imm v]⟩ : Instr).falls = true := rfl

/-! ## `ldir`, all its rounds -/

theorem eqv_ff {lo hi : Nat} {s t : Cpu} (E : EqvT lo hi false false s t) : Eqv lo hi s t := by
  unfold EqvT at E; rw [mask_ff] at E; exact E

theorem toNat_add1 (v : UInt16) (h : v.toNat + 1 < 65536) : (v + 1).toNat = v.toNat + 1 := by
  rw [UInt16.toNat_add]; simp only [UInt16.toNat_one]; omega

theorem toNat_sub1 (v : UInt16) (h : 1 ≤ v.toNat) : (v - 1).toNat = v.toNat - 1 := by
  rw [UInt16.toNat_sub_of_le]; · rfl
  rw [UInt16.le_iff_toNat_le]; exact h

/-- **All the rounds of an `ldir` within the RAM kept equal**, in both machines: `BC` the count, the
bytes read and written in that RAM. -/
theorem ldir_eq_rounds (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {kA kB : Nat}
    (hA : A.items[kA]? = some (.ins ⟨.ldir, []⟩)) (hB : B.items[kB]? = some (.ins ⟨.ldir, []⟩)) :
    ∀ (n : Nat) (x y : Cpu × D.W), Sync D A B lo hi G kA kB false false x y → x.1.bc.toNat = n + 1 →
      lo ≤ x.1.hl.toNat → x.1.hl.toNat + n + 1 ≤ hi → lo ≤ x.1.de.toNat → x.1.de.toNat + n + 1 ≤ hi →
      Sync D A B lo hi G (kA + 1) (kB + 1) false false (mrun D (n + 1) x) (mrun D (n + 1) y)
  | n, x, y, S, hbc, h1, h2, d1, d2 => by
    have E := eqv_ff S.E
    have hhl : x.1.hl = y.1.hl := RegsS.hl E.regs
    have hv : x.1.mem.get! x.1.hl.toNat = y.1.mem.get! y.1.hl.toNat := by rw [← hhl]; exact E.mem _ h1 (by omega)
    have st := seg_ldir D hhi hA hB S hv ⟨d1, by omega⟩
    obtain ⟨eA, _⟩ := ldir_mstep D hA S.LA S.atA x.2
    have hx : mstep D x = (ldirS x.1, x.2) := eA
    obtain ⟨rh, rd, rb⟩ := ldirS_regs x.1
    cases n with
    | zero =>
      have h0 : x.1.bc - 1 = 0 := by apply UInt16.toNat_inj.mp; rw [toNat_sub1 _ (by omega)]; simp [hbc]
      have hne : ¬ ((x.1.bc - 1 != 0) = true) := by rw [h0]; decide
      rw [if_neg hne] at st
      exact st
    | succ m =>
      have hne : (x.1.bc - 1 != 0) = true := by
        have h' : (x.1.bc - 1).toNat = m + 1 := by rw [toNat_sub1 _ (by omega)]; omega
        have : x.1.bc - 1 ≠ 0 := by intro e; rw [e] at h'; simp at h'
        simp [this]
      rw [if_pos hne] at st
      have r := ldir_eq_rounds D hhi hA hB m (mstep D x) (mstep D y) st
        (by rw [hx]; simp only; rw [rb, toNat_sub1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rh, toNat_add1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rh, toNat_add1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
      exact r

/-! ## `rt_ld32` -/

theorem mrun_8 (D : Dev) (x : Cpu × D.W) :
    mrun D 8 x = mstep D (mrun D 4 (mstep D (mstep D (mstep D x)))) := by
  show mrun D (3 + (4 + 1)) x = _
  rw [mrun_add, mrun_add]; rfl

/-- **`call rt_ld32` in both machines, the four bytes at `HL` in the RAM kept equal**: the routine's
items in each image (`ldItems`, at `r` and `q`), the accumulator `acc` in that RAM, room on the stack
for the return address: eight steps of each and the relation holds at the items after the calls. -/
theorem blk_ld32 (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc : Nat}
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym "rt_ld32" 0)]⟩))
    (hB : B.items[kB]? = some (.ins ⟨.call, [.imm (.sym "rt_ld32" 0)]⟩))
    (hLA : Has A r ldItems) (hLB : Has B q ldItems)
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB false false x y)
    (room : hi + 2 ≤ top x.1.sp) (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    Sync D A B lo hi G (kA + 1) (kB + 1) false false (mrun D 8 x) (mrun D 8 y) := by
  have l3A : A.items[r + 3]? = some (.label "rt_ld32") := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label "rt_ld32") := hLB.get 3 rfl
  have i4A : A.items[r + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLA.get 4 rfl
  have i4B : B.items[q + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLB.get 4 rfl
  have l5A : A.items[r + 5]? = some (.label "rt_ldw") := hLA.get 5 rfl
  have l5B : B.items[q + 5]? = some (.label "rt_ldw") := hLB.get 5 rfl
  have i6A : A.items[r + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLA.get 6 rfl
  have i6B : B.items[q + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLB.get 6 rfl
  have i7A : A.items[r + 7]? = some (.ins ⟨.ldir, []⟩) := hLA.get 7 rfl
  have i7B : B.items[q + 7]? = some (.ins ⟨.ldir, []⟩) := hLB.get 7 rfl
  have i8A : A.items[r + 8]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLA.get 8 rfl
  have i8B : B.items[q + 8]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLB.get 8 rfl
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  obtain ⟨sA, w⟩ := x
  simp only at room foot
  rw [mrun_8, mrun_8]
  -- the call
  obtain ⟨T, adA, _, _, _, _, eA1, _⟩ := call_mstep D hA l3A S.LA S.atA w
  have S1 := (seg_call D hhi hA l3A hB l3B S hlo h1 room).skip l3A l3B
  rw [eA1] at S1 ⊢
  obtain ⟨hl1, _, _⟩ := called_regs sA (UInt16.ofNat T)
  generalize called sA (UInt16.ofNat T) = s1 at S1 hl1 ⊢
  -- `ld bc,4`
  have S2 := (seg_ord D hhi (Form.ldBCI (.num 4)) (by intro h; cases h) i4A i4B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ (val_num 4)) (by simp) (by simp) S1
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)).skip l5A l5B
  have e2 : ∀ n4 : UInt16, n4 = Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩ →
      mstep D (s1, w) = (ldRP s1 0 n4, w) := by
    intro n4 hn
    exact mstep_exec D i4A S1.LA S1.atA w (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.bc, .imm (.num 4)]⟩ s1 inp = _
      rw [exec_ld_rp _ .bc 0 rfl (by decide), hn]; rfl) rfl
  have hn4 : (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩).toNat = 4 :=
    immW_toNat _ _ (.num 4) 4 rfl rfl (by decide)
  rw [e2 _ rfl] at S2 ⊢
  obtain ⟨bc2, hl2, _⟩ := ldRP_bc s1 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩)
  generalize ldRP s1 0 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩) = s2 at S2 bc2 hl2 ⊢
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S2
  -- `ld de,rt_acc`
  have S3 := seg_ord D hhi (Form.ldDEI (.sym "rt_acc" 0)) (by intro h; cases h) i6A i6B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ hvacc) (by simp) (by simp) S2
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
  have e3 : mstep D (s2, w) = (ldRP s2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩), w) :=
    mstep_exec D i6A S2.LA S2.atA w (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ s2 inp = _
      rw [exec_ld_rp _ .de 1 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccA pa) (by omega), immW_toNat _ _ _ acc rfl (haccA 0) (by omega)]) rfl
  have hacc3 : (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩).toNat = acc :=
    immW_toNat _ _ _ acc rfl (haccA 0) (by omega)
  rw [e3] at S3 ⊢
  obtain ⟨de3, hl3, bc3⟩ := ldRP_de s2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  generalize ldRP s2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩) = s3 at S3 de3 hl3 bc3 ⊢
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S3
  -- `ldir`, four rounds
  have S7 := ldir_eq_rounds D hhi i7A i7B 3 _ _ S3 (by simp only; rw [bc3, bc2, hn4])
    (by simp only; rw [hl3, hl2, hl1]; exact foot.1) (by simp only; rw [hl3, hl2, hl1]; omega)
    (by simp only; rw [de3, hacc3]; exact hacc.1) (by simp only; rw [de3, hacc3]; omega)
  -- `ret`
  have S8 := seg_ret D (cc := none) (fun _ h => by cases h) i8A i8B S7
  simp only [taken, if_true] at S8
  exact S8

/-- info: 'Ember.Proof.PassSim.blk_ld32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blk_ld32

/-! ## `rt_st32` -/

theorem mrun_9 (D : Dev) (x : Cpu × D.W) :
    mrun D 9 x = mstep D (mrun D 4 (mstep D (mstep D (mstep D (mstep D x))))) := by
  show mrun D (4 + (4 + 1)) x = _
  rw [mrun_add, mrun_add]; rfl

/-- The state after `ex de,hl`. -/
def exDH' (s : Cpu) : Cpu :=
  ({ op1 s with d := (op1 s).h, e := (op1 s).l, h := (op1 s).d, l := (op1 s).e } : Cpu).tick 4

theorem exDH'_regs (s : Cpu) : (exDH' s).de = s.hl ∧ (exDH' s).hl = s.de ∧ (exDH' s).bc = s.bc := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

set_option maxHeartbeats 2000000 in
/-- **`call rt_st32` in both machines, the four bytes at `HL` in the RAM kept equal**: the accumulator's
first four bytes written there; nine steps of each. -/
theorem blk_st32 (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc : Nat}
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym "rt_st32" 0)]⟩))
    (hB : B.items[kB]? = some (.ins ⟨.call, [.imm (.sym "rt_st32" 0)]⟩))
    (hLA : Has A r stItems) (hLB : Has B q stItems)
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB false false x y)
    (room : hi + 2 ≤ top x.1.sp) (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    Sync D A B lo hi G (kA + 1) (kB + 1) false false (mrun D 9 x) (mrun D 9 y) := by
  have l3A : A.items[r + 3]? = some (.label "rt_st32") := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label "rt_st32") := hLB.get 3 rfl
  have i4A : A.items[r + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLA.get 4 rfl
  have i4B : B.items[q + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLB.get 4 rfl
  have l5A : A.items[r + 5]? = some (.label "rt_stw") := hLA.get 5 rfl
  have l5B : B.items[q + 5]? = some (.label "rt_stw") := hLB.get 5 rfl
  have i6A : A.items[r + 6]? = some (.ins Form.exDEHL.instr) := hLA.get 6 rfl
  have i6B : B.items[q + 6]? = some (.ins Form.exDEHL.instr) := hLB.get 6 rfl
  have i7A : A.items[r + 7]? = some (.ins (Form.ldHLI (.sym "rt_acc" 0)).instr) := hLA.get 7 rfl
  have i7B : B.items[q + 7]? = some (.ins (Form.ldHLI (.sym "rt_acc" 0)).instr) := hLB.get 7 rfl
  have i8A : A.items[r + 8]? = some (.ins ⟨.ldir, []⟩) := hLA.get 8 rfl
  have i8B : B.items[q + 8]? = some (.ins ⟨.ldir, []⟩) := hLB.get 8 rfl
  have i9A : A.items[r + 9]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLA.get 9 rfl
  have i9B : B.items[q + 9]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLB.get 9 rfl
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  obtain ⟨sA, w⟩ := x
  simp only at room foot
  rw [mrun_9, mrun_9]
  -- the call
  obtain ⟨T, adA, _, _, _, _, eA1, _⟩ := call_mstep D hA l3A S.LA S.atA w
  have S1 := (seg_call D hhi hA l3A hB l3B S hlo h1 room).skip l3A l3B
  rw [eA1] at S1 ⊢
  obtain ⟨hl1, _, _⟩ := called_regs sA (UInt16.ofNat T)
  generalize called sA (UInt16.ofNat T) = s1 at S1 hl1 ⊢
  -- `ld bc,4`
  have S2 := (seg_ord D hhi (Form.ldBCI (.num 4)) (by intro h; cases h) i4A i4B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ (val_num 4)) (by simp) (by simp) S1
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)).skip l5A l5B
  have e2 : mstep D (s1, w) = (ldRP s1 0 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩), w) :=
    mstep_exec D i4A S1.LA S1.atA w (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.bc, .imm (.num 4)]⟩ s1 inp = _
      rw [exec_ld_rp _ .bc 0 rfl (by decide)]; rfl) rfl
  have hn4 : (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩).toNat = 4 :=
    immW_toNat _ _ (.num 4) 4 rfl rfl (by decide)
  rw [e2] at S2 ⊢
  obtain ⟨bc2, hl2, _⟩ := ldRP_bc s1 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩)
  generalize ldRP s1 0 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩) = s2 at S2 bc2 hl2 ⊢
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S2
  -- `ex de,hl`
  have S3 := seg_ord D hhi Form.exDEHL (by intro h; cases h) i6A i6B (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S2
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
  have e3 : mstep D (s2, w) = (exDH' s2, w) := mstep_exec D i6A S2.LA S2.atA w (fun _ _ => rfl) rfl
  rw [e3] at S3 ⊢
  obtain ⟨de3, hl3', bc3⟩ := exDH'_regs s2
  generalize exDH' s2 = s3 at S3 de3 hl3' bc3 ⊢
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S3
  -- `ld hl,rt_acc`
  have S4 := seg_ord D hhi (Form.ldHLI (.sym "rt_acc" 0)) (by intro h; cases h) i7A i7B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ hvacc) (by simp) (by simp) S3
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
  have e4 : mstep D (s3, w) = (ldRP s3 2 (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩), w) :=
    mstep_exec D i7A S3.LA S3.atA w (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩ s3 inp = _
      rw [exec_ld_rp _ .hl 2 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccA pa) (by omega), immW_toNat _ _ _ acc rfl (haccA 0) (by omega)]) rfl
  have hacc4 : (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩).toNat = acc :=
    immW_toNat _ _ _ acc rfl (haccA 0) (by omega)
  rw [e4] at S4 ⊢
  have hl4 : (ldRP s3 2 (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩)).hl =
      Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩ := by
    simp only [ldRP, Cpu.setRp, Cpu.idxSet, Cpu.setHL, Cpu.hl, Cpu.tick, skip, op1, Cpu.bumpR,
      Ember.Proof.Z80Gen.mk16_hi_lo]
  have de4 : (ldRP s3 2 (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩)).de = s3.de := rfl
  have bc4 : (ldRP s3 2 (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩)).bc = s3.bc := rfl
  generalize ldRP s3 2 (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym "rt_acc" 0)]⟩) = s4 at S4 hl4 de4 bc4 ⊢
  simp only [Form.writesH, Form.writesL, Bool.false_and, Bool.not_true, Bool.and_false] at S4
  -- `ldir`, four rounds: from the accumulator to the bytes at the old `HL`
  have S8 := ldir_eq_rounds D hhi i8A i8B 3 _ _ S4 (by simp only; rw [bc4, bc3, bc2, hn4])
    (by simp only; rw [hl4, hacc4]; exact hacc.1) (by simp only; rw [hl4, hacc4]; omega)
    (by simp only; rw [de4, de3, hl2, hl1]; exact foot.1) (by simp only; rw [de4, de3, hl2, hl1]; omega)
  -- `ret`
  have S9 := seg_ret D (cc := none) (fun _ h => by cases h) i9A i9B S8
  simp only [taken, if_true] at S9
  exact S9

/-- info: 'Ember.Proof.PassSim.blk_st32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blk_st32

end Ember.Proof.PassSim
