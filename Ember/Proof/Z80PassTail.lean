import Ember.Proof.Z80PassRet
import Ember.Proof.Z80PassBlock

/-!
# Ember.Proof.Z80PassTail — a routine of the runtime called in `A`, jumped to in `B` (plan M7.3)

`call rt_st32` (or `rt_or32`) before a return in `A` is `jp rt_st32` in
`B`.  The routine's body runs in both machines with any frames on the
stacks (`body_st32`, `body_bytes`: from its label to its `ret`); the
call that is a jump (`seg_tail`) before it and the returns after it
(`seg_retseq`: `A` through its own frame, then both through the frame
of the caller) make the segment (`blkT_st32`, `blkT_bytes`).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

theorem mrun_7 (D : Dev) (x : Cpu × D.W) :
    mrun D 7 x = mrun D 4 (mstep D (mstep D (mstep D x))) := by
  show mrun D (3 + 4) x = _
  rw [mrun_add]; rfl

set_option maxHeartbeats 2000000 in
/-- **The body of `rt_st32` in both machines** (from its label to its `ret`), any frames on the stacks:
the four bytes at `HL` in the RAM kept equal get the accumulator's first four; seven steps of each. -/
theorem body_st32 (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {r q acc : Nat}
    (hLA : Has A r stItems) (hLB : Has B q stItems)
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G (r + 3) (q + 3) false false x y)
    (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    Sync D A B lo hi G (r + 9) (q + 9) false false (mrun D 7 x) (mrun D 7 y) := by
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
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  have S1 := S.skip l3A l3B
  obtain ⟨s1, w⟩ := x
  simp only at foot
  rw [mrun_7, mrun_7]
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
  simp only [Form.writesH, Form.writesL, Bool.not_true, Bool.and_false] at S4
  -- `ldir`, four rounds: from the accumulator to the bytes at the old `HL`
  exact ldir_eq_rounds D hhi i8A i8B 3 _ _ S4 (by simp only; rw [bc4, bc3, bc2, hn4])
    (by simp only; rw [hl4, hacc4]; exact hacc.1) (by simp only; rw [hl4, hacc4]; omega)
    (by simp only; rw [de4, de3, hl2]; exact foot.1) (by simp only; rw [de4, de3, hl2]; omega)

/-- info: 'Ember.Proof.PassSim.body_st32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body_st32

/-- **`call rt_st32` before a return in `A`, `jp rt_st32` in `B`**: the call that is a jump, the body,
the returns; the relation at the return points of the frame of both on top of `A`'s own frames, that
frame popped. -/
theorem blkT_st32 (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc rA rB e : Nat} {ts : List (Nat × Nat)}
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym "rt_st32" 0)]⟩)) (hR : RetSeq A (kA + 1))
    (hB : B.items[kB]? = some (.ins ⟨.jp, [.imm (.sym "rt_st32" 0)]⟩))
    (hLA : Has A r stItems) (hLB : Has B q stItems)
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi) (hts : ∀ p, p ∈ ts → RetSeq A p.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) kA kB false false x y)
    (room : hi + 2 ≤ top x.1.sp) (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    ∃ n, 0 < n ∧ Sync D A B lo hi G rA rB false false (mrun D n x) (mrun D 9 y) := by
  have l3A : A.items[r + 3]? = some (.label "rt_st32") := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label "rt_st32") := hLB.get 3 rfl
  have i9A : A.items[r + 9]? = some (.ins ⟨.ret, []⟩) := hLA.get 9 rfl
  have i9B : B.items[q + 9]? = some (.ins ⟨.ret, []⟩) := hLB.get 9 rfl
  have S0 := seg_tail D hhi (Or.inl rfl) hA l3A hB l3B S hlo h1 room
  have hl0 : (mstep D x).1.hl = x.1.hl := by
    obtain ⟨sA, w⟩ := x
    obtain ⟨T, _, _, _, _, _, eA, _⟩ := call_mstep D hA l3A S.LA S.atA w
    rw [eA]; exact (called_regs sA _).1
  have S7 := body_st32 D hhi (G := tails ((kA + 1, r + 3) :: ts) ++ .ret rA rB e :: G) hLA hLB haccA haccB hacc
    S0 (by rw [hl0]; exact foot)
  obtain ⟨n, _, S9⟩ := seg_retseq D (ts := (kA + 1, r + 3) :: ts) ⟨r + 9, ⟨Nat.le_refl _, fun _ h1 h2 => by omega⟩,
    Or.inl i9A⟩ i9B (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hR
      · exact hts p hp) S7
  refine ⟨1 + (7 + n), by omega, ?_⟩
  rw [mrun_add, mrun_add, show 9 = 1 + (7 + 1) from rfl, mrun_add D 1, mrun_add D 7]
  exact S9

/-- info: 'Ember.Proof.PassSim.blkT_st32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkT_st32


set_option maxHeartbeats 2000000 in
/-- **The body of `rt_add32`, `rt_sub32`, `rt_or32` in both machines** (from the label `rt_…32` to the
`ret`), any frames on the stacks: the four bytes at `HL` in the RAM kept equal with the accumulator. -/
theorem body_bytes (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {r q acc : Nat}
    {name : String} {pre : List Item} {i : Instr} (k : UInt8)
    (hpre : pre = [] ∨ pre = [.ins Form.orA.instr])
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hLA : Has A r (bytewiseItems name pre i)) (hLB : Has B q (bytewiseItems name pre i))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G (r + 3) (q + 3) false false x y)
    (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    Sync D A B lo hi G (r + 14 + pre.length) (q + 14 + pre.length) false false
      (mrun D (26 + pre.length) x) (mrun D (26 + pre.length) y) := by
  rw [bytewise_split] at hLA hLB
  have l3A : A.items[r + 3]? = some (.label s!"rt_{name}32") := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label s!"rt_{name}32") := hLB.get 3 rfl
  have i4A : A.items[r + 4]? = some (.ins (Form.ldBI (.num 4)).instr) := hLA.get 4 rfl
  have i4B : B.items[q + 4]? = some (.ins (Form.ldBI (.num 4)).instr) := hLB.get 4 rfl
  have l5A : A.items[r + 5]? = some (.label s!"rt_{name}w") := hLA.get 5 rfl
  have l5B : B.items[q + 5]? = some (.label s!"rt_{name}w") := hLB.get 5 rfl
  have i6A : A.items[r + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLA.get 6 rfl
  have i6B : B.items[q + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLB.get 6 rfl
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  have S1 := S.skip l3A l3B
  have tA := hLA.right
  have tB := hLB.right
  simp only [List.length_cons, List.length_nil] at tA tB
  obtain ⟨s1, w⟩ := x
  simp only at foot
  rw [show 26 + pre.length = 2 + (pre.length + 24) by omega, mrun_add D 2 _ (s1, w), mrun_add D 2 _ y]
  show Sync D A B lo hi G _ _ false false (mrun D (pre.length + 24) (mstep D (mstep D (s1, w))))
    (mrun D (pre.length + 24) (mstep D (mstep D y)))
  -- `ld b,4`
  have S2 := (seg_ord D hhi (Form.ldBI (.num 4)) (by intro h; cases h) i4A i4B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ (val_num 4)) (by simp) (by simp) S1
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)).skip l5A l5B
  rw [mstep_exec D i4A S1.LA S1.atA w (s' := ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩))
      (fun pa inp => by
        show exec (A.a.env pa) ⟨.ld, [.b, .imm (.num 4)]⟩ s1 inp = _
        rw [exec_ld_b_n]; rfl) rfl] at S2 ⊢
  have hb2 : (ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩)).b.toNat = 4 := rfl
  obtain ⟨_, hl2, _⟩ := ldRN_b s1 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩)
  generalize ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩) = s2 at S2 hb2 hl2 ⊢
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
  obtain ⟨de3, hl3, _⟩ := ldRP_de s2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  have hb3 := ldRP_b1 s2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S3
  generalize Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ = nacc at S3 de3 hl3 hb3 hacc3 ⊢
  generalize ldRP s2 1 nacc = s3 at S3 de3 hl3 hb3 ⊢
  generalize mstep D (mstep D y) = y3 at S3 ⊢
  rcases hpre with rfl | rfl
  · have lA : A.items[r + 7]? = some (.label s!"rt_{name}w_l") := tA.get 0 rfl
    have lB : B.items[q + 7]? = some (.label s!"rt_{name}w_l") := tB.get 0 rfl
    have tA0 : Has A (r + 7) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by simpa using tA
    have tB0 : Has B (q + 7) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by simpa using tB
    have hlA := tA0.left
    have hlB := tB0.left
    have R := loop_eq_rounds D hhi k hexec hfi hlA hlB 3 _ _ (S3.skip lA lB)
      (by simp only; rw [hb3, hb2]) (by simp only; rw [hl3, hl2]; exact foot.1)
      (by simp only; rw [hl3, hl2]; omega) (by simp only; rw [de3, hacc3]; exact hacc.1)
      (by simp only; rw [de3, hacc3]; omega)
    simpa using R
  · have iA : A.items[r + 7]? = some (.ins Form.orA.instr) := tA.get 0 rfl
    have iB : B.items[q + 7]? = some (.ins Form.orA.instr) := tB.get 0 rfl
    have S4 := seg_ord D hhi Form.orA (by intro h; cases h) iA iB (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S3
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S4
    have lA : A.items[r + 7 + 1]? = some (.label s!"rt_{name}w_l") := tA.get 1 rfl
    have lB : B.items[q + 7 + 1]? = some (.label s!"rt_{name}w_l") := tB.get 1 rfl
    have e4 : mstep D (s3, w) = (orAS s3, w) := mstep_exec D iA S3.LA S3.atA _ (fun _ _ => rfl) rfl
    obtain ⟨hl4, de4, b4⟩ := orAS_regs s3
    have hlA : Has A (r + 7 + 1) (loopItems s!"rt_{name}w_l" i) := by
      have := tA.right; simpa using this.left
    have hlB : Has B (q + 7 + 1) (loopItems s!"rt_{name}w_l" i) := by
      have := tB.right; simpa using this.left
    rw [e4] at S4
    have R := loop_eq_rounds D hhi k hexec hfi hlA hlB 3 _ _ (S4.skip lA lB)
      (by simp only; rw [b4, hb3, hb2]) (by simp only; rw [hl4, hl3, hl2]; exact foot.1)
      (by simp only; rw [hl4, hl3, hl2]; omega) (by simp only; rw [de4, de3, hacc3]; exact hacc.1)
      (by simp only; rw [de4, de3, hacc3]; omega)
    rw [show [Item.ins Form.orA.instr].length + 24 = 1 + 24 from rfl, mrun_add, mrun_add]
    show Sync D A B lo hi G _ _ false false (mrun D 24 (mstep D (s3, w))) (mrun D 24 (mstep D y3))
    rw [e4]
    simpa using R

/-- info: 'Ember.Proof.PassSim.body_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body_bytes

/-- **`call rt_add32` (`rt_sub32`, `rt_or32`) before a return in `A`, a `jp` to it in `B`**: the call
that is a jump, the body, the returns. -/
theorem blkT_bytes (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc rA rB e : Nat} {ts : List (Nat × Nat)} {name : String} {pre : List Item}
    {i : Instr} (k : UInt8) (hpre : pre = [] ∨ pre = [.ins Form.orA.instr])
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩)) (hR : RetSeq A (kA + 1))
    (hB : B.items[kB]? = some (.ins ⟨.jp, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hLA : Has A r (bytewiseItems name pre i)) (hLB : Has B q (bytewiseItems name pre i))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi) (hts : ∀ p, p ∈ ts → RetSeq A p.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) kA kB false false x y)
    (room : hi + 2 ≤ top x.1.sp) (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    ∃ n, 0 < n ∧ Sync D A B lo hi G rA rB false false (mrun D n x) (mrun D (28 + pre.length) y) := by
  have hLA' := hLA
  have hLB' := hLB
  rw [bytewise_split] at hLA' hLB'
  have l3A : A.items[r + 3]? = some (.label s!"rt_{name}32") := hLA'.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label s!"rt_{name}32") := hLB'.get 3 rfl
  have iRA : A.items[r + 14 + pre.length]? = some (.ins ⟨.ret, []⟩) := by
    have := hLA'.right.right.right; simp at this
    have h := this.get 0 rfl
    simp only [loopItems, List.length_cons, List.length_nil] at h
    rw [show r + 7 + pre.length + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) + 0 = r + 14 + pre.length by omega] at h
    exact h
  have iRB : B.items[q + 14 + pre.length]? = some (.ins ⟨.ret, []⟩) := by
    have := hLB'.right.right.right; simp at this
    have h := this.get 0 rfl
    simp only [loopItems, List.length_cons, List.length_nil] at h
    rw [show q + 7 + pre.length + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) + 0 = q + 14 + pre.length by omega] at h
    exact h
  have S0 := seg_tail D hhi (Or.inl rfl) hA l3A hB l3B S hlo h1 room
  have hl0 : (mstep D x).1.hl = x.1.hl := by
    obtain ⟨sA, w⟩ := x
    obtain ⟨T, _, _, _, _, _, eA, _⟩ := call_mstep D hA l3A S.LA S.atA w
    rw [eA]; exact (called_regs sA _).1
  have SB := body_bytes D hhi (G := tails ((kA + 1, r + 3) :: ts) ++ .ret rA rB e :: G) k hpre hexec hfi
    hLA hLB haccA haccB hacc S0 (by rw [hl0]; exact foot)
  obtain ⟨n, _, S9⟩ := seg_retseq D (ts := (kA + 1, r + 3) :: ts)
    ⟨r + 14 + pre.length, ⟨Nat.le_refl _, fun _ h1 h2 => by omega⟩, Or.inl iRA⟩ iRB (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hR
      · exact hts p hp) SB
  refine ⟨1 + (26 + pre.length + n), by omega, ?_⟩
  rw [mrun_add, mrun_add, show 28 + pre.length = 1 + (26 + pre.length + 1) by omega, mrun_add D 1,
    mrun_add D (26 + pre.length)]
  exact S9

/-- info: 'Ember.Proof.PassSim.blkT_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkT_bytes

end Ember.Proof.PassSim
