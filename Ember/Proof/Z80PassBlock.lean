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

theorem toNat_sub1_8 (v : UInt8) (h : 1 ≤ v.toNat) : (v - 1).toNat = v.toNat - 1 := by
  rw [UInt8.toNat_sub_of_le]; · rfl
  rw [UInt8.le_iff_toNat_le]; exact h

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
  simp only [Form.writesH, Form.writesL, Bool.not_true, Bool.and_false] at S4
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

/-! ## The loop over four bytes (`rt_add32`, `rt_sub32`, `rt_or32`) -/

/-- The states after `ld a,(de)`, `ld (de),a`, `inc de`. -/
def ldADES (s : Cpu) : Cpu := ({ op1 s with a := (op1 s).rd (op1 s).de } : Cpu).tick 7
def stDEAS (s : Cpu) : Cpu := ((op1 s).wr (op1 s).de (op1 s).a).tick 7
def incDES (s : Cpu) : Cpu := ((op1 s).setRp .hl 1 ((op1 s).rp .hl 1 + 1)).tick 6

theorem ldADES_regs (s : Cpu) : (ldADES s).hl = s.hl ∧ (ldADES s).de = s.de ∧ (ldADES s).b = s.b := ⟨rfl, rfl, rfl⟩
theorem stDEAS_regs (s : Cpu) : (stDEAS s).hl = s.hl ∧ (stDEAS s).de = s.de ∧ (stDEAS s).b = s.b := by
  simp only [stDEAS, Cpu.wr, Cpu.tick]; refine ⟨?_, ?_, ?_⟩ <;> (split <;> rfl)
theorem aluMS_regs (k : UInt8) (s : Cpu) : (aluMS k s).hl = s.hl ∧ (aluMS k s).de = s.de ∧ (aluMS k s).b = s.b := by
  rw [aluMS_eq]; exact ⟨rfl, rfl, rfl⟩
theorem incHLS_regs (s : Cpu) : (incHLS s).hl = s.hl + 1 ∧ (incHLS s).de = s.de ∧ (incHLS s).b = s.b := by
  rw [incHLS_eq]
  refine ⟨?_, rfl, rfl⟩
  simp only [Cpu.hl, Ember.Proof.Z80Gen.mk16_hi_lo]
theorem incDES_regs (s : Cpu) : (incDES s).hl = s.hl ∧ (incDES s).de = s.de + 1 ∧ (incDES s).b = s.b := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [incDES, Cpu.setRp, Cpu.setDE, Cpu.rp, Cpu.de, Cpu.tick, op1, Cpu.bumpR, Ember.Proof.Z80Gen.mk16_hi_lo]
theorem djnzed_regs (s : Cpu) (p : UInt16) (c : UInt64) :
    (djnzed s p c).hl = s.hl ∧ (djnzed s p c).de = s.de ∧ (djnzed s p c).b = s.b - 1 := ⟨rfl, rfl, rfl⟩

theorem exec_ld_a_de (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env Form.ldADE.instr s inp = some (ldADES s) := rfl
theorem exec_ld_de_a (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env Form.stDEA.instr s inp = some (stDEAS s) := rfl
theorem exec_inc_hl (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env Form.incHL.instr s inp = some (incHLS s) := rfl
theorem exec_inc_de (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env Form.incDE.instr s inp = some (incDES s) := rfl


theorem mrun_6 (D : Dev) (x : Cpu × D.W) :
    mrun D 6 x = mstep D (mstep D (mstep D (mstep D (mstep D (mstep D x))))) := rfl

/-- **The loop over the bytes, all its rounds, within the RAM kept equal**, in both machines (`k`:
the operation's code; `B` the count, the bytes at `HL` and `DE` in that RAM). -/
theorem loop_eq_rounds (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {j m : Nat} {l : String} {i : Instr} (k : UInt8) (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s))
    (hfi : i.falls = true) (hLA : Has A j (loopItems l i)) (hLB : Has B m (loopItems l i)) :
    ∀ (n : Nat) (x y : Cpu × D.W), Sync D A B lo hi G (j + 1) (m + 1) false false x y → x.1.b.toNat = n + 1 →
      lo ≤ x.1.hl.toNat → x.1.hl.toNat + n + 1 ≤ hi → lo ≤ x.1.de.toNat → x.1.de.toNat + n + 1 ≤ hi →
      Sync D A B lo hi G (j + 7) (m + 7) false false (mrun D (6 * (n + 1)) x) (mrun D (6 * (n + 1)) y)
  | n, (s, w), y, S, hb, h1, h2, d1, d2 => by
    have l0A : A.items[j]? = some (.label l) := hLA.get 0 rfl
    have l0B : B.items[m]? = some (.label l) := hLB.get 0 rfl
    have i1A : A.items[j + 1]? = some (.ins Form.ldADE.instr) := hLA.get 1 rfl
    have i1B : B.items[m + 1]? = some (.ins Form.ldADE.instr) := hLB.get 1 rfl
    have i2A : A.items[j + 2]? = some (.ins i) := hLA.get 2 rfl
    have i2B : B.items[m + 2]? = some (.ins i) := hLB.get 2 rfl
    have i3A : A.items[j + 3]? = some (.ins Form.stDEA.instr) := hLA.get 3 rfl
    have i3B : B.items[m + 3]? = some (.ins Form.stDEA.instr) := hLB.get 3 rfl
    have i4A : A.items[j + 4]? = some (.ins Form.incHL.instr) := hLA.get 4 rfl
    have i4B : B.items[m + 4]? = some (.ins Form.incHL.instr) := hLB.get 4 rfl
    have i5A : A.items[j + 5]? = some (.ins Form.incDE.instr) := hLA.get 5 rfl
    have i5B : B.items[m + 5]? = some (.ins Form.incDE.instr) := hLB.get 5 rfl
    have i6A : A.items[j + 6]? = some (.ins ⟨.djnz, [.imm (.sym l 0)]⟩) := hLA.get 6 rfl
    have i6B : B.items[m + 6]? = some (.ins ⟨.djnz, [.imm (.sym l 0)]⟩) := hLB.get 6 rfl
    simp only at hb h1 h2 d1 d2
    rw [show 6 * (n + 1) = 6 + 6 * n by omega, mrun_add, mrun_add, mrun_6, mrun_6]
    -- `ld a,(de)`
    have S1 := seg_ord D hhi Form.ldADE (by intro h; cases h) i1A i1B (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S
      (by simp [Form.viaHL]) (fun _ => by simp only; exact ⟨d1, by omega⟩) (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i1A S.LA S.atA w (fun _ _ => exec_ld_a_de _ _ _) rfl] at S1 ⊢
    obtain ⟨a1, b1, c1⟩ := ldADES_regs s
    generalize ldADES s = s1 at S1 a1 b1 c1 ⊢
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S1
    -- the operation on `A` with the byte at `(HL)`
    have E1 := eqv_ff S1.E
    have hhl1 : s1.hl = (mstep D y).1.hl := RegsS.hl E1.regs
    have S2 := seg_aluM D hhi k hexec hfi i2A i2B S1 (by
      simp only; rw [← hhl1]; exact E1.mem _ (by rw [a1]; exact h1) (by rw [a1]; omega))
    rw [mstep_exec D i2A S1.LA S1.atA w (fun _ _ => hexec _ _ _) (by rw [aluMS_eq]; rfl)] at S2 ⊢
    obtain ⟨a2, b2, c2⟩ := aluMS_regs k s1
    generalize aluMS k s1 = s2 at S2 a2 b2 c2 ⊢
    -- `ld (de),a`
    have S3 := seg_ord D hhi Form.stDEA (by intro h; cases h) i3A i3B (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S2
      (by simp [Form.viaHL]) (fun _ => ⟨by rw [b2, b1]; exact d1, by rw [b2, b1]; omega⟩)
      (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i3A S2.LA S2.atA w (fun _ _ => exec_ld_de_a _ _ _) (by simp only [stDEAS, Cpu.wr, Cpu.tick]; split <;> rfl)] at S3 ⊢
    obtain ⟨a3, b3, c3⟩ := stDEAS_regs s2
    generalize stDEAS s2 = s3 at S3 a3 b3 c3 ⊢
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S3
    -- `inc hl`
    have S4 := seg_ord D hhi Form.incHL (by intro h; cases h) i4A i4B (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S3
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i4A S3.LA S3.atA w (fun _ _ => exec_inc_hl _ _ _) (by rw [incHLS_eq]; rfl)] at S4 ⊢
    obtain ⟨a4, b4, c4⟩ := incHLS_regs s3
    generalize incHLS s3 = s4 at S4 a4 b4 c4 ⊢
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S4
    -- `inc de`
    have S5 := seg_ord D hhi Form.incDE (by intro h; cases h) i5A i5B (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S4
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i5A S4.LA S4.atA w (fun _ _ => exec_inc_de _ _ _) rfl] at S5 ⊢
    obtain ⟨a5, b5, c5⟩ := incDES_regs s4
    generalize incDES s4 = s5 at S5 a5 b5 c5 ⊢
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S5
    -- `djnz`
    have S6 := seg_djnz D i6A l0A i6B l0B S5
    obtain ⟨p6, c6, e6, _, _⟩ := djnz_mstep D i6A l0A S5.LA S5.atA w
    have hb5 : s5.b.toNat = n + 1 := by rw [c5, c4, c3, c2, c1]; exact hb
    obtain ⟨d6h, d6d, d6b⟩ := djnzed_regs s5 p6 c6
    cases n with
    | zero =>
      have h0 : s5.b - 1 = 0 := by apply UInt8.toNat_inj.mp; rw [toNat_sub1_8 _ (by omega)]; simp [hb5]
      have hne : ¬ ((s5.b - 1 != 0) = true) := by rw [h0]; decide
      rw [if_neg hne] at S6
      simpa only [Nat.mul_zero, mrun] using S6
    | succ n' =>
      have hne : (s5.b - 1 != 0) = true := by
        have h' : (s5.b - 1).toNat = n' + 1 := by rw [toNat_sub1_8 _ (by omega)]; omega
        have : s5.b - 1 ≠ 0 := by intro e; rw [e] at h'; simp at h'
        simp [this]
      rw [if_pos hne] at S6
      have S6' := S6.skip l0A l0B
      rw [e6] at S6' ⊢
      exact loop_eq_rounds D hhi k hexec hfi hLA hLB n' _ _ S6'
        (by simp only; rw [d6b, toNat_sub1_8 _ (by omega)]; omega)
        (by simp only; rw [d6h, a5, a4, toNat_add1 _ (by rw [a3, a2, a1]; omega), a3, a2, a1]; omega)
        (by simp only; rw [d6h, a5, a4, toNat_add1 _ (by rw [a3, a2, a1]; omega), a3, a2, a1]; omega)
        (by simp only; rw [d6d, b5, toNat_add1 _ (by rw [b4, b3, b2, b1]; omega), b4, b3, b2, b1]; omega)
        (by simp only; rw [d6d, b5, toNat_add1 _ (by rw [b4, b3, b2, b1]; omega), b4, b3, b2, b1]; omega)

/-- info: 'Ember.Proof.PassSim.loop_eq_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_eq_rounds

/-! ## `rt_add32`, `rt_sub32`, `rt_or32` -/

/-- The state after `ld r,n` (`r` of `B C D E H L A`). -/
def ldRN (s : Cpu) (y : UInt8) (n : UInt8) : Cpu := ((skip (op1 s) 1).setReg .hl y n).tick 7

theorem exec_ld_b_n (env : Env) (v : Val) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.ld, [.b, .imm v]⟩ s inp = some (ldRN s 0 (Instr.immB env ⟨.ld, [.b, .imm v]⟩)) := rfl

theorem ldRN_b (s : Cpu) (n : UInt8) : (ldRN s 0 n).b = n ∧ (ldRN s 0 n).hl = s.hl ∧ (ldRN s 0 n).de = s.de := by
  refine ⟨rfl, rfl, rfl⟩

/-- The state after `or a`. -/
def orAS (s : Cpu) : Cpu := ((op1 s).alu 6 ((op1 s).reg .hl 7)).tick 4

theorem orAS_regs (s : Cpu) : (orAS s).hl = s.hl ∧ (orAS s).de = s.de ∧ (orAS s).b = s.b := by
  simp only [orAS, alu_struct]; exact ⟨rfl, rfl, rfl⟩

theorem Has.right {C : Code} {r : Nat} {l1 l2 : List Item} (h : Has C r (l1 ++ l2)) : Has C (r + l1.length) l2 := by
  intro j it hj
  have := h (l1.length + j) it (by rw [List.getElem?_append_right (by omega)]; simpa using hj)
  rw [← Nat.add_assoc] at this; exact this

theorem Has.left {C : Code} {r : Nat} {l1 l2 : List Item} (h : Has C r (l1 ++ l2)) : Has C r l1 := by
  intro j it hj
  have hlt : j < l1.length := by
    rcases Nat.lt_or_ge j l1.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  exact h j it (by rw [List.getElem?_append_left hlt]; exact hj)

theorem mrun_25 (D : Dev) (x : Cpu × D.W) : mrun D 25 x = mstep D (mrun D (6 * (3 + 1)) x) := by
  show mrun D (24 + 1) x = _; rw [mrun_add]; rfl

/-- The loop of four rounds and the `ret` after it, in both machines (the frame of the call on top). -/
theorem loop_ret (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {L M rA rB e : Nat} {l : String} {i : Instr} (k : UInt8)
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hLA : Has A L (loopItems l i ++ [.ins ⟨.ret, []⟩])) (hLB : Has B M (loopItems l i ++ [.ins ⟨.ret, []⟩]))
    {x y : Cpu × D.W} (S : Sync D A B lo hi (.ret rA rB e :: G) (L + 1) (M + 1) false false x y)
    (hb : x.1.b.toNat = 4) (h1 : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi)
    (d1 : lo ≤ x.1.de.toNat ∧ x.1.de.toNat + 4 ≤ hi) :
    Sync D A B lo hi G rA rB false false (mrun D 25 x) (mrun D 25 y) := by
  have S7 := loop_eq_rounds D hhi k hexec hfi hLA.left hLB.left 3 x y S hb h1.1 (by omega) d1.1 (by omega)
  have iA : A.items[L + 7]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := by
    have := hLA.right; exact this.get 0 rfl
  have iB : B.items[M + 7]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := by
    have := hLB.right; exact this.get 0 rfl
  have S8 := seg_ret D (cc := none) (fun _ h => by cases h) iA iB S7
  simp only [taken, if_true] at S8
  rw [mrun_25, mrun_25]; exact S8

/-- The beginning of `rt_add32`, `rt_sub32`, `rt_or32`: the call, `ld b,4`, `ld de,rt_acc`; the relation at
the item after (`r + 7`), `B` four, `DE` the accumulator, `HL` as at the call. -/
theorem bytes_head (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc : Nat} {name : String} {rest : List Item}
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hB : B.items[kB]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hLA : Has A r ([.label s!"rt_{name}64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym s!"rt_{name}w")]⟩,
      .label s!"rt_{name}32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
      .label s!"rt_{name}w", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++ rest))
    (hLB : Has B q ([.label s!"rt_{name}64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym s!"rt_{name}w")]⟩,
      .label s!"rt_{name}32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
      .label s!"rt_{name}w", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++ rest))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB false false x y) (room : hi + 2 ≤ top x.1.sp) :
    Sync D A B lo hi (.ret (kA + 1) (kB + 1) (r + 3) :: G) (r + 7) (q + 7) false false (mrun D 3 x) (mrun D 3 y) ∧
      (mrun D 3 x).1.b.toNat = 4 ∧ (mrun D 3 x).1.hl = x.1.hl ∧ (mrun D 3 x).1.de.toNat = acc := by
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
  obtain ⟨sA, w⟩ := x
  simp only at room
  show Sync D A B lo hi _ (r + 7) (q + 7) false false (mstep D (mstep D (mstep D (sA, w)))) (mstep D (mstep D (mstep D y))) ∧
    (mstep D (mstep D (mstep D (sA, w)))).1.b.toNat = 4 ∧ (mstep D (mstep D (mstep D (sA, w)))).1.hl = sA.hl ∧
    (mstep D (mstep D (mstep D (sA, w)))).1.de.toNat = acc
  obtain ⟨T, adA, _, _, _, _, eA1, _⟩ := call_mstep D hA l3A S.LA S.atA w
  have S1 := (seg_call D hhi hA l3A hB l3B S hlo h1 room).skip l3A l3B
  rw [eA1] at S1 ⊢
  obtain ⟨hl1, _, _⟩ := called_regs sA (UInt16.ofNat T)
  generalize called sA (UInt16.ofNat T) = s1 at S1 hl1 ⊢
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
  have hb3 : (ldRP s2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)).b = s2.b := rfl
  simp only [Form.writesH, Form.writesL, Bool.false_and] at S3
  refine ⟨S3, by simp only; rw [hb3]; exact hb2, by simp only; rw [hl3, hl2, hl1], by simp only; rw [de3, hacc3]⟩

theorem bytewise_split (name : String) (pre : List Item) (i : Instr) :
    bytewiseItems name pre i =
      [.label s!"rt_{name}64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym s!"rt_{name}w")]⟩,
        .label s!"rt_{name}32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
        .label s!"rt_{name}w", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++
      (pre ++ (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩])) := by
  simp only [bytewiseItems, List.append_assoc]

/-- **`call rt_add32`, `rt_sub32`, `rt_or32` in both machines, the four bytes at `HL` in the RAM kept
equal**: the routine's items in each image (`bytewiseItems`, with `or a` before the loop or nothing),
the accumulator in that RAM, room for the return address: the relation kept at the items after the
calls. -/
theorem blk_bytes (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc : Nat} {name : String} {pre : List Item} {i : Instr} (k : UInt8)
    (hpre : pre = [] ∨ pre = [.ins Form.orA.instr])
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hB : B.items[kB]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hLA : Has A r (bytewiseItems name pre i)) (hLB : Has B q (bytewiseItems name pre i))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB false false x y)
    (room : hi + 2 ≤ top x.1.sp) (foot : lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat + 4 ≤ hi) :
    Sync D A B lo hi G (kA + 1) (kB + 1) false false (mrun D (28 + pre.length) x) (mrun D (28 + pre.length) y) := by
  rw [bytewise_split] at hLA hLB
  obtain ⟨S3, hb3, hl3, de3⟩ := bytes_head D hhi hlo h1 hA hB hLA hLB haccA haccB hacc.2 S room
  have tA := hLA.right
  have tB := hLB.right
  simp only [List.length_cons, List.length_nil] at tA tB
  rcases hpre with rfl | rfl
  · have lA : A.items[r + 7]? = some (.label s!"rt_{name}w_l") := tA.get 0 rfl
    have lB : B.items[q + 7]? = some (.label s!"rt_{name}w_l") := tB.get 0 rfl
    have R := loop_ret D hhi k hexec hfi (L := r + 7) (M := q + 7) (by simpa using tA) (by simpa using tB)
      (S3.skip lA lB) hb3 (by rw [hl3]; exact ⟨foot.1, foot.2⟩) (by rw [de3]; exact ⟨hacc.1, hacc.2⟩)
    rw [show 28 + ([] : List Item).length = 3 + 25 from rfl, mrun_add, mrun_add]
    exact R
  · have iA : A.items[r + 7]? = some (.ins Form.orA.instr) := tA.get 0 rfl
    have iB : B.items[q + 7]? = some (.ins Form.orA.instr) := tB.get 0 rfl
    have S4 := seg_ord D hhi Form.orA (by intro h; cases h) iA iB (fun _ _ => ⟨rfl, rfl⟩) (by simp) (by simp) S3
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    simp only [Form.writesH, Form.writesL, Bool.false_and] at S4
    have lA : A.items[r + 7 + 1]? = some (.label s!"rt_{name}w_l") := tA.get 1 rfl
    have lB : B.items[q + 7 + 1]? = some (.label s!"rt_{name}w_l") := tB.get 1 rfl
    have e4 : mstep D (mrun D 3 x) = (orAS (mrun D 3 x).1, (mrun D 3 x).2) :=
      mstep_exec D iA S3.LA S3.atA _ (fun _ _ => rfl) rfl
    obtain ⟨hl4, de4, b4⟩ := orAS_regs (mrun D 3 x).1
    have tA' : Has A (r + 7 + 1) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by
      have := tA.right; simpa using this
    have tB' : Has B (q + 7 + 1) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by
      have := tB.right; simpa using this
    have R := loop_ret D hhi k hexec hfi tA' tB' (S4.skip lA lB)
      (by rw [e4]; simp only; rw [b4]; exact hb3)
      (by rw [e4]; simp only; rw [hl4, hl3]; exact ⟨foot.1, foot.2⟩)
      (by rw [e4]; simp only; rw [de4, de3]; exact ⟨hacc.1, hacc.2⟩)
    rw [show 28 + [Item.ins Form.orA.instr].length = 3 + (1 + 25) from rfl, mrun_add, mrun_add, mrun_add, mrun_add]
    exact R

/-- info: 'Ember.Proof.PassSim.blk_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blk_bytes

end Ember.Proof.PassSim
