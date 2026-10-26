import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80ShrW — `rt_shr32`, from its items (plan M7.3)

The runtime's right shift of the accumulator by `B`: `ld c,4`; nothing
when `B` is zero; else `B` rounds, each with `BC` kept on the stack, of a
loop over the accumulator's bytes from the top down (`dec hl; rr (hl);
djnz`), the carry cleared first.  `rt_shr32_ok`: the routine returns with
the accumulator's four bytes shifted right by `B`, nothing else written
but the free stack.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-! ## The bytes -/

/-- The loop in memory: the `n` bytes from `L`, from the top down, each shifted right with the
carry coming in at its top bit and its low bit the carry out. -/
def shrB : ByteArray → Nat → Nat → Bool → ByteArray
  | m, _, 0, _ => m
  | m, L, n + 1, c =>
    shrB (m.set! (L + n) ((m.get! (L + n) >>> 1) ||| ((if c then (1 : UInt8) else 0) <<< 7))) L n
      (m.get! (L + n) &&& 1 != 0)

/-- The loop writes the `n` bytes from `L` only. -/
theorem shrB_far : ∀ (n : Nat) (m : ByteArray) (L x : Nat) (c : Bool), x < L ∨ L + n ≤ x →
    (shrB m L n c).get! x = m.get! x
  | 0, _, _, _, _, _ => rfl
  | n + 1, m, L, x, c, hx => by
    rw [shrB, shrB_far n _ _ x _ (by omega), getBang_set _ _ _ _ (by omega)]

theorem shrB_size : ∀ (n : Nat) (m : ByteArray) (L : Nat) (c : Bool), (shrB m L n c).size = m.size
  | 0, _, _, _ => rfl
  | n + 1, m, L, c => by rw [shrB, shrB_size n, set_size]

theorem rr_toNat (v : UInt8) (c : Bool) :
    ((v >>> 1) ||| ((if c then (1 : UInt8) else 0) <<< 7)).toNat = v.toNat / 2 + 128 * c.toNat := by
  cases c
  · have h := (rr_byte v).2
    simp only [Bool.false_eq_true, if_false, Bool.toNat_false]
    omega
  · have h := (rr_byte v).1
    simp only [if_true, Bool.toNat_true]
    omega

theorem bit0_toNat (v : UInt8) : (v &&& 1 != 0).toNat = v.toNat % 2 := by
  rw [(srl_byte v).2]
  by_cases h : v.toNat % 2 = 1
  · rw [h]
    rfl
  · have h0 : v.toNat % 2 = 0 := by omega
    rw [h0]
    rfl

/-- The loop halves the `n` bytes at `L`, the carry coming in at the top. -/
theorem shrB_rd : ∀ (n : Nat) (m : ByteArray) (L : Nat) (c : Bool), m.size = 65536 → L + n ≤ 65536 →
    IR.Sem.rd (shrB m L n c) L n = (IR.Sem.rd m L n + 2 ^ (8 * n) * c.toNat) / 2
  | 0, m, L, c, _, _ => by cases c <;> simp [IR.Sem.rd]
  | n + 1, m, L, c, hsz, hL => by
    have hlt : L + n < m.size := by omega
    have r1 : ∀ X : ByteArray, IR.Sem.rd X (L + n) 1 = (X.get! (L + n)).toNat := fun X => by
      show (X.get! ((L + n) % 65536)).toNat + 256 * 0 = _
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [shrB, rd_add m L n 1]
    rw [rd_add _ L n 1, r1, r1, shrB_far n _ L (L + n) _ (Or.inr (Nat.le_refl _)), getBang_same _ _ _ hlt,
      rr_toNat, shrB_rd n _ L _ (by rw [set_size]; exact hsz) (by omega),
      rd_congr m _ L n (by omega) (fun x _ h2 => getBang_set _ _ _ _ (by omega)), bit0_toNat]
    have hp : (2 : Nat) ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      omega
    rw [hp]
    generalize IR.Sem.rd m L n = R
    generalize (2 : Nat) ^ (8 * n) = X
    generalize (m.get! (L + n)).toNat = v
    have e1 : X * v = X * (v % 2) + 2 * (X * (v / 2)) := by
      rw [← Nat.mul_left_comm X 2 (v / 2), ← Nat.mul_add, Nat.mod_add_div]
    have e2 : X * (v / 2 + 128 * c.toNat) = X * (v / 2) + 128 * (X * c.toNat) := by
      rw [Nat.mul_add, Nat.mul_left_comm X 128]
    have e3 : 256 * X * c.toNat = 256 * (X * c.toNat) := Nat.mul_assoc _ _ _
    rw [e1, e2, e3]
    generalize X * (v % 2) = A
    generalize X * (v / 2) = B
    generalize X * c.toNat = C
    omega

/-! ## The inner loop -/

theorem does_dec_hl : Does ⟨.dec, [.hl]⟩ decHL :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, decHL, zsim, and_self], fun s => by simp only [decHL, zsim]⟩

/-- `rr (hl)` as the model runs it. -/
def rrM (s : Cpu) : Cpu :=
  (((op2 s).rot 3 ((op2 s).rd (op2 s).hl)).2.wr (op2 s).hl ((op2 s).rot 3 ((op2 s).rd (op2 s).hl)).1).tick 15

theorem rot3_f (s : Cpu) (v : UInt8) :
    (s.rot 3 v).2.f = szxyp ((v >>> 1) ||| ((if s.flag FC then (1 : UInt8) else 0) <<< 7)) |||
      Cpu.bit (v &&& 1 != 0) FC := rfl
theorem rot3_b (s : Cpu) (v : UInt8) : (s.rot 3 v).2.b = s.b := rfl

/-- The body of the inner loop: `dec hl; rr (hl); djnz`. -/
def shrInner : List Item :=
  [.label "rt_shrw_i", .ins ⟨.dec, [.hl]⟩, .ins ⟨.rr, [.mhl]⟩, .ins ⟨.djnz, [.imm (.sym "rt_shrw_i")]⟩]

/-- **One round of the inner loop**: the byte below `HL` shifted right, the carry in at its top. -/
theorem shr_iter (ok : Z.OK) {j : Nat} (hhas : Has Z j shrInner) {s : Cpu} {H : Nat}
    (M : Mach Z s) (hat : At Z.addrs (j + 1) s) (hrs : s.ramStart.toNat = Z.ramStart)
    (hhl : s.hl.toNat = H + 1) (hram : Z.ramStart ≤ H) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
      s'.mem = s.mem.set! H ((s.mem.get! H >>> 1) ||| ((if s.flag FC then (1 : UInt8) else 0) <<< 7)) ∧
      s'.flag FC = (s.mem.get! H &&& 1 != 0) ∧ s'.hl.toNat = H ∧ s'.b = s.b - 1 ∧
      (if (s.b - 1 != 0) = true then At Z.addrs j s' else At Z.addrs (j + 4) s') := by
  have hHl := s.hl.toNat_lt
  -- dec hl
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_dec_hl (hhas.get 1 rfl) M hat
  have hhl1 : (decHL s).hl.toNat = H := by rw [decHL_hl, hhl]; omega
  have hf1 : (decHL s).f = s.f := by simp only [decHL, zsim]
  have hb1 : (decHL s).b = s.b := by simp only [decHL, zsim]
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = decHL s := ⟨_, rfl⟩
  rw [← hc1] at st1 at2 M1 hS1 hhl1 hf1 hb1
  -- rr (hl)
  obtain ⟨st2, at3⟩ := step_raw ok (hhas.get 2 rfl) M1 at2 (rrM c1) (fun _ _ _ => rfl) (by simp only [rrM, zsim])
  have e2hl : (op2 c1).hl = c1.hl := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hv : (op2 c1).rd (op2 c1).hl = s.mem.get! H := by
    simp only [Cpu.rd, e2hl, zsim]
    rw [hhl1, hS1.1]
  have hfc1 : (op2 c1).flag FC = s.flag FC := by
    rw [op2_flag]
    show (c1.f &&& FC != 0) = (s.f &&& FC != 0)
    rw [hf1]
  obtain ⟨r, hr⟩ : ∃ r : UInt8, r = (s.mem.get! H >>> 1) ||| ((if s.flag FC then (1 : UInt8) else 0) <<< 7) :=
    ⟨_, rfl⟩
  have hrot : ((op2 c1).rot 3 ((op2 c1).rd (op2 c1).hl)).1 = r := by rw [rot3_fst, hv, hfc1, hr]
  have hmem2 : (rrM c1).mem = s.mem.set! H r := by
    unfold rrM
    rw [hrot]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hhl1, hS1.2.1, hrs]; exact hram)]
    simp only [zsim]
    rw [hhl1, hS1.1]
  have hF2 : (rrM c1).ramStart = c1.ramStart ∧ (rrM c1).halted = c1.halted ∧ (rrM c1).sp = c1.sp ∧
      (rrM c1).b = c1.b := by
    simp only [rrM, rot3_b, zsim, and_self]
  have hhl2 : (rrM c1).hl = c1.hl := by show mk16 _ _ = mk16 _ _; simp only [rrM, zsim]
  have hfc2 : (rrM c1).flag FC = (s.mem.get! H &&& 1 != 0) := by
    show ((rrM c1).f &&& FC != 0) = _
    have e : (rrM c1).f = ((op2 c1).rot 3 ((op2 c1).rd (op2 c1).hl)).2.f := by simp only [rrM, tick_f, wr_f]
    rw [e, rot3_f, hv]
    exact rot_fc _ _
  have M2 : Mach Z (rrM c1) := by
    refine ⟨⟨by rw [hF2.1]; exact M1.1.rom, fun x b hx => ?_⟩, by rw [hF2.2.1]; exact M1.2⟩
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M.1.rom
    have hb' := M.1.bytes x b hx
    rw [Nat.zero_add] at hb' ⊢
    rw [hmem2, getBang_set _ _ _ _ (by omega)]
    exact hb'
  -- djnz
  obtain ⟨c3, st3, M3, hS3, hb3, _, hf3, _, hhl3, _, hat3⟩ :=
    djnz_step ok (hhas.get 3 rfl) (hhas.get 0 rfl) M2 (at3 rfl)
  have hb2 : (rrM c1).b = s.b := by rw [hF2.2.2.2, hb1]
  rw [hb2] at hat3 hb3
  refine ⟨c3, (st1.trans st2).trans st3, M3, ?_, ?_, ?_, ?_, ?_, hb3, hat3⟩
  · rw [hS3.2.2.2, hF2.2.2.1, hS1.2.2.2]
  · rw [hS3.2.1, hF2.1, hS1.2.1]
  · rw [hS3.1, hmem2, hr]
  · show (c3.f &&& FC != 0) = _
    rw [hf3]
    exact hfc2
  · rw [hhl3, hhl2]
    exact hhl1

/-- **The inner loop**: `B` rounds, as `shrB` has them. -/
theorem shr_inner (ok : Z.OK) {j : Nat} (hhas : Has Z j shrInner) :
    ∀ (n : Nat) (s : Cpu) (L : Nat), Mach Z s → At Z.addrs (j + 1) s → s.ramStart.toNat = Z.ramStart →
      s.hl.toNat = L + n + 1 → s.b.toNat = n + 1 → Z.ramStart ≤ L →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (j + 4) s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem = shrB s.mem L (n + 1) (s.flag FC) := by
  intro n
  induction n with
  | zero =>
    intro s L M hat hrs hhl hb hram
    obtain ⟨s1, st, M1, hsp, hr, hmem, _, _, _, hat1⟩ := shr_iter ok hhas M hat hrs hhl (by omega)
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat1
    exact ⟨s1, st, M1, hat1, hsp, hr, hmem⟩
  | succ n ih =>
    intro s L M hat hrs hhl hb hram
    obtain ⟨s1, st, M1, hsp, hr, hmem, hfc, hhl1, hb1, hat1⟩ :=
      shr_iter ok hhas M hat hrs (H := L + (n + 1)) (by rw [hhl]) (by omega)
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat1
    have at1 := at_label ok (hhas.get 0 rfl) hat1
    obtain ⟨s', st', M', at', hsp', hr', hmem'⟩ := ih s1 L M1 at1 (by rw [hr]; exact hrs)
      (by rw [hhl1]; omega) (by rw [hb1]; exact (b_sub1 s.b (n + 1) hb).1) hram
    refine ⟨s', st.trans st', M', at', by rw [hsp', hsp], by rw [hr', hr], ?_⟩
    rw [hmem', hmem, hfc]
    rfl

/-! ## A round of the outer loop -/

theorem does_ld_b_c : Does ⟨.ld, [.b, .c]⟩ (ldRR 0 1) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩
theorem does_ld_e_c : Does ⟨.ld, [.e, .c]⟩ (ldRR 3 1) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩

def ldD0 (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 2 (byteOf (Int.ofNat (0 % 256)))).tick 7
def ldC (k : Nat) (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 1 (byteOf (Int.ofNat (k % 256)))).tick 7

theorem does_ld_d_0 : Does ⟨.ld, [.d, .imm (.num 0)]⟩ ldD0 :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldD0, zsim, and_self], fun s => by simp only [ldD0, zsim]⟩
theorem does_ld_c_4 : Does ⟨.ld, [.c, .imm (.num 4)]⟩ (ldC 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldC, zsim, and_self], fun s => by simp only [ldC, zsim]⟩

/-- The routine: `ld c,4` (`ld c,8` for `rt_shr64`), nothing when `B` is zero, else `B` rounds. -/
def shrWItems : List Item :=
  [.label "rt_shr64", .ins ⟨.ld, [.c, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym "rt_shrw")]⟩,
   .label "rt_shr32", .ins ⟨.ld, [.c, .imm (.num 4)]⟩,
   .label "rt_shrw", .ins ⟨.inc, [.b]⟩, .ins ⟨.dec, [.b]⟩, .ins ⟨.ret, [.z]⟩,
   .label "rt_shrw_o", .ins ⟨.push, [.bc]⟩, .ins ⟨.ld, [.b, .c]⟩, .ins ⟨.ld, [.hl, .imm (.sym "rt_acc")]⟩,
   .ins ⟨.ld, [.e, .c]⟩, .ins ⟨.ld, [.d, .imm (.num 0)]⟩, .ins ⟨.add, [.hl, .de]⟩, .ins ⟨.or, [.a]⟩] ++
  shrInner ++ [.ins ⟨.pop, [.bc]⟩, .ins ⟨.djnz, [.imm (.sym "rt_shrw_o")]⟩, .ins ⟨.ret, []⟩]

/-- **A round of the outer loop**: `BC` kept on the stack while the inner loop halves the
accumulator; `B` one less. -/
theorem shr_round (ok : Z.OK) {k : Nat} (hhas : Has Z k shrWItems) {s : Cpu} {P : Nat}
    (M : Mach Z s) (hat : At Z.addrs (k + 10) s) (hrs : s.ramStart.toNat = Z.ramStart)
    (hmsz : s.mem.size = 65536) (hc : s.c = 4) (hsp : s.sp.toNat = P) (hlo : Z.stackLo + 2 ≤ P)
    (hhi : P ≤ Z.stackHi) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧ s'.mem.size = 65536 ∧
      (∀ x, x < P - 2 ∨ P ≤ x → x < Z.acc ∨ Z.acc + 4 ≤ x → s'.mem.get! x = s.mem.get! x) ∧
      IR.Sem.rd s'.mem Z.acc 4 = IR.Sem.rd s.mem Z.acc 4 / 2 ∧ s'.b = s.b - 1 ∧ s'.c = s.c ∧
      (if (s.b - 1 != 0) = true then At Z.addrs (k + 9) s' else At Z.addrs (k + 23) s') := by
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 12, _, 0, hhas.get 12 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hspl := s.sp.toNat_lt
  -- push bc
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((op1 s).push ((op1 s).rp .hl 0)).tick 11 := ⟨_, rfl⟩
  obtain ⟨st1, at1⟩ := step_raw ok (hhas.get 10 rfl) M hat c1 (fun _ _ _ => by rw [hc1]; rfl)
    (by rw [hc1]; simp only [zsim])
  have hpm := push_mem (op1 s) ((op1 s).rp .hl 0) (by simp only [zsim]; omega)
    (by simp only [zsim]; rw [hrs, hsp]; omega)
  simp only [zsim] at hpm
  have hmem1 : c1.mem = IR.Sem.wr s.mem (P - 2) 2 s.bc.toNat := by
    rw [hc1]
    simp only [zsim]
    rw [hpm, hsp]
  have hF1 : c1.ramStart = s.ramStart ∧ c1.halted = s.halted ∧ c1.sp = s.sp - 2 ∧ c1.b = s.b ∧ c1.c = s.c := by
    rw [hc1]
    simp only [zsim, and_self]
  have M1 : Mach Z c1 := ⟨Img.of_wr M.1 hF1.1 hmem1 (by rw [hrs]; omega) (by omega), by rw [hF1.2.1]; exact M.2⟩
  -- ld b,c
  obtain ⟨st2, at2, M2, hS2⟩ := does_raw ok does_ld_b_c (hhas.get 11 rfl) M1 (at1 rfl)
  have hbc2 : (ldRR 0 1 c1).b = s.c ∧ (ldRR 0 1 c1).c = s.c := by
    simp only [ldRR, zsim]
    exact ⟨hF1.2.2.2.2, hF1.2.2.2.2⟩
  -- ld hl,rt_acc
  obtain ⟨c3, ad3, had3, st3, at3, M3, hS3, hhl3, _, hbc3, _⟩ := ld_hl_imm ok (hhas.get 12 rfl) M2 at2
  have hhlv : c3.hl.toNat = Z.acc := by
    rw [hhl3]
    exact immW_toNat _ _ _ _ rfl (sym_val ad3 hacc) (by omega)
  have hb3 : c3.b = 4 := by
    have h := congrArg hi hbc3
    simp only [Cpu.bc, hi_mk16] at h
    rw [h, hbc2.1, hc]
  have hc3 : c3.c = 4 := by
    have h := congrArg lo hbc3
    simp only [Cpu.bc, lo_mk16] at h
    rw [h, hbc2.2, hc]
  -- ld e,c; ld d,0; add hl,de; or a
  obtain ⟨st4, at4, M4, hS4⟩ := does_raw ok does_ld_e_c (hhas.get 13 rfl) M3 at3
  obtain ⟨st5, at5, M5, hS5⟩ := does_raw ok does_ld_d_0 (hhas.get 14 rfl) M4 at4
  obtain ⟨st6, at6, M6, hS6⟩ := does_raw ok does_add_de (hhas.get 15 rfl) M5 at5
  obtain ⟨st7, at7, M7, hS7⟩ := does_raw ok does_or_a (hhas.get 16 rfl) M6 at6
  have hde5 : (ldD0 (ldRR 3 1 c3)).de.toNat = 4 := by
    rw [de_toNat]
    have hd : (ldD0 (ldRR 3 1 c3)).d = 0 := by simp only [ldD0, ldRR, zsim]; rfl
    have he : (ldD0 (ldRR 3 1 c3)).e = 4 := by simp only [ldD0, ldRR, zsim]; exact hc3
    rw [hd, he]
    rfl
  have hhl5 : (ldD0 (ldRR 3 1 c3)).hl = c3.hl := by show mk16 _ _ = mk16 _ _; simp only [ldD0, ldRR, zsim]
  obtain ⟨c7, hc7⟩ : ∃ c7 : Cpu, c7 = orA (addHLDE (ldD0 (ldRR 3 1 c3))) := ⟨_, rfl⟩
  rw [← hc7] at st7 at7 M7 hS7
  have hhl7 : c7.hl.toNat = Z.acc + 3 + 1 := by
    rw [hc7, orA_hl, addHLDE_hl, hde5, hhl5, hhlv]
    omega
  have hb7 : c7.b.toNat = 3 + 1 := by
    rw [hc7, orA_b]
    simp only [addHLDE, ldD0, ldRR, zsim]
    rw [hb3]
    rfl
  have hfc7 : c7.flag FC = false := by
    rw [hc7]
    simp only [orA, zsim]
    exact alu6_flag _ _
  have hS17 : Sys c1 c7 := hS2.trans (hS3.trans (hS4.trans (hS5.trans (hS6.trans hS7))))
  -- the inner loop
  have hL : Has Z (k + 17) shrInner :=
    Has.pre (l2 := [.ins ⟨.pop, [.bc]⟩, .ins ⟨.djnz, [.imm (.sym "rt_shrw_o")]⟩, .ins ⟨.ret, []⟩])
      hhas.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail
  have at18 := at_label ok (hL.get 0 rfl) at7
  obtain ⟨c8, st8, M8, at21, hsp8, hr8, hmem8⟩ := shr_inner ok hL 3 c7 Z.acc M7 at18
    (by rw [hS17.2.1, hF1.1]; exact hrs) hhl7 hb7 hram.1
  rw [hfc7, hS17.1, hmem1] at hmem8
  -- pop bc
  obtain ⟨w, hw'⟩ : ∃ w : UInt16, w = (op1 c8).rd16 (op1 c8).sp := ⟨_, rfl⟩
  obtain ⟨c9, hc9⟩ : ∃ c9 : Cpu, c9 = (({ (op1 c8) with sp := (op1 c8).sp + 2 } : Cpu).setRp .hl 0 w).tick 10 :=
    ⟨_, rfl⟩
  obtain ⟨st9, at22⟩ := step_raw ok (hhas.get 21 rfl) M8 at21 c9 (fun _ _ _ => by rw [hc9, hw']; rfl)
    (by rw [hc9]; simp only [zsim])
  have hsp8' : c8.sp = s.sp - 2 := by rw [hsp8, hS17.2.2.2, hF1.2.2.1]
  have hsp8n : c8.sp.toNat = P - 2 := by rw [hsp8', sub2_toNat _ (by omega), hsp]
  have hw : w = s.bc := by
    rw [hw']
    show c8.rd16 c8.sp = s.bc
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by rw [hsp8n]; omega), hsp8n, hmem8,
      rd_congr (IR.Sem.wr s.mem (P - 2) 2 s.bc.toNat) _ (P - 2) 2 (by omega)
        (fun x h1 h2 => shrB_far _ _ _ _ _ (by omega)),
      rd_wr _ _ _ _ (by rw [hmsz]; omega) (by rw [hmsz]; exact Nat.le_refl _)]
    exact Nat.mod_eq_of_lt s.bc.toNat_lt
  have hF9 : c9.mem = c8.mem ∧ c9.ramStart = c8.ramStart ∧ c9.halted = c8.halted ∧ c9.sp = c8.sp + 2 ∧
      c9.b = s.b ∧ c9.c = s.c := by
    rw [hc9]
    simp only [zsim, hw, Cpu.bc, hi_mk16, lo_mk16, and_self]
  have hsp9 : c9.sp = s.sp := by
    rw [hF9.2.2.2.1, hsp8']
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, sub2_toNat _ (by omega)]
    show (s.sp.toNat - 2 + 2) % 65536 = _
    omega
  have M9 : Mach Z c9 := ⟨M8.1.congr hF9.2.1 hF9.1, by rw [hF9.2.2.1]; exact M8.2⟩
  -- djnz
  obtain ⟨c10, st10, M10, hS10, hb10, _, _, hc10, _, _, hat10⟩ :=
    djnz_step ok (hhas.get 22 rfl) (hhas.get 9 rfl) M9 (at22 rfl)
  rw [hF9.2.2.2.2.1] at hat10 hb10
  have hm10 : c10.mem = shrB (IR.Sem.wr s.mem (P - 2) 2 s.bc.toNat) Z.acc 4 false := by
    rw [hS10.1, hF9.1, hmem8]
  have hfar1 : ∀ x, x < P - 2 ∨ P ≤ x → (IR.Sem.wr s.mem (P - 2) 2 s.bc.toNat).get! x = s.mem.get! x :=
    fun x hx => wr_get_far _ _ _ _ _ (by omega) (by omega)
  refine ⟨c10, ((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans
    st9).trans st10, M10, ?_, ?_, ?_, ?_, ?_, hb10, ?_, hat10⟩
  · rw [hS10.2.2.2, hsp9]
  · rw [hS10.2.1, hF9.2.1, hr8, hS17.2.1, hF1.1]
  · rw [hm10, shrB_size, wr_size]
    exact hmsz
  · intro x hx hx'
    rw [hm10, shrB_far _ _ _ _ _ hx', hfar1 x hx]
  · rw [hm10, shrB_rd 4 _ _ _ (by rw [wr_size]; exact hmsz) (by omega),
      rd_congr s.mem _ Z.acc 4 (by omega) (fun x _ _ => hfar1 x (by omega))]
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
  · rw [hc10, hF9.2.2.2.2.2]

/-- **The outer loop**: `B` rounds. -/
theorem shr_outer (ok : Z.OK) {k : Nat} (hhas : Has Z k shrWItems) {P : Nat} (hlo : Z.stackLo + 2 ≤ P)
    (hhi : P ≤ Z.stackHi) :
    ∀ (n : Nat) (s : Cpu), Mach Z s → At Z.addrs (k + 10) s → s.ramStart.toNat = Z.ramStart →
      s.mem.size = 65536 → s.c = 4 → s.sp.toNat = P → s.b.toNat = n + 1 →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (k + 23) s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem.size = 65536 ∧
        (∀ x, x < P - 2 ∨ P ≤ x → x < Z.acc ∨ Z.acc + 4 ≤ x → s'.mem.get! x = s.mem.get! x) ∧
        IR.Sem.rd s'.mem Z.acc 4 = IR.Sem.rd s.mem Z.acc 4 / 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro s M hat hrs hmsz hc hsp hb
    obtain ⟨s1, st, M1, hsp1, hr1, hsz1, hfar1, hrd1, _, _, hat1⟩ := shr_round ok hhas M hat hrs hmsz hc hsp hlo hhi
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat1
    exact ⟨s1, st, M1, hat1, hsp1, hr1, hsz1, hfar1, by rw [hrd1, Nat.zero_add, Nat.pow_one]⟩
  | succ n ih =>
    intro s M hat hrs hmsz hc hsp hb
    obtain ⟨s1, st, M1, hsp1, hr1, hsz1, hfar1, hrd1, hb1, hc1, hat1⟩ :=
      shr_round ok hhas M hat hrs hmsz hc hsp hlo hhi
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat1
    have at1 := at_label ok (hhas.get 9 rfl) hat1
    obtain ⟨s', st', M', at', hsp', hr', hsz', hfar', hrd'⟩ := ih s1 M1 at1 (by rw [hr1]; exact hrs) hsz1
      (by rw [hc1, hc]) (by rw [hsp1, hsp]) (by rw [hb1]; exact (b_sub1 s.b (n + 1) hb).1)
    refine ⟨s', st.trans st', M', at', by rw [hsp', hsp1], by rw [hr', hr1], hsz',
      fun x h1 h2 => by rw [hfar' x h1 h2, hfar1 x h1 h2], ?_⟩
    rw [hrd', hrd1, Nat.div_div_eq_div_mul, Nat.pow_succ 2 (n + 1), Nat.mul_comm 2]

/-- **`rt_shr32`**: the accumulator's four bytes shifted right by `B`; nothing else written but
the two bytes of the free stack that keep `BC` (the runtime is to have them: `2 ≤ rtK`). -/
theorem rt_shr32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) (hK : 2 ≤ Z.rtK) {k : Nat}
    (hhas : Has Z k shrWItems) :
    RtAcc Z "rt_shr32" (fun _ => True)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.Sem.rd s.mem Z.acc 4 / 2 ^ s.b.toNat) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi _ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  -- ld c,4; inc b; dec b; ret z
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_c_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨st2, at7, M2, hS2⟩ := does_raw ok does_inc_b (hhas.get 6 rfl) M1 at6
  obtain ⟨st3, at8, M3, hS3⟩ := does_raw ok does_dec_b (hhas.get 7 rfl) M2 at7
  obtain ⟨hb, _, _, hfz⟩ := incdec_b (ldC 4 s)
  have hc3 : (decB (incB (ldC 4 s))).c = 4 := by
    simp only [decB, incB, ldC, Cpu.dec8, Cpu.inc8, zsim]
    rfl
  have hb0 : (ldC 4 s).b = s.b := by simp only [ldC, zsim]
  have hS03 : Sys s (decB (incB (ldC 4 s))) := hS1.trans (hS2.trans hS3)
  obtain ⟨c4, st4, hm4, hh4, hr4, _, hb4, hcc4, _, hcase⟩ := ret_z_step ok (hhas.get 8 rfl) M3 at8
  rw [hfz, hb0] at hcase
  by_cases hz : s.b = 0
  · have hz' : (s.b == 0) = true := by simpa using hz
    rw [if_pos hz'] at hcase
    refine ⟨c4, ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ⟨?_, fun x _ _ _ => ?_⟩⟩
    · rw [hcase.1, rd16_sys hS03]
    · rw [hcase.2, hS03.2.2.2]
    · rw [hh4, hS03.2.2.1]; exact hh
    · rw [hr4, hS03.2.1]
    · rw [hm4, hS03.1]; exact hmsz
    · show IR.Sem.rd c4.mem Z.acc 4 = _
      rw [hm4, hS03.1, hz]
      simp
    · rw [hm4, hS03.1]
  · have hz' : ¬ ((s.b == 0) = true) := by simpa using hz
    rw [if_neg hz'] at hcase
    have hbn : s.b.toNat ≠ 0 := fun h => hz (UInt8.toNat_inj.mp (by rw [h]; rfl))
    have M4 : Mach Z c4 := ⟨M3.1.congr hr4 hm4, by rw [hh4]; exact M3.2⟩
    have hS04 : Sys s c4 :=
      ⟨by rw [hm4, hS03.1], by rw [hr4, hS03.2.1], by rw [hh4, hS03.2.2.1], by rw [hcase.2, hS03.2.2.2]⟩
    have at10 := at_label ok (hhas.get 9 rfl) hcase.1
    have hspl := s.sp.toNat_lt
    obtain ⟨c5, st5, M5, at23, hsp5, hr5, hsz5, hfar5, hrd5⟩ :=
      shr_outer ok hhas (P := s.sp.toNat) (by omega) (by omega) (s.b.toNat - 1) c4 M4 at10
        (by rw [hS04.2.1]; exact hrs) (by rw [hS04.1]; exact hmsz) (by rw [hcc4, hc3])
        (by rw [hS04.2.2.2]) (by rw [hb4, hb, hb0]; omega)
    obtain ⟨c', st6, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 23 rfl) M5 at23
    have hfar : ∀ x, x < s.sp.toNat - 2 ∨ s.sp.toNat ≤ x → x < Z.acc ∨ Z.acc + 4 ≤ x →
        c5.mem.get! x = s.mem.get! x := fun x h1 h2 => by rw [hfar5 x h1 h2, hS04.1]
    refine ⟨c', (((((st1.trans st2).trans st3).trans st4).trans st5).trans st6), ?_, ?_, ?_, ?_, ?_,
      ⟨?_, fun x hx _ hx' => ?_⟩⟩
    · rw [hpc', hsp5, hS04.2.2.2]
      apply UInt16.toNat_inj.mp
      rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
      exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega) (by omega))
    · rw [hsp', hsp5, hS04.2.2.2]
    · rw [hh']; exact M5.2
    · rw [hrs', hr5, hS04.2.1]
    · rw [hmem']; exact hsz5
    · show IR.Sem.rd c'.mem Z.acc 4 = _
      rw [hmem', hrd5, hS04.1, show s.b.toNat - 1 + 1 = s.b.toNat by omega]
    · rw [hmem']
      exact hfar x (by omega) (by omega)

#guard inRuntime shrWItems

/-- info: 'Ember.Proof.Z80Gen.rt_shr32_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rt_shr32_ok

end

end Ember.Proof.Z80Gen
