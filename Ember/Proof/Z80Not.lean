import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80Not — `rt_not32`, from its items (plan M7.3)

The runtime's complement of the accumulator: `ld b,4`, `ld hl,rt_acc`,
then a loop over the bytes at `HL` (`ld a,(hl); cpl; ld (hl),a; inc hl;
djnz`).  `rt_not32_ok`: the routine returns with the accumulator's four
bytes complemented and nothing else written but the free stack.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-- The loop in memory: `n` times, the byte at `H` becomes its complement. -/
def runN : ByteArray → Nat → Nat → ByteArray
  | m, _, 0 => m
  | m, H, n + 1 => runN (m.set! H (~~~ m.get! H)) (H + 1) n

/-- The body of the loop: `ld a,(hl); cpl; ld (hl),a; inc hl; djnz`. -/
def notItems (l : String) : List Item :=
  [.label l, .ins ⟨.ld, [.a, .mhl]⟩, .ins ⟨.cpl, []⟩, .ins ⟨.ld, [.mhl, .a]⟩, .ins ⟨.inc, [.hl]⟩,
   .ins ⟨.djnz, [.imm (.sym l)]⟩]

/-- **One round of the loop.** -/
theorem not_iter (ok : Z.OK) {j : Nat} {l : String} (hhas : Has Z j (notItems l)) {s : Cpu} {H : Nat}
    (M : Mach Z s) (hat : At Z.addrs (j + 1) s) (hrs : s.ramStart.toNat = Z.ramStart) (hhl : s.hl.toNat = H)
    (hram : Z.ramStart ≤ H) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
      s'.mem = s.mem.set! H (~~~ s.mem.get! H) ∧ s'.hl = s.hl + 1 ∧ s'.b = s.b - 1 ∧
      (if (s.b - 1 != 0) = true then At Z.addrs j s' else At Z.addrs (j + 6) s') := by
  -- ld a,(hl)
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_ld_a_m (hhas.get 1 rfl) M hat
  have ha1 : (ldAM s).a = s.mem.get! H := by
    simp only [ldAM, zsim]
    show s.mem.get! s.hl.toNat = _
    rw [hhl]
  have hhl1 : (ldAM s).hl = s.hl := by simp only [ldAM, zsim]
  have hb1 : (ldAM s).b = s.b := by simp only [ldAM, zsim]
  -- cpl
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_cpl (hhas.get 2 rfl) M1 at2
  have ha2 : (cplA (ldAM s)).a = ~~~ s.mem.get! H := by
    simp only [cplA, zsim]
    rw [ha1]
  have hhl2 : (cplA (ldAM s)).hl = s.hl := by
    rw [← hhl1]
    show mk16 _ _ = mk16 _ _
    simp only [cplA, zsim]
  have hb2 : (cplA (ldAM s)).b = s.b := by rw [← hb1]; simp only [cplA, zsim]
  -- ld (hl),a
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = cplA (ldAM s) := ⟨_, rfl⟩
  rw [← hc2] at st2 at3 M2 hS2 ha2 hhl2 hb2
  obtain ⟨c3, hc3⟩ : ∃ c3 : Cpu, c3 = ((op1 c2).wr (op1 c2).hl ((op1 c2).reg .hl 7)).tick 7 := ⟨_, rfl⟩
  obtain ⟨st3, at4⟩ := step_raw ok (hhas.get 3 rfl) M2 at3 c3 (fun _ _ _ => by rw [hc3]; rfl)
    (by rw [hc3]; simp only [zsim])
  have hS02 : Sys s c2 := hS1.trans hS2
  have hmem3 : c3.mem = s.mem.set! H (~~~ s.mem.get! H) := by
    rw [hc3]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hhl2, hhl, hS02.2.1, hrs]; exact hram)]
    simp only [zsim]
    rw [hhl2, hhl, hS02.1, ha2]
  have hF3 : c3.ramStart = c2.ramStart ∧ c3.halted = c2.halted ∧ c3.sp = c2.sp ∧ c3.b = c2.b := by
    rw [hc3]
    simp only [zsim, and_self]
  have hhl3 : c3.hl = s.hl := by rw [hc3, ← hhl2]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have M3 : Mach Z c3 := by
    refine ⟨⟨by rw [hF3.1]; exact M2.1.rom, fun x b hx => ?_⟩, by rw [hF3.2.1]; exact M2.2⟩
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M.1.rom
    have hb' := M.1.bytes x b hx
    rw [Nat.zero_add] at hb' ⊢
    rw [hmem3, getBang_set _ _ _ _ (by omega)]
    exact hb'
  -- inc hl
  obtain ⟨st4, at5, M4, hS4⟩ := does_raw ok does_inc_hl (hhas.get 4 rfl) M3 (at4 rfl)
  have hhl4 : (incHL c3).hl = s.hl + 1 := by
    apply UInt16.toNat_inj.mp
    rw [incHL_hl, UInt16.toNat_add, hhl3]
    rfl
  have hb4 : (incHL c3).b = s.b := by rw [← hb2, ← hF3.2.2.2]; simp only [incHL, zsim]
  -- djnz
  obtain ⟨c5, st5, M5, hS5, hb5, _, _, _, hhl5, _, hat5⟩ := djnz_step ok (hhas.get 5 rfl) (hhas.get 0 rfl) M4 at5
  rw [hb4] at hat5 hb5
  refine ⟨c5, (((st1.trans st2).trans st3).trans st4).trans st5, M5, ?_, ?_, ?_, ?_, hb5, hat5⟩
  · rw [hS5.2.2.2, hS4.2.2.2, hF3.2.2.1, hS02.2.2.2]
  · rw [hS5.2.1, hS4.2.1, hF3.1, hS02.2.1]
  · rw [hS5.1, hS4.1, hmem3]
  · rw [hhl5, hhl4]

/-- **The loop**: `B` rounds, as `runN` has them. -/
theorem not_loop (ok : Z.OK) {j : Nat} {l : String} (hhas : Has Z j (notItems l)) :
    ∀ (n : Nat) (s : Cpu) (H : Nat), Mach Z s → At Z.addrs (j + 1) s → s.ramStart.toNat = Z.ramStart →
      s.hl.toNat = H → s.b.toNat = n + 1 → Z.ramStart ≤ H → H + n + 1 ≤ 65536 →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (j + 6) s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem = runN s.mem H (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro s H M hat hrs hhl hb hram hbH
    obtain ⟨s1, st, M1, hsp, hr, hmem, _, _, hat1⟩ := not_iter ok hhas M hat hrs hhl hram
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat1
    exact ⟨s1, st, M1, hat1, hsp, hr, hmem⟩
  | succ n ih =>
    intro s H M hat hrs hhl hb hram hbH
    obtain ⟨s1, st, M1, hsp, hr, hmem, hhl1, hb1, hat1⟩ := not_iter ok hhas M hat hrs hhl hram
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat1
    have at1 := at_label ok (hhas.get 0 rfl) hat1
    obtain ⟨s', st', M', at', hsp', hr', hmem'⟩ := ih s1 (H + 1) M1 at1 (by rw [hr]; exact hrs)
      (by rw [hhl1, UInt16.toNat_add, hhl]; show (H + 1) % 65536 = _; omega)
      (by rw [hb1]; exact (b_sub1 s.b (n + 1) hb).1) (by omega) (by omega)
    refine ⟨s', st.trans st', M', at', by rw [hsp', hsp], by rw [hr', hr], ?_⟩
    rw [hmem', hmem]
    rfl

/-- The loop writes the `n` bytes from `H` only. -/
theorem runN_far : ∀ (n : Nat) (m : ByteArray) (H x : Nat), x < H ∨ H + n ≤ x → (runN m H n).get! x = m.get! x
  | 0, _, _, _, _ => rfl
  | n + 1, m, H, x, hx => by
    rw [runN, runN_far n _ _ x (by omega), getBang_set _ _ _ _ (by omega)]

theorem runN_size : ∀ (n : Nat) (m : ByteArray) (H : Nat), (runN m H n).size = m.size
  | 0, _, _ => rfl
  | n + 1, m, H => by rw [runN, runN_size n, set_size]

/-- The loop complements the `n` bytes at `H`. -/
theorem runN_rd : ∀ (n : Nat) (m : ByteArray) (H : Nat), m.size = 65536 → H + n ≤ 65536 →
    IR.Sem.rd (runN m H n) H n = 2 ^ (8 * n) - 1 - IR.Sem.rd m H n
  | 0, _, _, _, _ => by simp [IR.Sem.rd]
  | n + 1, m, H, hsz, hH => by
    rw [runN, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runN_far n _ _ H (Or.inl (by omega)), getBang_same _ _ _ (by omega),
      runN_rd n _ (H + 1) (by rw [set_size]; exact hsz) (by omega),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)), UInt8.toNat_not]
    have hb := (m.get! H).toNat_lt
    have hr := rd_lt m (H + 1) n
    have hp : (2 : Nat) ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      omega
    rw [hp]
    show 2 ^ 8 - 1 - (m.get! H).toNat + 256 * (2 ^ (8 * n) - 1 - IR.Sem.rd m (H + 1) n) =
      256 * 2 ^ (8 * n) - 1 - ((m.get! H).toNat + 256 * IR.Sem.rd m (H + 1) n)
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8]
    omega

/-- The routine: `ld b,4`, `ld hl,rt_acc`, then the loop. -/
def notWItems : List Item :=
  [.label "rt_not64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym "rt_notw")]⟩,
   .label "rt_not32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
   .label "rt_notw", .ins ⟨.ld, [.hl, .imm (.sym "rt_acc")]⟩] ++
  notItems "rt_notw_l" ++ [.ins ⟨.ret, []⟩]

/-- **`rt_not32`**: the accumulator's four bytes are complemented; nothing else is written. -/
theorem rt_not32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k notWItems) :
    RtAcc Z "rt_not32" (fun _ => True)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = 2 ^ (8 * 4) - 1 - IR.Sem.rd s.mem Z.acc 4) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 7) (notItems "rt_notw_l") :=
    Has.pre (l2 := [.ins ⟨.ret, []⟩]) hhas.tail.tail.tail.tail.tail.tail.tail
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi _ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_b_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hhl2, _, hbc2, _⟩ := ld_hl_imm ok (hhas.get 6 rfl) M1 at6
  have hhlv : c2.hl.toNat = Z.acc := by
    rw [hhl2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hb2 : c2.b = (ldB 4 s).b := by
    have h := congrArg hi hbc2
    simpa [Cpu.bc] using h
  have hS02 : Sys s c2 := hS1.trans hS2
  have at8 := at_label ok (hL.get 0 rfl) at7
  obtain ⟨c3, st3, M3, at13, hsp3, hr3, hmem3⟩ := not_loop ok hL 3 c2 Z.acc M2 at8
    (by rw [hS02.2.1]; exact hrs) hhlv (by rw [hb2, ldB_b 4 (by decide)]) hram.1 (by omega)
  obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 13 rfl) M3 at13
  rw [hS02.1] at hmem3
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 4 ≤ x → c3.mem.get! x = s.mem.get! x := fun x hx => by
    rw [hmem3]
    exact runN_far 4 _ _ x hx
  refine ⟨c', ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp3, hS02.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega))
  · rw [hsp', hsp3, hS02.2.2.2]
  · rw [hh']
    exact M3.2
  · rw [hrs', hr3, hS02.2.1]
  · rw [hmem', hmem3, runN_size]
    exact hmsz
  · show IR.Sem.rd c'.mem Z.acc 4 = _
    rw [hmem', hmem3, runN_rd 4 _ _ hmsz (by omega)]
  · intro x _ _ hx
    rw [hmem']
    exact hfar x (by omega)

#guard inRuntime notWItems

/-- info: 'Ember.Proof.Z80Gen.rt_not32_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rt_not32_ok

end

end Ember.Proof.Z80Gen
