import Ember.Proof.Z80Bytes

/-!
# Ember.Proof.Z80AndXor — `rt_and32` and `rt_xor32` from their items (plan M7.3)

The routines of the runtime that `and` and `xor` the runtime's
accumulator with the four bytes at `HL`, byte by byte (`bytewise "and"`,
`bytewise "xor"`), proved from their items as `rt_or32_ok` is: the loop
`ld a,(de); and (hl)` (or `xor (hl)`) `; ld (de),a; inc hl; inc de; djnz`
leaves in the accumulator the operation on the two values, and writes
nothing else.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-! ## `and` -/

theorem aluA_and (a f v : UInt8) : aluA 4 a f v = a &&& v := rfl

theorem aluA_xor (a f v : UInt8) : aluA 5 a f v = a ^^^ v := rfl

/-- The bits of `a0 + 256 * A`: those of `a0` below 8, those of `A` from 8 on. -/
theorem testBit_byte (a0 A i : Nat) (ha : a0 < 256) :
    (a0 + 256 * A).testBit i = if i < 8 then a0.testBit i else A.testBit (i - 8) := by
  have e : a0 + 256 * A = A <<< 8 ||| a0 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (show a0 < 2 ^ 8 from ha), Nat.shiftLeft_eq]
    omega
  rw [e, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 8
  · simp [hi, show ¬ (8 ≤ i) by omega]
  · have h0 : a0.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show a0 < 2 ^ 8 from ha) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, show 8 ≤ i by omega, h0]

theorem and_bytes (a0 b0 A B : Nat) (ha : a0 < 256) (hb : b0 < 256) :
    (a0 + 256 * A) &&& (b0 + 256 * B) = (a0 &&& b0) + 256 * (A &&& B) := by
  have hab : a0 &&& b0 < 256 := Nat.and_lt_two_pow (n := 8) a0 hb
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_byte _ _ _ ha, testBit_byte _ _ _ hb, testBit_byte _ _ _ hab]
  by_cases hi : i < 8 <;> simp [hi, Nat.testBit_and]

theorem xor_bytes (a0 b0 A B : Nat) (ha : a0 < 256) (hb : b0 < 256) :
    (a0 + 256 * A) ^^^ (b0 + 256 * B) = (a0 ^^^ b0) + 256 * (A ^^^ B) := by
  have hab : a0 ^^^ b0 < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_byte _ _ _ ha, testBit_byte _ _ _ hb, testBit_byte _ _ _ hab]
  by_cases hi : i < 8 <;> simp [hi, Nat.testBit_xor]

/-- The loop with `and`: the `n` bytes at `D` are those that were there, and-ed with those at `H`
(which are not among them). -/
theorem runB_and : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat), m.size = 65536 → D + n ≤ 65536 →
    H + n ≤ 65536 → (∀ i, i < n → H + i < D ∨ D + n ≤ H + i) →
    IR.Sem.rd (runB 4 f m D H n).1 D n = IR.Sem.rd m D n &&& IR.Sem.rd m H n
  | 0, _, _, _, _, _, _, _, _ => by simp [IR.Sem.rd]
  | n + 1, f, m, D, H, hsz, hD, hH, hap => by
    rw [runB, IR.Sem.rd, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
      Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runB_far 4 n _ _ _ _ D (Or.inl (by omega)), getBang_same _ _ _ (by omega),
      runB_and n _ _ (D + 1) (H + 1) (by rw [set_size]; exact hsz) (by omega) (by omega)
        (fun i hi => by have := hap (i + 1) (by omega); omega)]
    have h0 := hap 0 (by omega)
    rw [rd_congr m _ (D + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by
        have := hap (x - H) (by omega)
        omega))]
    rw [and_bytes _ _ _ _ (m.get! D).toNat_lt (m.get! H).toNat_lt, aluA_and, UInt8.toNat_and]

/-- The loop with `xor`. -/
theorem runB_xor : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat), m.size = 65536 → D + n ≤ 65536 →
    H + n ≤ 65536 → (∀ i, i < n → H + i < D ∨ D + n ≤ H + i) →
    IR.Sem.rd (runB 5 f m D H n).1 D n = IR.Sem.rd m D n ^^^ IR.Sem.rd m H n
  | 0, _, _, _, _, _, _, _, _ => by simp [IR.Sem.rd]
  | n + 1, f, m, D, H, hsz, hD, hH, hap => by
    rw [runB, IR.Sem.rd, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
      Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runB_far 5 n _ _ _ _ D (Or.inl (by omega)), getBang_same _ _ _ (by omega),
      runB_xor n _ _ (D + 1) (H + 1) (by rw [set_size]; exact hsz) (by omega) (by omega)
        (fun i hi => by have := hap (i + 1) (by omega); omega)]
    have h0 := hap 0 (by omega)
    rw [rd_congr m _ (D + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by
        have := hap (x - H) (by omega)
        omega))]
    rw [xor_bytes _ _ _ _ (m.get! D).toNat_lt (m.get! H).toNat_lt, aluA_xor, UInt8.toNat_xor]

/-- **`rt_and32`**: the accumulator's four bytes are and-ed with those at `HL`; nothing else is written. -/
theorem rt_and32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k (bytewiseItems "and" [] ⟨.and, [.mhl]⟩)) :
    RtAcc Z "rt_and32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.binOp .and 4 (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 7) (loopItems "rt_andw_l" ⟨.and, [.mhl]⟩) :=
    Has.pre (l2 := [.ins ⟨.ret, []⟩]) hhas.tail.tail.tail.tail.tail.tail.tail
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_b_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hde2, hhl2, _, _, hb2, hf2⟩ := ld_de_imm ok (hhas.get 6 rfl) M1 at6
  have hdev : c2.de.toNat = Z.acc := by
    rw [hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hS02 : Sys s c2 := hS1.trans hS2
  have at8 := at_label ok (hL.get 0 rfl) at7
  obtain ⟨c3, st3, M3, at14, hsp3, hr3, hmem3, hf3⟩ := byte_loop ok (k := 4) (fun _ _ _ => rfl) rfl hL 3 c2 Z.acc
    s.hl.toNat M2 at8 (by rw [hS02.2.1]; exact hrs) hdev (by rw [hhl2, ldB_hl]) (by rw [hb2, ldB_b 4 (by decide)]) hram.1
    (by omega) (by omega)
  obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 14 rfl) M3 at14
  rw [hS02.1] at hmem3
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 4 ≤ x → c3.mem.get! x = s.mem.get! x := fun x hx => by
    rw [hmem3]
    exact runB_far 4 4 _ _ _ _ x hx
  refine ⟨c', ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp3, hS02.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega))
  · rw [hsp', hsp3, hS02.2.2.2]
  · rw [hh']
    exact M3.2
  · rw [hrs', hr3, hS02.2.1]
  · rw [hmem', hmem3, runB_size]
    exact hmsz
  · show IR.Sem.rd c'.mem Z.acc 4 = _
    rw [hmem', hmem3, runB_and 4 _ _ _ _ hmsz (by omega) hb (fun i hi => by have := (hap i hi).1; omega)]
    show _ = (_ &&& _) % 2 ^ (8 * 4)
    rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (rd_lt _ _ _))]
  · intro x _ _ hx
    rw [hmem']
    exact hfar x (by omega)

#guard inRuntime (bytewiseItems "and" [] ⟨.and, [.mhl]⟩)

/-- **`rt_xor32`**: the accumulator's four bytes are xor-ed with those at `HL`; nothing else is written. -/
theorem rt_xor32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k (bytewiseItems "xor" [] ⟨.xor, [.mhl]⟩)) :
    RtAcc Z "rt_xor32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.binOp .xor 4 (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 7) (loopItems "rt_xorw_l" ⟨.xor, [.mhl]⟩) :=
    Has.pre (l2 := [.ins ⟨.ret, []⟩]) hhas.tail.tail.tail.tail.tail.tail.tail
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_b_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hde2, hhl2, _, _, hb2, hf2⟩ := ld_de_imm ok (hhas.get 6 rfl) M1 at6
  have hdev : c2.de.toNat = Z.acc := by
    rw [hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hS02 : Sys s c2 := hS1.trans hS2
  have at8 := at_label ok (hL.get 0 rfl) at7
  obtain ⟨c3, st3, M3, at14, hsp3, hr3, hmem3, hf3⟩ := byte_loop ok (k := 5) (fun _ _ _ => rfl) rfl hL 3 c2 Z.acc
    s.hl.toNat M2 at8 (by rw [hS02.2.1]; exact hrs) hdev (by rw [hhl2, ldB_hl]) (by rw [hb2, ldB_b 4 (by decide)]) hram.1
    (by omega) (by omega)
  obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 14 rfl) M3 at14
  rw [hS02.1] at hmem3
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 4 ≤ x → c3.mem.get! x = s.mem.get! x := fun x hx => by
    rw [hmem3]
    exact runB_far 5 4 _ _ _ _ x hx
  refine ⟨c', ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp3, hS02.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega))
  · rw [hsp', hsp3, hS02.2.2.2]
  · rw [hh']
    exact M3.2
  · rw [hrs', hr3, hS02.2.1]
  · rw [hmem', hmem3, runB_size]
    exact hmsz
  · show IR.Sem.rd c'.mem Z.acc 4 = _
    rw [hmem', hmem3, runB_xor 4 _ _ _ _ hmsz (by omega) hb (fun i hi => by have := (hap i hi).1; omega)]
    show _ = (_ ^^^ _) % 2 ^ (8 * 4)
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (rd_lt _ _ _) (rd_lt _ _ _))]
  · intro x _ _ hx
    rw [hmem']
    exact hfar x (by omega)

#guard inRuntime (bytewiseItems "xor" [] ⟨.xor, [.mhl]⟩)

end

/-- info: 'Ember.Proof.Z80Gen.rt_and32_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rt_and32_ok

/-- info: 'Ember.Proof.Z80Gen.rt_xor32_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rt_xor32_ok

end Ember.Proof.Z80Gen
