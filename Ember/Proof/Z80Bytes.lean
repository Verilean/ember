import Ember.Proof.Z80Wide

/-!
# Ember.Proof.Z80Bytes — the runtime's loops over the bytes of the accumulator (plan M7.3)

`djnz_step`: `djnz` to a label of the image.  On it, the routines that
go through the accumulator and the bytes at `HL` one byte at a time.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-- The state after `djnz e`. -/
def djnzTo (n : UInt8) (s : Cpu) : Cpu :=
  if (op1 s).b - 1 != 0 then
    ({ (skip { (op1 s) with b := (op1 s).b - 1 } 1) with
        pc := (skip { (op1 s) with b := (op1 s).b - 1 } 1).pc + sext n } : Cpu).tick 13
  else (skip { (op1 s) with b := (op1 s).b - 1 } 1).tick 8

/-- **`djnz` to a label**: `B` is one less; the jump is taken unless it is now zero.  Memory and
the other registers are as they were. -/
theorem djnz_step (ok : Z.OK) {k j : Nat} {l : String} (hk : Z.items[k]? = some (.ins ⟨.djnz, [.imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ Sys s s' ∧ s'.b = s.b - 1 ∧ s'.a = s.a ∧ s'.f = s.f ∧ s'.c = s.c ∧
      s'.hl = s.hl ∧ s'.de = s.de ∧
      (if (s.b - 1 != 0) = true then At Z.addrs j s' else At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next M.1 hk had
  have hval : (Z.a.env ad).val (.sym l) = Int.ofNat T := sym_val ad hsym
  have henc : ∃ lst, (rel (.sym l)).run (Z.a.env ad) = .ok lst ∧ bs.length = 2 := by
    have h' := encode_run hbs
    have he' : ((rel (.sym l)).run (Z.a.env ad)).bind _ = Except.ok bs := h'
    obtain ⟨lst, hl, hb⟩ := bind_ok he'
    have := rel_bytes hl
    subst this
    cases hb
    exact ⟨_, hl, rfl⟩
  obtain ⟨lst, hrel, hlen⟩ := henc
  obtain ⟨r1, r2⟩ := rel_range hrel rfl
  rw [hval] at r1 r2
  have hpcv : (Z.a.env ad).pc = Int.ofNat ad := rfl
  rw [hpcv] at r1 r2
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have himm : Instr.immB (Z.a.env ad) ⟨.djnz, [.imm (.sym l)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
    show byteOf ((Z.a.env ad).val (.sym l) - ((Z.a.env ad).pc + 2)) = _
    rw [hval]
    rfl
  have hexec : ∀ inp, exec (Z.a.env ad) ⟨.djnz, [.imm (.sym l)]⟩ s inp =
      some (djnzTo (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s) := by
    intro inp
    rw [← himm]
    rfl
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hexec inp)).1
  have hb1 : (op1 s).b = s.b := by simp only [zsim]
  by_cases hc : (s.b - 1 != 0) = true
  · have e : djnzTo (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s =
        ({ (skip { (op1 s) with b := (op1 s).b - 1 } 1) with
          pc := (skip { (op1 s) with b := (op1 s).b - 1 } 1).pc +
            sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) } : Cpu).tick 13 := by
      unfold djnzTo
      rw [hb1, if_pos hc]
    rw [e] at hst
    have hS : Sys s (({ (skip { (op1 s) with b := (op1 s).b - 1 } 1) with
          pc := (skip { (op1 s) with b := (op1 s).b - 1 } 1).pc +
            sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) } : Cpu).tick 13) := by
      simp only [Sys, skip, zsim, and_self]
    refine ⟨_, Steps.one hst (by simp only [skip, zsim]), M.sys hS, hS, by simp only [skip, zsim],
      by simp only [skip, zsim], by simp only [skip, zsim], by simp only [skip, zsim], ?_, ?_, ?_⟩
    · show mk16 _ _ = mk16 _ _
      simp only [skip, zsim]
    · show mk16 _ _ = mk16 _ _
      simp only [skip, zsim]
    · rw [if_pos hc]
      refine ⟨T, hT, ?_⟩
      simp only [skip, zsim]
      have hs := sext_val (Int.ofNat T - (Int.ofNat ad + 2)) r1 r2
      rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, hpc]
      show (((ad + 1) % 65536 + 1) % 65536 + (sext _).toNat) % 65536 = T
      rw [hlen] at hlt'
      generalize (sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2)))).toNat = sx at hs ⊢
      simp only [Int.ofNat_eq_coe] at hs r1 r2
      omega
  · have e : djnzTo (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s =
        (skip { (op1 s) with b := (op1 s).b - 1 } 1).tick 8 := by
      unfold djnzTo
      rw [hb1, if_neg hc]
    rw [e] at hst
    have hS : Sys s ((skip { (op1 s) with b := (op1 s).b - 1 } 1).tick 8) := by
      simp only [Sys, skip, zsim, and_self]
    refine ⟨_, Steps.one hst (by simp only [skip, zsim]), M.sys hS, hS, by simp only [skip, zsim],
      by simp only [skip, zsim], by simp only [skip, zsim], by simp only [skip, zsim], ?_, ?_, ?_⟩
    · show mk16 _ _ = mk16 _ _
      simp only [skip, zsim]
    · show mk16 _ _ = mk16 _ _
      simp only [skip, zsim]
    · rw [if_neg hc]
      refine ⟨ad + bs.length, hnext, ?_⟩
      simp only [skip, zsim]
      rw [UInt16.toNat_add, UInt16.toNat_add, hpc, hlen]
      show ((ad + 1) % 65536 + 1) % 65536 = _
      rw [hlen] at hlt'
      omega

/-! ## One byte of the accumulator and one at `HL` -/

/-- What an ALU operation leaves in `A` and in the flags, of `A`, the flags and the operand. -/
def aluA (k a f v : UInt8) : UInt8 := (({ a := a, f := f } : Cpu).alu k v).a
def aluF (k a f v : UInt8) : UInt8 := (({ a := a, f := f } : Cpu).alu k v).f

theorem alu_a (s : Cpu) (k v : UInt8) : (s.alu k v).a = aluA k s.a s.f v := by
  unfold aluA Cpu.alu
  split <;> rfl

theorem alu_f (s : Cpu) (k v : UInt8) : (s.alu k v).f = aluF k s.a s.f v := by
  unfold aluF Cpu.alu
  split <;> rfl

/-- The loop over the bytes, in memory: `n` times, the byte at `D` becomes the operation on it
and the byte at `H`, the flags going from one to the next. -/
def runB (k : UInt8) : UInt8 → ByteArray → Nat → Nat → Nat → ByteArray × UInt8
  | f, m, _, _, 0 => (m, f)
  | f, m, D, H, n + 1 =>
    runB k (aluF k (m.get! D) f (m.get! H)) (m.set! D (aluA k (m.get! D) f (m.get! H))) (D + 1) (H + 1) n

/-- The body of a loop over the bytes: `ld a,(de); op (hl); ld (de),a; inc hl; inc de; djnz`. -/
def loopItems (l : String) (i : Instr) : List Item :=
  [.label l, .ins ⟨.ld, [.a, .mde]⟩, .ins i, .ins ⟨.ld, [.mde, .a]⟩, .ins ⟨.inc, [.hl]⟩, .ins ⟨.inc, [.de]⟩,
   .ins ⟨.djnz, [.imm (.sym l)]⟩]

/-- **One round of the loop.** -/
theorem byte_iter (ok : Z.OK) {j : Nat} {l : String} {i : Instr} {k : UInt8}
    (hexec : ∀ env (s : Cpu) inp, exec env i s inp = some (((op1 s).alu k ((op1 s).rd (op1 s).hl)).tick 7))
    (hfalls : i.falls = true) (hhas : Has Z j (loopItems l i)) {s : Cpu} {D H : Nat} (M : Mach Z s)
    (hat : At Z.addrs (j + 1) s)
    (hrs : s.ramStart.toNat = Z.ramStart) (hde : s.de.toNat = D) (hhl : s.hl.toNat = H) (hram : Z.ramStart ≤ D) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
      s'.mem = s.mem.set! D (aluA k (s.mem.get! D) s.f (s.mem.get! H)) ∧
      s'.f = aluF k (s.mem.get! D) s.f (s.mem.get! H) ∧ s'.hl = s.hl + 1 ∧ s'.de = s.de + 1 ∧ s'.b = s.b - 1 ∧
      (if (s.b - 1 != 0) = true then At Z.addrs j s' else At Z.addrs (j + 7) s') := by
  -- ld a,(de)
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ({ (op1 s) with a := (op1 s).rd (op1 s).de } : Cpu).tick 7 := ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := step_raw ok (hhas.get 1 rfl) M hat c1 (fun _ _ _ => by rw [hc1]; rfl) (by rw [hc1]; simp only [zsim])
  have hS1 : Sys s c1 := by rw [hc1]; simp only [Sys, zsim, and_self]
  have M1 := M.sys hS1
  have e1de : (op1 s).de = s.de := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ha1 : c1.a = s.mem.get! D := by
    rw [hc1]
    simp only [zsim, Cpu.rd, e1de, hde]
  have hf1 : c1.f = s.f := by rw [hc1]; simp only [zsim]
  have hde1 : c1.de = s.de := by rw [hc1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hhl1 : c1.hl = s.hl := by rw [hc1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hb1 : c1.b = s.b := by rw [hc1]; simp only [zsim]
  -- the operation
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ((op1 c1).alu k ((op1 c1).rd (op1 c1).hl)).tick 7 := ⟨_, rfl⟩
  obtain ⟨st2, at3⟩ := step_raw ok (hhas.get 2 rfl) M1 (at2 rfl) c2 (fun _ _ inp => by rw [hc2]; exact hexec _ _ inp)
    (by rw [hc2]; simp only [zsim])
  have hS2 : Sys c1 c2 := by rw [hc2]; simp only [Sys, zsim, and_self]
  have M2 := M1.sys hS2
  have e2hl : (op1 c1).hl = c1.hl := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hv2 : (op1 c1).rd (op1 c1).hl = s.mem.get! H := by
    simp only [Cpu.rd, e2hl, hhl1, hhl, zsim]
    rw [hS1.1]
  have ha2 : c2.a = aluA k (s.mem.get! D) s.f (s.mem.get! H) := by
    rw [hc2, hv2]
    simp only [zsim]
    rw [alu_a]
    simp only [zsim, ha1, hf1]
  have hf2 : c2.f = aluF k (s.mem.get! D) s.f (s.mem.get! H) := by
    rw [hc2, hv2]
    simp only [zsim]
    rw [alu_f]
    simp only [zsim, ha1, hf1]
  have hde2 : c2.de = s.de := by rw [hc2, ← hde1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hhl2 : c2.hl = s.hl := by rw [hc2, ← hhl1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hb2 : c2.b = s.b := by rw [hc2, ← hb1]; simp only [zsim]
  -- ld (de),a
  obtain ⟨c3, hc3⟩ : ∃ c3 : Cpu, c3 = ((op1 c2).wr (op1 c2).de (op1 c2).a).tick 7 := ⟨_, rfl⟩
  obtain ⟨st3, at4⟩ := step_raw ok (hhas.get 3 rfl) M2 (at3 hfalls) c3 (fun _ _ _ => by rw [hc3]; rfl)
    (by rw [hc3]; simp only [zsim])
  have e3de : (op1 c2).de = c2.de := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hS02 : Sys s c2 := hS1.trans hS2
  have hmem3 : c3.mem = s.mem.set! D (aluA k (s.mem.get! D) s.f (s.mem.get! H)) := by
    rw [hc3]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hde2, hde, hS02.2.1, hrs]; exact hram)]
    simp only [zsim, hde2, hde, ha2, hS02.1]
  have hF3 : c3.ramStart = c2.ramStart ∧ c3.halted = c2.halted ∧ c3.sp = c2.sp ∧ c3.f = c2.f ∧ c3.b = c2.b := by
    rw [hc3]
    simp only [zsim, and_self]
  have hde3 : c3.de = s.de := by rw [hc3, ← hde2]; show mk16 _ _ = mk16 _ _; simp only [zsim]
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
  -- inc hl; inc de
  obtain ⟨st4, at5, M4, hS4⟩ := does_raw ok does_inc_hl (hhas.get 4 rfl) M3 (at4 rfl)
  obtain ⟨st5, at6, M5, hS5⟩ := does_raw ok does_inc_de (hhas.get 5 rfl) M4 at5
  obtain ⟨c5, hc5⟩ : ∃ c5 : Cpu, c5 = incDE (incHL c3) := ⟨_, rfl⟩
  rw [← hc5] at st5 at6 M5 hS5
  have hhl5 : c5.hl = s.hl + 1 := by
    rw [hc5, ← hhl3]
    simp only [incDE, incHL, zsim]
  have hde5 : c5.de = s.de + 1 := by
    rw [hc5, ← hde3]
    simp only [incDE, incHL, zsim]
  have hf5 : c5.f = c3.f := by rw [hc5]; simp only [incDE, incHL, zsim]
  have hb5 : c5.b = c3.b := by rw [hc5]; simp only [incDE, incHL, zsim]
  have hS35 : Sys c3 c5 := hS4.trans hS5
  -- djnz
  obtain ⟨c6, st6, M6, hS6, hb6, _, hf6, _, hhl6, hde6, hat6⟩ := djnz_step ok (hhas.get 6 rfl) (hhas.get 0 rfl) M5 at6
  have hbb : c5.b = s.b := by rw [hb5, hF3.2.2.2.2, hb2]
  rw [hbb] at hat6 hb6
  refine ⟨c6, ((((st1.trans st2).trans st3).trans st4).trans st5).trans st6, M6, ?_, ?_, ?_, ?_, ?_, ?_, hb6, hat6⟩
  · rw [hS6.2.2.2, hS35.2.2.2, hF3.2.2.1, hS02.2.2.2]
  · rw [hS6.2.1, hS35.2.1, hF3.1, hS02.2.1]
  · rw [hS6.1, hS35.1, hmem3]
  · rw [hf6, hf5, hF3.2.2.2.1, hf2]
  · rw [hhl6, hhl5]
  · rw [hde6, hde5]

theorem b_sub1 (b : UInt8) (n : Nat) (h : b.toNat = n + 1) : (b - 1).toNat = n ∧ ((b - 1 != 0) = true ↔ n ≠ 0) := by
  have hl := b.toNat_lt
  have e : (b - 1).toNat = n := by
    rw [UInt8.toNat_sub]
    show (2 ^ 8 - 1 + b.toNat) % 2 ^ 8 = n
    omega
  refine ⟨e, ?_⟩
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h1 h2
    exact h1 (UInt8.toNat_inj.mp (by rw [e, h2]; rfl))
  · intro h1 h2
    have := congrArg UInt8.toNat h2
    rw [e] at this
    exact h1 this

/-- **The loop**: `B` rounds, as `runB` has them. -/
theorem byte_loop (ok : Z.OK) {j : Nat} {l : String} {i : Instr} {k : UInt8}
    (hexec : ∀ env (s : Cpu) inp, exec env i s inp = some (((op1 s).alu k ((op1 s).rd (op1 s).hl)).tick 7))
    (hfalls : i.falls = true) (hhas : Has Z j (loopItems l i)) :
    ∀ (n : Nat) (s : Cpu) (D H : Nat), Mach Z s → At Z.addrs (j + 1) s → s.ramStart.toNat = Z.ramStart →
      s.de.toNat = D → s.hl.toNat = H → s.b.toNat = n + 1 → Z.ramStart ≤ D → D + n + 1 ≤ 65536 →
      H + n + 1 ≤ 65536 →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (j + 7) s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem = (runB k s.f s.mem D H (n + 1)).1 ∧ s'.f = (runB k s.f s.mem D H (n + 1)).2 := by
  intro n
  induction n with
  | zero =>
    intro s D H M hat hrs hde hhl hb hram hbD hbH
    obtain ⟨s1, st, M1, hsp, hr, hmem, hf, _, _, _, hat1⟩ := byte_iter ok hexec hfalls hhas M hat hrs hde hhl hram
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat1
    exact ⟨s1, st, M1, hat1, hsp, hr, hmem, hf⟩
  | succ n ih =>
    intro s D H M hat hrs hde hhl hb hram hbD hbH
    obtain ⟨s1, st, M1, hsp, hr, hmem, hf, hhl1, hde1, hb1, hat1⟩ := byte_iter ok hexec hfalls hhas M hat hrs hde hhl hram
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat1
    have at1 := at_label ok (hhas.get 0 rfl) hat1
    obtain ⟨s', st', M', at', hsp', hr', hmem', hf'⟩ := ih s1 (D + 1) (H + 1) M1 at1 (by rw [hr]; exact hrs)
      (by rw [hde1, UInt16.toNat_add, hde]; show (D + 1) % 65536 = _; omega)
      (by rw [hhl1, UInt16.toNat_add, hhl]; show (H + 1) % 65536 = _; omega)
      (by rw [hb1]; exact (b_sub1 s.b (n + 1) hb).1) (by omega) (by omega) (by omega)
    refine ⟨s', st.trans st', M', at', by rw [hsp', hsp], by rw [hr', hr], ?_, ?_⟩
    · rw [hmem', hf, hmem]
      rfl
    · rw [hf', hf, hmem]
      rfl

/-- The loop writes the `n` bytes from `D` only. -/
theorem runB_far (k : UInt8) : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H x : Nat), x < D ∨ D + n ≤ x →
    (runB k f m D H n).1.get! x = m.get! x
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, f, m, D, H, x, hx => by
    rw [runB, runB_far k n _ _ _ _ x (by omega), getBang_set _ _ _ _ (by omega)]

theorem runB_size (k : UInt8) : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat),
    (runB k f m D H n).1.size = m.size
  | 0, _, _, _, _ => rfl
  | n + 1, f, m, D, H => by rw [runB, runB_size k n, set_size]

/-! ## `or` -/

theorem aluA_or (a f v : UInt8) : aluA 6 a f v = a ||| v := rfl

theorem or_bytes (a0 b0 A B : Nat) (ha : a0 < 256) (hb : b0 < 256) :
    (a0 + 256 * A) ||| (b0 + 256 * B) = (a0 ||| b0) + 256 * (A ||| B) := by
  have hab : a0 ||| b0 < 2 ^ 8 := Nat.or_lt_two_pow ha hb
  have e1 : a0 + 256 * A = A <<< 8 ||| a0 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (show a0 < 2 ^ 8 from ha), Nat.shiftLeft_eq]
    omega
  have e2 : b0 + 256 * B = B <<< 8 ||| b0 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (show b0 < 2 ^ 8 from hb), Nat.shiftLeft_eq]
    omega
  have e3 : (a0 ||| b0) + 256 * (A ||| B) = (A ||| B) <<< 8 ||| (a0 ||| b0) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hab, Nat.shiftLeft_eq]
    omega
  rw [e1, e2, e3, Nat.shiftLeft_or_distrib]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or]
  cases Nat.testBit a0 i <;> cases Nat.testBit b0 i <;> cases (A <<< 8).testBit i <;> cases (B <<< 8).testBit i <;> rfl

/-- The loop with `or`: the `n` bytes at `D` are those that were there, or-ed with those at `H`
(which are not among them). -/
theorem runB_or : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat), m.size = 65536 → D + n ≤ 65536 →
    H + n ≤ 65536 → (∀ i, i < n → H + i < D ∨ D + n ≤ H + i) →
    IR.Sem.rd (runB 6 f m D H n).1 D n = IR.Sem.rd m D n ||| IR.Sem.rd m H n
  | 0, _, _, _, _, _, _, _, _ => by simp [runB, IR.Sem.rd]
  | n + 1, f, m, D, H, hsz, hD, hH, hap => by
    rw [runB, IR.Sem.rd, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
      Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runB_far 6 n _ _ _ _ D (Or.inl (by omega)), getBang_same _ _ _ (by omega),
      runB_or n _ _ (D + 1) (H + 1) (by rw [set_size]; exact hsz) (by omega) (by omega)
        (fun i hi => by have := hap (i + 1) (by omega); omega)]
    have h0 := hap 0 (by omega)
    rw [rd_congr m _ (D + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by
        have := hap (x - H) (by omega)
        omega))]
    rw [or_bytes _ _ _ _ (m.get! D).toNat_lt (m.get! H).toNat_lt, aluA_or, UInt8.toNat_or]

theorem does_ld_b_4 : Does ⟨.ld, [.b, .imm (.num 4)]⟩ (ldB 4) := does_ld_b 4

theorem ldB_f (v : Nat) (s : Cpu) : (ldB v s).f = s.f := by simp only [ldB, zsim]
theorem ldB_a (v : Nat) (s : Cpu) : (ldB v s).a = s.a := by simp only [ldB, zsim]
theorem ldB_hl (v : Nat) (s : Cpu) : (ldB v s).hl = s.hl := by
  show mk16 _ _ = mk16 _ _
  simp only [ldB, zsim]

/-- A routine that is `ld b,4`, `ld de,rt_acc`, then a loop over the bytes. -/
def bytewiseItems (name : String) (pre : List Item) (i : Instr) : List Item :=
  [.label s!"rt_{name}64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym s!"rt_{name}w")]⟩,
   .label s!"rt_{name}32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
   .label s!"rt_{name}w", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++ pre ++
  loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]

/-- **`rt_or32`**: the accumulator's four bytes are or-ed with those at `HL`; nothing else is written. -/
theorem rt_or32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k (bytewiseItems "or" [] ⟨.or, [.mhl]⟩)) :
    RtAcc Z "rt_or32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.binOp .or 4 (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 7) (loopItems "rt_orw_l" ⟨.or, [.mhl]⟩) :=
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
  obtain ⟨c3, st3, M3, at14, hsp3, hr3, hmem3, hf3⟩ := byte_loop ok (k := 6) (fun _ _ _ => rfl) rfl hL 3 c2 Z.acc
    s.hl.toNat M2 at8 (by rw [hS02.2.1]; exact hrs) hdev (by rw [hhl2, ldB_hl]) (by rw [hb2, ldB_b 4 (by decide)]) hram.1
    (by omega) (by omega)
  obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 14 rfl) M3 at14
  rw [hS02.1] at hmem3
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 4 ≤ x → c3.mem.get! x = s.mem.get! x := fun x hx => by
    rw [hmem3]
    exact runB_far 6 4 _ _ _ _ x hx
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
    rw [hmem', hmem3, runB_or 4 _ _ _ _ hmsz (by omega) hb (fun i hi => by have := (hap i hi).1; omega)]
    show _ = (_ ||| _) % 2 ^ (8 * 4)
    rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow (rd_lt _ _ _) (rd_lt _ _ _))]
  · intro x _ _ hx
    rw [hmem']
    exact hfar x (by omega)

#guard inRuntime (bytewiseItems "or" [] ⟨.or, [.mhl]⟩)

end

end Ember.Proof.Z80Gen
