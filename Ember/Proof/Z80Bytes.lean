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

/-! ## `adc` and `sbc`: the carry from one byte to the next -/

/-- The carry in the flags, as a number. -/
def cin (f : UInt8) : Nat := if (f &&& FC != 0) = true then 1 else 0

theorem cin_le (f : UInt8) : cin f ≤ 1 := by unfold cin; split <;> omega

theorem adc_val (a f v : UInt8) : (aluA 1 a f v).toNat = (a.toNat + v.toNat + cin f) % 256 := by
  show (add8 a v (f &&& FC != 0)).1.toNat = _
  have ha := a.toNat_lt
  have hv := v.toNat_lt
  unfold cin
  cases hc : (f &&& FC != 0) <;>
    simp only [add8, UInt16.toNat_toUInt8, UInt16.toNat_add, UInt8.toNat_toUInt16, Bool.false_eq_true, if_false, if_true] <;>
    (first
      | (show (((a.toNat + v.toNat) % 65536 + 0) % 65536) % 256 = _; omega)
      | (show (((a.toNat + v.toNat) % 65536 + 1) % 65536) % 256 = _; omega))

theorem add8_c (a v : UInt8) (c : Bool) :
    ((add8 a v c).2 &&& FC != 0) = decide (255 < a.toNat + v.toNat + (if c = true then 1 else 0)) := by
  have ha := a.toNat_lt
  have hv := v.toNat_lt
  rw [flagC_bit]
  cases c
  · simp only [add8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
    simp [FZ, FH, FPV, FC, Nat.testBit]
    rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_add, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16]
    show 255 < (a.toNat + v.toNat) % 65536 ↔ _
    omega
  · simp only [add8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
    simp [FZ, FH, FPV, FC, Nat.testBit]
    rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_add, UInt16.toNat_add, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16]
    show 255 < ((a.toNat + v.toNat) % 65536 + 1) % 65536 ↔ _
    omega

theorem adc_c (a f v : UInt8) : cin (aluF 1 a f v) = (a.toNat + v.toNat + cin f) / 256 := by
  have ha := a.toNat_lt
  have hv := v.toNat_lt
  have hc1 := cin_le f
  show (if ((add8 a v (f &&& FC != 0)).2 &&& FC != 0) = true then 1 else 0) = _
  rw [add8_c]
  show _ = (a.toNat + v.toNat + cin f) / 256
  have e : (if (f &&& FC != 0) = true then 1 else 0) = cin f := rfl
  rw [e]
  by_cases h : 255 < a.toNat + v.toNat + cin f
  · simp only [h, decide_true, if_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

theorem sbc_val (a f v : UInt8) : (aluA 3 a f v).toNat = (a.toNat + 512 - v.toNat - cin f) % 256 := by
  show (sub8 a v (f &&& FC != 0)).1.toNat = _
  have ha := a.toNat_lt
  have hv := v.toNat_lt
  unfold cin
  cases hc : (f &&& FC != 0)
  · simp only [sub8, UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16, Bool.false_eq_true, if_false]
    show ((2 ^ 16 - 0 + (2 ^ 16 - v.toNat + a.toNat) % 2 ^ 16) % 2 ^ 16) % 256 = _
    omega
  · simp only [sub8, UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16, if_true]
    show ((2 ^ 16 - 1 + (2 ^ 16 - v.toNat + a.toNat) % 2 ^ 16) % 2 ^ 16) % 256 = _
    omega

theorem sub8_cc (a v : UInt8) (c : Bool) :
    ((sub8 a v c).2 &&& FC != 0) = decide (a.toNat < v.toNat + (if c = true then 1 else 0)) := by
  have ha := a.toNat_lt
  have hv := v.toNat_lt
  rw [flagC_bit]
  cases c
  · simp only [sub8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
    simp [FZ, FH, FPV, FN, FC, Nat.testBit]
    rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_sub, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16]
    show 255 < (2 ^ 16 - v.toNat + a.toNat) % 2 ^ 16 ↔ _
    omega
  · simp only [sub8, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and, bit_testBit]
    simp [FZ, FH, FPV, FN, FC, Nat.testBit]
    rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_sub, UInt16.toNat_sub, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16]
    show 255 < (2 ^ 16 - 1 + (2 ^ 16 - v.toNat + a.toNat) % 2 ^ 16) % 2 ^ 16 ↔ _
    omega

theorem sbc_c (a f v : UInt8) : cin (aluF 3 a f v) = if a.toNat < v.toNat + cin f then 1 else 0 := by
  show (if ((sub8 a v (f &&& FC != 0)).2 &&& FC != 0) = true then 1 else 0) = _
  rw [sub8_cc]
  have e : (if (f &&& FC != 0) = true then 1 else 0) = cin f := rfl
  rw [e]
  by_cases h : a.toNat < v.toNat + cin f
  · simp only [h, decide_true, if_true]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]

/-- The loop with `adc`: the `n` bytes at `D`, with the carry out above them, are the sum of
those that were there, those at `H` and the carry in. -/
theorem runB_add : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat), m.size = 65536 → D + n ≤ 65536 →
    H + n ≤ 65536 → (∀ i, i < n → H + i < D ∨ D + n ≤ H + i) →
    IR.Sem.rd (runB 1 f m D H n).1 D n + 2 ^ (8 * n) * cin (runB 1 f m D H n).2 =
      IR.Sem.rd m D n + IR.Sem.rd m H n + cin f
  | 0, _, _, _, _, _, _, _, _ => by simp [runB, IR.Sem.rd]
  | n + 1, f, m, D, H, hsz, hD, hH, hap => by
    rw [runB, IR.Sem.rd, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
      Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runB_far 1 n _ _ _ _ D (Or.inl (by omega)), getBang_same _ _ _ (by omega)]
    have ih := runB_add n (aluF 1 (m.get! D) f (m.get! H)) (m.set! D (aluA 1 (m.get! D) f (m.get! H))) (D + 1) (H + 1)
      (by rw [set_size]; exact hsz) (by omega) (by omega) (fun i hi => by have := hap (i + 1) (by omega); omega)
    have h0 := hap 0 (by omega)
    rw [rd_congr m _ (D + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by
        have := hap (x - H) (by omega)
        omega))] at ih
    have hv := adc_val (m.get! D) f (m.get! H)
    have hc := adc_c (m.get! D) f (m.get! H)
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl,
      Nat.mul_comm (2 ^ (8 * n)) 256, Nat.mul_assoc]
    generalize 2 ^ (8 * n) * cin (runB 1 _ _ (D + 1) (H + 1) n).2 = P at ih ⊢
    omega

/-- The loop with `sbc`: the `n` bytes at `D` are those that were there less those at `H` and
the borrow in, the borrow out above them. -/
theorem runB_sub : ∀ (n : Nat) (f : UInt8) (m : ByteArray) (D H : Nat), m.size = 65536 → D + n ≤ 65536 →
    H + n ≤ 65536 → (∀ i, i < n → H + i < D ∨ D + n ≤ H + i) →
    IR.Sem.rd (runB 3 f m D H n).1 D n + IR.Sem.rd m H n + cin f =
      IR.Sem.rd m D n + 2 ^ (8 * n) * cin (runB 3 f m D H n).2
  | 0, _, _, _, _, _, _, _, _ => by simp [runB, IR.Sem.rd]
  | n + 1, f, m, D, H, hsz, hD, hH, hap => by
    rw [runB, IR.Sem.rd, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
      Nat.mod_eq_of_lt (show H < 65536 by omega)]
    rw [runB_far 3 n _ _ _ _ D (Or.inl (by omega)), getBang_same _ _ _ (by omega)]
    have ih := runB_sub n (aluF 3 (m.get! D) f (m.get! H)) (m.set! D (aluA 3 (m.get! D) f (m.get! H))) (D + 1) (H + 1)
      (by rw [set_size]; exact hsz) (by omega) (by omega) (fun i hi => by have := hap (i + 1) (by omega); omega)
    have h0 := hap 0 (by omega)
    rw [rd_congr m _ (D + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by omega)),
      rd_congr m _ (H + 1) n (by omega) (fun x h1 h2 => getBang_set _ _ _ _ (by
        have := hap (x - H) (by omega)
        omega))] at ih
    have hv := sbc_val (m.get! D) f (m.get! H)
    have hc := sbc_c (m.get! D) f (m.get! H)
    have ha := (m.get! D).toNat_lt
    have hb := (m.get! H).toNat_lt
    have hc1 := cin_le f
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl,
      Nat.mul_comm (2 ^ (8 * n)) 256, Nat.mul_assoc]
    generalize 2 ^ (8 * n) * cin (runB 3 _ _ (D + 1) (H + 1) n).2 = P at ih ⊢
    split at hc <;> omega

theorem orA_cin (s : Cpu) : cin (orA s).f = 0 := by
  have h : (orA s).flag FC = false := by
    simp only [orA, zsim]
    exact alu6_flag _ _
  show (if ((orA s).f &&& FC != 0) = true then 1 else 0) = 0
  have h' : ((orA s).f &&& FC != 0) = false := h
  rw [h']
  rfl

theorem orA_b (s : Cpu) : (orA s).b = s.b := by simp only [orA, zsim]
theorem orA_hl (s : Cpu) : (orA s).hl = s.hl := by simp only [orA, zsim]
theorem orA_de (s : Cpu) : (orA s).de = s.de := by simp only [orA, zsim]

/-- **A routine that clears the carry and goes through the four bytes with it**: what the loop
gives from a clear carry is what the routine leaves in the accumulator; nothing else is written. -/
theorem bytewise_carry_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} {name : String} {i : Instr}
    {kk : UInt8} {g : Nat → Nat → Nat}
    (hexec : ∀ env (s : Cpu) inp, exec env i s inp = some (((op1 s).alu kk ((op1 s).rd (op1 s).hl)).tick 7))
    (hfalls : i.falls = true) (hhas : Has Z k (bytewiseItems name [.ins ⟨.or, [.a]⟩] i))
    (hval : ∀ (f : UInt8) (m : ByteArray) (H : Nat), cin f = 0 → m.size = 65536 → H + 4 ≤ 65536 →
      (∀ j, j < 4 → H + j < Z.acc ∨ Z.acc + 4 ≤ H + j) →
      IR.Sem.rd (runB kk f m Z.acc H 4).1 Z.acc 4 = g (IR.Sem.rd m Z.acc 4) (IR.Sem.rd m H 4)) :
    RtAcc Z s!"rt_{name}32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = g (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 8) (loopItems s!"rt_{name}w_l" i) :=
    Has.pre (l2 := [.ins ⟨.ret, []⟩]) hhas.tail.tail.tail.tail.tail.tail.tail.tail
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_b_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hde2, hhl2, _, _, hb2, hf2⟩ := ld_de_imm ok (hhas.get 6 rfl) M1 at6
  obtain ⟨st3, at8, M3, hS3⟩ := does_raw ok does_or_a (hhas.get 7 rfl) M2 at7
  have hdev : (orA c2).de.toNat = Z.acc := by
    rw [orA_de, hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hS03 : Sys s (orA c2) := (hS1.trans hS2).trans hS3
  have at9 := at_label ok (hL.get 0 rfl) at8
  obtain ⟨c4, st4, M4, at15, hsp4, hr4, hmem4, hf4⟩ := byte_loop ok hexec hfalls hL 3 (orA c2) Z.acc
    s.hl.toNat M3 at9 (by rw [hS03.2.1]; exact hrs) hdev (by rw [orA_hl, hhl2, ldB_hl])
    (by rw [orA_b, hb2, ldB_b 4 (by decide)]) hram.1 (by omega) (by omega)
  obtain ⟨c', st5, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 15 rfl) M4 at15
  rw [hS03.1] at hmem4
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 4 ≤ x → c4.mem.get! x = s.mem.get! x := fun x hx => by
    rw [hmem4]
    exact runB_far kk 4 _ _ _ _ x hx
  refine ⟨c', (((st1.trans st2).trans st3).trans st4).trans st5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp4, hS03.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega))
  · rw [hsp', hsp4, hS03.2.2.2]
  · rw [hh']
    exact M4.2
  · rw [hrs', hr4, hS03.2.1]
  · rw [hmem', hmem4, runB_size]
    exact hmsz
  · show IR.Sem.rd c'.mem Z.acc 4 = _
    rw [hmem', hmem4]
    exact hval _ _ _ (orA_cin c2) hmsz hb (fun j hj => by have := (hap j hj).1; omega)
  · intro x _ _ hx
    rw [hmem']
    exact hfar x (by omega)

/-- **`rt_add32`**: the accumulator's four bytes are their sum with those at `HL`, modulo 2³². -/
theorem rt_add32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k (bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩)) :
    RtAcc Z "rt_add32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.binOp .add 4 (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) :=
  bytewise_carry_ok ok hsz (kk := 1) (fun _ _ _ => rfl) rfl hhas (fun f m H hc hm hH hap => by
    have ha := ok.accRam
    have h := runB_add 4 f m Z.acc H hm (by omega) hH hap
    have h1 := rd_lt (runB 1 f m Z.acc H 4).1 Z.acc 4
    have h2 := cin_le (runB 1 f m Z.acc H 4).2
    rw [hc] at h
    show _ = (_ + _) % 2 ^ (8 * 4)
    rw [show (2 : Nat) ^ (8 * 4) = 4294967296 from rfl] at h h1 ⊢
    omega)

/-- **`rt_sub32`**: the accumulator's four bytes are theirs less those at `HL`, modulo 2³². -/
theorem rt_sub32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k (bytewiseItems "sub" [.ins ⟨.or, [.a]⟩] ⟨.sbc, [.a, .mhl]⟩)) :
    RtAcc Z "rt_sub32" (HLApart Z 4)
      (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.binOp .sub 4 (IR.Sem.rd s.mem Z.acc 4) (IR.Sem.rd s.mem s.hl.toNat 4)) :=
  bytewise_carry_ok ok hsz (kk := 3) (fun _ _ _ => rfl) rfl hhas (fun f m H hc hm hH hap => by
    have ha := ok.accRam
    have h := runB_sub 4 f m Z.acc H hm (by omega) hH hap
    have h1 := rd_lt (runB 3 f m Z.acc H 4).1 Z.acc 4
    have h2 := cin_le (runB 3 f m Z.acc H 4).2
    have h3 := rd_lt m Z.acc 4
    have h4 := rd_lt m H 4
    rw [hc] at h
    show _ = (_ + 2 ^ (8 * 4) - _) % 2 ^ (8 * 4)
    rw [show (2 : Nat) ^ (8 * 4) = 4294967296 from rfl] at h h1 h3 h4 ⊢
    omega)

#guard inRuntime (bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩)
#guard inRuntime (bytewiseItems "sub" [.ins ⟨.or, [.a]⟩] ⟨.sbc, [.a, .mhl]⟩)

/-! ## `rt_shr8` -/

/-- **`ret z`**: it returns when `Z` is set, and goes on to the next item when not. -/
theorem ret_z_step (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ret, [.z]⟩)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ s'.mem = s.mem ∧ s'.halted = s.halted ∧ s'.ramStart = s.ramStart ∧ s'.a = s.a ∧
      s'.b = s.b ∧ s'.c = s.c ∧ s'.hl = s.hl ∧
      (if s.flag FZ = true then s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 else At Z.addrs (k + 1) s' ∧ s'.sp = s.sp) := by
  obtain ⟨ad, had, hpcad⟩ := hat
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = (if (op1 s).cond 1 then (retTo (op1 s)).tick 11 else (op1 s).tick 5) :=
    ⟨_, rfl⟩
  have hst := fun inp => (step_item ok.placed M.1 hk had hpcad M.2 (inp := inp) (s' := c4) (by rw [hc4]; rfl)).1
  have hcond : (op1 s).cond 1 = s.flag FZ := cond_op1 s 1
  by_cases hz : s.flag FZ = true
  · rw [hcond, hz, if_pos rfl] at hc4
    refine ⟨c4, Steps.one hst (by rw [hc4]; simp only [retTo, zsim]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; simp only [retTo, zsim]
    · rw [hc4]; show mk16 _ _ = mk16 _ _; simp only [retTo, zsim]
    · rw [if_pos hz]
      refine ⟨?_, ?_⟩
      · rw [hc4]; simp only [retTo, zsim]
      · rw [hc4]; simp only [retTo, zsim]
  · have hz' : s.flag FZ = false := by simpa using hz
    rw [hcond, hz'] at hc4
    simp only [Bool.false_eq_true, if_false] at hc4
    obtain ⟨bs, hbs, hnext, hlt65⟩ := ok.placed.next M.1 hk had
    have hbs' : bs = [0xC8] := by
      have : Item.encode (.ins ⟨.ret, [.z]⟩) (Z.a.env ad) = .ok [0xC8] := rfl
      rw [this] at hbs
      exact (Except.ok.inj hbs).symm
    refine ⟨c4, Steps.one hst (by rw [hc4]; simp only [zsim]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; simp only [zsim]
    · rw [hc4]; show mk16 _ _ = mk16 _ _; simp only [zsim]
    · rw [if_neg hz]
      refine ⟨⟨ad + 1, by rw [hbs'] at hnext; exact hnext, ?_⟩, by rw [hc4]; simp only [zsim]⟩
      have hb1 := hlt65 (by rw [hbs']; exact List.cons_ne_nil _ _)
      rw [hbs'] at hb1
      have hb1' : ad + 1 < 65536 := hb1
      rw [hc4]
      simp only [zsim]
      rw [UInt16.toNat_add, hpcad]
      show (ad + 1) % 65536 = ad + 1
      omega

def incB (s : Cpu) : Cpu :=
  (((op1 s).inc8 ((op1 s).reg .hl 0)).2.setReg .hl 0 ((op1 s).inc8 ((op1 s).reg .hl 0)).1).tick 4
def decB (s : Cpu) : Cpu :=
  (((op1 s).dec8 ((op1 s).reg .hl 0)).2.setReg .hl 0 ((op1 s).dec8 ((op1 s).reg .hl 0)).1).tick 4

theorem does_inc_b : Does ⟨.inc, [.b]⟩ incB :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, incB, Cpu.inc8, zsim, and_self],
    fun s => by simp only [incB, Cpu.inc8, zsim]⟩
theorem does_dec_b : Does ⟨.dec, [.b]⟩ decB :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, decB, Cpu.dec8, zsim, and_self],
    fun s => by simp only [decB, Cpu.dec8, zsim]⟩

/-- `inc b; dec b`: `B`, `A` and `HL` as they were, `Z` when `B` is zero. -/
theorem incdec_b (s : Cpu) : (decB (incB s)).b = s.b ∧ (decB (incB s)).a = s.a ∧ (decB (incB s)).hl = s.hl ∧
    (decB (incB s)).flag FZ = (s.b == 0) := by
  have hb : (incB s).b = s.b + 1 := by simp only [incB, Cpu.inc8, zsim]
  have e : s.b + 1 - 1 = s.b := by
    apply UInt8.toNat_inj.mp
    have := s.b.toNat_lt
    rw [UInt8.toNat_sub, UInt8.toNat_add]
    show (2 ^ 8 - 1 + (s.b.toNat + 1) % 2 ^ 8) % 2 ^ 8 = _
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [decB, Cpu.dec8, zsim, hb, e]
  · simp only [decB, incB, Cpu.dec8, Cpu.inc8, zsim]
  · show mk16 _ _ = mk16 _ _
    simp only [decB, incB, Cpu.dec8, Cpu.inc8, zsim]
  · show ((decB (incB s)).f &&& FZ != 0) = _
    rw [flagZ_bit]
    simp only [decB, Cpu.dec8, zsim, hb, e, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and,
      bit_testBit]
    simp [FZ, FH, FPV, FN, FC, Nat.testBit]

def shrItems : List Item :=
  [.label "rt_shr8", .ins ⟨.inc, [.b]⟩, .ins ⟨.dec, [.b]⟩, .ins ⟨.ret, [.z]⟩,
   .label "rt_shr8_l", .ins ⟨.srl, [.a]⟩, .ins ⟨.djnz, [.imm (.sym "rt_shr8_l")]⟩, .ins ⟨.ret, []⟩]

#guard inRuntime shrItems

/-- The loop of `rt_shr8`: `B` (not zero) times `srl a`. -/
theorem shr_loop (ok : Z.OK) {k : Nat} (hhas : Has Z k shrItems) :
    ∀ (n : Nat) (s : Cpu), Mach Z s → At Z.addrs (k + 5) s → s.b.toNat = n + 1 →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (k + 7) s' ∧ Sys s s' ∧ s'.a.toNat = s.a.toNat / 2 ^ (n + 1) ∧
        s'.hl = s.hl := by
  intro n
  induction n with
  | zero =>
    intro s M hat hb
    obtain ⟨st1, at6, M1, hS1⟩ := does_raw ok does_srl_a (hhas.get 5 rfl) M hat
    have hb1 : (rotR 7 7 s).b = s.b := by simp only [rotR, Cpu.rot, zsim]
    have hhl1 : (rotR 7 7 s).hl = s.hl := by simp only [rotR, Cpu.rot, zsim]; rfl
    obtain ⟨c2, st2, M2, hS2, _, ha2, _, _, hhl2, _, hat2⟩ := djnz_step ok (hhas.get 6 rfl) (hhas.get 4 rfl) M1 at6
    rw [hb1] at hat2
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat2
    exact ⟨c2, st1.trans st2, M2, hat2, hS1.trans hS2, by rw [ha2, rotR_srl_a], by rw [hhl2, hhl1]⟩
  | succ n ih =>
    intro s M hat hb
    obtain ⟨st1, at6, M1, hS1⟩ := does_raw ok does_srl_a (hhas.get 5 rfl) M hat
    have hb1 : (rotR 7 7 s).b = s.b := by simp only [rotR, Cpu.rot, zsim]
    have hhl1 : (rotR 7 7 s).hl = s.hl := by simp only [rotR, Cpu.rot, zsim]; rfl
    obtain ⟨c2, st2, M2, hS2, hb2, ha2, _, _, hhl2, _, hat2⟩ := djnz_step ok (hhas.get 6 rfl) (hhas.get 4 rfl) M1 at6
    rw [hb1] at hat2 hb2
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat2
    have at5 := at_label ok (hhas.get 4 rfl) hat2
    obtain ⟨s', st', M', at', hS', ha', hhl'⟩ := ih c2 M2 at5 (by rw [hb2]; exact (b_sub1 s.b (n + 1) hb).1)
    refine ⟨s', (st1.trans st2).trans st', M', at', (hS1.trans hS2).trans hS', ?_, by rw [hhl', hhl2, hhl1]⟩
    rw [ha', ha2, rotR_srl_a, Nat.div_div_eq_div_mul, Nat.pow_succ 2 (n + 1), Nat.mul_comm]

/-- **`rt_shr8`**: `A` shifted right by `B`; `HL` and memory as they were. -/
theorem rt_shr8_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k shrItems) :
    RtPure Z "rt_shr8" (fun s s' => s'.a.toNat = s.a.toNat / 2 ^ s.b.toNat ∧ s'.hl = s.hl) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi _ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) s := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_inc_b (hhas.get 1 rfl) M at1
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_dec_b (hhas.get 2 rfl) M1 at2
  obtain ⟨hb, ha, hhl, hfz⟩ := incdec_b s
  have hS02 : Sys s (decB (incB s)) := hS1.trans hS2
  obtain ⟨c3, st3, hm3, hh3, hr3, ha3, hb3, _, hhl3, hcase⟩ := ret_z_step ok (hhas.get 3 rfl) M2 at3
  rw [hfz] at hcase
  by_cases hz : s.b = 0
  · have hz' : (s.b == 0) = true := by simpa using hz
    rw [if_pos hz'] at hcase
    refine ⟨c3, (st1.trans st2).trans st3, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, fun x _ _ => ?_⟩
    · rw [hcase.1, rd16_sys hS02]
    · rw [hcase.2, hS02.2.2.2]
    · rw [hh3, hS02.2.2.1]; exact hh
    · rw [hr3, hS02.2.1]
    · rw [hm3, hS02.1]; exact hmsz
    · rw [ha3, ha, hz]
      show _ = s.a.toNat / 2 ^ 0
      simp
    · rw [hhl3, hhl]
    · rw [hm3, hS02.1]
  · have hz' : ¬ ((s.b == 0) = true) := by simpa using hz
    rw [if_neg hz'] at hcase
    have hbn : s.b.toNat ≠ 0 := fun h => hz (UInt8.toNat_inj.mp (by rw [h]; rfl))
    have M3 : Mach Z c3 := ⟨M2.1.congr hr3 hm3, by rw [hh3]; exact M2.2⟩
    have at5 := at_label ok (hhas.get 4 rfl) hcase.1
    obtain ⟨c4, st4, M4, at7, hS4, ha4, hhl4⟩ := shr_loop ok hhas (s.b.toNat - 1) c3 M3 at5 (by rw [hb3, hb]; omega)
    obtain ⟨c', st5, hpc', hsp', hmem', hh', hrs', _, _, ha'⟩ := ret_raw ok (hhas.get 7 rfl) M4 at7
    have hS03 : Sys s c3 := ⟨by rw [hm3, hS02.1], by rw [hr3, hS02.2.1], by rw [hh3, hS02.2.2.1], by rw [hcase.2, hS02.2.2.2]⟩
    have hS : Sys s c4 := hS03.trans hS4
    refine ⟨c', ((((st1.trans st2).trans st3).trans st4).trans st5), ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, fun x _ _ => ?_⟩
    · rw [hpc', rd16_sys hS]
    · rw [hsp', hS.2.2.2]
    · rw [hh']; exact M4.2
    · rw [hrs', hS.2.1]
    · rw [hmem', hS.1]; exact hmsz
    · rw [ha', ha4, ha3, ha, show s.b.toNat - 1 + 1 = s.b.toNat by omega]
    · apply UInt16.toNat_inj.mp
      rw [hl_toNat, ‹c'.h = c4.h›, ‹c'.l = c4.l›, ← hl_toNat, hhl4, hhl3, hhl]
    · rw [hmem', hS.1]

/-! ## `rt_cmp32` -/

/-- The loop of `rt_cmp32`: a byte of the accumulator less the byte at `HL` and the borrow; the
difference is or-ed into `C` with `AF` kept on the stack meanwhile. -/
def cmpLoop : List Item :=
  [.label "rt_cmpw_l", .ins ⟨.ld, [.a, .mde]⟩, .ins ⟨.sbc, [.a, .mhl]⟩, .ins ⟨.push, [.af]⟩, .ins ⟨.or, [.c]⟩,
   .ins ⟨.ld, [.c, .a]⟩, .ins ⟨.pop, [.af]⟩, .ins ⟨.inc, [.hl]⟩, .ins ⟨.inc, [.de]⟩,
   .ins ⟨.djnz, [.imm (.sym "rt_cmpw_l")]⟩]

/-- **One round of the loop of `rt_cmp32`.**  It writes the two bytes below the stack pointer only. -/
theorem cmp_iter (ok : Z.OK) {j : Nat} (hhas : Has Z j cmpLoop) {s : Cpu} {D H P : Nat} (M : Mach Z s)
    (hat : At Z.addrs (j + 1) s) (hrs : s.ramStart.toNat = Z.ramStart) (hmsz : s.mem.size = 65536)
    (hde : s.de.toNat = D) (hhl : s.hl.toNat = H) (hsp : s.sp.toNat = P) (hP : Z.ramStart + 2 ≤ P) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧ s'.mem.size = 65536 ∧
      (∀ x, x < P - 2 ∨ P ≤ x → s'.mem.get! x = s.mem.get! x) ∧
      s'.f = aluF 3 (s.mem.get! D) s.f (s.mem.get! H) ∧
      s'.c = aluA 3 (s.mem.get! D) s.f (s.mem.get! H) ||| s.c ∧
      s'.hl = s.hl + 1 ∧ s'.de = s.de + 1 ∧ s'.b = s.b - 1 ∧
      (if (s.b - 1 != 0) = true then At Z.addrs j s' else At Z.addrs (j + 10) s') := by
  have hspl := s.sp.toNat_lt
  -- ld a,(de)
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ({ (op1 s) with a := (op1 s).rd (op1 s).de } : Cpu).tick 7 := ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := step_raw ok (hhas.get 1 rfl) M hat c1 (fun _ _ _ => by rw [hc1]; rfl) (by rw [hc1]; simp only [zsim])
  have hS1 : Sys s c1 := by rw [hc1]; simp only [Sys, zsim, and_self]
  have M1 := M.sys hS1
  have e1de : (op1 s).de = s.de := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ha1 : c1.a = s.mem.get! D := by
    rw [hc1]
    simp only [zsim, Cpu.rd, e1de, hde]
  have hF1 : c1.f = s.f ∧ c1.b = s.b ∧ c1.c = s.c := by rw [hc1]; simp only [zsim, and_self]
  have hde1 : c1.de = s.de := by rw [hc1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hhl1 : c1.hl = s.hl := by rw [hc1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  -- sbc a,(hl)
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ((op1 c1).alu 3 ((op1 c1).rd (op1 c1).hl)).tick 7 := ⟨_, rfl⟩
  obtain ⟨st2, at3⟩ := step_raw ok (hhas.get 2 rfl) M1 (at2 rfl) c2 (fun _ _ _ => by rw [hc2]; rfl)
    (by rw [hc2]; simp only [zsim])
  have hS2 : Sys c1 c2 := by rw [hc2]; simp only [Sys, zsim, and_self]
  have M2 := M1.sys hS2
  have e2hl : (op1 c1).hl = c1.hl := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hv2 : (op1 c1).rd (op1 c1).hl = s.mem.get! H := by
    simp only [Cpu.rd, e2hl, hhl1, hhl, zsim]
    rw [hS1.1]
  have ha2 : c2.a = aluA 3 (s.mem.get! D) s.f (s.mem.get! H) := by
    rw [hc2, hv2]
    simp only [zsim]
    rw [← alu3_a, alu_a]
    simp only [zsim, ha1, hF1.1]
  have hf2 : c2.f = aluF 3 (s.mem.get! D) s.f (s.mem.get! H) := by
    rw [hc2, hv2]
    simp only [zsim]
    rw [alu_f]
    simp only [zsim, ha1, hF1.1]
  have hde2 : c2.de = s.de := by rw [hc2, ← hde1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hhl2 : c2.hl = s.hl := by rw [hc2, ← hhl1]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hF2 : c2.b = s.b ∧ c2.c = s.c := by
    rw [hc2, ← hF1.2.1, ← hF1.2.2]
    simp only [zsim, and_self]
  have hS02 : Sys s c2 := hS1.trans hS2
  -- push af
  obtain ⟨c3, hc3⟩ : ∃ c3 : Cpu, c3 = ((op1 c2).push (op1 c2).af).tick 11 := ⟨_, rfl⟩
  obtain ⟨st3, at4⟩ := step_raw ok (hhas.get 3 rfl) M2 (at3 rfl) c3 (fun _ _ _ => by rw [hc3]; rfl)
    (by rw [hc3]; simp only [zsim])
  have hsp2 : c2.sp.toNat = P := by rw [hS02.2.2.2]; exact hsp
  have hpm := push_mem (op1 c2) (op1 c2).af (by simp only [zsim]; omega)
    (by simp only [zsim]; rw [hS02.2.1, hrs, hsp2]; omega)
  simp only [zsim] at hpm
  have hmem3 : c3.mem = IR.Sem.wr s.mem (P - 2) 2 (mk16 c2.a c2.f).toNat := by
    rw [hc3]
    simp only [zsim]
    rw [hpm, hsp2, hS02.1]
    rfl
  have hF3 : c3.ramStart = c2.ramStart ∧ c3.halted = c2.halted ∧ c3.sp = c2.sp - 2 ∧ c3.a = c2.a ∧ c3.f = c2.f ∧
      c3.b = c2.b ∧ c3.c = c2.c := by
    rw [hc3]
    simp only [zsim, and_self]
  have hde3 : c3.de = s.de := by rw [hc3, ← hde2]; simp only [zsim]
  have hhl3 : c3.hl = s.hl := by rw [hc3, ← hhl2]; simp only [zsim]
  have M3 : Mach Z c3 := ⟨Img.of_wr M.1 (by rw [hF3.1, hS02.2.1]) hmem3 (by rw [hrs]; omega) (by omega),
    by rw [hF3.2.1]; exact M2.2⟩
  -- or c; ld c,a
  obtain ⟨st4, at5, M4, hS4⟩ := does_raw ok does_or_c (hhas.get 4 rfl) M3 (at4 rfl)
  obtain ⟨st5, at6, M5, hS5⟩ := does_raw ok does_ld_c_a (hhas.get 5 rfl) M4 at5
  obtain ⟨c5, hc5⟩ : ∃ c5 : Cpu, c5 = ldRA 1 (orC c3) := ⟨_, rfl⟩
  rw [← hc5] at st5 at6 M5 hS5
  have hS35 : Sys c3 c5 := hS4.trans hS5
  have hc5c : c5.c = c2.a ||| s.c := by
    rw [hc5, ldRA1_c]
    simp only [orC, zsim]
    rw [hF3.2.2.2.1, hF3.2.2.2.2.2.2, hF2.2]
  have hb5 : c5.b = s.b := by
    rw [hc5]
    simp only [ldRA, orC, zsim]
    rw [hF3.2.2.2.2.2.1, hF2.1]
  have hde5 : c5.de = s.de := by rw [hc5, ← hde3]; simp only [ldRA, orC, zsim]
  have hhl5 : c5.hl = s.hl := by rw [hc5, ← hhl3]; simp only [ldRA, orC, zsim]
  -- pop af
  obtain ⟨c6, hc6⟩ : ∃ c6 : Cpu, c6 = ({ ({ (op1 c5) with sp := (op1 c5).sp + 2 } : Cpu) with
      a := hi ((op1 c5).rd16 (op1 c5).sp), f := lo ((op1 c5).rd16 (op1 c5).sp) } : Cpu).tick 10 := ⟨_, rfl⟩
  obtain ⟨st6, at7⟩ := step_raw ok (hhas.get 6 rfl) M5 at6 c6 (fun _ _ _ => by rw [hc6]; rfl)
    (by rw [hc6]; simp only [zsim])
  have hsp5 : c5.sp = s.sp - 2 := by rw [hS35.2.2.2, hF3.2.2.1, hS02.2.2.2]
  have hsp5n : c5.sp.toNat = P - 2 := by rw [hsp5, sub2_toNat _ (by omega), hsp]
  have hw : c5.rd16 c5.sp = mk16 c2.a c2.f := by
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by rw [hsp5n]; omega), hsp5n, hS35.1, hmem3,
      rd_wr _ _ _ _ (by rw [hmsz]; omega) (by rw [hmsz]; exact Nat.le_refl _)]
    exact Nat.mod_eq_of_lt (mk16 c2.a c2.f).toNat_lt
  have hF6 : c6.mem = c5.mem ∧ c6.ramStart = c5.ramStart ∧ c6.halted = c5.halted ∧ c6.sp = c5.sp + 2 ∧
      c6.b = c5.b ∧ c6.c = c5.c := by
    rw [hc6]
    simp only [zsim, and_self]
  have hf6 : c6.f = c2.f := by rw [hc6]; simp only [zsim]; rw [hw, lo_mk16]
  have hde6 : c6.de = s.de := by rw [hc6, ← hde5]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hhl6 : c6.hl = s.hl := by rw [hc6, ← hhl5]; show mk16 _ _ = mk16 _ _; simp only [zsim]
  have hsp6 : c6.sp = s.sp := by
    rw [hF6.2.2.2.1, hsp5]
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, sub2_toNat _ (by omega)]
    show (s.sp.toNat - 2 + 2) % 65536 = _
    omega
  have M6 : Mach Z c6 := ⟨M5.1.congr hF6.2.1 hF6.1, by rw [hF6.2.2.1]; exact M5.2⟩
  -- inc hl; inc de
  obtain ⟨st7, at8, M7, hS7⟩ := does_raw ok does_inc_hl (hhas.get 7 rfl) M6 (at7 rfl)
  obtain ⟨st8, at9, M8, hS8⟩ := does_raw ok does_inc_de (hhas.get 8 rfl) M7 at8
  obtain ⟨c8, hc8⟩ : ∃ c8 : Cpu, c8 = incDE (incHL c6) := ⟨_, rfl⟩
  rw [← hc8] at st8 at9 M8 hS8
  have hhl8 : c8.hl = s.hl + 1 := by rw [hc8, ← hhl6]; simp only [incDE, incHL, zsim]
  have hde8 : c8.de = s.de + 1 := by rw [hc8, ← hde6]; simp only [incDE, incHL, zsim]
  have hF8 : c8.f = c6.f ∧ c8.b = c6.b ∧ c8.c = c6.c := by rw [hc8]; simp only [incDE, incHL, zsim, and_self]
  have hS68 : Sys c6 c8 := hS7.trans hS8
  -- djnz
  obtain ⟨c9, st9, M9, hS9, hb9, _, hf9, hc9, hhl9, hde9, hat9⟩ := djnz_step ok (hhas.get 9 rfl) (hhas.get 0 rfl) M8 at9
  have hbb : c8.b = s.b := by rw [hF8.2.1, hF6.2.2.2.2.1, hb5]
  rw [hbb] at hat9 hb9
  have hmem9 : c9.mem = IR.Sem.wr s.mem (P - 2) 2 (mk16 c2.a c2.f).toNat := by
    rw [hS9.1, hS68.1, hF6.1, hS35.1, hmem3]
  refine ⟨c9, (((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9, M9,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb9, hat9⟩
  · rw [hS9.2.2.2, hS68.2.2.2, hsp6]
  · rw [hS9.2.1, hS68.2.1, hF6.2.1, hS35.2.1, hF3.1, hS02.2.1]
  · rw [hmem9, wr_size]
    exact hmsz
  · intro x hx
    rw [hmem9, wr_get_far _ _ _ _ _ (by omega) (by omega)]
  · rw [hf9, hF8.1, hf6, hf2]
  · rw [hc9, hF8.2.2, hF6.2.2.2.2.2, hc5c, ha2]
  · rw [hhl9, hhl8]
  · rw [hde9, hde8]

/-- The loop of `rt_cmp32`, on the flags and `C`: memory is read only. -/
def cmpB : UInt8 → UInt8 → ByteArray → Nat → Nat → Nat → UInt8 × UInt8
  | f, c, _, _, _, 0 => (f, c)
  | f, c, m, D, H, n + 1 =>
    cmpB (aluF 3 (m.get! D) f (m.get! H)) (aluA 3 (m.get! D) f (m.get! H) ||| c) m (D + 1) (H + 1) n

theorem cmpB_congr : ∀ (n : Nat) (f c : UInt8) (m m' : ByteArray) (D H : Nat),
    (∀ i, i < n → m'.get! (D + i) = m.get! (D + i) ∧ m'.get! (H + i) = m.get! (H + i)) →
    cmpB f c m' D H n = cmpB f c m D H n
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, f, c, m, m', D, H, h => by
    have h0 : m'.get! D = m.get! D ∧ m'.get! H = m.get! H := h 0 (by omega)
    rw [cmpB, cmpB, h0.1, h0.2]
    exact cmpB_congr n _ _ m m' (D + 1) (H + 1) (fun i hi => by
      have := h (i + 1) (by omega)
      rw [show D + 1 + i = D + (i + 1) by omega, show H + 1 + i = H + (i + 1) by omega]
      exact this)

/-- **The loop of `rt_cmp32`**: `B` rounds, as `cmpB` has them; it writes the two bytes below the
stack pointer only. -/
theorem cmp_loop (ok : Z.OK) {j : Nat} (hhas : Has Z j cmpLoop) {P : Nat} (hP : Z.ramStart + 2 ≤ P) :
    ∀ (n : Nat) (s : Cpu) (D H : Nat), Mach Z s → At Z.addrs (j + 1) s → s.ramStart.toNat = Z.ramStart →
      s.mem.size = 65536 → s.de.toNat = D → s.hl.toNat = H → s.sp.toNat = P → s.b.toNat = n + 1 →
      D + n + 1 ≤ 65536 → H + n + 1 ≤ 65536 →
      (∀ i, i ≤ n → (D + i < P - 2 ∨ P ≤ D + i) ∧ (H + i < P - 2 ∨ P ≤ H + i)) →
      ∃ s', Steps s s' ∧ Mach Z s' ∧ At Z.addrs (j + 10) s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem.size = 65536 ∧ (∀ x, x < P - 2 ∨ P ≤ x → s'.mem.get! x = s.mem.get! x) ∧
        s'.f = (cmpB s.f s.c s.mem D H (n + 1)).1 ∧ s'.c = (cmpB s.f s.c s.mem D H (n + 1)).2 := by
  intro n
  induction n with
  | zero =>
    intro s D H M hat hrs hmsz hde hhl hsp hb hbD hbH hap
    obtain ⟨s1, st, M1, hsp1, hr, hsz1, hfar, hf, hc, _, _, _, hat1⟩ := cmp_iter ok hhas M hat hrs hmsz hde hhl hsp hP
    have hz : ¬ ((s.b - 1 != 0) = true) := fun h => ((b_sub1 s.b 0 hb).2.mp h) rfl
    rw [if_neg hz] at hat1
    exact ⟨s1, st, M1, hat1, hsp1, hr, hsz1, hfar, hf, hc⟩
  | succ n ih =>
    intro s D H M hat hrs hmsz hde hhl hsp hb hbD hbH hap
    obtain ⟨s1, st, M1, hsp1, hr, hsz1, hfar, hf, hc, hhl1, hde1, hb1, hat1⟩ :=
      cmp_iter ok hhas M hat hrs hmsz hde hhl hsp hP
    have hnz : (s.b - 1 != 0) = true := (b_sub1 s.b (n + 1) hb).2.mpr (by omega)
    rw [if_pos hnz] at hat1
    have at1 := at_label ok (hhas.get 0 rfl) hat1
    obtain ⟨s', st', M', at', hsp', hr', hsz', hfar', hf', hc'⟩ := ih s1 (D + 1) (H + 1) M1 at1 (by rw [hr]; exact hrs)
      hsz1 (by rw [hde1, UInt16.toNat_add, hde]; show (D + 1) % 65536 = _; omega)
      (by rw [hhl1, UInt16.toNat_add, hhl]; show (H + 1) % 65536 = _; omega) (by rw [hsp1]; exact hsp)
      (by rw [hb1]; exact (b_sub1 s.b (n + 1) hb).1) (by omega) (by omega)
      (fun i hi => by
        have := hap (i + 1) (by omega)
        rw [show D + 1 + i = D + (i + 1) by omega, show H + 1 + i = H + (i + 1) by omega]
        exact this)
    have hcong : cmpB s1.f s1.c s1.mem (D + 1) (H + 1) (n + 1) = cmpB s1.f s1.c s.mem (D + 1) (H + 1) (n + 1) :=
      cmpB_congr (n + 1) _ _ s.mem s1.mem (D + 1) (H + 1) (fun i hi => by
        have := hap (i + 1) (by omega)
        exact ⟨hfar _ (by omega), hfar _ (by omega)⟩)
    have e : cmpB s.f s.c s.mem D H (n + 1 + 1) =
        cmpB (aluF 3 (s.mem.get! D) s.f (s.mem.get! H)) (aluA 3 (s.mem.get! D) s.f (s.mem.get! H) ||| s.c) s.mem
          (D + 1) (H + 1) (n + 1) := by rw [cmpB]
    refine ⟨s', st.trans st', M', at', by rw [hsp', hsp1], by rw [hr', hr], hsz',
      fun x hx => by rw [hfar' x hx, hfar x hx], ?_, ?_⟩
    · rw [hf', hcong, hf, hc, e]
    · rw [hc', hcong, hf, hc, e]

theorem u8_or_zero (a b : UInt8) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h0 : a.toNat ||| b.toNat = 0 := by
      have := congrArg UInt8.toNat h
      rw [UInt8.toNat_or] at this
      exact this
    have h1 : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
    have h2 : b.toNat ≤ a.toNat ||| b.toNat := Nat.right_le_or
    exact ⟨UInt8.toNat_inj.mp (by show a.toNat = 0; omega), UInt8.toNat_inj.mp (by show b.toNat = 0; omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- What the loop leaves: the borrow of the `n` bytes at `D` less those at `H`, and `C` zero
when it was and the difference is. -/
theorem cmpB_spec : ∀ (n : Nat) (f c : UInt8) (m : ByteArray) (D H : Nat), D + n ≤ 65536 → H + n ≤ 65536 →
    ∃ R, R < 2 ^ (8 * n) ∧
      R + IR.Sem.rd m H n + cin f = IR.Sem.rd m D n + 2 ^ (8 * n) * cin (cmpB f c m D H n).1 ∧
      ((cmpB f c m D H n).2 = 0 ↔ c = 0 ∧ R = 0)
  | 0, f, c, m, D, H, _, _ => ⟨0, by simp, by simp [cmpB, IR.Sem.rd], by simp [cmpB]⟩
  | n + 1, f, c, m, D, H, hD, hH => by
    obtain ⟨R, hR, heq, hz⟩ := cmpB_spec n (aluF 3 (m.get! D) f (m.get! H)) (aluA 3 (m.get! D) f (m.get! H) ||| c) m
      (D + 1) (H + 1) (by omega) (by omega)
    have hv := sbc_val (m.get! D) f (m.get! H)
    have hc := sbc_c (m.get! D) f (m.get! H)
    have ha := (m.get! D).toNat_lt
    have hb := (m.get! H).toNat_lt
    have hr := (aluA 3 (m.get! D) f (m.get! H)).toNat_lt
    have hc1 := cin_le f
    refine ⟨(aluA 3 (m.get! D) f (m.get! H)).toNat + 256 * R, ?_, ?_, ?_⟩
    · rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl]
      omega
    · rw [cmpB, IR.Sem.rd, IR.Sem.rd, Nat.mod_eq_of_lt (show D < 65536 by omega),
        Nat.mod_eq_of_lt (show H < 65536 by omega)]
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl,
        Nat.mul_comm (2 ^ (8 * n)) 256, Nat.mul_assoc]
      generalize 2 ^ (8 * n) * cin (cmpB _ _ m (D + 1) (H + 1) n).1 = Q at heq ⊢
      split at hc <;> omega
    · rw [cmpB, hz, u8_or_zero]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h2, ?_⟩
        rw [h1, h3]
        rfl
      · rintro ⟨h1, h2⟩
        have h3 : (aluA 3 (m.get! D) f (m.get! H)).toNat = 0 := by omega
        exact ⟨⟨UInt8.toNat_inj.mp h3, h1⟩, by omega⟩

def ldC0 (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 1 (byteOf (Int.ofNat (0 % 256)))).tick 7
theorem does_ld_c_0 : Does ⟨.ld, [.c, .imm (.num 0)]⟩ ldC0 :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldC0, zsim, and_self], fun s => by simp only [ldC0, zsim]⟩

def incC (s : Cpu) : Cpu :=
  (((op1 s).inc8 ((op1 s).reg .hl 1)).2.setReg .hl 1 ((op1 s).inc8 ((op1 s).reg .hl 1)).1).tick 4
def decC (s : Cpu) : Cpu :=
  (((op1 s).dec8 ((op1 s).reg .hl 1)).2.setReg .hl 1 ((op1 s).dec8 ((op1 s).reg .hl 1)).1).tick 4

theorem does_inc_c : Does ⟨.inc, [.c]⟩ incC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, incC, Cpu.inc8, zsim, and_self],
    fun s => by simp only [incC, Cpu.inc8, zsim]⟩
theorem does_dec_c : Does ⟨.dec, [.c]⟩ decC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, decC, Cpu.dec8, zsim, and_self],
    fun s => by simp only [decC, Cpu.dec8, zsim]⟩

/-- `inc c; dec c`: `Z` when `C` is zero, the carry as it was. -/
theorem incdec_c (s : Cpu) : (decC (incC s)).flag FZ = (s.c == 0) ∧ (decC (incC s)).flag FC = s.flag FC := by
  have hc : (incC s).c = s.c + 1 := by simp only [incC, Cpu.inc8, zsim]
  have e : s.c + 1 - 1 = s.c := by
    apply UInt8.toNat_inj.mp
    have := s.c.toNat_lt
    rw [UInt8.toNat_sub, UInt8.toNat_add]
    show (2 ^ 8 - 1 + (s.c.toNat + 1) % 2 ^ 8) % 2 ^ 8 = _
    omega
  constructor
  · show ((decC (incC s)).f &&& FZ != 0) = _
    rw [flagZ_bit]
    simp only [decC, Cpu.dec8, zsim, hc, e, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or, Nat.testBit_and,
      bit_testBit]
    simp [FZ, FH, FPV, FN, FC, Nat.testBit]
  · show ((decC (incC s)).f &&& FC != 0) = (s.f &&& FC != 0)
    rw [flagC_bit, flagC_bit]
    simp only [decC, incC, Cpu.dec8, Cpu.inc8, zsim, szxy, UInt8.toNat_or, UInt8.toNat_and, Nat.testBit_or,
      Nat.testBit_and, bit_testBit]
    simp [FZ, FH, FPV, FN, FC, Nat.testBit]

/-- `ret`, with the flags. -/
theorem ret_raw_f (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ret, []⟩)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 ∧ s'.mem = s.mem ∧ s'.halted = s.halted ∧
      s'.ramStart = s.ramStart ∧ s'.f = s.f := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp)
    (s' := (retTo (op1 s)).tick 10) rfl).1
  refine ⟨_, Steps.one hst rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [retTo, zsim]

/-- The items of `rt_cmp64` and `rt_cmp32`. -/
def cmpItems : List Item :=
  [.label "rt_cmp64", .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym "rt_cmpw")]⟩,
   .label "rt_cmp32", .ins ⟨.ld, [.b, .imm (.num 4)]⟩,
   .label "rt_cmpw", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩, .ins ⟨.ld, [.c, .imm (.num 0)]⟩, .ins ⟨.or, [.a]⟩] ++
  cmpLoop ++ [.ins ⟨.inc, [.c]⟩, .ins ⟨.dec, [.c]⟩, .ins ⟨.ret, []⟩]

#guard inRuntime cmpItems

/-- **`rt_cmp32`**: `Z` when the accumulator's four bytes are those at `HL`, `C` when they are
less.  It keeps `AF` on the stack while it works — two bytes, which the runtime is to have
(`2 ≤ rtK`) — and writes nothing else. -/
theorem rt_cmp32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) (hK : 2 ≤ Z.rtK) {k : Nat}
    (hhas : Has Z k cmpItems) :
    RtPre Z "rt_cmp32" (HLApart Z 4)
      (fun s s' => s'.flag FZ = (IR.Sem.rd s.mem Z.acc 4 == IR.Sem.rd s.mem s.hl.toNat 4) ∧
        s'.flag FC = decide (IR.Sem.rd s.mem Z.acc 4 < IR.Sem.rd s.mem s.hl.toNat 4)) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  have hL : Has Z (k + 9) cmpLoop :=
    Has.pre (l2 := [.ins ⟨.inc, [.c]⟩, .ins ⟨.dec, [.c]⟩, .ins ⟨.ret, []⟩])
      hhas.tail.tail.tail.tail.tail.tail.tail.tail.tail
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at5, M1, hS1⟩ := does_raw ok does_ld_b_4 (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hde2, hhl2, _, _, hb2, hf2⟩ := ld_de_imm ok (hhas.get 6 rfl) M1 at6
  obtain ⟨st3, at8, M3, hS3⟩ := does_raw ok does_ld_c_0 (hhas.get 7 rfl) M2 at7
  obtain ⟨st4, at9, M4, hS4⟩ := does_raw ok does_or_a (hhas.get 8 rfl) M3 at8
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = orA (ldC0 c2) := ⟨_, rfl⟩
  rw [← hc4] at st4 at9 M4 hS4
  have hS04 : Sys s c4 := ((hS1.trans hS2).trans hS3).trans hS4
  have hde4 : c4.de.toNat = Z.acc := by
    rw [hc4, orA_de]
    have : (ldC0 c2).de = c2.de := by simp only [ldC0, zsim]
    rw [this, hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hhl4 : c4.hl = s.hl := by
    rw [hc4, orA_hl]
    have : (ldC0 c2).hl = c2.hl := by simp only [ldC0, zsim]
    rw [this, hhl2, ldB_hl]
  have hb4 : c4.b.toNat = 3 + 1 := by
    rw [hc4, orA_b]
    have : (ldC0 c2).b = c2.b := by simp only [ldC0, zsim]
    rw [this, hb2, ldB_b 4 (by decide)]
  have hcc4 : c4.c = 0 := by
    rw [hc4]
    have : (orA (ldC0 c2)).c = (ldC0 c2).c := by simp only [orA, zsim]
    rw [this]
    simp only [ldC0, zsim]
    rfl
  have hcin4 : cin c4.f = 0 := by rw [hc4]; exact orA_cin _
  have at10 := at_label ok (hL.get 0 rfl) at9
  have hspP : c4.sp.toNat = s.sp.toNat := by rw [hS04.2.2.2]
  obtain ⟨c5, st5, M5, at19, hsp5, hr5, hsz5, hfar, hf5, hc5⟩ := cmp_loop ok hL (P := s.sp.toNat) (by omega) 3 c4
    Z.acc s.hl.toNat M4 at10 (by rw [hS04.2.1]; exact hrs) (by rw [hS04.1]; exact hmsz) hde4 (by rw [hhl4]) hspP hb4
    (by omega) (by omega) (fun i hi => by
      have := hap i (by omega)
      exact ⟨by omega, by omega⟩)
  rw [hS04.1] at hfar hf5 hc5
  obtain ⟨st6, at20, M6, hS6⟩ := does_raw ok does_inc_c (hhas.get 19 rfl) M5 at19
  obtain ⟨st7, at21, M7, hS7⟩ := does_raw ok does_dec_c (hhas.get 20 rfl) M6 at20
  obtain ⟨hfz, hfc⟩ := incdec_c c5
  obtain ⟨c', st8, hpc', hsp', hmem', hh', hrs', hf'⟩ := ret_raw_f ok (hhas.get 21 rfl) M7 at21
  have hS57 : Sys c5 (decC (incC c5)) := hS6.trans hS7
  obtain ⟨R, hR, heq, hz⟩ := cmpB_spec 4 c4.f c4.c s.mem Z.acc s.hl.toNat (by omega) hb
  have hf5' : c5.f = (cmpB c4.f c4.c s.mem Z.acc s.hl.toNat 4).1 := hf5
  have hc5' : c5.c = (cmpB c4.f c4.c s.mem Z.acc s.hl.toNat 4).2 := hc5
  rw [← hf5', hcin4] at heq
  rw [← hc5', hcc4] at hz
  have hA := rd_lt s.mem Z.acc 4
  have hB := rd_lt s.mem s.hl.toNat 4
  have hc1 := cin_le c5.f
  rw [show (2 : Nat) ^ (8 * 4) = 4294967296 from rfl] at hR heq hA hB
  have hflags : ∀ t : Cpu, t.f = (decC (incC c5)).f →
      t.flag FZ = (IR.Sem.rd s.mem Z.acc 4 == IR.Sem.rd s.mem s.hl.toNat 4) ∧
      t.flag FC = decide (IR.Sem.rd s.mem Z.acc 4 < IR.Sem.rd s.mem s.hl.toNat 4) := by
    intro t ht
    have e1 : t.flag FZ = (decC (incC c5)).flag FZ := by simp only [Cpu.flag, ht]
    have e2 : t.flag FC = (decC (incC c5)).flag FC := by simp only [Cpu.flag, ht]
    rw [e1, e2, hfz, hfc]
    constructor
    · rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      rw [hz]
      constructor
      · rintro ⟨_, h⟩
        omega
      · intro h
        exact ⟨rfl, by omega⟩
    · have hcf : c5.flag FC = decide (cin c5.f = 1) := by
        show (c5.f &&& FC != 0) = _
        unfold cin
        cases (c5.f &&& FC != 0) <;> simp
      rw [hcf]
      congr 1
      apply propext
      constructor <;> intro h <;> omega
  refine ⟨c', (((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8), ?_, ?_, ?_, ?_,
    ?_, hflags c' hf', fun x hx _ => ?_⟩
  · rw [hpc', hS57.2.2.2, hsp5, hS04.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => by rw [hS57.1]; exact hfar x (by omega))
  · rw [hsp', hS57.2.2.2, hsp5, hS04.2.2.2]
  · rw [hh']
    exact M7.2
  · rw [hrs', hS57.2.1, hr5, hS04.2.1]
  · rw [hmem', hS57.1]
    exact hsz5
  · rw [hmem', hS57.1]
    exact hfar x (by omega)

end

end Ember.Proof.Z80Gen
