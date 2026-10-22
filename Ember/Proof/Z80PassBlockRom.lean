import Ember.Proof.Z80PassBlock

/-!
# Ember.Proof.Z80PassBlockRom — a routine of the runtime reading a literal of the ROM, in both machines (plan M7.3)

`ld hl,lit` before the call: each machine's `HL` points to the literal in
its own image (the two literals the same bytes, at other addresses), so
`H` and `L` are free in the relation; the routine reads the bytes there,
the same in both, and writes in the RAM kept equal.  The loops are
followed in both machines at once (`HL` of each).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

/-- **All the rounds of an `ldir` from the ROM to the RAM kept equal**, in both machines, `H` and `L`
free: the bytes each reads from its own `HL` on the same, below the RAM; the bytes written in it. -/
theorem ldir_rom_rounds (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {kA kB : Nat}
    (hA : A.items[kA]? = some (.ins ⟨.ldir, []⟩)) (hB : B.items[kB]? = some (.ins ⟨.ldir, []⟩)) :
    ∀ (n : Nat) (x y : Cpu × D.W), Sync D A B lo hi G kA kB true true x y → x.1.bc.toNat = n + 1 →
      x.1.hl.toNat + n + 1 ≤ lo → y.1.hl.toNat + n + 1 ≤ lo →
      (∀ i, i ≤ n → x.1.mem.get! (x.1.hl.toNat + i) = y.1.mem.get! (y.1.hl.toNat + i)) →
      lo ≤ x.1.de.toNat → x.1.de.toNat + n + 1 ≤ hi →
      Sync D A B lo hi G (kA + 1) (kB + 1) true true (mrun D (n + 1) x) (mrun D (n + 1) y)
  | n, x, y, S, hbc, h1, g1, hby, d1, d2 => by
    have hv : x.1.mem.get! x.1.hl.toNat = y.1.mem.get! y.1.hl.toNat := by
      have := hby 0 (by omega); simpa using this
    have st := seg_ldir D hhi hA hB S hv ⟨d1, by omega⟩
    obtain ⟨eA, _⟩ := ldir_mstep D hA S.LA S.atA x.2
    obtain ⟨eB, _⟩ := ldir_mstep D hB S.LB S.atB y.2
    have hx : mstep D x = (ldirS x.1, x.2) := eA
    have hy : mstep D y = (ldirS y.1, y.2) := eB
    obtain ⟨rh, rd, rb⟩ := ldirS_regs x.1
    obtain ⟨rh', _, _⟩ := ldirS_regs y.1
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
      have hszA : x.1.mem.size = 65536 := S.msz
      have hszB : y.1.mem.size = 65536 := by
        have := S.E.msz; have h2 : (mask true true x.1 y.1).mem = y.1.mem := by cases y.1; rfl
        rw [h2] at this; rw [← this]; exact hszA
      have hrsA : x.1.ramStart.toNat ≤ lo := S.rs
      have hrsB : y.1.ramStart.toNat ≤ lo := by
        have := RegsS.ramStart S.E.regs; rw [mask_ramStart] at this; rw [← this]; exact hrsA
      have hdeB : y.1.de = x.1.de := by
        have := RegsS.de S.E.regs; rw [mask_de] at this; exact this.symm
      have rA : x.1.ramStart.toNat ≤ x.1.de.toNat := by omega
      have rB : y.1.ramStart.toNat ≤ y.1.de.toNat := by rw [hdeB]; omega
      have hyde : lo ≤ y.1.de.toNat := by rw [hdeB]; omega
      have r := ldir_rom_rounds D hhi hA hB m (mstep D x) (mstep D y) st
        (by rw [hx]; simp only; rw [rb, toNat_sub1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rh, toNat_add1 _ (by omega)]; omega)
        (by rw [hy]; simp only; rw [rh', toNat_add1 _ (by omega)]; omega)
        (fun i hi' => by
          rw [hx, hy]; simp only
          rw [rh, rh', toNat_add1 _ (by omega), toNat_add1 _ (by omega),
            ldirS_mem x.1 _ hszA rA, ldirS_mem y.1 _ hszB rB, if_neg (by omega), if_neg (by omega)]
          have := hby (i + 1) (by omega)
          rw [show x.1.hl.toNat + 1 + i = x.1.hl.toNat + (i + 1) by omega,
            show y.1.hl.toNat + 1 + i = y.1.hl.toNat + (i + 1) by omega]
          exact this)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
      exact r

/-- info: 'Ember.Proof.PassSim.ldir_rom_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ldir_rom_rounds

end Ember.Proof.PassSim
