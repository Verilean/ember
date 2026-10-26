import Ember.Proof.Z80Wide

/-!
# Ember.Proof.Z80BootInit — start-up: the copy of an initial value (plan M7.3)

After `rt_zero`, `rt_init` copies the initial values of the variables
that have one from the ROM: `ld hl,init_x; ld de,g_x; ld bc,n; ldir`
for each.  `copy_ok`: one such copy, from its items — the `n` bytes at
the source are at the destination, no other byte changes, the stack
pointer stays.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

/-- The copy of `n` bytes from `src` to `dst`. -/
def copyItems (src dst : String) (n : Nat) : List Item :=
  [.ins ⟨.ld, [.hl, .imm (.sym src)]⟩, .ins ⟨.ld, [.de, .imm (.sym dst)]⟩,
   .ins ⟨.ld, [.bc, .imm (.num (Int.ofNat n))]⟩, .ins ⟨.ldir, []⟩]

section
variable {Z : ZCtx}

/-- **A copy of `m + 1` bytes**, the source and the destination apart, the destination in RAM. -/
theorem copy_ok (ok : Z.OK) {k : Nat} {src dst : String} {m S D : Nat}
    (hhas : Has Z k (copyItems src dst (m + 1))) (hS : Z.sym src S) (hD : Z.sym dst D)
    (hram : Z.ramStart ≤ D) (hSb : S + m + 1 ≤ 65536) (hDb : D + m + 1 ≤ 65536)
    (hap : S + m + 1 ≤ D ∨ D + m + 1 ≤ S) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s)
    (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 4) s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
      s'.mem.size = 65536 ∧ (∀ j, j ≤ m → s'.mem.get! (D + j) = s.mem.get! (S + j)) ∧
      (∀ x, x < D ∨ D + m + 1 ≤ x → s'.mem.get! x = s.mem.get! x) := by
  obtain ⟨c1, ad1, had1, st1, at1, M1, hS1, hhl1, _, _, _⟩ := ld_hl_imm ok (hhas.get 0 rfl) M hat
  obtain ⟨c2, ad2, had2, st2, at2, M2, hS2, hde2, hhl2, _, _, _, _⟩ := ld_de_imm ok (hhas.get 1 rfl) M1 at1
  obtain ⟨c3, ad3, had3, st3, at3, M3, hS3, hbc3, hhl3, hde3, _⟩ := ld_bc_imm ok (hhas.get 2 rfl) M2 at2
  have hS03 : Sys s c3 := (hS1.trans hS2).trans hS3
  have hhlv : c3.hl.toNat = S := by
    rw [hhl3, hhl2, hhl1]
    exact immW_toNat _ _ _ _ rfl (sym_val ad1 hS) (by omega)
  have hdev : c3.de.toNat = D := by
    rw [hde3, hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hD) (by omega)
  have hbcv : c3.bc.toNat = m + 1 := by
    rw [hbc3]
    exact immW_toNat _ _ _ (m + 1) rfl rfl (by omega)
  obtain ⟨c4, st4, at4, M4, hsp4, hr4, hsz4, hcp, hkeep⟩ := ldir_copy ok (hhas.get 3 rfl) m c3 S D M3 at3
    (by rw [hS03.2.1]; exact hrs) hhlv hdev hbcv hram (by omega) (by omega) (by rw [hS03.1]; exact hsz)
    (fun j hj => by omega)
  rw [hS03.1] at hcp hkeep
  exact ⟨c4, ((st1.trans st2).trans st3).trans st4, at4, M4, by rw [hsp4, hS03.2.2.2], by rw [hr4, hS03.2.1], hsz4,
    hcp, hkeep⟩

end

end Ember.Proof.Z80Gen
