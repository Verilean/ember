import Ember.Proof.Z80Boot

/-!
# Ember.Proof.Z80Note — the harness's `rt_note` (plan M7.3)

A note is its code and its value.  The harness is given both: the four
bytes of the value on port `0xDA`, least significant first, then the
code on `0xD6` (`Ember.Z80.Machine`).  `harness_note`: the routine of
the harness's runtime does this with `A` and the accumulator, which is
what `RtEff` asks of the routine of the effect.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (Effect World)

section
variable {Z : ZCtx}

theorem sym_val_off (pc : Nat) {name : String} {entry : Nat} (off : Nat) (h : Z.sym name entry) :
    (Z.a.env pc).val (.sym name (Int.ofNat off)) = Int.ofNat (entry + off) := by
  unfold ZCtx.sym at h
  rw [val_sym _ _ _ (Int.ofNat entry) (by simp [Assembled.env, h])]
  simp

/-- `ld a,(name+off)`: `A` is that byte; `C` is kept. -/
theorem ld_a_cell_off (ok : Z.OK) {k A : Nat} {name : String} (off : Nat)
    (hk : Z.items[k]? = some (.ins ⟨.ld, [.a, .mem (.sym name (Int.ofNat off))]⟩)) (hsym : Z.sym name A)
    (hA : A + off < 65536) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' ∧ s'.a = s.mem.get! (A + off) ∧ s'.c = s.c := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym name (Int.ofNat off))]⟩).toNat = A + off :=
    immW_toNat _ _ _ _ rfl (sym_val_off ad off hsym) hA
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = (({ (skip (op1 s) 2) with
      a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym name (Int.ofNat off))]⟩) } : Cpu).tick 13) := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; rfl)
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  refine ⟨c1, st, at' rfl, M.sys hS, hS, ?_, ?_⟩
  · rw [hc1]
    show (op1 s).mem.get! (Instr.immW _ _).toNat = _
    rw [hnn]
    rfl
  · rw [hc1]
    simp only [skip, zsim]

/-- `out (n),a`: the write is `A` to a port whose low byte is `n`; the registers are kept. -/
theorem out_step (ok : Z.OK) {k port : Nat} (hport : port < 256)
    (hk : Z.items[k]? = some (.ins ⟨.out, [.mem (.num (Int.ofNat port)), .a]⟩)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) (w : Z.W) :
    ∃ s' p, lo p = UInt8.ofNat port ∧ WSteps Z (s, w) (s', Z.dev w (.write p s.a)) ∧ At Z.addrs (k + 1) s' ∧
      Mach Z s' ∧ Sys s s' ∧ s'.a = s.a ∧ s'.c = s.c := by
  obtain ⟨st1, at2⟩ := wstep_item ok hk M hat w
    (s' := (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat port))) (op1 s).a } : Cpu).tick 11)) (fun ad _ => rfl)
  have hS : Sys s (({ (skip (op1 s) 1) with
      io := .write (mk16 (op1 s).a (byteOf (Int.ofNat port))) (op1 s).a } : Cpu).tick 11) := by
    simp only [Sys, skip, zsim, and_self]
  refine ⟨_, mk16 s.a (byteOf (Int.ofNat port)), ?_, st1, at2 rfl, M.sys hS, hS, ?_, ?_⟩
  · rw [lo_mk16]
    apply UInt8.toNat_inj.mp
    rw [byteOf_toNat, UInt8.toNat_ofNat']
    show ((port : Int) % 256).toNat = port % 256
    omega
  · simp only [skip, zsim]
  · simp only [skip, zsim]

theorem does_ld_c_a : Does ⟨.ld, [.c, .a]⟩ (ldRA 1) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRA, zsim, and_self], fun s => by simp only [ldRA, zsim]⟩
theorem does_ld_a_c : Does ⟨.ld, [.a, .c]⟩ (ldAR 1) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldAR, zsim, and_self], fun s => by simp only [ldAR, zsim]⟩
theorem ldRA1_c (s : Cpu) : (ldRA 1 s).c = s.a := by simp only [ldRA, zsim]
theorem ldAR1_a (s : Cpu) : (ldAR 1 s).a = s.c := by simp only [ldAR, zsim]

theorem rd16_sys {s s' : Cpu} (h : Sys s s') : s'.rd16 s'.sp = s.rd16 s.sp := by
  simp only [Cpu.rd16, Cpu.rd, h.1, h.2.2.2]

/-- The items of the harness's `rt_note`. -/
def noteItems : List Item :=
  [.label "rt_note", .ins ⟨.ld, [.c, .a]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_acc" 0)]⟩, .ins ⟨.out, [.mem (.num 0xDA), .a]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_acc" 1)]⟩, .ins ⟨.out, [.mem (.num 0xDA), .a]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_acc" 2)]⟩, .ins ⟨.out, [.mem (.num 0xDA), .a]⟩,
   .ins ⟨.ld, [.a, .mem (.sym "rt_acc" 3)]⟩, .ins ⟨.out, [.mem (.num 0xDA), .a]⟩,
   .ins ⟨.ld, [.a, .c]⟩, .ins ⟨.out, [.mem (.num 0xD6), .a]⟩, .ins ⟨.ret, []⟩]

/-- These are the items of the piece of the harness's runtime that has `rt_note` (`#guard`). -/
def noteInRuntime : Bool :=
  Runtime.harness.any fun pc => match Asm.parse pc.src with
    | .ok l => l == noteItems
    | .error _ => false

#guard noteInRuntime

/-- **The harness's `rt_note`**: the world has the note of the code in
`A` with the value in the accumulator; memory is as it was. -/
theorem harness_note (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k noteItems) : RtEff Z .note := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 2, _, 0, hhas.get 2 rfl, rfl⟩
  have hram := ok.accRam
  refine ⟨T, hsym, by omega, fun c w wd vs hpc I hh hrs hmsz _ _ hw hargs => ?_⟩
  have M : Mach Z c := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) c := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_ld_c_a (hhas.get 1 rfl) M at1
  obtain ⟨c2, st2, at3, M2, hS2, ha2, hc2⟩ := ld_a_cell_off ok 0 (hhas.get 2 rfl) hacc (by omega) M1 at2
  obtain ⟨c3, p0, hp0, st3, at4, M3, hS3, ha3, hc3⟩ := out_step ok (port := 0xDA) (by decide) (hhas.get 3 rfl) M2 at3 w
  obtain ⟨c4, st4, at5, M4, hS4, ha4, hc4⟩ := ld_a_cell_off ok 1 (hhas.get 4 rfl) hacc (by omega) M3 at4
  obtain ⟨c5, p1, hp1, st5, at6, M5, hS5, ha5, hc5⟩ := out_step ok (port := 0xDA) (by decide) (hhas.get 5 rfl) M4 at5 _
  obtain ⟨c6, st6, at7, M6, hS6, ha6, hc6⟩ := ld_a_cell_off ok 2 (hhas.get 6 rfl) hacc (by omega) M5 at6
  obtain ⟨c7, p2, hp2, st7, at8, M7, hS7, ha7, hc7⟩ := out_step ok (port := 0xDA) (by decide) (hhas.get 7 rfl) M6 at7 _
  obtain ⟨c8, st8, at9, M8, hS8, ha8, hc8⟩ := ld_a_cell_off ok 3 (hhas.get 8 rfl) hacc (by omega) M7 at8
  obtain ⟨c9, p3, hp3, st9, at10, M9, hS9, ha9, hc9⟩ := out_step ok (port := 0xDA) (by decide) (hhas.get 9 rfl) M8 at9 _
  obtain ⟨st10, at11, M10, hS10⟩ := does_raw ok does_ld_a_c (hhas.get 10 rfl) M9 at10
  obtain ⟨c11, p, hp, st11, at12, M11, hS11, ha11, hc11⟩ :=
    out_step ok (port := 0xD6) (by decide) (hhas.get 11 rfl) M10 at11 _
  obtain ⟨c', st12, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 12 rfl) M11 at12
  have hS : Sys c c11 := (((((((((hS1.trans hS2).trans hS3).trans hS4).trans hS5).trans hS6).trans hS7).trans hS8).trans
    hS9).trans hS10).trans hS11
  have hm2 : (ldRA 1 c).mem = c.mem := hS1.1
  have hm4 : c3.mem = c.mem := ((hS1.trans hS2).trans hS3).1
  have hm6 : c5.mem = c.mem := ((((hS1.trans hS2).trans hS3).trans hS4).trans hS5).1
  have hm8 : c7.mem = c.mem := ((((((hS1.trans hS2).trans hS3).trans hS4).trans hS5).trans hS6).trans hS7).1
  have hk : (ldAR 1 c9).a = c.a := by
    rw [ldAR1_a, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, ldRA1_c]
  have hv : vs = [c.a.toNat, IR.Sem.rd c.mem Z.acc 4] := hargs
  have hrd : IR.Sem.rd c.mem Z.acc 4 = (c.mem.get! (Z.acc + 0)).toNat + 256 * ((c.mem.get! (Z.acc + 1)).toNat +
      256 * ((c.mem.get! (Z.acc + 2)).toNat + 256 * ((c.mem.get! (Z.acc + 3)).toNat + 256 * 0))) := by
    simp only [IR.Sem.rd]
    rw [Nat.mod_eq_of_lt (show Z.acc < 65536 by omega), Nat.mod_eq_of_lt (show Z.acc + 1 < 65536 by omega),
      Nat.mod_eq_of_lt (show Z.acc + 1 + 1 < 65536 by omega), Nat.mod_eq_of_lt (show Z.acc + 1 + 1 + 1 < 65536 by omega)]
    rfl
  have hW := H.wrNote wd w p0 p1 p2 p3 p c2.a c4.a c6.a c8.a (ldAR 1 c9).a hp0 hp1 hp2 hp3 hp hw
  have hval : [(ldAR 1 c9).a.toNat, c2.a.toNat + 256 * (c4.a.toNat + 256 * (c6.a.toNat + 256 * (c8.a.toNat + 256 * 0)))] =
      vs := by
    rw [hk, ha2, ha4, ha6, ha8, hm2, hm4, hm6, hm8, ← hrd, ← hv]
  rw [hval] at hW
  refine ⟨c', _, (((((((((((Steps.lift ok st1 w).trans (Steps.lift ok st2 w)).trans st3).trans
      (Steps.lift ok st4 _)).trans st5).trans (Steps.lift ok st6 _)).trans st7).trans (Steps.lift ok st8 _)).trans
      st9).trans (Steps.lift ok st10 _)).trans st11).trans (Steps.lift ok st12 _), ?_, ?_, ?_, ?_, ?_, ?_, hW, ?_⟩
  · rw [hpc', rd16_sys hS]
  · rw [hsp', hS.2.2.2]
  · rw [hh', hS.2.2.1]
    exact hh
  · rw [hrs', hS.2.1]
  · rw [hmem', hS.1]
    exact hmsz
  · intro x _ _
    rw [hmem', hS.1]
  · intro r hr
    cases hr

end

end Ember.Proof.Z80Gen
