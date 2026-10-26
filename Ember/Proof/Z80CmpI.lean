import Ember.Proof.Z80Jump

/-!
# Ember.Proof.Z80CmpI — a comparison as a value (plan M7.3)

After the flags (`Z80Cmp.lean`), `cmp` leaves 0 or 1 in `A`: a jump
over `inc a` for `eq` and `ne`, the carry rotated in for `lt`, `sbc a,a;
inc a` for `ge`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- `ld a,n` and `rla` as the model runs them. -/
def ldAN (v : Nat) (s : Cpu) : Cpu := ((skip (op1 s) 1).setReg .hl 7 (byteOf (Int.ofNat (v % 256)))).tick 7

def rlaA (s : Cpu) : Cpu :=
  ({ (op1 s) with
      a := ((op1 s).a <<< 1) ||| (if (op1 s).flag FC then 1 else 0),
      f := ((op1 s).f &&& (FS ||| FZ ||| FPV)) ||| ((((op1 s).a <<< 1) ||| (if (op1 s).flag FC then 1 else 0)) &&& FXY) |||
        Cpu.bit ((op1 s).a &&& 0x80 != 0) FC } : Cpu).tick 4

theorem does_ld_a_n (v : Nat) : Does ⟨.ld, [.a, n8 v]⟩ (ldAN v) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldAN, zsim, and_self], fun s => by simp only [ldAN, zsim]⟩

theorem does_rla : Does ⟨.rla, []⟩ rlaA := ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, rlaA, zsim, and_self], fun s => by simp only [rlaA, zsim]⟩

theorem does_sbc_a_a : Does ⟨.sbc, [.a, .a]⟩ (aluR 3 7) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, aluR, zsim, and_self], fun s => by simp only [aluR, zsim]⟩

/-- `ld a,0; rla`: the carry as a number. -/
theorem lt_val (s : Cpu) : (rlaA (ldAN 0 s)).a.toNat = if s.flag FC then 1 else 0 := by
  simp only [rlaA, ldAN, zsim]
  by_cases h : s.flag FC = true
  · simp only [h, if_true]
    rfl
  · simp only [h, Bool.false_eq_true, if_false]
    rfl

theorem sub8_self (a : UInt8) (c : Bool) : (sub8 a a c).1 = if c then 255 else 0 := by
  cases c <;> simp [sub8] <;> decide

/-- `sbc a,a; inc a`: the carry, negated, as a number. -/
theorem ge_val (s : Cpu) : (incA (aluR 3 7 s)).a.toNat = if s.flag FC then 0 else 1 := by
  simp only [incA, aluR, zsim]
  rw [sub8_self]
  by_cases h : s.flag FC = true
  · simp only [h, if_true]
    rfl
  · simp only [h, Bool.false_eq_true, if_false]
    rfl

theorem wpg_newLabel {E : GEnv} {s : GS} (Q : String → GS → Prop) :
    wpg newLabel E Q s ↔ Q s!"x_{sanitize E.fn.name}_{s.labels}" { s with labels := s.labels + 1 } := Iff.rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem push4_get {α : Type} (o : Array α) (a b c d : α) :
    ((((o.push a).push b).push c).push d)[o.size]? = some a ∧
    ((((o.push a).push b).push c).push d)[o.size + 1]? = some b ∧
    ((((o.push a).push b).push c).push d)[o.size + 2]? = some c ∧
    ((((o.push a).push b).push c).push d)[o.size + 3]? = some d := by
  have h : ((((o.push a).push b).push c).push d).toList = o.toList ++ [a, b, c, d] := by simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [← Array.getElem?_toList, h, List.getElem?_append_right (by simp)]
     simp)

/-- An instruction of the image that leaves memory alone, run. -/
theorem run_at (ok : Z.OK) {k : Nat} {i : Instr} {f : Cpu → Cpu} (hk : Z.items[k]? = some (.ins i)) (hd : Does i f)
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    Steps s (f s) ∧ At Z.addrs (k + 1) (f s) ∧ Mach Z (f s) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := fun inp => step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hd.exec _ _ _)
  exact ⟨Steps.one (fun inp => (hst inp).1) (hd.io s), (hst (fun _ => 0)).2 hd.falls, M.sys (hd.sys s)⟩

/-- What the code that turns the flags into 0 or 1 promises. -/
def Mat (Z : ZCtx) (base : Nat) (sF : GS) (op : Cmp) (s1 : GS) (_ : Unit) (s2 : GS) : Prop :=
  GExt s1 s2 ∧ s2.regs = s1.regs ∧
    (GExt s2 sF → ∀ s x y, Mach Z s → At Z.addrs (base + s1.out.size) s → FlagsOf op x y s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s2.out.size) s' ∧ Sys s s' ∧ s'.hl = s.hl ∧
        s'.a.toNat = if IR.cmpOp op x y then 1 else 0)

theorem mat_lt (ok : Z.OK) (F : GFinal Z base sF) (s1 : GS) :
    wpg (do ins .ld [.a, n8 0]; ins .rla) E (Mat Z base sF .lt s1) s1 := by
  simp only [wpg_bind, wpg_ins]
  refine ⟨pushL_ext [⟨.ld, [.a, n8 0]⟩, ⟨.rla, []⟩] s1, rfl, fun hx s x y M hat hf => ?_⟩
  obtain ⟨st, at', _, hS⟩ := run_list ok F [(⟨.ld, [.a, n8 0]⟩, ldAN 0), (⟨.rla, []⟩, rlaA)]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact does_ld_a_n 0
      · exact does_rla) s1 s hx M hat
  refine ⟨_, st, at', hS, by simp only [List.map, runL, rlaA, ldAN, zsim, Cpu.hl], ?_⟩
  show (rlaA (ldAN 0 s)).a.toNat = _
  rw [lt_val, show s.flag FC = decide (x < y) from hf]
  rfl

theorem mat_ge (ok : Z.OK) (F : GFinal Z base sF) (s1 : GS) :
    wpg (do ins .sbc [.a, .a]; ins .inc [.a]) E (Mat Z base sF .ge s1) s1 := by
  simp only [wpg_bind, wpg_ins]
  refine ⟨pushL_ext [⟨.sbc, [.a, .a]⟩, ⟨.inc, [.a]⟩] s1, rfl, fun hx s x y M hat hf => ?_⟩
  obtain ⟨st, at', _, hS⟩ := run_list ok F [(⟨.sbc, [.a, .a]⟩, aluR 3 7), (⟨.inc, [.a]⟩, incA)]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact does_sbc_a_a
      · exact does_inc_a) s1 s hx M hat
  refine ⟨_, st, at', hS, by simp only [List.map, runL, incA, aluR, zsim], ?_⟩
  show (incA (aluR 3 7 s)).a.toNat = _
  rw [ge_val, show s.flag FC = decide (x < y) from hf]
  show _ = if decide (x ≥ y) = true then 1 else 0
  by_cases h : x < y <;> simp [h] <;> omega

/-- `eq` and `ne`: a jump over `inc a`. -/
theorem mat_eq (ok : Z.OK) (F : GFinal Z base sF) (z : Bool) (op : Cmp)
    (hop : ∀ x y s, FlagsOf op x y s → (s.flag FZ = z ↔ IR.cmpOp op x y = false)) (s1 : GS) :
    wpg (do
      let l ← newLabel
      ins .ld [.a, n8 0]
      ins .jr [if z then .z else .nz, .imm (.sym l)]
      ins .inc [.a]
      modify fun s => { s with out := s.out.push (.label l) }) E (Mat Z base sF op s1) s1 := by
  simp only [wpg_bind, wpg_newLabel, wpg_ins, wpg_modify]
  refine ⟨GExt.of_out (by simp) rfl rfl, rfl, fun hx s x y M hat hf => ?_⟩
  -- the four items
  have i0 := F.at hx (push4_get _ _ _ _ _).1
  have i1 := F.at hx (push4_get _ _ _ _ _).2.1
  have i2 := F.at hx (push4_get _ _ _ _ _).2.2.1
  have i3 := F.at hx (push4_get _ _ _ _ _).2.2.2
  simp only [← Nat.add_assoc] at i1 i2 i3
  obtain ⟨st1, at1, M1⟩ := run_at ok i0 (does_ld_a_n 0) M hat
  obtain ⟨t2, st2, M2, S2, K2, hcase⟩ := jr_cc_step ok z i1 i3 M1 at1
  have hfz : (ldAN 0 s).flag FZ = s.flag FZ := by simp only [ldAN, zsim]
  have ha1 : (ldAN 0 s).a.toNat = 0 := by simp only [ldAN, zsim]; rfl
  have hend : ∀ t, At Z.addrs (base + s1.out.size + 3) t → At Z.addrs (base + (s1.out.size + 4)) t :=
    fun t h => at_skip ok.placed i3 (fun _ => rfl) h
  by_cases hc : (ldAN 0 s).flag FZ = z
  · -- the jump is taken: `A` stays 0
    rw [if_pos hc] at hcase
    have hcmp := (hop x y s hf).mp (by rw [← hfz]; exact hc)
    refine ⟨t2, st1.trans st2, by simp only [Array.size_push]; exact hend t2 hcase, ((does_ld_a_n 0).sys s).trans S2, ?_, ?_⟩
    · rw [hl_congr K2.2.2.2.2.2.2.1 K2.2.2.2.2.2.2.2.1]
      simp only [ldAN, zsim]
    · rw [K2.1, ha1, hcmp]
      rfl
  · rw [if_neg hc] at hcase
    have hcmp : IR.cmpOp op x y = true := by
      cases h : IR.cmpOp op x y
      · exact absurd ((hop x y s hf).mpr h) (by rw [← hfz]; exact hc)
      · rfl
    obtain ⟨st3, at3, _⟩ := run_at ok i2 does_inc_a M2 hcase
    refine ⟨incA t2, (st1.trans st2).trans st3, by simp only [Array.size_push]; exact hend _ at3,
      (((does_ld_a_n 0).sys s).trans S2).trans (does_inc_a.sys t2), ?_, ?_⟩
    · have : (incA t2).hl = t2.hl := by simp only [incA, zsim]
      rw [this, hl_congr K2.2.2.2.2.2.2.1 K2.2.2.2.2.2.2.2.1]
      simp only [ldAN, zsim]
    · have : (incA t2).a.toNat = (t2.a.toNat + 1) % 256 := by
        simp only [incA, zsim]
        rw [UInt8.toNat_add]
        rfl
      rw [this, K2.1, ha1, hcmp]
      rfl

/-- **The code of `cmp` on one or two bytes does what the IR's instruction does.** -/
theorem cmp_core (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Cmp) (n : Nat)
    (d : Dst) (a b : Opd) (Pa Pb : Prop) (s0 : GS)
    (hflags : wpg (genFlags op n a b) E (FlagsG Z E base sF dt op n a b Pa Pb s0) s0) :
    wpg (genInstr (.cmp op n d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.cmp op n d a b) (Pa ∧ Pb ∧ Wr Z E 1 d) s0)
      s0 := by
  have fin : ∀ (m : GM Unit), (∀ s1, wpg m E (Mat Z base sF op s1) s1) →
      wpg (do genFlags op n a b; m; setRegs fun r => { r with a := [] }; storeA d) E
        (InsPost Z E base sF dt (dtAfter dt d) (.cmp op n d a b) (Pa ∧ Pb ∧ Wr Z E 1 d) s0)
        s0 := by
    intro m hm
    simp only [wpg_bind]
    refine wpg_mono hflags ?_
    intro _ s1 ⟨hx1, hf⟩
    refine wpg_mono (hm s1) ?_
    intro _ s2 ⟨hx2, hr2, hmat⟩
    rw [wpg_setRegs]
    refine wpg_mono (storeA_ok (dt := dt) ok hT F d _) ?_
    intro _ s3 ⟨hx3, _, _, hs⟩
    refine ⟨hx1.trans (hx2.trans ((GExt.regs _ _).trans hx3)), fun hxF ⟨hra, hrb, hwr⟩ fr ist tmps s R hat => ?_⟩
    obtain ⟨s', st1, at1, R1, hfl⟩ := hf (hx2.trans ((GExt.regs _ _).trans (hx3.trans hxF))) fr ist tmps s hra hrb R hat
    obtain ⟨s'', st2, at2, S2, hhl, hA⟩ := hmat ((GExt.regs _ _).trans (hx3.trans hxF)) s' _ _ R1.mach at1 hfl
    have R2 : Rel Z E fr dt { s2.regs with a := [] } ist tmps s'' :=
      R1.of_sys S2 rfl (fun o ho => by rw [← hr2]; exact ho)
        (fun o ho hown => by rw [hhl]; exact R1.rhl o (by rw [← hr2]; exact ho) hown)
        (fun n o h => by rw [← hr2]; exact h)
    obtain ⟨s3', st3, at3, R3, _⟩ := hs hxF fr ist tmps s''
      (if IR.cmpOp op (IR.Sem.opd Z.c ist tmps n a) (IR.Sem.opd Z.c ist tmps n b) then 1 else 0) hwr R2 at2 (by
        rw [hA]
        split <;> rfl)
    exact ⟨s3', (st1.trans st2).trans st3, at3, R3⟩
  cases op
  · exact fin _ (fun s1 => mat_eq ok F false .eq (fun x y s h => by
      rw [show s.flag FZ = (x == y) from h]
      exact Iff.rfl) s1)
  · exact fin _ (fun s1 => mat_eq ok F true .ne (fun x y s h => by
      rw [show s.flag FZ = (x == y) from h]
      show (x == y) = true ↔ (!(x == y)) = false
      cases (x == y) <;> simp) s1)
  · exact fin _ (fun s1 => mat_lt ok F s1)
  · exact fin _ (fun s1 => mat_ge ok F s1)

/-- **`cmp` of one and two bytes.** -/
theorem cmp_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Cmp) (n : Nat) (hn : n = 1 ∨ n = 2)
    (d : Dst) (a b : Opd) (s0 : GS) :
    wpg (genInstr (.cmp op n d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.cmp op n d a b) (Rd Z E dt n a ∧ Rd Z E dt n b ∧ Wr Z E 1 d) s0)
      s0 :=
  cmp_core ok hT F op n d a b _ _ s0 (genFlagsG_ok ok F op n hn a b s0)

end

end Ember.Proof.Z80Gen
