import Ember.Proof.Z80Fields

/-!
# Ember.Proof.Z80Load — loading an operand into a register (plan M7.3)

What `Codegen.loadA` emits leaves the operand's byte in `A`, from states
that agree to states that agree, changing nothing else but the flags
(`loadA_ok`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area)

/-- The operand can be read from where it is, `n` bytes of it. -/
def Rd (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (n : Nat) : Opd → Prop
  | .const _ => True
  | .slot sl => (∃ ad, Z.c.layout.areaAddr sl.area = some ad) ∧ Z.c.layout.addr sl + n ≤ 65536 ∧
      (∀ j, j < n → Z.data (Z.c.layout.addr sl + j)) ∧ Own E (.slot sl) ∧ Z.use (sl, n)
  | .tmp t => E.spilled[t]! = true →
      dt t ∧ (∃ ad, Z.c.layout.areaAddr (.frame E.fn.name) = some ad) ∧
        tmpAddr Z E t + E.fn.tmps[t]! ≤ 65536 ∧ n ≤ E.fn.tmps[t]!

theorem Rd.own {Z : ZCtx} {E : GEnv} {dt : Nat → Prop} {n : Nat} {o : Opd} (h : Rd Z E dt n o) : Own E o := by
  cases o with
  | const v => trivial
  | tmp t => trivial
  | slot sl => exact h.2.2.2.1

theorem Rd.use {Z : ZCtx} {E : GEnv} {dt : Nat → Prop} {n : Nat} {sl : Slot} (h : Rd Z E dt n (.slot sl)) :
    Z.use (sl, n) := h.2.2.2.2

/-- Where an operand is, as the generator names it. -/
def opdVal (E : GEnv) : Opd → Val
  | .slot s => slotVal s
  | .tmp t => slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }
  | .const _ => .num 0

/-- Its address. -/
def opdAddr (Z : ZCtx) (E : GEnv) : Opd → Nat
  | .slot s => Z.c.layout.addr s
  | .tmp t => tmpAddr Z E t
  | .const _ => 0

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem wpg_noteRead (sl : Slot) (s : GS) (Q : Unit → GS → Prop)
    (h : ∀ s1 : GS, s1.out = s.out → s1.regs = s.regs → Q () s1) : wpg (noteRead sl) E Q s := by
  unfold noteRead
  simp only [wpg_bind, wpg_read]
  split
  · rw [wpg_modify]
    refine h _ ?_ ?_ <;> split <;> rfl
  · exact h s rfl rfl

/-- `addrOf`: the operand's place, for an operand that has one. -/
theorem addrOf_ok (o : Opd) (s : GS) :
    wpg (addrOf o) E (fun p s1 => s1.out = s.out ∧ s1.regs = s.regs ∧ p = opdVal E o ∧
      (∀ t, o = .tmp t → E.spilled[t]! = true) ∧ ∀ v, o ≠ .const v) s := by
  unfold addrOf
  cases o with
  | const v => exact wpg_throw _ _
  | slot sl =>
    simp only [wpg_bind]
    refine wpg_noteRead sl s _ (fun s1 h1 h2 => ?_)
    rw [wpg_pure]
    exact ⟨h1, h2, rfl, (fun t ht => by cases ht), (fun v hv => by cases hv)⟩
  | tmp t =>
    simp only [wpg_bind, wpg_read]
    split
    · rename_i hsp
      rw [wpg_bind, wpg_modify, wpg_pure]
      exact ⟨rfl, rfl, rfl, (fun t' ht => by cases ht; exact hsp), (fun v hv => by cases hv)⟩
    · exact wpg_throw _ _

/-- The address of a readable operand, as the image has it. -/
theorem opd_val (ok : Z.OK) {n : Nat} {o : Opd} (hrd : Rd Z E dt n o) (hsp : ∀ t, o = .tmp t → E.spilled[t]! = true)
    (hc : ∀ v, o ≠ .const v) (pc : Nat) :
    (Z.a.env pc).val (opdVal E o) = Int.ofNat (opdAddr Z E o) ∧ opdAddr Z E o + n ≤ 65536 := by
  cases o with
  | const v => exact absurd rfl (hc v)
  | slot sl =>
    obtain ⟨⟨ad, had⟩, hb, _⟩ := hrd
    exact ⟨slot_val ok sl ad pc had, hb⟩
  | tmp t =>
    obtain ⟨_, ⟨ad, had⟩, hb, hn⟩ := hrd (hsp t rfl)
    exact ⟨slot_val ok { area := .frame E.fn.name, off := E.tmpOff[t]! } ad pc had, by
      show tmpAddr Z E t + n ≤ 65536
      omega⟩

/-- What is at a readable operand's address is its value. -/
theorem opd_mem {n : Nat} {o : Opd} (hrd : Rd Z E dt n o) (hsp : ∀ t, o = .tmp t → E.spilled[t]! = true)
    (hc : ∀ v, o ≠ .const v) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) :
    IR.Sem.rd s.mem (opdAddr Z E o) n = IR.Sem.opd Z.c ist tmps n o := by
  cases o with
  | const v => exact absurd rfl (hc v)
  | slot sl =>
    obtain ⟨_, hb, hd, _⟩ := hrd
    exact rd_congr _ _ _ _ hb (fun x h1 h2 => by
      have := hd (x - Z.c.layout.addr sl) (by omega)
      rw [show Z.c.layout.addr sl + (x - Z.c.layout.addr sl) = x by omega] at this
      exact (R.mem x this).symm) |>.symm
  | tmp t =>
    obtain ⟨hdt, _, hb, hn⟩ := hrd (hsp t rfl)
    have h := R.tmp t hdt (hsp t rfl)
    show IR.Sem.rd s.mem (tmpAddr Z E t) n = IR.modN n (tmps.getD t 0)
    rw [← h, IR.modN]
    have := rd_low s.mem (tmpAddr Z E t) n (E.fn.tmps[t]! - n)
    rw [show n + (E.fn.tmps[t]! - n) = E.fn.tmps[t]! by omega] at this
    exact this

/-- Nothing but `A`, the flags and the program counter changed. -/
def KeepA (s s' : Cpu) : Prop :=
  s'.b = s.b ∧ s'.c = s.c ∧ s'.d = s.d ∧ s'.e = s.e ∧ s'.h = s.h ∧ s'.l = s.l ∧ s'.sp = s.sp ∧ s'.mem = s.mem

theorem KeepA.refl (s : Cpu) : KeepA s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Nothing but `HL` and the program counter changed. -/
def KeepHL (s s' : Cpu) : Prop :=
  s'.a = s.a ∧ s'.f = s.f ∧ s'.b = s.b ∧ s'.c = s.c ∧ s'.d = s.d ∧ s'.e = s.e ∧ s'.sp = s.sp ∧ s'.mem = s.mem

theorem KeepHL.refl (s : Cpu) : KeepHL s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

macro "unfold_keep" : tactic => `(tactic| simp only [KeepA, KeepHL, zsim, and_self])

/-- What `loadA o` promises. -/
def LoadA (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (o : Opd) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.hl = s0.regs.hl ∧ o ∈ s1.regs.a ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 o → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧ KeepA s s' ∧
        s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o)

/-- One instruction, emitted and run. -/
theorem run_ins (ok : Z.OK) (F : GFinal Z base sF) {s0 s1 : GS} {i : Instr} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins i)) {s s' : Cpu} (I : Img Z.a 0 s) (hh : s.halted = false)
    (hat : At Z.addrs (base + s0.out.size) s)
    (hexec : ∀ ad, Z.addrs[base + s0.out.size]? = some ad → exec (Z.a.env ad) i s Z.inp = some s')
    (hf : i.falls = true) : Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨hst, hnext⟩ := step_item ok.placed I (F.emitted hx ho) had hpc hh (hexec ad had)
  refine ⟨Steps.one hst, ?_⟩
  have := hnext hf
  rw [ho, Array.size_push, ← Nat.add_assoc]
  exact this

theorem loadA_ok (ok : Z.OK) (F : GFinal Z base sF) (o : Opd) (s0 : GS) :
    wpg (loadA o) E (LoadA Z E base sF dt o s0) s0 := by
  unfold loadA
  simp only [wpg_bind, wpg_get, wpg_pure]
  by_cases h1 : s0.regs.a.contains o = true
  · simp only [h1, if_true, wpg_pure]
    have hmem : o ∈ s0.regs.a := by simpa using h1
    exact ⟨GExt.refl _, rfl, hmem, fun _ fr ist tmps s hrd R hat =>
      ⟨s, Steps.refl _ _, hat, R, KeepA.refl s, R.ra o hmem hrd.own⟩⟩
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : (s0.regs.hl.contains o && isSlot o) = true
    · simp only [h2, if_true, wpg_bind, wpg_ins, wpg_setRegs]
      simp only [Bool.and_eq_true] at h2
      have hmem : o ∈ s0.regs.hl := by simpa using h2.1
      refine ⟨GExt.push _ _, rfl, by simp, fun hx fr ist tmps s hrd R hat => ?_⟩
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0) hx rfl R.img R.run hat
        (s' := ((op1 s).setReg .hl 7 ((op1 s).reg .hl 5)).tick 4) (fun ad _ => rfl) rfl
      have hval : s.l.toNat = IR.Sem.opd Z.c ist tmps 1 o := by
        cases o with
        | slot sl =>
          have h := R.rhl _ hmem hrd.own
          show _ = IR.Sem.rd ist.mem _ 1
          have hlow := rd_low ist.mem (Z.c.layout.addr sl) 1 1
          rw [hlow]
          show _ = IR.Sem.rd ist.mem _ 2 % 256
          have h' : s.hl.toNat = IR.Sem.rd ist.mem (Z.c.layout.addr sl) 2 := h
          rw [← h', hl_toNat]
          have := s.l.toNat_lt
          omega
        | const v => simp [isSlot] at h2
        | tmp t => simp [isSlot] at h2
      have hval' : (((op1 s).setReg .hl 7 ((op1 s).reg .hl 5)).tick 4).a.toNat = IR.Sem.opd Z.c ist tmps 1 o := by
        simp only [zsim]
        exact hval
      refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' _ => ?_) (fun o' ho' => R.rhl o' ho')
          (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; first | (subst hsl; exact hrd.use) | cases hsl) R.inhl,
        (by unfold_keep), hval'⟩
      simp only [List.mem_singleton] at ho'
      subst ho'
      exact hval'
    · simp only [h2, Bool.false_eq_true, if_false]
      -- from memory
      have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
          wpg (do
            let p ← addrOf o
            ins .ld [.a, .mem p]
            setRegs fun r => { r with a := [o] }) E (LoadA Z E base sF dt o s0) s0 := by
        intro o hc
        simp only [wpg_bind]
        refine wpg_mono (addrOf_ok o s0) ?_
        intro p s1 ⟨ho1, hr1, hp, hsp, _⟩
        subst hp
        simp only [wpg_ins, wpg_setRegs]
        refine ⟨by simp [GExt, ho1], (by show s1.regs.hl = s0.regs.hl; rw [hr1]), by simp, fun hx fr ist tmps s hrd R hat => ?_⟩
        obtain ⟨ad, had, hpc⟩ := hat
        obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
        have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o := by
          show (w16 (byteOf ((Z.a.env ad).val (opdVal E o))) (byteOf ((Z.a.env ad).val (opdVal E o) / 256))).toNat = _
          rw [hv]
          exact w16_val _ (by omega)
        obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1) (i := ⟨.ld, [.a, .mem (opdVal E o)]⟩) hx rfl R.img R.run
          (by rw [ho1]; exact ⟨ad, had, hpc⟩)
          (s' := ({ (skip (op1 s) 2) with
            a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩) }).tick 13)
          (fun ad' had' => by
            rw [ho1, had] at had'
            cases had'
            rfl) rfl
        have hval : (({ (skip (op1 s) 2) with
            a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩) } : Cpu).tick 13).a.toNat =
            IR.Sem.opd Z.c ist tmps 1 o := by
          simp only [zsim]
          show (s.mem.get! _).toNat = _
          rw [hnn, ← rd_one _ _ (by omega)]
          exact opd_mem hrd hsp hc R
        refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' _ => ?_)
          (fun o' ho' => R.rhl o' (by rw [← hr1]; exact ho'))
          (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; first | (subst hsl; exact hrd.use) | cases hsl)
          (fun sl hsl => R.inhl sl (by rw [← hr1]; exact hsl)), (by unfold_keep), hval⟩
        simp only [List.mem_singleton] at ho'
        subst ho'
        exact hval
      cases o with
      | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
      | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
      | const v =>
        simp only [wpg_bind]
        by_cases hz : (v % 256 == 0) = true
        · simp only [hz, if_true, wpg_ins, wpg_setRegs]
          refine ⟨GExt.push _ _, rfl, by simp, fun hx fr ist tmps s hrd R hat => ?_⟩
          obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0) (i := ⟨.xor, [.a]⟩) hx rfl R.img R.run hat
            (s' := ((op1 s).alu 5 ((op1 s).reg .hl 7)).tick 4) (fun ad _ => rfl) rfl
          have hval : (((op1 s).alu 5 ((op1 s).reg .hl 7)).tick 4).a.toNat = IR.Sem.opd Z.c ist tmps 1 (.const v) := by
            simp only [zsim]
            show (s.a ^^^ s.a).toNat = IR.modN 1 v
            have hz' : v % 256 = 0 := by simpa using hz
            simp [IR.modN, hz']
          refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' _ => ?_) (fun o' ho' => R.rhl o' ho')
          (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; first | (subst hsl; exact hrd.use) | cases hsl) R.inhl,
            (by unfold_keep), hval⟩
          simp only [List.mem_singleton] at ho'
          subst ho'
          exact hval
        · simp only [hz, Bool.false_eq_true, if_false, wpg_ins, wpg_setRegs]
          refine ⟨GExt.push _ _, rfl, by simp, fun hx fr ist tmps s hrd R hat => ?_⟩
          obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0) (i := ⟨.ld, [.a, n8 v]⟩) hx rfl R.img R.run hat
            (s' := ((skip (op1 s) 1).setReg .hl 7 (byteOf (Int.ofNat (v % 256)))).tick 7) (fun ad _ => rfl) rfl
          have hval : (((skip (op1 s) 1).setReg .hl 7 (byteOf (Int.ofNat (v % 256)))).tick 7).a.toNat =
              IR.Sem.opd Z.c ist tmps 1 (.const v) := by
            simp only [zsim]
            show (byteOf (Int.ofNat (v % 256))).toNat = IR.modN 1 v
            rw [byteOf_toNat, IR.modN]
            have : (Int.ofNat (v % 256) : Int) = ((v % 256 : Nat) : Int) := rfl
            rw [this]
            omega
          refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' _ => ?_) (fun o' ho' => R.rhl o' ho')
          (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; first | (subst hsl; exact hrd.use) | cases hsl) R.inhl,
            (by unfold_keep), hval⟩
          simp only [List.mem_singleton] at ho'
          subst ho'
          exact hval

/-- What `loadHL o` promises. -/
def LoadHL (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (o : Opd) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.a = s0.regs.a ∧ o ∈ s1.regs.hl ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 2 o → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧ KeepHL s s' ∧
        s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o)

theorem loadHL_ok (ok : Z.OK) (F : GFinal Z base sF) (o : Opd) (s0 : GS) :
    wpg (loadHL o) E (LoadHL Z E base sF dt o s0) s0 := by
  unfold loadHL
  simp only [wpg_bind, wpg_get]
  by_cases h1 : s0.regs.hl.contains o = true
  · simp only [h1, if_true, wpg_pure]
    have hmem : o ∈ s0.regs.hl := by simpa using h1
    exact ⟨GExt.refl _, rfl, hmem, fun _ fr ist tmps s hrd R hat =>
      ⟨s, Steps.refl _ _, hat, R, KeepHL.refl s, R.rhl o hmem hrd.own⟩⟩
  · simp only [h1, Bool.false_eq_true, if_false]
    have mem_case : ∀ o : Opd, (∀ v, o ≠ .const v) →
        wpg (do
          let p ← addrOf o
          ins .ld [.hl, .mem p]
          setRegs fun r => { r with hl := [o] }) E (LoadHL Z E base sF dt o s0) s0 := by
      intro o hc
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok o s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _⟩
      subst hp
      simp only [wpg_ins, wpg_setRegs]
      refine ⟨by simp [GExt, ho1], (by show s1.regs.a = s0.regs.a; rw [hr1]), by simp,
        fun hx fr ist tmps s hrd R hat => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o :=
        immW_toNat _ _ _ _ rfl hv (by omega)
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1) (i := ⟨.ld, [.hl, .mem (opdVal E o)]⟩) hx rfl R.img R.run
        (by rw [ho1]; exact ⟨ad, had, hpc⟩)
        (s' := ((skip (op1 s) 2).setHL
          ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16)
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          rfl) rfl
      have hval : (((skip (op1 s) 2).setHL
          ((op1 s).rd16 (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .mem (opdVal E o)]⟩))).tick 16).hl.toNat =
          IR.Sem.opd Z.c ist tmps 2 o := by
        simp only [zsim]
        rw [cpu_rd16 _ _ (by rw [hnn]; omega), hnn]
        exact opd_mem hrd hsp hc R
      refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' => R.ra o' (by rw [← hr1]; exact ho'))
        (fun o' ho' _ => ?_) (fun sl hsl => R.ina sl (by rw [← hr1]; exact hsl))
        (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; first | (subst hsl; exact hrd.use) | cases hsl), (by unfold_keep), hval⟩
      simp only [List.mem_singleton] at ho'
      subst ho'
      exact hval
    cases o with
    | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
    | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
    | const v =>
      simp only [wpg_bind, wpg_ins, wpg_setRegs]
      refine ⟨GExt.push _ _, rfl, by simp, fun hx fr ist tmps s hrd R hat => ?_⟩
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s0) (i := ⟨.ld, [.hl, n16 v]⟩) hx rfl R.img R.run hat
        (s' := ((skip (op1 s) 2).setHL (w16 (byteOf (Int.ofNat (v % 65536))) (byteOf (Int.ofNat (v % 65536) / 256)))).tick 10)
        (fun ad _ => rfl) rfl
      have hval : (((skip (op1 s) 2).setHL
          (w16 (byteOf (Int.ofNat (v % 65536))) (byteOf (Int.ofNat (v % 65536) / 256)))).tick 10).hl.toNat =
          IR.Sem.opd Z.c ist tmps 2 (.const v) := by
        simp only [zsim]
        rw [w16_val _ (Nat.mod_lt _ (by decide))]
        rfl
      refine ⟨_, hst, hat', R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (fun o' ho' => R.ra o' ho') (fun o' ho' _ => ?_)
        R.ina (fun sl hsl _ => by simp only [List.mem_singleton] at hsl; cases hsl),
        (by unfold_keep), hval⟩
      simp only [List.mem_singleton] at ho'
      subst ho'
      exact hval

end

end Ember.Proof.Z80Gen
