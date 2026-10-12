import Ember.Proof.Z80Load

/-!
# Ember.Proof.Z80Store — storing a register to a destination (plan M7.3)

The IR writes a destination; the generated code writes the same bytes,
or leaves a store out that nothing reads from memory.  `Rel.wr_slot`,
`Rel.wr_dead` and `Rel.wr_tmp` say that the states agree again;
`storeA_ok` is `Codegen.storeA`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area)

/-- A byte of the slot of a temporary. -/
def TmpByte (Z : ZCtx) (E : GEnv) (x : Nat) : Prop :=
  ∃ t, E.spilled[t]! = true ∧ tmpAddr Z E t ≤ x ∧ x < tmpAddr Z E t + E.fn.tmps[t]!

/-- A slot can be written, `n` bytes of it. -/
structure WrSlot (Z : ZCtx) (E : GEnv) (n : Nat) (sl : Slot) : Prop where
  area : ∃ ad, Z.c.layout.areaAddr sl.area = some ad
  dst : Z.dst (sl, n)
  use : Own E (.slot sl) → Z.use (sl, n)
  ram : Z.ramStart ≤ Z.c.layout.addr sl
  notmp : ∀ j, j < n → ¬ TmpByte Z E (Z.c.layout.addr sl + j)
  /-- A store the generator leaves out is to bytes that are not shared. -/
  dead : sl.area = .frame E.fn.name → ∀ lv, E.live = some lv →
    (∀ k, k < n → lv.getD (sl.off + k) true = false) → ∀ j, j < n → ¬ Z.data (Z.c.layout.addr sl + j)

/-- Where the temporaries of the function have their slots. -/
structure FnLay (Z : ZCtx) (E : GEnv) : Prop where
  area : ∃ ad, Z.c.layout.areaAddr (.frame E.fn.name) = some ad
  bound : ∀ t, E.spilled[t]! = true → tmpAddr Z E t + E.fn.tmps[t]! ≤ 65536
  ram : ∀ t, E.spilled[t]! = true → Z.ramStart ≤ tmpAddr Z E t
  nodata : ∀ t, E.spilled[t]! = true → ∀ j, j < E.fn.tmps[t]! → ¬ Z.data (tmpAddr Z E t + j)
  apart : ∀ t t', t ≠ t' → E.spilled[t]! = true → E.spilled[t']! = true →
    tmpAddr Z E t' + E.fn.tmps[t']! ≤ tmpAddr Z E t ∨ tmpAddr Z E t + E.fn.tmps[t]! ≤ tmpAddr Z E t'

/-- A temporary can be assigned `n` bytes: it is one of the function's, of that size. -/
structure WrTmp (E : GEnv) (n : Nat) (t : Nat) : Prop where
  lt : t < E.fn.tmps.size
  size : E.fn.tmps[t]! = n

def Wr (Z : ZCtx) (E : GEnv) (n : Nat) : Dst → Prop
  | .slot sl => WrSlot Z E n sl
  | .tmp t => WrTmp E n t

/-- The temporaries assigned once `d` is. -/
def dtAfter (dt : Nat → Prop) (d : Dst) (x : Nat) : Prop := dt x ∨ d = .tmp x

section
variable {Z : ZCtx} {E : GEnv} {dt : Nat → Prop}

/-! ## Operands a write leaves alone -/

theorem opd_wr_keep (ok : Z.OK) {o : Opd} {m n : Nat} {sl : Slot} (huse : ∀ a, o = .slot a → Z.use (a, m))
    (hdst : Z.dst (sl, n)) (hno : overlaps o m sl n = false) (ist : IR.Sem.St) (tmps : Array Nat) (v : Nat) :
    IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps m o =
      IR.Sem.opd Z.c ist tmps m o := by
  cases o with
  | const x => rfl
  | tmp t => rfl
  | slot a =>
    have hu := huse a rfl
    rcases ok.apart a m sl n hu hdst with h | h
    · have : overlaps (.slot a) m sl n = IR.slotsOverlap a m sl n := rfl
      rw [this, h] at hno
      cases hno
    · exact rd_wr_far _ _ _ _ _ _ (ok.ubound a m hu) (ok.dbound sl n hdst) h

theorem opd_tmp_keep (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (t x m : Nat) {o : Opd}
    (hne : o ≠ .tmp t) : IR.Sem.opd c ist (tmps.setIfInBounds t x) m o = IR.Sem.opd c ist tmps m o := by
  cases o with
  | const y => rfl
  | slot a => rfl
  | tmp t' =>
    have : t ≠ t' := fun e => hne (by rw [e])
    simp only [IR.Sem.opd, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne this]

/-! ## The states after a write -/

/-- The code wrote the bytes the IR writes. -/
theorem Rel.wr_slot (ok : Z.OK) (hT : FnLay Z E) {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s s' : Cpu}
    (R : Rel Z E dt regs ist tmps s) {n : Nat} {sl : Slot} (W : WrSlot Z E n sl) (v : Nat)
    (hm : s'.mem = IR.Sem.wr s.mem (Z.c.layout.addr sl) n v) (hr : s'.ramStart = s.ramStart)
    (hh : s'.halted = s.halted)
    (ha : ∀ o, o ∈ regs'.a → Own E o → s'.a.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 1 o)
    (hhl : ∀ o, o ∈ regs'.hl → Own E o → s'.hl.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 2 o)
    (hina : ∀ a, Opd.slot a ∈ regs'.a → Own E (.slot a) → Z.use (a, 1))
    (hinhl : ∀ a, Opd.slot a ∈ regs'.hl → Own E (.slot a) → Z.use (a, 2)) :
    Rel Z E dt regs' { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps s' := by
  have hb := ok.dbound sl n W.dst
  refine ⟨⟨by rw [hr]; exact R.img.rom, fun x b hx => ?_⟩, by rw [hh]; exact R.run, fun x hx => ?_,
    fun t h1 h2 => ?_, by rw [hr]; exact R.rs, by rw [hm, wr_size]; exact R.msz, by
      show (IR.Sem.wr ist.mem _ n v).size = 65536
      rw [wr_size]; exact R.isz, R.tsz, ha, hhl, hina, hinhl⟩
  · -- the image is below the RAM
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := R.img.rom
    have hrs := R.rs
    have hram := W.ram
    rw [hm, wr_get_far _ _ _ _ _ hb (by omega)]
    exact R.img.bytes x b hx
  · show s'.mem.get! x = (IR.Sem.wr ist.mem _ n v).get! x
    rw [hm, wr_get _ _ _ _ _ (by rw [R.msz]; exact hb) (by rw [R.msz]; exact Nat.le_refl _),
      wr_get _ _ _ _ _ (by rw [R.isz]; exact hb) (by rw [R.isz]; exact Nat.le_refl _)]
    split
    · rfl
    · exact R.mem x hx
  · rw [hm]
    have hold := R.tmp t h1 h2
    rw [← hold]
    refine rd_congr _ _ _ _ ?_ (fun x hx1 hx2 => wr_get_far _ _ _ _ _ hb ?_)
    · exact hT.bound t h2
    · rcases Nat.lt_or_ge x (Z.c.layout.addr sl) with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge x (Z.c.layout.addr sl + n) with h' | h'
        · have := W.notmp (x - Z.c.layout.addr sl) (by omega)
          rw [show Z.c.layout.addr sl + (x - Z.c.layout.addr sl) = x by omega] at this
          exact absurd ⟨t, h2, hx1, hx2⟩ this
        · exact Or.inr h'

/-- The IR wrote bytes that are not shared: the code left the store out. -/
theorem Rel.wr_dead (ok : Z.OK) {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E dt regs ist tmps s) {n : Nat} {sl : Slot} (W : WrSlot Z E n sl) (v : Nat)
    (hdead : ∀ j, j < n → ¬ Z.data (Z.c.layout.addr sl + j))
    (ha : ∀ o, o ∈ regs'.a → Own E o → s.a.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 1 o)
    (hhl : ∀ o, o ∈ regs'.hl → Own E o → s.hl.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 2 o)
    (hina : ∀ a, Opd.slot a ∈ regs'.a → Own E (.slot a) → Z.use (a, 1))
    (hinhl : ∀ a, Opd.slot a ∈ regs'.hl → Own E (.slot a) → Z.use (a, 2)) :
    Rel Z E dt regs' { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps s := by
  have hb := ok.dbound sl n W.dst
  refine ⟨R.img, R.run, fun x hx => ?_, R.tmp, R.rs, R.msz, by
    show (IR.Sem.wr ist.mem _ n v).size = 65536
    rw [wr_size]; exact R.isz, R.tsz, ha, hhl, hina, hinhl⟩
  show s.mem.get! x = (IR.Sem.wr ist.mem _ n v).get! x
  rw [wr_get_far _ _ _ _ _ hb ?_]
  · exact R.mem x hx
  · rcases Nat.lt_or_ge x (Z.c.layout.addr sl) with h | h
    · exact Or.inl h
    · rcases Nat.lt_or_ge x (Z.c.layout.addr sl + n) with h' | h'
      · have := hdead (x - Z.c.layout.addr sl) (by omega)
        rw [show Z.c.layout.addr sl + (x - Z.c.layout.addr sl) = x by omega] at this
        exact absurd hx this
      · exact Or.inr h'

/-- A temporary is assigned: its slot, if it has one, was written. -/
theorem Rel.wr_tmp (ok : Z.OK) (hT : FnLay Z E) {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat}
    {s s' : Cpu} (R : Rel Z E dt regs ist tmps s) {n t : Nat} (W : WrTmp E n t) (v : Nat)
    (hm : if E.spilled[t]! = true then s'.mem = IR.Sem.wr s.mem (tmpAddr Z E t) n v else s'.mem = s.mem)
    (hr : s'.ramStart = s.ramStart) (hh : s'.halted = s.halted)
    (ha : ∀ o, o ∈ regs'.a → Own E o → s'.a.toNat =
      IR.Sem.opd Z.c ist (tmps.setIfInBounds t (IR.modN n v)) 1 o)
    (hhl : ∀ o, o ∈ regs'.hl → Own E o → s'.hl.toNat =
      IR.Sem.opd Z.c ist (tmps.setIfInBounds t (IR.modN n v)) 2 o)
    (hina : ∀ a, Opd.slot a ∈ regs'.a → Own E (.slot a) → Z.use (a, 1))
    (hinhl : ∀ a, Opd.slot a ∈ regs'.hl → Own E (.slot a) → Z.use (a, 2)) :
    Rel Z E (dtAfter dt (.tmp t)) regs' ist (tmps.setIfInBounds t (IR.modN n v)) s' := by
  by_cases hsp : E.spilled[t]! = true
  · rw [if_pos hsp] at hm
    have hb : tmpAddr Z E t + n ≤ 65536 := by have := hT.bound t hsp; rw [W.size] at this; exact this
    have hram := hT.ram t hsp
    refine ⟨⟨by rw [hr]; exact R.img.rom, fun x b hx => ?_⟩, by rw [hh]; exact R.run, fun x hx => ?_,
      fun t' h1 h2 => ?_, by rw [hr]; exact R.rs, by rw [hm, wr_size]; exact R.msz, R.isz,
      by rw [Array.size_setIfInBounds]; exact R.tsz, ha, hhl, hina, hinhl⟩
    · have hlt : x < Z.a.bytes.size := by
        rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at hx; cases hx
      have hrom := R.img.rom
      have hrs := R.rs
      rw [hm, wr_get_far _ _ _ _ _ hb (by omega)]
      exact R.img.bytes x b hx
    · rw [hm, wr_get_far _ _ _ _ _ hb ?_]
      · exact R.mem x hx
      · rcases Nat.lt_or_ge x (tmpAddr Z E t) with h | h
        · exact Or.inl h
        · rcases Nat.lt_or_ge x (tmpAddr Z E t + n) with h' | h'
          · have := hT.nodata t hsp (x - tmpAddr Z E t) (by rw [W.size]; omega)
            rw [show tmpAddr Z E t + (x - tmpAddr Z E t) = x by omega] at this
            exact absurd hx this
          · exact Or.inr h'
    · by_cases htt : t' = t
      · subst htt
        rw [hm, W.size, rd_wr _ _ _ _ (by rw [R.msz]; exact hb) (by rw [R.msz]; exact Nat.le_refl _)]
        have hlt : t' < tmps.size := by rw [R.tsz]; exact W.lt
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hlt, IR.modN]
      · have hd : dt t' := by
          rcases h1 with h | h
          · exact h
          · cases h; exact absurd rfl htt
        have hold := R.tmp t' hd h2
        rw [hm, rd_wr_far _ _ _ _ _ _ (hT.bound t' h2) hb ?_, hold]
        · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm htt)]
        · have := hT.apart t t' (Ne.symm htt) hsp h2
          rw [W.size] at this
          omega
  · rw [if_neg hsp] at hm
    refine ⟨R.img.congr hr hm, by rw [hh]; exact R.run, fun x hx => by rw [hm]; exact R.mem x hx,
      fun t' h1 h2 => ?_, by rw [hr]; exact R.rs, by rw [hm]; exact R.msz, R.isz,
      by rw [Array.size_setIfInBounds]; exact R.tsz, ha, hhl, hina, hinhl⟩
    have htt : t' ≠ t := fun e => hsp (e ▸ h2)
    have hd : dt t' := by
      rcases h1 with h | h
      · exact h
      · cases h; exact absurd rfl htt
    rw [hm, R.tmp t' hd h2]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm htt)]

/-! ## What the CPU writes -/

theorem cpu_wr_mem (s : Cpu) (x : UInt16) (v : UInt8) (h : s.ramStart.toNat ≤ x.toNat) :
    (s.wr x v).mem = s.mem.set! x.toNat v := by
  unfold Cpu.wr
  have : ¬ x < s.ramStart := by
    rw [UInt16.not_lt]
    exact UInt16.le_iff_toNat_le.mpr h
  rw [if_neg this]

/-- One byte, as the IR writes it. -/
theorem wr_one (m : ByteArray) (a v : Nat) (ha : a < 65536) (b : UInt8) (hb : b.toNat = v % 256) :
    m.set! a b = IR.Sem.wr m a 1 v := by
  have : b = UInt8.ofNat (v % 256) := by
    apply UInt8.toNat_inj.mp
    rw [hb, UInt8.toNat_ofNat']
    omega
  simp [IR.Sem.wr, Nat.mod_eq_of_lt ha, this]

theorem Rel.dt_mono {dt' : Nat → Prop} {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E dt regs ist tmps s) (h : ∀ t, dt' t → dt t) : Rel Z E dt' regs ist tmps s :=
  ⟨R.img, R.run, R.mem, fun t h1 h2 => R.tmp t (h t h1) h2, R.rs, R.msz, R.isz, R.tsz, R.ra, R.rhl, R.ina, R.inhl⟩

theorem wpg_storeNeeded (sl : Slot) (n : Nat) (s0 : GS) (Q : Bool → GS → Prop)
    (h : ∀ b, (b = false → sl.area = .frame E.fn.name ∧
      ∃ lv, E.live = some lv ∧ ∀ k, k < n → lv.getD (sl.off + k) true = false) → Q b s0) :
    wpg (storeNeeded sl n) E Q s0 := by
  unfold storeNeeded
  simp only [wpg_bind, wpg_read]
  split
  · rw [wpg_pure]
    exact h true (fun hb => by cases hb)
  · rename_i hne
    have harea : sl.area = .frame E.fn.name := by simpa using hne
    split
    · rw [wpg_pure]
      exact h true (fun hb => by cases hb)
    · rename_i lv hlv
      rw [wpg_pure]
      refine h _ (fun hb => ⟨harea, lv, hlv, fun k hk => ?_⟩)
      have := List.any_eq_false.mp hb k (by simpa using hk)
      simpa using this

theorem wpg_tmpSlot (t : Nat) (s0 : GS) (Q : Option Val → GS → Prop)
    (h : Q (if E.spilled[t]! = true then some (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }) else none) s0) :
    wpg (tmpSlot t) E Q s0 := by
  unfold tmpSlot
  simp only [wpg_bind, wpg_read]
  split
  · rename_i hsp
    rw [wpg_pure]
    rw [if_pos hsp] at h
    exact h
  · rename_i hsp
    rw [wpg_pure]
    rw [if_neg hsp] at h
    exact h

/-- The registers and the stack pointer are as they were. -/
def KeepR (s s' : Cpu) : Prop :=
  s'.a = s.a ∧ s'.f = s.f ∧ s'.b = s.b ∧ s'.c = s.c ∧ s'.d = s.d ∧ s'.e = s.e ∧ s'.h = s.h ∧ s'.l = s.l ∧
    s'.sp = s.sp

theorem KeepR.refl (s : Cpu) : KeepR s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What `storeA d` promises: the byte in `A` is stored as the IR stores `v`. -/
def StoreA (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (d : Dst) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ d.opd ∈ s1.regs.a ∧ (∀ o, o ∈ s1.regs.hl → o ∈ s0.regs.hl) ∧
    (GExt s1 sF → ∀ ist tmps s v, Wr Z E 1 d → Rel Z E dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → s.a.toNat = v % 256 →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E (dtAfter dt d) s1.regs (IR.Sem.setDst Z.c ist tmps 1 d v).1 (IR.Sem.setDst Z.c ist tmps 1 d v).2 s' ∧
        KeepR s s')

/-- What the tracker keeps across a write of `n` bytes at `sl` still holds. -/
theorem kill_keep (ok : Z.OK) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E dt regs ist tmps s) {n : Nat} {sl : Slot} (hdst : Z.dst (sl, n)) (v : Nat) :
    (∀ o, o ∈ regs.a.filter (fun o => !overlaps o 1 sl n) → Own E o → s.a.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 1 o) ∧
    (∀ o, o ∈ regs.hl.filter (fun o => !overlaps o 2 sl n) → Own E o → s.hl.toNat =
      IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps 2 o) := by
  refine ⟨fun o ho hown => ?_, fun o ho hown => ?_⟩
  · obtain ⟨hin, hno⟩ := List.mem_filter.mp ho
    rw [opd_wr_keep ok (fun a ha => R.ina a (ha ▸ hin) (ha ▸ hown)) hdst (by simpa using hno)]
    exact R.ra o hin hown
  · obtain ⟨hin, hno⟩ := List.mem_filter.mp ho
    rw [opd_wr_keep ok (fun a ha => R.inhl a (ha ▸ hin) (ha ▸ hown)) hdst (by simpa using hno)]
    exact R.rhl o hin hown

/-- What the tracker keeps when the temporary `t` is assigned still holds. -/
theorem forget_keep {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E dt regs ist tmps s) (t x : Nat) :
    (∀ o, o ∈ regs.a.filter (· != .tmp t) → Own E o → s.a.toNat =
      IR.Sem.opd Z.c ist (tmps.setIfInBounds t x) 1 o) ∧
    (∀ o, o ∈ regs.hl.filter (· != .tmp t) → Own E o → s.hl.toNat =
      IR.Sem.opd Z.c ist (tmps.setIfInBounds t x) 2 o) := by
  refine ⟨fun o ho hown => ?_, fun o ho hown => ?_⟩
  · obtain ⟨hin, hne⟩ := List.mem_filter.mp ho
    rw [opd_tmp_keep _ _ _ _ _ _ (by simpa using hne)]
    exact R.ra o hin hown
  · obtain ⟨hin, hne⟩ := List.mem_filter.mp ho
    rw [opd_tmp_keep _ _ _ _ _ _ (by simpa using hne)]
    exact R.rhl o hin hown

/-- `ld (nn),a` at a slot's address writes the byte the IR writes. -/
theorem ld_mem_a (ok : Z.OK) {s : Cpu} {sl : Slot} {ad pc v : Nat} {i : Instr}
    (hi : i.immVal? = some (slotVal sl)) (harea : Z.c.layout.areaAddr sl.area = some ad)
    (hb : Z.c.layout.addr sl + 1 ≤ 65536) (hram : s.ramStart.toNat ≤ Z.c.layout.addr sl)
    (hA : s.a.toNat = v % 256) :
    (((skip (op1 s) 2).wr (i.immW (Z.a.env pc)) (op1 s).a).tick 13).mem =
      IR.Sem.wr s.mem (Z.c.layout.addr sl) 1 v := by
  have hnn : (i.immW (Z.a.env pc)).toNat = Z.c.layout.addr sl :=
    immW_toNat _ _ _ _ hi (slot_val ok sl ad pc harea) (by omega)
  simp only [zsim]
  rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hnn]; exact hram)]
  simp only [zsim]
  rw [hnn]
  exact wr_one _ _ _ (by omega) _ hA

theorem storeA_ok {base : Nat} {sF : GS} (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst)
    (s0 : GS) : wpg (storeA d) E (StoreA Z E base sF dt d s0) s0 := by
  unfold storeA
  cases d with
  | slot sl =>
    simp only [wpg_bind, killWrite, wpg_setRegs]
    refine wpg_storeNeeded sl 1 _ _ (fun b hb => ?_)
    cases b with
    | true =>
      simp only [if_true, wpg_ins, wpg_setRegs]
      refine ⟨GExt.push _ _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hA => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨ad0, harea⟩ := W.area
      have hb := ok.dbound sl 1 W.dst
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := { s0 with regs := _ }) (i := ⟨.ld, [.mem (slotVal sl), .a]⟩) hx rfl
        R.img R.run ⟨ad, had, hpc⟩
        (s' := ((skip (op1 s) 2).wr (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (slotVal sl), .a]⟩) (op1 s).a).tick 13)
        (fun ad' had' => by
          rw [had] at had'
          cases had'
          rfl) rfl
      have hmem := ld_mem_a ok (s := s) (pc := ad) (i := ⟨.ld, [.mem (slotVal sl), .a]⟩) rfl harea hb
        (by rw [R.rs]; exact W.ram) hA
      obtain ⟨ka, khl⟩ := kill_keep ok R W.dst v
      refine ⟨_, hst, hat', ?_, by simp only [KeepR, zsim, and_self]⟩
      refine Rel.dt_mono (Rel.wr_slot ok hT R W v hmem (by simp only [zsim]) (by simp only [zsim])
        (fun o ho hown => ?_) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_))
        (fun t ht => by rcases ht with h | h; exact h; cases h)
      · simp only [zsim]
        rcases List.mem_cons.mp ho with rfl | ho'
        · show _ = IR.Sem.rd (IR.Sem.wr ist.mem _ 1 v) _ 1
          rw [rd_wr _ _ _ _ (by rw [R.isz]; exact hb) (by rw [R.isz]; exact Nat.le_refl _), hA]
        · exact ka o ho' hown
      · simp only [zsim]
        exact khl o ho hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
          exact W.use hown
        · exact R.ina a (List.mem_filter.mp ha').1 hown
      · exact R.inhl a (List.mem_filter.mp ha).1 hown
    | false =>
      simp only [Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      obtain ⟨harea', lv, hlv, hdeadk⟩ := hb rfl
      refine ⟨GExt.refl _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hA => ?_⟩
      have hb := ok.dbound sl 1 W.dst
      obtain ⟨ka, khl⟩ := kill_keep ok R W.dst v
      refine ⟨s, Steps.refl _ _, hat, ?_, KeepR.refl s⟩
      refine Rel.dt_mono (Rel.wr_dead ok R W v (W.dead harea' lv hlv hdeadk)
        (fun o ho hown => ?_) (fun o ho hown => khl o ho hown) (fun a ha hown => ?_) (fun a ha hown => ?_))
        (fun t ht => by rcases ht with h | h; exact h; cases h)
      · rcases List.mem_cons.mp ho with rfl | ho'
        · show _ = IR.Sem.rd (IR.Sem.wr ist.mem _ 1 v) _ 1
          rw [rd_wr _ _ _ _ (by rw [R.isz]; exact hb) (by rw [R.isz]; exact Nat.le_refl _), hA]
        · exact ka o ho' hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
          exact W.use hown
        · exact R.ina a (List.mem_filter.mp ha').1 hown
      · exact R.inhl a (List.mem_filter.mp ha).1 hown
  | tmp t =>
    simp only [wpg_bind, forget, wpg_setRegs]
    refine wpg_tmpSlot t _ _ ?_
    have head : ∀ (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) (v : Nat) (regs : Regs),
        Rel Z E dt regs ist tmps s → WrTmp E 1 t → s.a.toNat = v % 256 →
        s.a.toNat = IR.Sem.opd Z.c ist (tmps.setIfInBounds t (IR.modN 1 v)) 1 (.tmp t) := by
      intro ist tmps s v regs R W hA
      have hlt : t < tmps.size := by rw [R.tsz]; exact W.lt
      show _ = IR.modN 1 ((tmps.setIfInBounds t (IR.modN 1 v)).getD t 0)
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hlt, IR.modN, hA]
    by_cases hsp : E.spilled[t]! = true
    · simp only [hsp, if_true, wpg_ins, wpg_setRegs]
      refine ⟨GExt.push _ _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hA => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨ad0, harea⟩ := hT.area
      have hb : tmpAddr Z E t + 1 ≤ 65536 := by have := hT.bound t hsp; rw [W.size] at this; exact this
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := { s0 with regs := _ })
        (i := ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .a]⟩) hx rfl
        R.img R.run ⟨ad, had, hpc⟩
        (s' := ((skip (op1 s) 2).wr (Instr.immW (Z.a.env ad)
          ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .a]⟩) (op1 s).a).tick 13)
        (fun ad' had' => by
          rw [had] at had'
          cases had'
          rfl) rfl
      have hmem := ld_mem_a ok (s := s) (pc := ad) (sl := { area := .frame E.fn.name, off := E.tmpOff[t]! })
        (i := ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .a]⟩) rfl harea hb
        (by rw [R.rs]; exact hT.ram t hsp) hA
      obtain ⟨ka, khl⟩ := forget_keep R t (IR.modN 1 v)
      refine ⟨_, hst, hat', ?_, by simp only [KeepR, zsim, and_self]⟩
      refine Rel.wr_tmp ok hT R W v (by rw [if_pos hsp]; exact hmem) (by simp only [zsim]) (by simp only [zsim])
        (fun o ho hown => ?_) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_)
      · simp only [zsim]
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R W hA
        · exact ka o ho' hown
      · simp only [zsim]
        exact khl o ho hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
        · exact R.ina a (List.mem_filter.mp ha').1 hown
      · exact R.inhl a (List.mem_filter.mp ha).1 hown
    · simp only [hsp, Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      refine ⟨GExt.refl _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hA => ?_⟩
      obtain ⟨ka, khl⟩ := forget_keep R t (IR.modN 1 v)
      refine ⟨s, Steps.refl _ _, hat, ?_, KeepR.refl s⟩
      refine Rel.wr_tmp ok hT R W v (by rw [if_neg hsp]) rfl rfl
        (fun o ho hown => ?_) (fun o ho hown => khl o ho hown) (fun a ha hown => ?_) (fun a ha hown => ?_)
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R W hA
        · exact ka o ho' hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
        · exact R.ina a (List.mem_filter.mp ha').1 hown
      · exact R.inhl a (List.mem_filter.mp ha).1 hown

/-! ## Two bytes -/

/-- Two bytes, as the IR writes them. -/
theorem wr_two (m : ByteArray) (a v : Nat) (ha : a + 1 < 65536) (b0 b1 : UInt8) (h0 : b0.toNat = v % 256)
    (h1 : b1.toNat = v / 256 % 256) : (m.set! a b0).set! (a + 1) b1 = IR.Sem.wr m a 2 v := by
  have e0 : b0 = UInt8.ofNat (v % 256) := by
    apply UInt8.toNat_inj.mp
    rw [h0, UInt8.toNat_ofNat']
    omega
  have e1 : b1 = UInt8.ofNat (v / 256 % 256) := by
    apply UInt8.toNat_inj.mp
    rw [h1, UInt8.toNat_ofNat']
    omega
  simp [IR.Sem.wr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : a < 65536), e0, e1]

/-- `ld (nn),hl` at a slot's address writes the two bytes the IR writes. -/
theorem ld_mem_hl (ok : Z.OK) {s : Cpu} {sl : Slot} {ad pc v : Nat} {i : Instr}
    (hi : i.immVal? = some (slotVal sl)) (harea : Z.c.layout.areaAddr sl.area = some ad)
    (hb : Z.c.layout.addr sl + 2 ≤ 65536) (hram : s.ramStart.toNat ≤ Z.c.layout.addr sl)
    (hHL : s.hl.toNat = v % 65536) :
    (((skip (op1 s) 2).wr16 (i.immW (Z.a.env pc)) (op1 s).hl).tick 16).mem =
      IR.Sem.wr s.mem (Z.c.layout.addr sl) 2 v := by
  have hnn : (i.immW (Z.a.env pc)).toNat = Z.c.layout.addr sl :=
    immW_toNat _ _ _ _ hi (slot_val ok sl ad pc harea) (by omega)
  have hnn1 : (i.immW (Z.a.env pc) + 1).toNat = Z.c.layout.addr sl + 1 := by
    rw [UInt16.toNat_add, hnn]
    show (Z.c.layout.addr sl + 1) % 65536 = _
    omega
  simp only [zsim, Cpu.wr16]
  rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hnn1]; omega),
    cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hnn]; exact hram)]
  simp only [zsim]
  rw [hnn, hnn1]
  refine wr_two _ _ _ (by omega) _ _ ?_ ?_
  · rw [UInt16.toNat_toUInt8, hHL]
    omega
  · rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, hHL]
    rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]
    omega

/-- What `storeHL d` promises: the word in `HL` is stored as the IR stores `v`. -/
def StoreHL (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (d : Dst) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ d.opd ∈ s1.regs.hl ∧ (∀ o, o ∈ s1.regs.a → o ∈ s0.regs.a) ∧
    (GExt s1 sF → ∀ ist tmps s v, Wr Z E 2 d → Rel Z E dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → s.hl.toNat = v % 65536 →
      ∃ s', Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E (dtAfter dt d) s1.regs (IR.Sem.setDst Z.c ist tmps 2 d v).1 (IR.Sem.setDst Z.c ist tmps 2 d v).2 s' ∧
        KeepR s s')

theorem storeHL_ok {base : Nat} {sF : GS} (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (d : Dst)
    (s0 : GS) : wpg (storeHL d) E (StoreHL Z E base sF dt d s0) s0 := by
  unfold storeHL
  cases d with
  | slot sl =>
    simp only [wpg_bind, killWrite, wpg_setRegs]
    refine wpg_storeNeeded sl 2 _ _ (fun b hb => ?_)
    have head : ∀ (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) (v : Nat) (regs : Regs),
        Rel Z E dt regs ist tmps s → Z.c.layout.addr sl + 2 ≤ 65536 → s.hl.toNat = v % 65536 →
        s.hl.toNat = IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) 2 v } tmps 2 (.slot sl) := by
      intro ist tmps s v regs R hb hHL
      show _ = IR.Sem.rd (IR.Sem.wr ist.mem _ 2 v) _ 2
      rw [rd_wr _ _ _ _ (by rw [R.isz]; exact hb) (by rw [R.isz]; exact Nat.le_refl _), hHL]
    cases b with
    | true =>
      simp only [if_true, wpg_ins, wpg_setRegs]
      refine ⟨GExt.push _ _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hHL => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨ad0, harea⟩ := W.area
      have hb := ok.dbound sl 2 W.dst
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := { s0 with regs := _ }) (i := ⟨.ld, [.mem (slotVal sl), .hl]⟩) hx rfl
        R.img R.run ⟨ad, had, hpc⟩
        (s' := ((skip (op1 s) 2).wr16 (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (slotVal sl), .hl]⟩) (op1 s).hl).tick 16)
        (fun ad' had' => by
          rw [had] at had'
          cases had'
          rfl) rfl
      have hmem := ld_mem_hl ok (s := s) (pc := ad) (i := ⟨.ld, [.mem (slotVal sl), .hl]⟩) rfl harea hb
        (by rw [R.rs]; exact W.ram) hHL
      obtain ⟨ka, khl⟩ := kill_keep ok R W.dst v
      refine ⟨_, hst, hat', ?_, by simp only [KeepR, zsim, and_self]⟩
      refine Rel.dt_mono (Rel.wr_slot ok hT R W v hmem (by simp only [zsim]) (by simp only [zsim])
        (fun o ho hown => ?_) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_))
        (fun t ht => by rcases ht with h | h; exact h; cases h)
      · simp only [zsim]
        exact ka o ho hown
      · simp only [zsim]
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R hb hHL
        · exact khl o ho' hown
      · exact R.ina a (List.mem_filter.mp ha).1 hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
          exact W.use hown
        · exact R.inhl a (List.mem_filter.mp ha').1 hown
    | false =>
      simp only [Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      obtain ⟨harea', lv, hlv, hdeadk⟩ := hb rfl
      refine ⟨GExt.refl _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hHL => ?_⟩
      have hb := ok.dbound sl 2 W.dst
      obtain ⟨ka, khl⟩ := kill_keep ok R W.dst v
      refine ⟨s, Steps.refl _ _, hat, ?_, KeepR.refl s⟩
      refine Rel.dt_mono (Rel.wr_dead ok R W v (W.dead harea' lv hlv hdeadk)
        (fun o ho hown => ka o ho hown) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_))
        (fun t ht => by rcases ht with h | h; exact h; cases h)
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R hb hHL
        · exact khl o ho' hown
      · exact R.ina a (List.mem_filter.mp ha).1 hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
          exact W.use hown
        · exact R.inhl a (List.mem_filter.mp ha').1 hown
  | tmp t =>
    simp only [wpg_bind, forget, wpg_setRegs]
    refine wpg_tmpSlot t _ _ ?_
    have head : ∀ (ist : IR.Sem.St) (tmps : Array Nat) (s : Cpu) (v : Nat) (regs : Regs),
        Rel Z E dt regs ist tmps s → WrTmp E 2 t → s.hl.toNat = v % 65536 →
        s.hl.toNat = IR.Sem.opd Z.c ist (tmps.setIfInBounds t (IR.modN 2 v)) 2 (.tmp t) := by
      intro ist tmps s v regs R W hHL
      have hlt : t < tmps.size := by rw [R.tsz]; exact W.lt
      show _ = IR.modN 2 ((tmps.setIfInBounds t (IR.modN 2 v)).getD t 0)
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hlt, IR.modN, hHL]
    by_cases hsp : E.spilled[t]! = true
    · simp only [hsp, if_true, wpg_ins, wpg_setRegs]
      refine ⟨GExt.push _ _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hHL => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨ad0, harea⟩ := hT.area
      have hb : tmpAddr Z E t + 2 ≤ 65536 := by have := hT.bound t hsp; rw [W.size] at this; exact this
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := { s0 with regs := _ })
        (i := ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .hl]⟩) hx rfl
        R.img R.run ⟨ad, had, hpc⟩
        (s' := ((skip (op1 s) 2).wr16 (Instr.immW (Z.a.env ad)
          ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .hl]⟩) (op1 s).hl).tick 16)
        (fun ad' had' => by
          rw [had] at had'
          cases had'
          rfl) rfl
      have hmem := ld_mem_hl ok (s := s) (pc := ad) (sl := { area := .frame E.fn.name, off := E.tmpOff[t]! })
        (i := ⟨.ld, [.mem (slotVal { area := .frame E.fn.name, off := E.tmpOff[t]! }), .hl]⟩) rfl harea hb
        (by rw [R.rs]; exact hT.ram t hsp) hHL
      obtain ⟨ka, khl⟩ := forget_keep R t (IR.modN 2 v)
      refine ⟨_, hst, hat', ?_, by simp only [KeepR, zsim, and_self]⟩
      refine Rel.wr_tmp ok hT R W v (by rw [if_pos hsp]; exact hmem) (by simp only [zsim]) (by simp only [zsim])
        (fun o ho hown => ?_) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_)
      · simp only [zsim]
        exact ka o ho hown
      · simp only [zsim]
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R W hHL
        · exact khl o ho' hown
      · exact R.ina a (List.mem_filter.mp ha).1 hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
        · exact R.inhl a (List.mem_filter.mp ha').1 hown
    · simp only [hsp, Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      refine ⟨GExt.refl _, by simp [Dst.opd], fun o ho => (List.mem_filter.mp ho).1,
        fun hx ist tmps s v W R hat hHL => ?_⟩
      obtain ⟨ka, khl⟩ := forget_keep R t (IR.modN 2 v)
      refine ⟨s, Steps.refl _ _, hat, ?_, KeepR.refl s⟩
      refine Rel.wr_tmp ok hT R W v (by rw [if_neg hsp]) rfl rfl
        (fun o ho hown => ka o ho hown) (fun o ho hown => ?_) (fun a ha hown => ?_) (fun a ha hown => ?_)
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact head ist tmps s v _ R W hHL
        · exact khl o ho' hown
      · exact R.ina a (List.mem_filter.mp ha).1 hown
      · rcases List.mem_cons.mp ha with h | ha'
        · cases h
        · exact R.inhl a (List.mem_filter.mp ha').1 hown

end

end Ember.Proof.Z80Gen
