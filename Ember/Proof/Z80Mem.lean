import Ember.Proof.Z80After
import Ember.Proof.Z80Addr

/-!
# Ember.Proof.Z80Mem — memory through an address: `lea`, `load` (plan M7.3)

The address by `genAddr_ok`; a trap of the index check is the trap of
the IR's instruction.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The `n` bytes at the address are shared bytes, whatever the index (below its bound). -/
def AddrData (Z : ZCtx) (p : IR.Addr) (n : Nat) : Prop :=
  ∀ ist tmps a, IR.Sem.addr Z.c ist tmps p = some a → IR.Sem.inBound Z.c ist tmps p = true →
    a + n ≤ 65536 ∧ ∀ j, j < n → Z.data (a + j)

/-- `ld a,(hl)`, `ld h,(hl)` as the model runs them. -/
def ldAM (s : Cpu) : Cpu := ((op1 s).setReg .hl 7 ((op1 s).rd (op1 s).hl)).tick 7
def ldHM (s : Cpu) : Cpu := ((op1 s).setReg .hl 4 ((op1 s).rd (op1 s).hl)).tick 7

theorem does_ld_a_m : Does ⟨.ld, [.a, .mhl]⟩ ldAM :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldAM, zsim, and_self], fun s => by simp only [ldAM, zsim]⟩
theorem does_ld_h_m : Does ⟨.ld, [.h, .mhl]⟩ ldHM :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldHM, zsim, and_self], fun s => by simp only [ldHM, zsim]⟩
theorem does_inc_hl : Does ⟨.inc, [.hl]⟩ incHL :=
  ⟨fun _ _ _ => rfl, rfl, fun s => (incHL_keep s).1, fun _ => rfl⟩

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- **`lea`**: the address, stored. -/
theorem lea_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.lea d p)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ Wr Z E 2 d → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.lea d p) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.lea d p)))) s0 := by
  simp only [genInstr, wpg_bind]
  refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
  intro _ s1 ⟨hx1, _, _, ha⟩
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hN, hwr⟩ fr ist tmps s R hat => ?_⟩
  have h1 := ha (hx2.trans hxF) hN fr ist tmps s R hat
  simp only [IR.Sem.step]
  cases haddr : IR.Sem.addr Z.c ist tmps p with
  | none =>
    rw [haddr] at h1
    exact h1
  | some a =>
    rw [haddr] at h1
    by_cases hb : IR.Sem.inBound Z.c ist tmps p = true
    · simp only [hb, if_true]
      obtain ⟨s', st, at', R', _, _, hv⟩ := h1
      obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' (a % 65536) hwr R' at' (by rw [hv, Nat.mod_mod])
      exact ⟨s'', st.trans st2, at2, R2⟩
    · simp only [hb, Bool.false_eq_true, if_false]
      trivial

/-- **`load` of one byte.** -/
theorem load1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.load 1 d p)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrData Z p 1 ∧ Wr Z E 1 d → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.load 1 d p) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.load 1 d p)))) s0 := by
  simp only [genInstr, store, wpg_bind, beq_self_eq_true, if_true]
  refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
  intro _ s1 ⟨hx1, hhl1, _, ha⟩
  simp only [wpg_ins, wpg_setRegs]
  refine wpg_mono (storeA_ok (dt := dt) ok hT F d _) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans (((GExt.push _ _).trans (GExt.regs _ _)).trans hx2),
    fun hxF ⟨hN, hD, hwr⟩ fr ist tmps s R hat => ?_⟩
  have hxm : GExt { s1 with out := s1.out.push (.ins ⟨.ld, [.a, .mhl]⟩) } sF :=
    (GExt.regs _ _).trans (hx2.trans hxF)
  have h1 := ha ((GExt.push _ _).trans hxm) hN fr ist tmps s R hat
  simp only [IR.Sem.step]
  cases haddr : IR.Sem.addr Z.c ist tmps p with
  | none =>
    rw [haddr] at h1
    exact h1
  | some a =>
    rw [haddr] at h1
    by_cases hb : IR.Sem.inBound Z.c ist tmps p = true
    · simp only [hb, if_true]
      obtain ⟨s', st, at', R', _, _, hv⟩ := h1
      obtain ⟨hbd, hdat⟩ := hD ist tmps a haddr hb
      obtain ⟨st1, at1, _⟩ := run_reg ok F (s0 := s1) hxm rfl R'.mach at' (ldAM s') (fun _ _ => rfl) rfl
        (does_ld_a_m.sys s')
      have hval : (ldAM s').a.toNat = IR.Sem.rd ist.mem a 1 := by
        simp only [ldAM, zsim]
        show (s'.mem.get! s'.hl.toNat).toNat = _
        rw [hv, Nat.mod_eq_of_lt (by omega), R'.mem a (hdat 0 (by omega)), rd_one _ _ (by omega)]
      obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps (ldAM s') (IR.Sem.rd ist.mem a 1) hwr
        (R'.of_sys (does_ld_a_m.sys s') rfl (fun o h => h) (fun o ho => by rw [hhl1] at ho; cases ho)
          (fun n o h => h)) at1 (by
          rw [hval]
          exact (Nat.mod_eq_of_lt (rd_lt _ _ 1)).symm)
      exact ⟨s'', (st.trans st1).trans st2, at2, R2⟩
    · simp only [hb, Bool.false_eq_true, if_false]
      trivial

/-- **`load` of two bytes.** -/
theorem load2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.load 2 d p)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrData Z p 2 ∧ Wr Z E 2 d → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.load 2 d p) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.load 2 d p)))) s0 := by
  simp only [genInstr, store, wpg_bind, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
    beq_self_eq_true, if_true]
  refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
  intro _ s1 ⟨hx1, hhl1, _, ha⟩
  simp only [wpg_ins, wpg_setRegs]
  refine wpg_mono (storeHL_ok (dt := dt) ok hT F d _) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  have hxm0 : GExt s1 (pushL [⟨.ld, [.a, .mhl]⟩, ⟨.inc, [.hl]⟩, ⟨.ld, [.h, .mhl]⟩, ⟨.ld, [.l, .a]⟩] s1) :=
    pushL_ext _ _
  refine ⟨hx1.trans ((hxm0.trans (GExt.regs _ _)).trans hx2),
    fun hxF ⟨hN, hD, hwr⟩ fr ist tmps s R hat => ?_⟩
  have hxm : GExt (pushL [⟨.ld, [.a, .mhl]⟩, ⟨.inc, [.hl]⟩, ⟨.ld, [.h, .mhl]⟩, ⟨.ld, [.l, .a]⟩] s1) sF :=
    (GExt.regs _ _).trans (hx2.trans hxF)
  have h1 := ha (hxm0.trans hxm) hN fr ist tmps s R hat
  simp only [IR.Sem.step]
  cases haddr : IR.Sem.addr Z.c ist tmps p with
  | none =>
    rw [haddr] at h1
    exact h1
  | some a =>
    rw [haddr] at h1
    by_cases hb : IR.Sem.inBound Z.c ist tmps p = true
    · simp only [hb, if_true]
      obtain ⟨s', st, at', R', _, _, hv⟩ := h1
      obtain ⟨hbd, hdat⟩ := hD ist tmps a haddr hb
      obtain ⟨st1, at1, _, hS⟩ := run_list ok F
        [(⟨.ld, [.a, .mhl]⟩, ldAM), (⟨.inc, [.hl]⟩, incHL), (⟨.ld, [.h, .mhl]⟩, ldHM), (⟨.ld, [.l, .a]⟩, ldRA 5)]
        (by
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · exact does_ld_a_m
          · exact does_inc_hl
          · exact does_ld_h_m
          · exact does_ld_l_a) s1 s' hxm R'.mach at'
      have hhl : s'.hl.toNat = a := by rw [hv, Nat.mod_eq_of_lt (by omega)]
      have e1 : (ldAM s').a = s'.mem.get! a := by
        simp only [ldAM, zsim]
        show s'.mem.get! s'.hl.toNat = _
        rw [hhl]
      have e2 : (incHL (ldAM s')).hl.toNat = a + 1 := by
        rw [incHL_hl]
        simp only [ldAM, zsim]
        rw [hhl, Nat.mod_eq_of_lt (by omega)]
      have e3 : (ldHM (incHL (ldAM s'))).h = s'.mem.get! (a + 1) := by
        simp only [ldHM, zsim]
        show (incHL (ldAM s')).mem.get! (incHL (ldAM s')).hl.toNat = _
        rw [e2, (incHL_keep _).1.1]
        simp only [ldAM, zsim]
      have e4 : (ldHM (incHL (ldAM s'))).a = s'.mem.get! a := by
        simp only [ldHM, zsim]
        rw [(incHL_keep _).2.1, e1]
      have hval : (ldRA 5 (ldHM (incHL (ldAM s')))).hl.toNat = IR.Sem.rd ist.mem a 2 := by
        rw [hl_toNat]
        simp only [ldRA, zsim]
        rw [e3, e4, rd_two _ _ (by omega), R'.mem a (hdat 0 (by omega)), R'.mem (a + 1) (hdat 1 (by omega))]
      obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps _ (IR.Sem.rd ist.mem a 2) hwr
        (R'.hl_gone hS rfl (Or.inl rfl) (fun n o h => h)) at1 (by
          show (ldRA 5 (ldHM (incHL (ldAM s')))).hl.toNat = _
          rw [hval]
          exact (Nat.mod_eq_of_lt (rd_lt _ _ 2)).symm)
      exact ⟨s'', (st.trans st1).trans st2, at2, R2⟩
    · simp only [hb, Bool.false_eq_true, if_false]
      trivial

/-! ## A write through an address -/

theorem opd_mem_irrel (c : IR.Ctx) (ist : IR.Sem.St) (m : ByteArray) (tmps : Array Nat) (n : Nat) {o : Opd}
    (h : isSlot o = false) : IR.Sem.opd c { ist with mem := m } tmps n o = IR.Sem.opd c ist tmps n o := by
  cases o with
  | slot sl => cases h
  | const v => rfl
  | tmp t => rfl

theorem own_of_noslot {o : Opd} (h : isSlot o = false) : Own E o := by
  cases o with
  | slot sl => cases h
  | const v => trivial
  | tmp t => trivial

/-- A byte with a property is not among bytes without it. -/
theorem far_of {P : Nat → Prop} {a n x : Nat} (h : ∀ j, j < n → P (a + j)) (hx : ¬ P x) : x < a ∨ a + n ≤ x := by
  rcases Nat.lt_or_ge x a with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge x (a + n) with h2 | h2
    · have := h (x - a) (by omega)
      rw [show a + (x - a) = x by omega] at this
      exact absurd this hx
    · exact Or.inr h2

/-- **The states agree after a write of shared bytes**, the tracker
claiming nothing of the slots. -/
theorem Rel.wr_mem {fr : Fr} (ok : Z.OK) (hT : FnLay Z E) {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat}
    {s s' : Cpu} (R : Rel Z E fr dt regs ist tmps s) {a n v : Nat} (hn : 0 < n) (hb : a + n ≤ 65536)
    (hd : ∀ j, j < n → Z.data (a + j)) (hw : ∀ j, j < n → Z.wr E.fn.name (a + j))
    (hacc : a + n ≤ Z.acc ∨ Z.acc + 8 ≤ a)
    (hm : s'.mem = IR.Sem.wr s.mem a n v) (hr : s'.ramStart = s.ramStart) (hh : s'.halted = s.halted)
    (hsp : s'.sp = s.sp)
    (hra : ∀ o, o ∈ regs'.a → isSlot o = false ∧ s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o)
    (hrhl : ∀ o, o ∈ regs'.hl → isSlot o = false ∧ s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o)
    (hracc : ∀ m o, regs'.acc = some (m, o) → isSlot o = false ∧ regs.acc = some (m, o)) :
    Rel Z E fr dt regs' { ist with mem := IR.Sem.wr ist.mem a n v } tmps s' := by
  have hroom := R.room
  have hram := (ok.ram a (by simpa using hd 0 hn)).1
  have hfar : ∀ x, ¬ Z.data x → s'.mem.get! x = s.mem.get! x := by
    intro x hx
    rw [hm, wr_get_far _ _ _ _ _ hb (far_of hd hx)]
  refine ⟨Img.of_wr R.img hr hm (by rw [R.rs]; exact hram) hb, by rw [hh]; exact R.run, fun x hx => ?_,
    fun t h1 h2 => ?_, by rw [hr]; exact R.rs, by rw [hm, wr_size]; exact R.msz, by
      show (IR.Sem.wr ist.mem a n v).size = 65536
      rw [wr_size]; exact R.isz, R.tsz, by rw [hsp]; exact R.sp, R.room, fun x h1 h2 => ?_, fun x hx => ?_,
      fun o ho _ => ?_, fun o ho _ => ?_, fun m o h _ => ?_, fun sl h => ?_, fun sl h => ?_, fun m sl h => ?_,
      fun m o h => R.nacc m o (hracc m o h).2⟩
  · show s'.mem.get! x = (IR.Sem.wr ist.mem a n v).get! x
    rw [hm, wr_get _ _ _ _ _ (by rw [R.msz]; exact hb) (by rw [R.msz]; exact Nat.le_refl _),
      wr_get _ _ _ _ _ (by rw [R.isz]; exact hb) (by rw [R.isz]; exact Nat.le_refl _)]
    split
    · rfl
    · exact R.mem x hx
  · rw [← R.tmp t h1 h2]
    refine rd_congr _ _ _ _ (hT.bound t h2) (fun x hx1 hx2 => hfar x ?_)
    have := hT.nodata t h2 (x - tmpAddr Z E t) (by omega)
    rwa [show tmpAddr Z E t + (x - tmpAddr Z E t) = x by omega] at this
  · rw [hfar x (fun hxd => by have := ok.nostack x hxd; omega)]
    exact R.stk x h1 h2
  · rw [hm, wr_get_far _ _ _ _ _ hb (far_of hw hx)]
    exact R.out x hx
  · rw [opd_mem_irrel _ _ _ _ _ (hra o ho).1]
    exact (hra o ho).2
  · rw [opd_mem_irrel _ _ _ _ _ (hrhl o ho).1]
    exact (hrhl o ho).2
  · obtain ⟨h1, h2⟩ := hracc m o h
    have h8 := R.nacc m o h2
    have hacr := ok.accRam
    rw [opd_mem_irrel _ _ _ _ _ h1, ← R.racc m o h2 (own_of_noslot h1)]
    refine rd_congr _ _ _ _ (by omega) (fun x hx1 hx2 => ?_)
    rw [hm, wr_get_far _ _ _ _ _ hb (by omega)]
  · exact absurd (hra _ h).1 (by simp [isSlot])
  · exact absurd (hrhl _ h).1 (by simp [isSlot])
  · exact absurd (hracc _ _ h).1 (by simp [isSlot])

/-- The bytes at the address can be written: shared, the function's to write, apart from the accumulator. -/
def AddrStore (Z : ZCtx) (E : GEnv) (p : IR.Addr) (n : Nat) : Prop :=
  ∀ ist tmps a, IR.Sem.addr Z.c ist tmps p = some a → IR.Sem.inBound Z.c ist tmps p = true →
    a + n ≤ 65536 ∧ (∀ j, j < n → Z.data (a + j)) ∧ (∀ j, j < n → Z.wr E.fn.name (a + j)) ∧
      (a + n ≤ Z.acc ∨ Z.acc + 8 ≤ a)

/-- The operands `killSlots` keeps. -/
def keepOpd (o : Opd) : Bool := match o with | .slot _ => false | _ => true

def killedRegs (r : Regs) : Regs :=
  { a := r.a.filter keepOpd, hl := r.hl.filter keepOpd, acc := r.acc.filter fun (_, o) => keepOpd o }

theorem wpg_killSlots (s : GS) (Q : Unit → GS → Prop) :
    wpg killSlots E Q s ↔ Q () { s with regs := killedRegs s.regs } := Iff.rfl

theorem keepOpd_noslot {o : Opd} (h : keepOpd o = true) : isSlot o = false := by
  cases o with
  | slot sl => cases h
  | const v => rfl
  | tmp t => rfl

theorem killed_acc {r : Regs} {m : Nat} {o : Opd} (h : (killedRegs r).acc = some (m, o)) :
    isSlot o = false ∧ r.acc = some (m, o) := by
  unfold killedRegs at h
  cases hr : r.acc with
  | none => rw [hr] at h; cases h
  | some q =>
    obtain ⟨m', o'⟩ := q
    rw [hr] at h
    by_cases hk : keepOpd o' = true
    · have : Option.filter (fun x : Nat × Opd => keepOpd x.2) (some (m', o')) = some (m', o') := by
        simp [Option.filter, hk]
      have h' : Option.filter (fun x : Nat × Opd => keepOpd x.2) (some (m', o')) = some (m, o) := h
      rw [this] at h'
      cases h'
      exact ⟨keepOpd_noslot hk, rfl⟩
    · have : Option.filter (fun x : Nat × Opd => keepOpd x.2) (some (m', o')) = none := by
        simp [Option.filter, hk]
      have h' : Option.filter (fun x : Nat × Opd => keepOpd x.2) (some (m', o')) = some (m, o) := h
      rw [this] at h'
      cases h'

/-- A byte written at the address in `HL`, as the IR writes it. -/
theorem wr_at_hl (c s : Cpu) (x : UInt8) (hl : UInt16) {a v : Nat} (hmem : c.mem = s.mem)
    (hrs : c.ramStart = s.ramStart) (hhl : hl.toNat = a) (hram : s.ramStart.toNat ≤ a) (ha : a < 65536)
    (hx : x.toNat = v % 256) : (c.wr hl x).mem = IR.Sem.wr s.mem a 1 v := by
  rw [cpu_wr_mem _ _ _ (by rw [hrs, hhl]; exact hram), hmem, hhl]
  exact wr_one _ _ _ ha _ hx

/-- **The states agree after a byte is written through `HL`**, the slots forgotten. -/
theorem Rel.wr_kill {fr : Fr} (ok : Z.OK) (hT : FnLay Z E) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat}
    {s s' : Cpu} (R : Rel Z E fr dt regs ist tmps s) {a n v : Nat} (hn : 0 < n)
    (hS : a + n ≤ 65536 ∧ (∀ j, j < n → Z.data (a + j)) ∧ (∀ j, j < n → Z.wr E.fn.name (a + j)) ∧
      (a + n ≤ Z.acc ∨ Z.acc + 8 ≤ a))
    (hm : s'.mem = IR.Sem.wr s.mem a n v) (hr : s'.ramStart = s.ramStart) (hh : s'.halted = s.halted)
    (hsp : s'.sp = s.sp) (ha : s'.a = s.a) (hreg : regs.hl = []) :
    Rel Z E fr dt (killedRegs regs) { ist with mem := IR.Sem.wr ist.mem a n v } tmps s' := by
  refine R.wr_mem ok hT hn hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 hm hr hh hsp (fun o ho => ?_) (fun o ho => ?_)
    (fun m o h => killed_acc h)
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp ho
    exact ⟨keepOpd_noslot h2, by rw [ha]; exact R.ra o h1 (own_of_noslot (keepOpd_noslot h2))⟩
  · have : o ∈ regs.hl := (List.mem_filter.mp ho).1
    rw [hreg] at this
    cases this

/-- The shape of a store: the trap of the index check, or the write. -/
theorem after_store {fr : Fr} {n : Nat} (p : IR.Addr) (src : Opd) (s1 : GS) {ist : IR.Sem.St} {tmps : Array Nat}
    {s : Cpu} (P : Nat → Cpu → Prop)
    (h1 : match IR.Sem.addr Z.c ist tmps p with
      | some a => ∃ s', P a s'
      | none => ∃ s', Steps s s' ∧ Trapped Z ist s')
    (hok : ∀ a s', IR.Sem.addr Z.c ist tmps p = some a → IR.Sem.inBound Z.c ist tmps p = true → P a s' →
      ∃ s'', Steps s s'' ∧ At Z.addrs (base + s1.out.size) s'' ∧
        Rel Z E fr dt s1.regs { ist with mem := IR.Sem.wr ist.mem a n (IR.Sem.opd Z.c ist tmps n src) } tmps s'') :
    After Z E base fr dt (.store n p src) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.store n p src)) := by
  simp only [IR.Sem.step]
  cases haddr : IR.Sem.addr Z.c ist tmps p with
  | none =>
    rw [haddr] at h1
    exact h1
  | some a =>
    rw [haddr] at h1
    by_cases hb : IR.Sem.inBound Z.c ist tmps p = true
    · simp only [hb, if_true]
      obtain ⟨s', hP⟩ := h1
      exact hok a s' haddr hb hP
    · simp only [hb, Bool.false_eq_true, if_false]
      trivial

/-- **`store` of one byte.** -/
theorem store1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (p : IR.Addr) (src : Opd) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.store 1 p src)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrStore Z E p 1 ∧ Rd Z E dt 1 src → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.store 1 p src) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.store 1 p src)))) s0 := by
  simp only [genInstr, wpg_bind, wpg_get, beq_self_eq_true, if_true]
  have nonconst : ∀ o : Opd, (∀ v, o ≠ .const v) →
      wpg (if s0.regs.a.contains o = true then do
          genAddr p
          ins .ld [.mhl, .a]
          killSlots
        else do
          genAddr p
          let q ← addrOf o
          ins .ld [.a, .mem q]
          ins .ld [.mhl, .a]
          setRegs fun r => { r with a := [o] }
          killSlots) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrStore Z E p 1 ∧ Rd Z E dt 1 o → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.store 1 p o) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.store 1 p o)))) s0 := by
    intro o hc
    by_cases hin : s0.regs.a.contains o = true
    · simp only [hin, if_true, wpg_bind]
      have hmem : o ∈ s0.regs.a := by simpa using hin
      refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
      intro _ s1 ⟨hx1, hhl1, ha1, ha⟩
      simp only [wpg_ins, wpg_killSlots]
      refine ⟨hx1.trans ((GExt.push _ _).trans (GExt.regs _ _)), fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
      have hxm : GExt { s1 with out := s1.out.push (.ins ⟨.ld, [.mhl, .a]⟩) } sF := (GExt.regs _ _).trans hxF
      refine after_store p o _ (fun a s' => Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt s1.regs ist tmps s' ∧ s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = a % 65536)
        (ha ((GExt.push _ _).trans hxm) hN fr ist tmps s R hat) (fun a s' haddr hb ⟨st, at', R', ha', _, hv⟩ => ?_)
      have hS := hD ist tmps a haddr hb
      have hhl : s'.hl.toNat = a := by rw [hv, Nat.mod_eq_of_lt (by omega)]
      have hram := (ok.ram a (by simpa using hS.2.1 0 Nat.one_pos)).1
      obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1) (i := ⟨.ld, [.mhl, .a]⟩) hxm rfl R'.img R'.run at'
        (s' := ((op1 s').wr (op1 s').hl ((op1 s').reg .hl 7)).tick 7) (fun _ _ => rfl) rfl
      have hval : s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o % 256 := by
        rw [ha', R.ra o hmem hrd.own]
        exact (Nat.mod_eq_of_lt (opd_lt _ _ _ 1 _)).symm
      exact ⟨_, st.trans hst, hat', R'.wr_kill ok hT Nat.one_pos hS
        (by
          simp only [zsim]
          exact wr_at_hl _ s' _ _ (by simp only [zsim]) (by simp only [zsim]) hhl (by rw [R'.rs]; exact hram)
            (by omega) hval)
        (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) hhl1⟩
    · simp only [hin, Bool.false_eq_true, if_false, wpg_bind]
      refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
      intro _ s1 ⟨hx1, hhl1, ha1, ha⟩
      refine wpg_mono (addrOf_ok o s1) ?_
      intro q s2 ⟨ho2, hr2, hq, hsp, _, hj2, hl2, hlv⟩
      subst hq
      simp only [wpg_ins, wpg_setRegs, wpg_killSlots]
      have hx12 : GExt s1 s2 := ⟨by simp [ho2], by simp [hj2], by simp [hl2]⟩
      have hxp : GExt s2 (pushL [⟨.ld, [.a, .mem (opdVal E o)]⟩, ⟨.ld, [.mhl, .a]⟩] s2) := pushL_ext _ _
      refine ⟨hx1.trans (hx12.trans (hxp.trans ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _⟩)),
        fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
      have hxm : GExt (pushL [⟨.ld, [.a, .mem (opdVal E o)]⟩, ⟨.ld, [.mhl, .a]⟩] s2) sF := by
        refine GExt.trans ⟨?_, ?_, ?_⟩ hxF
        · exact List.prefix_refl _
        · exact List.suffix_refl _
        · exact List.suffix_refl _
      refine after_store p o _ (fun a s' => Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt s1.regs ist tmps s' ∧ s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = a % 65536)
        (ha (hx12.trans (hxp.trans hxm)) hN fr ist tmps s R hat) (fun a s' haddr hb ⟨st, at', R', _, _, hv⟩ => ?_)
      have hS := hD ist tmps a haddr hb
      have hhl : s'.hl.toNat = a := by rw [hv, Nat.mod_eq_of_lt (by omega)]
      have hram := (ok.ram a (by simpa using hS.2.1 0 Nat.one_pos)).1
      obtain ⟨ad, had, hpc⟩ := at'
      obtain ⟨hvv, hbb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩).toNat = opdAddr Z E o := by
        show (w16 (byteOf ((Z.a.env ad).val (opdVal E o))) (byteOf ((Z.a.env ad).val (opdVal E o) / 256))).toNat = _
        rw [hvv]
        exact w16_val _ (by omega)
      obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ({ (skip (op1 s') 2) with
          a := (op1 s').rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (opdVal E o)]⟩) } : Cpu).tick 13 := ⟨_, rfl⟩
      obtain ⟨hst1, hat1⟩ := run_ins ok F (s0 := s2)
        (s1 := { s2 with out := s2.out.push (.ins ⟨.ld, [.a, .mem (opdVal E o)]⟩) })
        (i := ⟨.ld, [.a, .mem (opdVal E o)]⟩) ((GExt.push _ _).trans hxm) rfl R'.img R'.run
        (by rw [ho2]; exact ⟨ad, had, hpc⟩) (s' := c2)
        (fun ad' had' => by
          rw [ho2, had] at had'
          cases had'
          intro _
          rw [hc2]
          rfl) rfl (by rw [hc2]; rfl)
      have hA : c2.a.toNat = IR.Sem.opd Z.c ist tmps 1 o := by
        rw [hc2]
        simp only [zsim]
        show (s'.mem.get! _).toNat = _
        rw [hnn, ← rd_one _ _ (by omega)]
        exact opd_mem hrd hsp hc hlv R'
      have hm2 : c2.mem = s'.mem := by rw [hc2]; simp only [zsim]
      have hrs2 : c2.ramStart = s'.ramStart := by rw [hc2]; simp only [zsim]
      have hh2 : c2.halted = s'.halted := by rw [hc2]; simp only [zsim]
      have hsp2 : c2.sp = s'.sp := by rw [hc2]; simp only [zsim]
      have hhl2 : c2.hl = s'.hl := hl_congr (by rw [hc2]; simp only [zsim]) (by rw [hc2]; simp only [zsim])
      have R1 : Rel Z E fr dt { s1.regs with a := [o] } ist tmps c2 :=
        R'.regs_only hm2 hrs2 hh2 hsp2
          (fun o' ho' _ => by
            simp only [List.mem_singleton] at ho'
            subst ho'
            exact hA)
          (fun o' ho' _ => by rw [hhl1] at ho'; cases ho')
          (fun sl hsl _ => by
            simp only [List.mem_singleton] at hsl
            first | (subst hsl; exact hrd.use) | cases hsl)
          (fun sl hsl => R'.inhl sl hsl) (fun n o h => h)
      obtain ⟨hst2, hat2⟩ := run_ins ok F
        (s0 := { s2 with out := s2.out.push (.ins ⟨.ld, [.a, .mem (opdVal E o)]⟩) })
        (s1 := pushL [⟨.ld, [.a, .mem (opdVal E o)]⟩, ⟨.ld, [.mhl, .a]⟩] s2) (i := ⟨.ld, [.mhl, .a]⟩)
        hxm rfl R1.img R1.run hat1 (s' := ((op1 c2).wr (op1 c2).hl ((op1 c2).reg .hl 7)).tick 7)
        (fun _ _ => rfl) rfl
      have Rf := R1.wr_kill ok hT Nat.one_pos hS (v := IR.Sem.opd Z.c ist tmps 1 o)
        (s' := ((op1 c2).wr (op1 c2).hl ((op1 c2).reg .hl 7)).tick 7)
        (by
          simp only [zsim]
          refine wr_at_hl _ c2 _ _ (by simp only [zsim]) (by simp only [zsim]) (by rw [hhl2]; exact hhl)
            (by rw [hrs2, R'.rs]; exact hram) (by omega) ?_
          show c2.a.toNat = _
          rw [hA]
          exact (Nat.mod_eq_of_lt (opd_lt _ _ _ 1 _)).symm)
        (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) hhl1
      refine ⟨_, (st.trans hst1).trans hst2, hat2, ?_⟩
      have hreg : ({ s2.regs with a := [o] } : Regs) = { s1.regs with a := [o] } := by rw [hr2]
      show Rel Z E fr dt (killedRegs { s2.regs with a := [o] }) _ tmps _
      rw [hreg]
      exact Rf
  cases src with
  | slot sl => exact nonconst (.slot sl) (fun v h => by cases h)
  | tmp t => exact nonconst (.tmp t) (fun v h => by cases h)
  | const v =>
    simp only [wpg_bind]
    refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
    intro _ s1 ⟨hx1, hhl1, ha1, ha⟩
    simp only [wpg_ins, wpg_killSlots]
    refine ⟨hx1.trans ((GExt.push _ _).trans (GExt.regs _ _)), fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
    have hxm : GExt { s1 with out := s1.out.push (.ins ⟨.ld, [.mhl, n8 v]⟩) } sF := (GExt.regs _ _).trans hxF
    refine after_store p (.const v) _ (fun a s' => Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr dt s1.regs ist tmps s' ∧ s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = a % 65536)
      (ha ((GExt.push _ _).trans hxm) hN fr ist tmps s R hat) (fun a s' haddr hb ⟨st, at', R', _, _, hv⟩ => ?_)
    have hS := hD ist tmps a haddr hb
    have hhl : s'.hl.toNat = a := by rw [hv, Nat.mod_eq_of_lt (by omega)]
    have hram := (ok.ram a (by simpa using hS.2.1 0 Nat.one_pos)).1
    obtain ⟨hst, hat'⟩ := run_ins ok F (s0 := s1) (i := ⟨.ld, [.mhl, n8 v]⟩) hxm rfl R'.img R'.run at'
      (s' := ((skip (op1 s') 1).wr (op1 s').hl (byteOf (Int.ofNat (v % 256)))).tick 10) (fun _ _ => rfl) rfl
    exact ⟨_, st.trans hst, hat', R'.wr_kill ok hT Nat.one_pos hS
      (by
        simp only [zsim]
        refine wr_at_hl _ s' _ _ (by simp only [zsim]) (by simp only [zsim]) hhl (by rw [R'.rs]; exact hram)
          (by omega) ?_
        rw [byteOf_toNat]
        have e : IR.Sem.opd Z.c ist tmps 1 (.const v) = v % 256 := rfl
        have e' : (Int.ofNat (v % 256) : Int) = ((v % 256 : Nat) : Int) := rfl
        rw [e, e']
        omega)
      (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) hhl1⟩

/-- `ex de,hl`, `ld (hl),r` as the model runs them. -/
def exDH (s : Cpu) : Cpu :=
  ({ (op1 s) with d := (op1 s).h, e := (op1 s).l, h := (op1 s).d, l := (op1 s).e } : Cpu).tick 4
def wrMR (z : UInt8) (s : Cpu) : Cpu := ((op1 s).wr (op1 s).hl ((op1 s).reg .hl z)).tick 7

theorem exDH_sys (s : Cpu) : Sys s (exDH s) := ⟨rfl, rfl, rfl, rfl⟩
theorem exDH_a (s : Cpu) : (exDH s).a = s.a := rfl
theorem exDH_de (s : Cpu) : (exDH s).de = s.hl := rfl

/-- **The two bytes of `DE` written at `HL`**, the slots forgotten. -/
theorem wr2_tail (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (s1 : GS) :
    wpg (do
      ins .ld [.mhl, .e]
      ins .inc [.hl]
      ins .ld [.mhl, .d]
      killSlots) E (fun _ s2 => GExt s1 s2 ∧
      (GExt s2 sF → ∀ fr ist tmps c a v, Rel Z E fr dt s1.regs ist tmps c → s1.regs.hl = [] →
        At Z.addrs (base + s1.out.size) c → c.hl.toNat = a → c.de.toNat = v % 65536 →
        (a + 2 ≤ 65536 ∧ (∀ j, j < 2 → Z.data (a + j)) ∧ (∀ j, j < 2 → Z.wr E.fn.name (a + j)) ∧
          (a + 2 ≤ Z.acc ∨ Z.acc + 8 ≤ a)) →
        ∃ s'', Steps c s'' ∧ At Z.addrs (base + s2.out.size) s'' ∧
          Rel Z E fr dt s2.regs { ist with mem := IR.Sem.wr ist.mem a 2 v } tmps s'')) s1 := by
  simp only [wpg_bind, wpg_ins, wpg_killSlots]
  have hxp : GExt s1 (pushL [⟨.ld, [.mhl, .e]⟩, ⟨.inc, [.hl]⟩, ⟨.ld, [.mhl, .d]⟩] s1) := pushL_ext _ _
  refine ⟨hxp.trans (GExt.regs _ _), fun hxF fr ist tmps c a v R hhl0 hat hhl hde hS => ?_⟩
  have hxm : GExt (pushL [⟨.ld, [.mhl, .e]⟩, ⟨.inc, [.hl]⟩, ⟨.ld, [.mhl, .d]⟩] s1) sF := (GExt.regs _ _).trans hxF
  have hram := (ok.ram a (by simpa using hS.2.1 0 (by omega))).1
  have hrs := R.rs
  -- the low byte
  obtain ⟨st1, at1⟩ := run_ins ok F (s0 := s1) (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.mhl, .e]⟩) })
    (i := ⟨.ld, [.mhl, .e]⟩) ((pushL_ext [⟨.inc, [.hl]⟩, ⟨.ld, [.mhl, .d]⟩] _).trans hxm) rfl R.img R.run hat
    (s' := wrMR 3 c) (fun _ _ => rfl) rfl (by simp only [wrMR, zsim])
  have hm1 : (wrMR 3 c).mem = c.mem.set! a c.e := by
    simp only [wrMR, zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hhl, hrs]; exact hram)]
    simp only [zsim]
    rw [hhl]
  have M1 : Mach Z (wrMR 3 c) :=
    ⟨((R.img.congr (s' := op1 c) rfl rfl).wr (op1 c).hl ((op1 c).reg .hl 3)).congr rfl rfl,
      by simp only [wrMR, zsim]; exact R.run⟩
  -- the address of the high byte
  obtain ⟨st2, at2, M2⟩ := run_reg ok F (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.mhl, .e]⟩) })
    (s1 := pushL [⟨.ld, [.mhl, .e]⟩, ⟨.inc, [.hl]⟩] s1) ((pushL_ext [⟨.ld, [.mhl, .d]⟩] _).trans hxm) rfl M1 at1
    (incHL (wrMR 3 c)) (fun _ _ => rfl) rfl (incHL_keep _).1
  have hhl2 : (incHL (wrMR 3 c)).hl.toNat = a + 1 := by
    rw [incHL_hl]
    simp only [wrMR, zsim]
    rw [hhl, Nat.mod_eq_of_lt (by omega)]
  -- the high byte
  obtain ⟨st3, at3⟩ := run_ins ok F (s0 := pushL [⟨.ld, [.mhl, .e]⟩, ⟨.inc, [.hl]⟩] s1)
    (s1 := pushL [⟨.ld, [.mhl, .e]⟩, ⟨.inc, [.hl]⟩, ⟨.ld, [.mhl, .d]⟩] s1)
    (i := ⟨.ld, [.mhl, .d]⟩) hxm rfl M2.1 M2.2 at2 (s' := wrMR 2 (incHL (wrMR 3 c))) (fun _ _ => rfl) rfl (by simp only [wrMR, zsim])
  have hrs2 : (incHL (wrMR 3 c)).ramStart = c.ramStart := by
    rw [(incHL_keep _).1.2.1]
    simp only [wrMR, zsim]
  have hd2 : (incHL (wrMR 3 c)).d = c.d := by
    have := (incHL_keep (wrMR 3 c)).2.2
    simp only [incHL, wrMR, zsim]
  have hm3 : (wrMR 2 (incHL (wrMR 3 c))).mem = (c.mem.set! a c.e).set! (a + 1) c.d := by
    have hmem2 : (incHL (wrMR 3 c)).mem = c.mem.set! a c.e := by rw [(incHL_keep _).1.1, hm1]
    generalize incHL (wrMR 3 c) = c2 at hhl2 hrs2 hd2 hmem2
    simp only [wrMR, zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hhl2, hrs2, hrs]; omega)]
    simp only [zsim]
    rw [hhl2, hmem2]
    show (c.mem.set! a c.e).set! (a + 1) c2.d = _
    rw [hd2]
  have hdev := de_toNat c
  have hmem : (wrMR 2 (incHL (wrMR 3 c))).mem = IR.Sem.wr c.mem a 2 v := by
    rw [hm3]
    have := c.e.toNat_lt
    have := c.d.toNat_lt
    exact wr_two _ _ _ (by omega) _ _ (by omega) (by omega)
  refine ⟨_, (st1.trans st2).trans st3, at3, ?_⟩
  refine R.wr_kill ok hT (by omega) hS hmem ?_ ?_ ?_ ?_ hhl0
  · simp only [wrMR, zsim]
    rw [(incHL_keep _).1.2.1]
    simp only [wrMR, zsim]
  · simp only [wrMR, zsim]
    rw [(incHL_keep _).1.2.2.1]
    simp only [wrMR, zsim]
  · simp only [wrMR, zsim]
    rw [(incHL_keep _).1.2.2.2]
    simp only [wrMR, zsim]
  · simp only [wrMR, zsim]
    rw [(incHL_keep _).2.1]
    simp only [wrMR, zsim]

/-- **`store` of two bytes.** -/
theorem store2_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (p : IR.Addr) (src : Opd) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.store 2 p src)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrStore Z E p 2 ∧ Rd Z E dt 2 src → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.store 2 p src) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.store 2 p src)))) s0 := by
  simp only [genInstr, wpg_bind, wpg_get, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
    beq_self_eq_true, if_true]
  by_cases hin : s0.regs.hl.contains src = true
  · simp only [hin, if_true, wpg_bind]
    rw [wpg_ins, wpg_setRegs]
    have hmem : src ∈ s0.regs.hl := by simpa using hin
    refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov _) ?_
    intro _ s1 ⟨hx1, hhl1, _, ha⟩
    have ht := wr2_tail (dt := dt) ok hT F s1
    simp only [wpg_bind] at ht
    refine wpg_mono ht ?_
    intro _ sa h1
    refine wpg_mono h1 ?_
    intro _ sb h2
    refine wpg_mono h2 ?_
    intro _ sc h3
    refine wpg_mono h3 ?_
    intro _ s2 ⟨hx2, hw⟩
    refine ⟨((GExt.push _ _).trans (GExt.regs _ _)).trans (hx1.trans hx2), fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
    have hxe : GExt { s0 with out := s0.out.push (.ins ⟨.ex, [.de, .hl]⟩) } sF :=
      (GExt.regs _ _).trans (hx1.trans (hx2.trans hxF))
    obtain ⟨st0, at0, _⟩ := run_reg ok F (s0 := s0) hxe rfl R.mach hat (exDH s) (fun _ _ => rfl) rfl (exDH_sys s)
    have R0 : Rel Z E fr dt { s0.regs with hl := [] } ist tmps (exDH s) :=
      R.hl_gone (exDH_sys s) rfl (Or.inr ⟨rfl, exDH_a s⟩) (fun n o h => h)
    refine after_store p src _ (fun a s' => Steps (exDH s) s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr dt s1.regs ist tmps s' ∧ s'.a = (exDH s).a ∧ s'.de = (exDH s).de ∧ s'.hl.toNat = a % 65536)
      (by
        have := ha (hx2.trans hxF) hN fr ist tmps (exDH s) R0 at0
        cases haddr : IR.Sem.addr Z.c ist tmps p with
        | none =>
          rw [haddr] at this
          obtain ⟨s', st, htr⟩ := this
          exact ⟨s', st0.trans st, htr⟩
        | some a =>
          rw [haddr] at this
          exact this) (fun a s' haddr hb ⟨st, at', R', _, hde, hv⟩ => ?_)
    have hS := hD ist tmps a haddr hb
    obtain ⟨s'', st2, at2, R2⟩ := hw hxF fr ist tmps s' a (IR.Sem.opd Z.c ist tmps 2 src) R' hhl1 at'
      (by rw [hv, Nat.mod_eq_of_lt (by omega)])
      (by
        rw [hde, exDH_de, R.rhl src hmem hrd.own]
        exact (Nat.mod_eq_of_lt (opd_lt _ _ _ 2 _)).symm) hS
    exact ⟨s'', (st0.trans st).trans st2, at2, R2⟩
  · simp only [hin, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s0) ?_
    intro _ s1 ⟨hx1, hhl1, _, ha⟩
    refine wpg_mono (loadDE_ok (dt := dt) ok F src s1) ?_
    intro _ s1' ⟨hx1', hr1', hld⟩
    have ht := wr2_tail (dt := dt) ok hT F s1'
    simp only [wpg_bind] at ht
    refine wpg_mono ht ?_
    intro _ sa h1
    refine wpg_mono h1 ?_
    intro _ sb h2
    refine wpg_mono h2 ?_
    intro _ sc h3
    refine wpg_mono h3 ?_
    intro _ s2 ⟨hx2, hw⟩
    refine ⟨hx1.trans (hx1'.trans hx2), fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
    refine after_store p src _ (fun a s' => Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
      Rel Z E fr dt s1.regs ist tmps s' ∧ s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = a % 65536)
      (ha (hx1'.trans (hx2.trans hxF)) hN fr ist tmps s R hat) (fun a s' haddr hb ⟨st, at', R', _, _, hv⟩ => ?_)
    have hS := hD ist tmps a haddr hb
    obtain ⟨c, stc, atc, Rc, hhlc, _, hdec⟩ := hld (hx2.trans hxF) fr ist tmps s' hrd R' at'
    obtain ⟨s'', st2, at2, R2⟩ := hw hxF fr ist tmps c a (IR.Sem.opd Z.c ist tmps 2 src) Rc (by rw [hr1']; exact hhl1) atc
      (by rw [hhlc, hv, Nat.mod_eq_of_lt (by omega)])
      (by
        rw [hdec]
        exact (Nat.mod_eq_of_lt (opd_lt _ _ _ 2 _)).symm) hS
    exact ⟨s'', (st.trans stc).trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
