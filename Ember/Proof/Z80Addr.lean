import Ember.Proof.Z80Ext
import Ember.Proof.Z80CmpI
import Ember.Proof.Z80Ret

/-!
# Ember.Proof.Z80Addr — an address into `HL` (plan M7.3)

`genAddr_ok`: the code of `Codegen.genAddr` leaves in `HL` the address
`IR.Sem.addr` gives, `A` and `DE` as they were — or, when the index is
not below the length, gets to `rt_trap`.  For an address with a static
root; the index of one or two bytes, checked in line, by `rt_bound`, or
not at all; scaled by a power of two.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- `ld bc,nn`, `add hl,bc`, `add hl,hl` as the model runs them. -/
def ldBC (v : Nat) (s : Cpu) : Cpu :=
  ((skip (op1 s) 2).setRp .hl 0 (w16 (byteOf (Int.ofNat (v % 65536))) (byteOf (Int.ofNat (v % 65536) / 256)))).tick 10
def addHLBC (s : Cpu) : Cpu :=
  (((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 0)).2.setHL ((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 0)).1).tick 11
def addHLHL (s : Cpu) : Cpu :=
  (((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 2)).2.setHL ((op1 s).add16 (op1 s).hl ((op1 s).rp .hl 2)).1).tick 11

theorem does_ld_bc (v : Nat) : Does ⟨.ld, [.bc, n16 v]⟩ (ldBC v) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldBC, zsim, and_self], fun s => by simp only [ldBC, zsim]⟩
theorem does_add_hl_bc : Does ⟨.add, [.hl, .bc]⟩ addHLBC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, addHLBC, zsim, and_self], fun s => by simp only [addHLBC, zsim]⟩
theorem does_add_hl_hl : Does ⟨.add, [.hl, .hl]⟩ addHLHL :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, addHLHL, zsim, and_self], fun s => by simp only [addHLHL, zsim]⟩

theorem ldBC_keep (v : Nat) (s : Cpu) : KeepADE s (ldBC v s) := by simp only [KeepADE, Sys, ldBC, zsim, and_self]
theorem ldBC_hl (v : Nat) (s : Cpu) : (ldBC v s).hl = s.hl := by simp only [ldBC, zsim]
theorem ldBC_bc (v : Nat) (s : Cpu) : (ldBC v s).bc.toNat = v % 65536 := by
  simp only [ldBC, zsim]
  exact w16_val _ (Nat.mod_lt _ (by decide))

theorem addHLBC_keep (s : Cpu) : KeepADE s (addHLBC s) := by simp only [KeepADE, Sys, addHLBC, zsim, and_self]
theorem addHLBC_hl (s : Cpu) : (addHLBC s).hl.toNat = (s.hl.toNat + s.bc.toNat) % 65536 := by
  simp only [addHLBC, zsim]
  exact add16_val _ _ _
theorem addHLBC_c (s : Cpu) : (addHLBC s).flag FC = decide (65536 ≤ s.hl.toNat + s.bc.toNat) := by
  simp only [addHLBC, zsim]
  exact add16_fc _ _ _

theorem addHLHL_keep (s : Cpu) : KeepADE s (addHLHL s) := by simp only [KeepADE, Sys, addHLHL, zsim, and_self]
theorem addHLHL_hl (s : Cpu) : (addHLHL s).hl.toNat = (s.hl.toNat * 2) % 65536 := by
  simp only [addHLHL, zsim]
  rw [show s.hl.toNat * 2 = s.hl.toNat + s.hl.toNat by omega]
  exact add16_val _ _ _

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-- `HL` times a power of two. -/
theorem scale_ok (ok : Z.OK) (F : GFinal Z base sF) : ∀ (fuel sc : Nat) (s0 : GS),
    wpg (scaleHL fuel sc) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → ∀ s, Mach Z s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Mach Z s' ∧ KeepADE s s' ∧
          ∀ k, sc = 2 ^ k → k ≤ fuel → s'.hl.toNat = s.hl.toNat * sc % 65536)) s0
  | 0, sc, s0 => by
    rw [scaleHL, wpg_pure]
    refine ⟨GExt.refl _, rfl, fun _ s M hat => ⟨s, Steps.refl _, hat, M, KeepADE.refl s, fun k hk hle => ?_⟩⟩
    have : k = 0 := by omega
    subst this
    subst hk
    have := s.hl.toNat_lt
    omega
  | fuel + 1, sc, s0 => by
    rw [scaleHL]
    by_cases h : sc > 1
    · rw [if_pos h, wpg_bind, wpg_ins]
      refine wpg_mono (scale_ok ok F fuel (sc / 2) _) ?_
      intro _ s1 ⟨hx, hr, hs⟩
      refine ⟨(GExt.push _ _).trans hx, hr, fun hxF s M hat => ?_⟩
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.add, [.hl, .hl]⟩) })
        (hx.trans hxF) rfl M hat (addHLHL s) (fun _ _ => rfl) rfl (does_add_hl_hl.sys s)
      obtain ⟨s', st2, at2, M2, hk2, hv⟩ := hs hxF _ M1 at1
      refine ⟨s', st1.trans st2, at2, M2, (addHLHL_keep s).trans hk2, fun k hk hle => ?_⟩
      cases k with
      | zero => subst hk; omega
      | succ k =>
        have h2 : sc / 2 = 2 ^ k := by rw [hk, Nat.pow_succ]; omega
        rw [hv k h2 (by omega), addHLHL_hl, h2, hk, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1
        rw [Nat.mul_assoc, Nat.mul_comm 2]
    · rw [if_neg h, wpg_pure]
      refine ⟨GExt.refl _, rfl, fun _ s M hat => ⟨s, Steps.refl _, hat, M, KeepADE.refl s, fun k hk hle => ?_⟩⟩
      have hk0 : sc = 1 := by
        cases k with
        | zero => exact hk
        | succ k =>
          have := Nat.two_pow_pos k
          rw [Nat.pow_succ] at hk
          omega
      have := s.hl.toNat_lt
      rw [hk0]
      omega

theorem KeepR.ade {s s' : Cpu} (hS : Sys s s') (h : KeepR s s') : KeepADE s s' :=
  ⟨hS, h.1, de_congr h.2.2.2.2.1 h.2.2.2.2.2.1⟩

/-- The check in line: `HL − len` carries when the index is too large. -/
theorem checkInline_ok (ok : Z.OK) (F : GFinal Z base sF) (len : Nat) (s0 : GS) :
    wpg (do
      ins .ld [.bc, n16 (65536 - len)]
      ins .add [.hl, .bc]
      ins .jp [.c, .imm (.sym "rt_trap")]) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → 0 < len ∧ len ≤ 65536 → ∀ j : Nat, Z.items[j]? = some (Item.label "rt_trap") → ∀ s, Mach Z s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ Mach Z s' ∧ KeepADE s s' ∧
          (if s.hl.toNat < len then At Z.addrs (base + s1.out.size) s' ∧ s'.hl.toNat = s.hl.toNat + 65536 - len
           else At Z.addrs j s'))) s0 := by
  simp only [wpg_bind, wpg_ins]
  refine ⟨pushL_ext [⟨.ld, [.bc, n16 (65536 - len)]⟩, ⟨.add, [.hl, .bc]⟩, ⟨.jp, [.c, .imm (.sym "rt_trap")]⟩] s0, trivial,
    fun hx hlen j hj s M hat => ?_⟩
  obtain ⟨st, at', M', hS⟩ := run_list ok F
    [(⟨.ld, [.bc, n16 (65536 - len)]⟩, ldBC (65536 - len)), (⟨.add, [.hl, .bc]⟩, addHLBC)]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact does_ld_bc _
      · exact does_add_hl_bc) s0 s ((GExt.push _ _).trans hx) M hat
  have hk : Z.items[base + (pushL [⟨.ld, [.bc, n16 (65536 - len)]⟩, ⟨.add, [.hl, .bc]⟩] s0).out.size]? =
      some (.ins ⟨.jp, [condOf .lt, .imm (.sym "rt_trap")]⟩) :=
    F.at hx (by
      show (((s0.out.push _).push _).push _)[((s0.out.push _).push _).size]? = some _
      rw [Array.getElem?_push_size]
      rfl)
  obtain ⟨s', st2, M2, hS2, hK2, hcase⟩ := jp_cc_step ok .lt hk hj M' at'
  have hk1 : KeepADE s (addHLBC (ldBC (65536 - len) s)) := (ldBC_keep _ s).trans (addHLBC_keep _)
  have hhl : (addHLBC (ldBC (65536 - len) s)).hl.toNat = (s.hl.toNat + (65536 - len) % 65536) % 65536 := by
    rw [addHLBC_hl, ldBC_hl, ldBC_bc]
  have hc : (addHLBC (ldBC (65536 - len) s)).flag FC = decide (65536 ≤ s.hl.toNat + (65536 - len) % 65536) := by
    rw [addHLBC_c, ldBC_hl, ldBC_bc]
  have hsl := s.hl.toNat_lt
  refine ⟨s', st.trans st2, M2, hk1.trans (hK2.ade hS2), ?_⟩
  have hcond : (addHLBC (ldBC (65536 - len) s)).cond (ccOf .lt) = decide (65536 ≤ s.hl.toNat + (65536 - len) % 65536) := hc
  simp only [List.map, runL] at hcase
  rw [hcond] at hcase
  by_cases hin : s.hl.toNat < len
  · rw [if_pos hin]
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)] at hcase
    refine ⟨by simpa [pushL, Nat.add_assoc] using hcase, ?_⟩
    rw [hl_congr hK2.2.2.2.2.2.2.1 hK2.2.2.2.2.2.2.2.1]
    simp only [List.map, runL]
    rw [hhl]
    omega
  · rw [if_neg hin]
    rw [if_pos (by simp only [decide_eq_true_eq]; omega)] at hcase
    exact hcase

/-! ## The check of the index -/

/-- The index is below the length, where there is one. -/
def lenOK (len? : Option Nat) (i : Nat) : Prop := ∀ len, len? = some len → i < len

/-- What the check in line leaves added to the index. -/
def checkDelta (x : IR.Index) (inl : Option Nat) : Nat :=
  match x.len, inl with
  | some len, some _ => 65536 - len
  | _, _ => 0

structure CheckNeed (Z : ZCtx) (x : IR.Index) (inl : Option Nat) : Prop where
  trap : ∀ len, x.len = some len → ∃ j : Nat, Z.items[j]? = some (Item.label "rt_trap")
  len : ∀ len, x.len = some len → 0 < len ∧ len ≤ 65536 ∧ (inl = none → len < 65536)

theorem bc_congr {s s' : Cpu} (hb : s'.b = s.b) (hc : s'.c = s.c) : s'.bc = s.bc := by
  simp only [Cpu.bc, hb, hc]

/-- The check by `rt_bound`. -/
theorem checkRt_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (len : Nat) (s0 : GS) :
    wpg (do
      ins .ld [.bc, n16 len]
      call "rt_bound") E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → len < 65536 → ∀ fr ist tmps regs s, regs.hl = [] → Rel Z E fr dt regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧
          (s.hl.toNat < len → At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt regs ist tmps s' ∧
            s'.a = s.a ∧ s'.de = s.de ∧ s'.hl = s.hl) ∧
          (¬ s.hl.toNat < len → Trapped Z ist s'))) s0 := by
  simp only [wpg_bind, wpg_ins, wpg_call]
  refine ⟨(GExt.push _ _).trans (GExt.push _ _), trivial, fun hx hlen fr ist tmps regs s hhl R hat => ?_⟩
  obtain ⟨entry, hsym, hent, hspec⟩ := hrt.bound ⟨_, F.emitted hx rfl⟩
  have hroom := R.room
  have hstk := ok.stack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  obtain ⟨st0, at0, M0⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.bc, n16 len]⟩) })
    ((GExt.push _ _).trans hx) rfl R.mach hat (ldBC len s) (fun _ _ => rfl) rfl ((does_ld_bc len).sys s)
  have hk0 := ldBC_keep len s
  have R0 : Rel Z E fr dt regs ist tmps (ldBC len s) := R.keep hk0.1 hk0.2.1 (ldBC_hl len s)
  have hsp0 : (ldBC len s).sp.toNat = fr.sp.toNat := by rw [R0.sp]
  obtain ⟨c1, st1, cs, hpc1, I1, hh1, hrs1, hback⟩ :=
    call_step ok (F.emitted hx rfl) hsym hent at0 R0.img R0.run R0.rs R0.msz (by omega) (by omega)
  have hc1sp : c1.sp.toNat = (ldBC len s).sp.toNat - 2 := by rw [cs.sp]; exact sub2_toNat _ (by omega)
  obtain ⟨s', st2, hh', hrs', hsz', hfree, ha', hde', hcase⟩ := hspec c1 hpc1 I1 hh1 (by rw [hrs1]; exact R0.rs)
    (by rw [cs.size]; exact R0.msz) (by omega) (by omega)
  have hc1hl : c1.hl = s.hl := by rw [hl_congr cs.h cs.l, ldBC_hl]
  have hc1bc : c1.bc.toNat = len := by
    rw [bc_congr cs.b cs.c, ldBC_bc, Nat.mod_eq_of_lt hlen]
  rw [hc1hl, hc1bc] at hcase
  have hmem : FreeStack Z (ldBC len s) s' := by
    intro x hx' hnrt
    rw [hfree x (by omega) hnrt, cs.mem x (by omega)]
  refine ⟨s', (st0.trans st1).trans st2, fun hin => ?_, fun hin => ?_⟩
  · rw [if_pos hin] at hcase
    obtain ⟨hpc', hsp', hhl'⟩ := hcase
    have hsp'' : s'.sp = (ldBC len s).sp := by rw [hsp', cs.sp]; exact UInt16.sub_add_cancel _ _
    have ha'' : s'.a = s.a := by rw [ha', cs.a, hk0.2.1]
    refine ⟨?_, ?_, ha'', ?_, ?_⟩
    · have := hback s' (by
        rw [hpc', cpu_rd16 _ _ (by omega), hc1sp])
      simpa [Nat.add_assoc] using this
    · exact R0.free_stack ok hT hmem hsz' (by rw [hrs', hrs1]) (by rw [hh', R0.run]) hsp''
        (fun o ho hown => by rw [ha'', ← R.ra o ho hown]) (fun o ho => by rw [hhl] at ho; cases ho)
        R.ina (fun sl hsl => by rw [hhl] at hsl; cases hsl) (fun n o h => h)
    · rw [hde', de_congr cs.d cs.e, hk0.2.2]
    · exact hhl'
  · rw [if_neg hin] at hcase
    obtain ⟨j, hj, hatj⟩ := hcase
    refine ⟨j, hj, hatj, hh', fun x hxd => ?_⟩
    have hns := ok.nostack x hxd
    rw [hmem x (by omega) (ok.rtData x hxd), hk0.1.1]
    exact R.mem x hxd

/-- **The check of an index in `HL`.** -/
theorem genCheck_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (x : IR.Index) (inl : Option Nat) (s0 : GS) :
    wpg (genCheck x inl) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → CheckNeed Z x inl → ∀ fr ist tmps regs s, regs.hl = [] → Rel Z E fr dt regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧
          (lenOK x.len s.hl.toNat → At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt regs ist tmps s' ∧
            s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = s.hl.toNat + checkDelta x inl) ∧
          (¬ lenOK x.len s.hl.toNat → Trapped Z ist s'))) s0 := by
  unfold genCheck
  cases hl : x.len with
  | none =>
    refine ⟨GExt.refl _, rfl, fun _ _ fr ist tmps regs s _ R hat =>
      ⟨s, Steps.refl _, fun _ => ⟨hat, R, rfl, rfl, by simp [checkDelta, hl]⟩, fun h => ?_⟩⟩
    exact absurd (fun len h' => by cases h') h
  | some len =>
    have hlen : ∀ i, lenOK (some len) i ↔ i < len :=
      fun i => ⟨fun h => h len rfl, fun h l hl' => by cases hl'; exact h⟩
    cases inl with
    | some l' =>
      refine wpg_mono (checkInline_ok ok F len s0) ?_
      intro _ s1 ⟨hx1, hr1, h⟩
      refine ⟨hx1, hr1, fun hx N fr ist tmps regs s hhl R hat => ?_⟩
      obtain ⟨j, hj⟩ := N.trap len hl
      have hl3 := N.len len hl
      obtain ⟨s', st, M', hk, hcase⟩ := h hx ⟨hl3.1, hl3.2.1⟩ j hj s R.mach hat
      refine ⟨s', st, fun hin => ?_, fun hin => ?_⟩
      · rw [if_pos ((hlen _).mp hin)] at hcase
        refine ⟨hcase.1, R.hl_gone hk.1 hhl (Or.inr ⟨rfl, hk.2.1⟩) (fun n o h => h), hk.2.1, hk.2.2, ?_⟩
        rw [hcase.2]
        have := (hlen _).mp hin
        simp only [checkDelta, hl]
        omega
      · rw [if_neg (fun h' => hin ((hlen _).mpr h'))] at hcase
        exact ⟨j, hj, hcase, M'.2, fun y hyd => by rw [hk.1.1]; exact R.mem y hyd⟩
    | none =>
      refine wpg_mono (checkRt_ok (dt := dt) ok hT F hrt hdep len s0) ?_
      intro _ s1 ⟨hx1, hr1, h⟩
      refine ⟨hx1, hr1, fun hx N fr ist tmps regs s hhl R hat => ?_⟩
      obtain ⟨s', st, hin', hout'⟩ := h hx ((N.len len hl).2.2 rfl) fr ist tmps regs s hhl R hat
      refine ⟨s', st, fun hin => ?_, fun hin => hout' (fun h' => hin ((hlen _).mpr h'))⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hin' ((hlen _).mp hin)
      exact ⟨h1, h2, h3, h4, by rw [h5]; simp [checkDelta, hl]⟩

/-! ## The base -/

theorem wpg_noteAddr (sl : Slot) (s : GS) (Q : Unit → GS → Prop)
    (h : ∀ s1 : GS, s1.out = s.out → s1.regs = s.regs → s1.jumps = s.jumps → s1.labelRegs = s.labelRegs → Q () s1) :
    wpg (noteAddr sl) E Q s := by
  unfold noteAddr
  simp only [wpg_bind, wpg_read]
  split
  · rw [wpg_modify]
    exact h _ rfl rfl rfl rfl
  · exact h s rfl rfl rfl rfl

theorem addr_off (l : IR.Layout) (sl : Slot) (k : Nat) :
    l.addr { sl with off := sl.off + k } = l.addr sl + k := by
  simp only [IR.Layout.addr]
  omega

/-- `ld bc,base; add hl,bc`. -/
theorem addBase_ok (ok : Z.OK) (F : GFinal Z base sF) (sl : Slot) (off : Nat) (s0 : GS) :
    wpg (do
      noteAddr sl
      ins .ld [.bc, .imm (slotVal { sl with off := sl.off + off })]
      ins .add [.hl, .bc]) E (fun _ s1 => GExt s0 s1 ∧ s1.regs = s0.regs ∧
      (GExt s1 sF → (∃ ad, Z.c.layout.areaAddr sl.area = some ad) → Z.c.layout.addr sl + off < 65536 →
        ∀ s, Mach Z s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Mach Z s' ∧ KeepADE s s' ∧
          s'.hl.toNat = (s.hl.toNat + (Z.c.layout.addr sl + off)) % 65536)) s0 := by
  simp only [wpg_bind]
  refine wpg_noteAddr sl _ _ (fun s1 ho1 hr1 hj1 hl1 => ?_)
  simp only [wpg_ins]
  refine ⟨⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩, hr1, fun hx ⟨ad0, had0⟩ hlt s M hat => ?_⟩
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.bc, .imm (slotVal { sl with off := sl.off + off })]⟩).toNat =
      Z.c.layout.addr sl + off := by
    rw [← addr_off]
    exact immW_toNat _ _ _ _ rfl (slot_val ok { sl with off := sl.off + off } ad0 ad had0)
      (by rw [addr_off]; exact hlt)
  have hS1 : Sys s (((skip (op1 s) 2).setRp .hl 0
      (Instr.immW (Z.a.env ad) ⟨.ld, [.bc, .imm (slotVal { sl with off := sl.off + off })]⟩)).tick 10) := by
    simp only [Sys, zsim, and_self]
  obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.bc, .imm (slotVal { sl with off := sl.off + off })]⟩) })
    ((GExt.push _ _).trans hx) rfl M (by rw [ho1]; exact ⟨ad, had, hpc⟩) _
    (fun ad' had' => by
      rw [ho1, had] at had'
      cases had'
      intro _
      rfl) rfl hS1
  obtain ⟨st2, at2, M2⟩ := run_reg ok F
    (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.bc, .imm (slotVal { sl with off := sl.off + off })]⟩) })
    hx rfl M1 at1 (addHLBC _) (fun _ _ => rfl) rfl (does_add_hl_bc.sys _)
  refine ⟨_, st1.trans st2, at2, M2, ⟨hS1.trans (does_add_hl_bc.sys _), by simp only [addHLBC, zsim],
    by simp only [addHLBC, zsim]⟩, ?_⟩
  rw [addHLBC_hl]
  simp only [zsim]
  rw [hnn]

/-! ## The address -/

/-- The addresses covered: a static root, an index of one or two bytes. -/
def addrCov (p : IR.Addr) : Bool :=
  (match p.root with | .static _ => true | .ptr _ => false) &&
    (match p.idx with | none => true | some x => x.size == 1 || x.size == 2)

/-- What an address needs of the program. -/
def AddrNeed (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (p : IR.Addr) : Prop :=
  ∀ sl, p.root = .static sl → (∃ ad, Z.c.layout.areaAddr sl.area = some ad) ∧
    match p.idx with
    | none => Z.c.layout.addr sl + p.off < 65536
    | some x => Rd Z E dt x.size x.opd ∧ (∃ k, x.scale = 2 ^ k) ∧ CheckNeed Z x (inlineLen x p.root) ∧
        Z.c.layout.addr sl + p.off + (inlineLen x p.root).getD 0 < 65536

theorem genAddr_none (p : IR.Addr) (sl : Slot) (hr : p.root = .static sl) (hi : p.idx = none) :
    genAddr p = (do
      noteAddr sl
      ins .ld [.hl, .imm (slotVal { sl with off := sl.off + p.off })]
      setRegs fun r => { r with hl := [] }) := by
  obtain ⟨root, off, idx⟩ := p
  simp only at hr hi
  subst hr hi
  rfl

theorem genAddr_some (p : IR.Addr) (sl : Slot) (x : IR.Index) (hr : p.root = .static sl) (hi : p.idx = some x) :
    genAddr p = (do
      if x.size == 2 then loadHL x.opd else loadHLByte x.opd
      genCheck x (inlineLen x p.root)
      scaleHL x.scale x.scale
      noteAddr sl
      ins .ld [.bc, .imm (slotVal { sl with off := sl.off + (p.off + (inlineLen x p.root).getD 0) })]
      ins .add [.hl, .bc]
      setRegs fun r => { r with hl := [] }) := by
  obtain ⟨root, off, idx⟩ := p
  simp only at hr hi
  subst hr hi
  simp only [genAddr, Nat.add_assoc]

/-- The check in line is made for an index scaled by one, and adds the length to the base. -/
theorem inline_cases (x : IR.Index) (root : IR.Root) :
    (checkDelta x (inlineLen x root) = 0 ∧ (inlineLen x root).getD 0 = 0) ∨
      ∃ len, x.len = some len ∧ x.scale = 1 ∧ checkDelta x (inlineLen x root) = 65536 - len ∧
        (inlineLen x root).getD 0 = len := by
  unfold inlineLen checkDelta
  cases hl : x.len with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some len =>
    cases root with
    | ptr q => exact Or.inl ⟨rfl, rfl⟩
    | static sl =>
      by_cases h1 : (x.scale == 1) = true
      · simp only [h1, if_true]
        exact Or.inr ⟨len, rfl, by simpa using h1, rfl, rfl⟩
      · simp only [h1, Bool.false_eq_true, if_false]
        exact Or.inl ⟨trivial, rfl⟩

theorem addr_static_some (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (p : IR.Addr) (sl : Slot) (x : IR.Index)
    (hr : p.root = .static sl) (hi : p.idx = some x) :
    (lenOK x.len (IR.Sem.opd c ist tmps x.size x.opd) →
      IR.Sem.addr c ist tmps p = some (c.layout.addr sl + p.off + IR.Sem.opd c ist tmps x.size x.opd * x.scale)) ∧
    (¬ lenOK x.len (IR.Sem.opd c ist tmps x.size x.opd) → IR.Sem.addr c ist tmps p = none) := by
  simp only [IR.Sem.addr, hr, hi]
  cases hl : x.len with
  | none => exact ⟨fun _ => rfl, fun h => absurd (fun len h' => by cases h') h⟩
  | some len =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [if_pos (h len rfl)]
    · have : ¬ IR.Sem.opd c ist tmps x.size x.opd < len := fun h' => h (fun l hl' => by cases hl'; exact h')
      simp only [if_neg this]

/-- What `genAddr` promises. -/
def AddrPost (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (p : IR.Addr) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.hl = [] ∧ s1.regs.a = s0.regs.a ∧
    (GExt s1 sF → AddrNeed Z E dt p → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      match IR.Sem.addr Z.c ist tmps p with
      | some a => ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.a = s.a ∧ s'.de = s.de ∧ s'.hl.toNat = a % 65536
      | none => ∃ s', Steps s s' ∧ Trapped Z ist s')

/-- **The address into `HL`.** -/
theorem genAddr_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genAddr p) E (AddrPost Z E base sF dt p s0) s0 := by
  unfold addrCov at hcov
  cases hr : p.root with
  | ptr q => simp [hr] at hcov
  | static sl =>
    cases hi : p.idx with
    | none =>
      rw [genAddr_none p sl hr hi]
      simp only [wpg_bind]
      refine wpg_noteAddr sl _ _ (fun s1 ho1 hr1 hj1 hl1 => ?_)
      simp only [wpg_ins, wpg_setRegs]
      refine ⟨⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩, rfl, (by show s1.regs.a = s0.regs.a; rw [hr1]),
        fun hx N fr ist tmps s R hat => ?_⟩
      obtain ⟨⟨ad0, had0⟩, hlt⟩ := N sl hr
      rw [hi] at hlt
      obtain ⟨ad, had, hpc⟩ := hat
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (slotVal { sl with off := sl.off + p.off })]⟩).toNat =
          Z.c.layout.addr sl + p.off := by
        rw [← addr_off]
        exact immW_toNat _ _ _ _ rfl (slot_val ok { sl with off := sl.off + p.off } ad0 ad had0)
          (by rw [addr_off]; exact hlt)
      have hS : Sys s (((skip (op1 s) 2).setHL
          (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (slotVal { sl with off := sl.off + p.off })]⟩)).tick 10) := by
        simp only [Sys, zsim, and_self]
      obtain ⟨st, at', _⟩ := run_reg ok F (s0 := s1)
        (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (slotVal { sl with off := sl.off + p.off })]⟩) })
        ((GExt.regs _ _).trans hx) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩) _
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          intro _
          rfl) rfl hS
      have haddr : IR.Sem.addr Z.c ist tmps p = some (Z.c.layout.addr sl + p.off) := by
        simp only [IR.Sem.addr, hr, hi]
      rw [haddr]
      refine ⟨_, st, at', R.hl_gone hS rfl (Or.inr ⟨(by show s1.regs.a = s0.regs.a; rw [hr1]), by simp only [zsim]⟩)
          (fun n o h => by rw [← hr1]; exact h),
        by simp only [zsim], by simp only [zsim], ?_⟩
      simp only [zsim]
      rw [hnn, Nat.mod_eq_of_lt hlt]
    | some x =>
      have hsz : x.size = 1 ∨ x.size = 2 := by
        rw [hr, hi] at hcov
        simpa using hcov
      rw [genAddr_some p sl x hr hi]
      -- what follows the index
      have rest : ∀ (first : GM Unit), wpg first E (fun _ s1 =>
          GExt s0 s1 ∧ s1.regs.a = s0.regs.a ∧
          (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt x.size x.opd → Rel Z E fr dt s0.regs ist tmps s →
            At Z.addrs (base + s0.out.size) s →
            ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
              Rel Z E fr dt { s1.regs with hl := [] } ist tmps s' ∧ s'.a = s.a ∧ s'.de = s.de ∧
              s'.hl.toNat = IR.Sem.opd Z.c ist tmps x.size x.opd)) s0 →
          wpg (do
            first
            genCheck x (inlineLen x p.root)
            scaleHL x.scale x.scale
            noteAddr sl
            ins .ld [.bc, .imm (slotVal { sl with off := sl.off + (p.off + (inlineLen x p.root).getD 0) })]
            ins .add [.hl, .bc]
            setRegs fun r => { r with hl := [] }) E (AddrPost Z E base sF dt p s0) s0 := by
        intro first idx
        simp only [wpg_bind]
        refine wpg_mono idx ?_
        intro _ s1 ⟨hx1, ha1, hidx⟩
        refine wpg_mono (genCheck_ok (dt := dt) ok hT F hrt hdep x (inlineLen x p.root) s1) ?_
        intro _ s2 ⟨hx2, hr2, hchk⟩
        refine wpg_mono (scale_ok ok F x.scale x.scale s2) ?_
        intro _ s3 ⟨hx3, hr3, hsc⟩
        have hb := addBase_ok (E := E) ok F sl (p.off + (inlineLen x p.root).getD 0) s3
        simp only [wpg_bind] at hb
        refine wpg_mono hb ?_
        intro _ sa hb1
        refine wpg_mono hb1 ?_
        intro _ sb hb2
        refine wpg_mono hb2 ?_
        intro _ s4 ⟨hx4, hr4, hbase⟩
        rw [wpg_setRegs]
        have hreg4 : s4.regs = s1.regs := by rw [hr4, hr3, hr2]
        refine ⟨hx1.trans (hx2.trans (hx3.trans (hx4.trans (GExt.regs _ _)))), rfl, by rw [hreg4, ha1],
          fun hx N fr ist tmps s R hat => ?_⟩
        obtain ⟨harea, hN⟩ := N sl hr
        rw [hi] at hN
        obtain ⟨hrd, ⟨k, hk⟩, hcn, hlt⟩ := hN
        have hx4F : GExt s4 sF := (GExt.regs _ _).trans hx
        obtain ⟨s1', st1, at1, R1, ha1', hde1, hv1⟩ :=
          hidx (hx2.trans (hx3.trans (hx4.trans hx4F))) fr ist tmps s hrd R hat
        obtain ⟨s2', st2, hin, hout⟩ := hchk (hx3.trans (hx4.trans hx4F)) hcn fr ist tmps _ s1' rfl R1 at1
        rw [hv1] at hin hout
        obtain ⟨hA1, hA2⟩ := addr_static_some Z.c ist tmps p sl x hr hi
        by_cases hok : lenOK x.len (IR.Sem.opd Z.c ist tmps x.size x.opd)
        · rw [hA1 hok]
          obtain ⟨at2, R2, ha2, hde2, hv2⟩ := hin hok
          obtain ⟨s3', st3, at3, M3, hk3, hv3⟩ := hsc (hx4.trans hx4F) s2' R2.mach at2
          obtain ⟨s4', st4, at4, M4, hk4, hv4⟩ := hbase hx4F harea (by omega) s3' M3 at3
          have hkk := hk3.trans hk4
          refine ⟨s4', ((st1.trans st2).trans st3).trans st4, at4, ?_, ?_, ?_, ?_⟩
          · exact (R2.hl_gone hkk.1 rfl (Or.inr ⟨rfl, hkk.2.1⟩) (fun n o h => h)).weaken
              ⟨fun o h => (by rw [hreg4] at h; exact h), fun o h => (by cases h), fun n o h => (by rw [hreg4] at h; exact h)⟩
          · rw [hkk.2.1, ha2, ha1']
          · rw [hkk.2.2, hde2, hde1]
          · rw [hv4, hv3 k hk (by rw [hk]; exact Nat.le_of_lt Nat.lt_two_pow_self), hv2]
            rcases inline_cases x p.root with ⟨hd, hg⟩ | ⟨len, hlen, hs1, hd, hg⟩
            · rw [hd, hg, Nat.add_zero, Nat.add_zero]
              omega
            · rw [hd, hg, hs1, Nat.mul_one, Nat.mul_one]
              have := hok len hlen
              have := (hcn.len len hlen).2.1
              omega
        · rw [hA2 hok]
          obtain ⟨s2'', htr⟩ : ∃ s'', s'' = s2' := ⟨_, rfl⟩
          exact ⟨s2', st1.trans st2, hout hok⟩

      rcases hsz with h1 | h2
      · simp only [h1, show ((1 : Nat) == 2) = false from rfl, Bool.false_eq_true, if_false]
        refine rest _ ?_
        rw [h1]
        refine wpg_mono (loadHLByte_ok (dt := dt) ok F x.opd s0) ?_
        intro _ s1 ⟨hx1, hr1, h⟩
        refine ⟨hx1, by rw [hr1], fun hx fr ist tmps s hrd R hat => ?_⟩
        obtain ⟨s', st, at', hk, hv⟩ := h hx fr ist tmps s hrd R hat
        exact ⟨s', st, at', R.hl_gone hk.1 rfl (Or.inr ⟨by rw [hr1], hk.2.1⟩) (fun n o h => by rw [← hr1]; exact h),
          hk.2.1, hk.2.2, hv⟩
      · simp only [h2, beq_self_eq_true, if_true]
        refine rest _ ?_
        rw [h2]
        refine wpg_mono (loadHL_ok (dt := dt) ok F x.opd s0) ?_
        intro _ s1 ⟨hx1, ha1, _, h⟩
        refine ⟨hx1, ha1, fun hx fr ist tmps s hrd R hat => ?_⟩
        obtain ⟨s', st, at', R', hk, hv⟩ := h hx fr ist tmps s hrd R hat
        exact ⟨s', st, at', R'.weaken ⟨fun o h => h, fun o h => (by cases h), fun n o h => h⟩, hk.1,
          de_congr hk.2.2.2.2.1 hk.2.2.2.2.2.1, hv⟩

end

/-- info: 'Ember.Proof.Z80Gen.genAddr_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms genAddr_ok

end Ember.Proof.Z80Gen
