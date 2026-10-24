import Ember.Proof.Z80MemW

/-!
# Ember.Proof.Z80StoreW — a `store` of four bytes through an address (plan M7.3)

The code: the value into the accumulator (`loadAcc`: nothing when the
tracker says it holds it), the address into `HL` (`genAddr`), `call
rt_st32` (`RtW.st`: the accumulator written at `HL`).  That the value is
still in the accumulator after `genAddr` (which may call `rt_bound`) is
`genAddr_ok` — the states agree after it with the tracker's claims, the
accumulator's among them — with `genAddr_acc`: the tracker's claim on
the accumulator is the one it had before.  No stack beyond what every
function has (`rtK + 2`) is needed.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

theorem wpg_and {α : Type} {m : GM α} {E : GEnv} {s : GS} {Q1 Q2 : α → GS → Prop} (h1 : wpg m E Q1 s)
    (h2 : wpg m E Q2 s) : wpg m E (fun a s' => Q1 a s' ∧ Q2 a s') s := by
  unfold wpg at h1 h2 ⊢
  cases hm : m E s with
  | error e => trivial
  | ok p => rw [hm] at h1 h2; exact ⟨h1, h2⟩

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop}

/-! ## `genAddr` leaves what the tracker says of the accumulator -/

theorem loadHL_acc (o : Opd) (s0 : GS) :
    wpg (loadHL o) E (fun _ s1 => s1.regs.acc = s0.regs.acc) s0 := by
  unfold loadHL
  simp only [wpg_bind, wpg_get]
  by_cases h1 : s0.regs.hl.contains o = true
  · simp only [h1, if_true, wpg_pure]
  · simp only [h1, Bool.false_eq_true, if_false]
    cases o with
    | const v =>
      simp only [wpg_bind, wpg_ins, wpg_setRegs]
    | slot sl =>
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok (.slot sl) s0) ?_
      intro _ s1 ⟨_, hr, _⟩
      simp only [wpg_ins, wpg_setRegs]
      show s1.regs.acc = s0.regs.acc
      rw [hr]
    | tmp t =>
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok (.tmp t) s0) ?_
      intro _ s1 ⟨_, hr, _⟩
      simp only [wpg_ins, wpg_setRegs]
      show s1.regs.acc = s0.regs.acc
      rw [hr]

/-- **`genAddr` keeps the accumulator's claim.** -/
theorem genAddr_acc (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (p : IR.Addr) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genAddr p) E (fun _ s1 => s1.regs.acc = s0.regs.acc) s0 := by
  unfold addrCov at hcov
  cases hr : p.root with
  | ptr q => simp [hr] at hcov
  | static sl =>
    cases hi : p.idx with
    | none =>
      rw [genAddr_none p sl hr hi]
      simp only [wpg_bind]
      refine wpg_noteAddr sl _ _ (fun s1 _ hr1 _ _ => ?_)
      simp only [wpg_ins, wpg_setRegs]
      show s1.regs.acc = s0.regs.acc
      rw [hr1]
    | some x =>
      rw [genAddr_some p sl x hr hi]
      have rest : ∀ (first : GM Unit), wpg first E (fun _ s1 => s1.regs.acc = s0.regs.acc) s0 →
          wpg (do
            first
            genCheck x (inlineLen x p.root)
            scaleHL x.scale x.scale
            noteAddr sl
            ins .ld [.bc, .imm (slotVal { sl with off := sl.off + (p.off + (inlineLen x p.root).getD 0) })]
            ins .add [.hl, .bc]
            setRegs fun r => { r with hl := [] }) E (fun _ s1 => s1.regs.acc = s0.regs.acc) s0 := by
        intro first h0
        simp only [wpg_bind]
        refine wpg_mono h0 ?_
        intro _ s1 h1
        refine wpg_mono (genCheck_ok (dt := fun _ => False) ok hT F hrt hdep x (inlineLen x p.root) s1) ?_
        intro _ s2 ⟨_, hr2, _⟩
        refine wpg_mono (scale_ok ok F x.scale x.scale s2) ?_
        intro _ s3 ⟨_, hr3, _⟩
        have hb := addBase_ok (E := E) ok F sl (p.off + (inlineLen x p.root).getD 0) s3
        simp only [wpg_bind] at hb
        refine wpg_mono hb ?_
        intro _ sa hb1
        refine wpg_mono hb1 ?_
        intro _ sb hb2
        refine wpg_mono hb2 ?_
        intro _ s4 ⟨_, hr4, _⟩
        rw [wpg_setRegs]
        show s4.regs.acc = s0.regs.acc
        rw [hr4, hr3, hr2, h1]
      by_cases h2 : (x.size == 2) = true
      · simp only [h2, if_true]
        exact rest _ (loadHL_acc x.opd s0)
      · simp only [h2, Bool.false_eq_true, if_false]
        exact rest _ (wpg_mono (loadHLByte_ok (dt := fun _ => False) ok F x.opd s0) (fun _ s1 h => by rw [h.2.1]))

/-! ## `call rt_st32` -/

/-- The regs the tracker keeps after the store: nothing in `A` and `HL`, no slot. -/
def stRegs (r : Regs) : Regs := killedRegs { r with a := [], hl := [] }

/-- **The tail of the store**: the address in `HL`, the value in the
accumulator, `call rt_st32`; the tracker forgets `A`, `HL` and the slots
(not the accumulator: the routine writes elsewhere). -/
theorem st4_tail (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (s1 : GS) :
    wpg (do
      call s!"rt_st{bits 4}"
      setRegs fun r => { r with a := [], hl := [] }
      killSlots) E (fun _ s2 => GExt s1 s2 ∧ s2.regs = stRegs s1.regs ∧
      (GExt s2 sF → ∀ {fr : Fr} {ist tmps} {s : Cpu} {a : Nat}, Rel Z E fr dt s1.regs ist tmps s →
        At Z.addrs (base + s1.out.size) s → s.hl.toNat = a →
        a + 4 ≤ 65536 ∧ (∀ j, j < 4 → Z.data (a + j)) ∧ (∀ j, j < 4 → Z.wr E.fn.name (a + j)) ∧
          (a + 4 ≤ Z.acc ∨ Z.acc + 8 ≤ a) →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
          Rel Z E fr dt s2.regs { ist with mem := IR.Sem.wr ist.mem a 4 (IR.Sem.rd s.mem Z.acc 4) } tmps s')) s1 := by
  simp only [wpg_bind, wpg_call, wpg_setRegs, wpg_killSlots]
  refine ⟨⟨by simp, List.suffix_refl _, List.suffix_refl _⟩, rfl, fun hx fr ist tmps s a R hat hhl hS => ?_⟩
  obtain ⟨hb, hd, hw, hna⟩ := hS
  have hemit : Z.items[base + s1.out.size]? = some (.ins ⟨.call, [.imm (.sym s!"rt_st{bits 4}")]⟩) := F.emitted hx rfl
  obtain ⟨entry, hsym, hent, hR⟩ := hrt.wide.st ⟨_, hemit⟩
  have hroom := R.room
  have hstk := ok.stack
  have hacr := ok.accRam
  have hacs := ok.accStack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  have hram : Z.ramStart ≤ a := (ok.ram a (by simpa using hd 0 (by omega))).1
  obtain ⟨c1, s', cs, st, at', hsp', hh', hrs', hsz', hQ⟩ := call_rule ok hemit hsym hent hR hat R.img R.run R.rs
    R.msz (by omega) (by omega) (fun c1 cs => by
      have hc1 : c1.hl.toNat = a := by rw [hl_congr cs.h cs.l]; exact hhl
      refine ⟨by rw [hc1]; exact hram, by rw [hc1]; exact hb, fun j hj => ?_⟩
      rw [hc1]
      have := ok.nostack _ (hd j hj)
      exact ⟨by omega, by omega⟩)
  have hc1sp : c1.sp.toNat = s.sp.toNat - 2 := by
    rw [cs.sp]
    exact sub2_toNat _ (by omega)
  have hc1hl : c1.hl.toNat = a := by rw [hl_congr cs.h cs.l]; exact hhl
  have hc1m : ∀ y, y < s.sp.toNat - 2 ∨ s.sp.toNat ≤ y → c1.mem.get! y = s.mem.get! y := cs.mem
  have hacc : IR.Sem.rd c1.mem Z.acc 4 = IR.Sem.rd s.mem Z.acc 4 :=
    rd_congr _ _ _ _ (by omega) (fun y h1 h2 => hc1m y (by omega))
  have hfree : FreeStack Z { s with mem := IR.Sem.wr s.mem a 4 (IR.Sem.rd s.mem Z.acc 4) } s' := by
    intro x hx' hnrt
    have hx'' : x < Z.stackLo ∨ s.sp.toNat ≤ x := hx'
    rw [hQ x (by omega) hnrt, hc1hl, hacc]
    show (IR.Sem.wr c1.mem a 4 _).get! x = (IR.Sem.wr s.mem a 4 _).get! x
    rw [wr_get _ _ _ _ _ (by rw [cs.size, R.msz]; exact hb) (by rw [cs.size, R.msz]; exact Nat.le_refl _),
      wr_get _ _ _ _ _ (by rw [R.msz]; exact hb) (by rw [R.msz]; exact Nat.le_refl _)]
    split
    · rfl
    · exact hc1m x (by omega)
  have Rm : Rel Z E fr dt (stRegs s1.regs) { ist with mem := IR.Sem.wr ist.mem a 4 (IR.Sem.rd s.mem Z.acc 4) } tmps
      { s with mem := IR.Sem.wr s.mem a 4 (IR.Sem.rd s.mem Z.acc 4) } :=
    R.wr_mem ok hT (by decide) hb hd hw hna rfl rfl rfl rfl
      (fun o ho => by simp [stRegs, killedRegs] at ho) (fun o ho => by simp [stRegs, killedRegs] at ho)
      (fun m o h => killed_acc h)
  refine ⟨s', st, by simpa [Nat.add_assoc] using at', ?_⟩
  exact Rm.free_stack ok hT hfree hsz' hrs' (by rw [hh', R.run]) hsp'
    (fun o ho => by simp [killedRegs] at ho) (fun o ho => by simp [killedRegs] at ho)
    (fun sl h => by simp [killedRegs] at h) (fun sl h => by simp [killedRegs] at h)
    (fun n o h => h)

/-! ## The store -/

/-- **`store` of four bytes.** -/
theorem store4_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (p : IR.Addr) (src : Opd) (hcov : addrCov p = true) (s0 : GS) :
    wpg (genInstr (.store 4 p src)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → AddrNeed Z E dt p ∧ AddrStore Z E p 4 ∧ RdW Z E dt 4 src → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        After Z E base fr dt (.store 4 p src) s1 ist tmps s (IR.Sem.step Z.c ist tmps (.store 4 p src)))) s0 := by
  simp only [genInstr, wpg_bind, wpg_get, show ((4 : Nat) == 1) = false from rfl,
    show ((4 : Nat) == 2) = false from rfl, Bool.false_eq_true, if_false]
  refine wpg_mono (loadAcc_ok (dt := dt) ok hT F ⟨by decide, by decide⟩ hrt.wide hdep src s0) ?_
  intro _ s1 ⟨hx1, hacc1, hl⟩
  refine wpg_mono (wpg_and (genAddr_ok (dt := dt) ok hT F hrt hdep p hcov s1)
    (genAddr_acc ok hT F hrt hdep p hcov s1)) ?_
  intro _ s2 ⟨⟨hx2, _, _, ha⟩, hacc2⟩
  have t := st4_tail (dt := dt) ok hT F hrt hdep s2
  simp only [wpg_bind] at t
  refine wpg_mono t ?_
  intro _ sa t1
  refine wpg_mono t1 ?_
  intro _ sb t2
  refine wpg_mono t2 ?_
  intro _ s3 ⟨hx3, _, hw⟩
  refine ⟨hx1.trans (hx2.trans hx3), fun hxF ⟨hN, hD, hrd⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨sl, stl, atl, Rl⟩ := hl (hx2.trans (hx3.trans hxF)) fr ist tmps s hrd R hat
  refine after_store p src _ (fun a s' => Steps s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
      Rel Z E fr dt s2.regs ist tmps s' ∧ s'.hl.toNat = a % 65536) (by
      have := ha (hx3.trans hxF) hN fr ist tmps sl Rl atl
      cases haddr : IR.Sem.addr Z.c ist tmps p with
      | none =>
        rw [haddr] at this
        obtain ⟨s', st, htr⟩ := this
        exact ⟨s', stl.trans st, htr⟩
      | some a =>
        rw [haddr] at this
        obtain ⟨s', st, at', R', _, _, hv⟩ := this
        exact ⟨s', stl.trans st, at', R', hv⟩)
    (fun a s' haddr hb ⟨st, at', R', hv⟩ => ?_)
  obtain ⟨hb4, hd, hwr, hna⟩ := hD ist tmps a haddr hb
  have hval : IR.Sem.rd s'.mem Z.acc 4 = IR.Sem.opd Z.c ist tmps 4 src :=
    R'.racc 4 src (by rw [hacc2, hacc1]) (Rd.own_w hrd)
  obtain ⟨s'', st2, at2, R2⟩ := hw hxF R' at' (by rw [hv, Nat.mod_eq_of_lt (by omega)]) ⟨hb4, hd, hwr, hna⟩
  rw [hval] at R2
  exact ⟨s'', st.trans st2, at2, R2⟩

end

/-- info: 'Ember.Proof.Z80Gen.store4_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store4_ok

end Ember.Proof.Z80Gen
