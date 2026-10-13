import Ember.Proof.Z80Ext

/-!
# Ember.Proof.Z80Acc — values wider than two bytes: the accumulator (plan M7.3)

A value of four bytes lives in the runtime's `rt_acc`: `loadAcc` brings
an operand there (a constant from the literal pool), `storeAcc` stores
it — both by routines of the runtime taken with specifications (`RtW`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The constant `v` of `n` bytes is in the literal pool of the image. -/
def LitOK (Z : ZCtx) (n v : Nat) : Prop :=
  ∃ ad, Z.sym s!"lit{bits n}_{v % 2 ^ bits n}" ad ∧ ad + n ≤ Z.ramStart ∧
    ∀ s : Cpu, Img Z.a 0 s → IR.Sem.rd s.mem ad n = v % 2 ^ (8 * n)

/-- A wide operand can be read: a constant from the pool, the others where they are. -/
def RdW (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (n : Nat) : Opd → Prop
  | .const v => LitOK Z n v
  | o => Rd Z E dt n o

/-- An operand of `n` bytes can be read: where it is, or (wider than two bytes) a constant from the pool. -/
def RdN (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (n : Nat) (o : Opd) : Prop :=
  if n ≤ 2 then Rd Z E dt n o else RdW Z E dt n o

/-- Where a wide operand is, as the generator names it. -/
def ptrVal (E : GEnv) (n : Nat) : Opd → Val
  | .const v => .sym s!"lit{bits n}_{v % 2 ^ bits n}"
  | o => opdVal E o

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem ptrOf_ok (n : Nat) (o : Opd) (s : GS) :
    wpg (ptrOf n o) E (fun p s1 => s1.out = s.out ∧ s1.regs = s.regs ∧ p = ptrVal E n o ∧
      (∀ t, o = .tmp t → E.spilled[t]! = true) ∧ s1.jumps = s.jumps ∧ s1.labelRegs = s.labelRegs ∧
      MemLive E o) s := by
  unfold ptrOf
  cases o with
  | const v =>
    simp only [wpg_bind, wpg_modify, wpg_pure]
    refine ⟨?_, ?_, rfl, fun t h => (by cases h), ?_, ?_, trivial⟩ <;> split <;> rfl
  | slot sl =>
    refine wpg_mono (addrOf_ok (.slot sl) s) ?_
    intro p s1 ⟨h1, h2, h3, h4, _, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h6, h7, h8⟩
  | tmp t =>
    refine wpg_mono (addrOf_ok (.tmp t) s) ?_
    intro p s1 ⟨h1, h2, h3, h4, _, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h6, h7, h8⟩

theorem Rd.own_w {n : Nat} {o : Opd} (h : RdW Z E dt n o) : Own E o := by
  cases o with
  | const v => trivial
  | tmp t => trivial
  | slot sl => exact Rd.own (dt := dt) (n := n) h

/-- **The address of a wide operand**, what is there, and that it is not in the stack. -/
theorem ptr_ok (ok : Z.OK) (hT : FnLay Z E) {n : Nat} (hn : 0 < n) {o : Opd} (hrd : RdW Z E dt n o)
    (hsp : ∀ t, o = .tmp t → E.spilled[t]! = true) (hlv : MemLive E o) (pc : Nat) :
    ∃ A, (Z.a.env pc).val (ptrVal E n o) = Int.ofNat A ∧ A + n ≤ 65536 ∧
      (∀ j, j < n → A + j < Z.stackLo ∨ Z.stackHi ≤ A + j) ∧
      (∀ j, j < n → A + j < Z.acc ∨ Z.acc + 8 ≤ A + j) ∧
      ∀ regs ist tmps (s : Cpu), Rel Z E fr dt regs ist tmps s →
        IR.Sem.rd s.mem A n = IR.Sem.opd Z.c ist tmps n o := by
  have hstk := ok.stack
  have hacr := ok.accRam
  cases o with
  | const v =>
    obtain ⟨ad, hsym, hb, hval⟩ := hrd
    refine ⟨ad, sym_val pc hsym, by omega, fun j hj => Or.inl (by omega), fun j hj => Or.inl (by omega),
      fun regs ist tmps s R => ?_⟩
    rw [hval s R.img]
    rfl
  | slot sl =>
    obtain ⟨hv, hb⟩ := opd_val (dt := dt) ok (o := .slot sl) hrd hsp (fun v h => by cases h) pc
    refine ⟨_, hv, hb, fun j hj => ok.nostack _ (hrd.2.2.1 hlv j hj), fun j hj => ok.accData _ (hrd.2.2.1 hlv j hj),
      fun regs ist tmps s R => ?_⟩
    exact opd_mem (dt := dt) (o := .slot sl) hrd hsp (fun v h => by cases h) hlv R
  | tmp t =>
    obtain ⟨hv, hb⟩ := opd_val (dt := dt) ok (o := .tmp t) hrd hsp (fun v h => by cases h) pc
    have hns := hT.nostack t (hsp t rfl)
    have hsz := (hrd (hsp t rfl)).2.2.2
    have hna := hT.noacc t (hsp t rfl)
    refine ⟨_, hv, hb, fun j hj => ?_, fun j hj => ?_, fun regs ist tmps s R => ?_⟩
    · show tmpAddr Z E t + j < Z.stackLo ∨ Z.stackHi ≤ tmpAddr Z E t + j
      omega
    · show tmpAddr Z E t + j < Z.acc ∨ Z.acc + 8 ≤ tmpAddr Z E t + j
      omega
    · exact opd_mem (dt := dt) (o := .tmp t) hrd hsp (fun v h => by cases h) hlv R

/-- What `loadAcc n o` promises: the operand in the accumulator. -/
def LoadAcc (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (n : Nat) (o : Opd) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.acc = some (n, o) ∧
    (GExt s1 sF → ∀ fr ist tmps s, RdW Z E dt n o → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s')

theorem loadAcc_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 0 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (o : Opd) (s0 : GS) :
    wpg (loadAcc n o) E (LoadAcc Z E base sF dt n o s0) s0 := by
  unfold loadAcc
  simp only [wpg_bind, wpg_get]
  by_cases h1 : (s0.regs.acc == some (n, o)) = true
  · simp only [h1, if_true, wpg_pure]
    have hacc : s0.regs.acc = some (n, o) := by simpa using h1
    exact ⟨GExt.refl _, hacc, fun _ fr ist tmps s _ R hat => ⟨s, Steps.refl _, hat, R⟩⟩
  · simp only [h1, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (ptrOf_ok n o s0) ?_
    intro p s1 ⟨ho1, hr1, hp, hsp, hj1, hl1, hlv⟩
    subst hp
    simp only [wpg_ins, wpg_call, wpg_setRegs]
    have hx01 : GExt s0 s1 := ⟨by simp [ho1], by simp [hj1], by simp [hl1]⟩
    have hxp : GExt s1 (pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1) :=
      pushL_ext _ _
    refine ⟨hx01.trans (hxp.trans (GExt.regs _ _)), rfl, fun hx fr ist tmps s hrd R hat => ?_⟩
    have hxm : GExt (pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1) sF :=
      (GExt.regs _ _).trans hx
    obtain ⟨ad, had, hpc⟩ := hat
    obtain ⟨A, hv, hb, hns, hna, hmem⟩ := ptr_ok (fr := fr) ok hT hn.1 hrd hsp hlv ad
    have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩).toNat = A :=
      immW_toNat _ _ _ _ rfl hv (by omega)
    have hS : Sys s (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩)).tick 10) := by
      simp only [Sys, zsim, and_self]
    obtain ⟨st1, at1, _⟩ := run_reg ok F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩) })
      ((GExt.push _ _).trans hxm) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩) _
      (fun ad' had' => by
        rw [ho1, had] at had'
        cases had'
        intro _
        rfl) rfl hS
    have R1 : Rel Z E fr dt { s0.regs with hl := [] } ist tmps
        (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩)).tick 10) :=
      R.hl_gone hS rfl (Or.inr ⟨rfl, by simp only [zsim]⟩) (fun n o h => h)
    obtain ⟨c1, s', cs, st2, at2, hrel, hfree, hsp', hh', hrs', hsz'⟩ := acc_call ok F
      (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (ptrVal E n o)]⟩) })
      (s1 := pushL [⟨.ld, [.hl, .imm (ptrVal E n o)]⟩, ⟨.call, [.imm (.sym s!"rt_ld{bits n}")]⟩] s1)
      hxm rfl hrt.ld hdep R1 at1 (fun c1 cs => by
        have hc1 : c1.hl.toNat = A := by
          rw [hl_congr cs.h cs.l]
          simp only [zsim]
          exact hnn
        exact ⟨by rw [hc1]; exact hb, fun j hj => by rw [hc1]; exact ⟨hna j hj, hns j hj⟩⟩)
    refine ⟨s', st1.trans st2, at2, R1.acc_free ok hT hfree hsz' hrs' hh' hsp' (fun o' ho' => by cases ho')
      (fun o' ho' => by cases ho') (fun sl h => by cases h) (fun sl h => by cases h) (fun m o' h hown => ?_)
      (fun m sl h hown => ?_) (fun m o' h => ?_)⟩
    · cases h
      rw [hrel, hl_congr cs.h cs.l]
      simp only [zsim]
      rw [hnn, ← hmem _ ist tmps _ R]
      have hroom := R.room
      have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
      have hstk := ok.stack
      refine rd_congr _ _ _ _ hb (fun x hx1 hx2 => ?_)
      have := hns (x - A) (by omega)
      rw [show A + (x - A) = x by omega] at this
      rw [cs.mem x (by simp only [zsim]; omega)]
      simp only [zsim]
    · cases h
      exact Rd.use (dt := dt) (n := n) hrd
    · cases h
      exact hn.2

/-! ## Storing the accumulator -/

/-- `ld hl,p; call rt_st`: the accumulator written at `A`, as far as
the states are compared (outside the free stack and the runtime's bytes). -/
theorem st_run (ok : Z.OK) (F : GFinal Z base sF) {n : Nat} (hn : 0 < n ∧ n ≤ 8) (hrt : RtW Z n)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) {s1 : GS} {p : Val}
    (hx : GExt (pushL [⟨.ld, [.hl, .imm p]⟩, ⟨.call, [.imm (.sym s!"rt_st{bits n}")]⟩] s1) sF)
    {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu} (R : Rel Z E fr dt regs ist tmps s)
    (hat : At Z.addrs (base + s1.out.size) s) {A : Nat}
    (hv : ∀ pc, (Z.a.env pc).val p = Int.ofNat A) (hram : Z.ramStart ≤ A) (hb : A + n ≤ 65536)
    (hna : A + n ≤ Z.acc ∨ Z.acc + 8 ≤ A) (hnst : A + n ≤ Z.stackLo ∨ Z.stackHi ≤ A) :
    ∃ s', Steps s s' ∧
      At Z.addrs (base + (pushL [⟨.ld, [.hl, .imm p]⟩, ⟨.call, [.imm (.sym s!"rt_st{bits n}")]⟩] s1).out.size) s' ∧
      s'.sp = s.sp ∧ s'.halted = s.halted ∧ s'.ramStart = s.ramStart ∧ s'.mem.size = 65536 ∧
      FreeStack Z { s with mem := IR.Sem.wr s.mem A n (IR.Sem.rd s.mem Z.acc n) } s' := by
  obtain ⟨entry, hsym, hent, hR⟩ := hrt.st ⟨_,
    F.emitted (s := pushL [⟨.ld, [.hl, .imm p]⟩, ⟨.call, [.imm (.sym s!"rt_st{bits n}")]⟩] s1) hx rfl⟩
  have hroom := R.room
  have hstk := ok.stack
  have hacr := ok.accRam
  have hacs := ok.accStack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm p]⟩).toNat = A :=
    immW_toNat _ _ _ _ rfl (hv ad) (by omega)
  have hS : Sys s (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm p]⟩)).tick 10) := by
    simp only [Sys, zsim, and_self]
  obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1) (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm p]⟩) })
    ((GExt.push _ _).trans hx) rfl R.mach ⟨ad, had, hpc⟩ _ (fun ad' had' => by
      rw [had] at had'
      cases had'
      intro _
      rfl) rfl hS
  obtain ⟨c1, s', cs, st2, at2, hsp', hh', hrs', hsz', hQ⟩ := call_rule ok
    (F.emitted (s := pushL [⟨.ld, [.hl, .imm p]⟩, ⟨.call, [.imm (.sym s!"rt_st{bits n}")]⟩] s1) hx rfl) hsym hent hR
    at1 M1.1 M1.2 (by rw [hS.2.1]; exact R.rs) (by rw [hS.1]; exact R.msz) (by rw [hS.2.2.2]; omega)
    (by rw [hS.2.2.2]; omega) (fun c1 cs => by
      have hc1 : c1.hl.toNat = A := by
        rw [hl_congr cs.h cs.l]
        simp only [zsim]
        exact hnn
      exact ⟨by rw [hc1]; exact hram, by rw [hc1]; exact hb, fun j hj => by rw [hc1]; exact ⟨by omega, by omega⟩⟩)
  have hc1sp : c1.sp.toNat = s.sp.toNat - 2 := by
    rw [cs.sp, hS.2.2.2]
    exact sub2_toNat _ (by omega)
  have hc1hl : c1.hl.toNat = A := by
    rw [hl_congr cs.h cs.l]
    simp only [zsim]
    exact hnn
  have hc1m : ∀ y, y < s.sp.toNat - 2 ∨ s.sp.toNat ≤ y → c1.mem.get! y = s.mem.get! y := by
    intro y hy
    rw [cs.mem y (by rw [hS.2.2.2]; exact hy), hS.1]
  have hacc : IR.Sem.rd c1.mem Z.acc n = IR.Sem.rd s.mem Z.acc n :=
    rd_congr _ _ _ _ (by omega) (fun y h1 h2 => hc1m y (by omega))
  refine ⟨s', st1.trans st2, by simpa [pushL, Nat.add_assoc] using at2, by rw [hsp', hS.2.2.2],
    by rw [hh', R.run], by rw [hrs', hS.2.1], hsz', fun x hx' hnrt => ?_⟩
  have hx'' : x < Z.stackLo ∨ s.sp.toNat ≤ x := hx'
  rw [hQ x (by omega) hnrt, hc1hl, hacc]
  show (IR.Sem.wr c1.mem A n _).get! x = (IR.Sem.wr s.mem A n _).get! x
  rw [wr_get _ _ _ _ _ (by rw [cs.size, hS.1, R.msz]; exact hb) (by rw [cs.size, hS.1, R.msz]; exact Nat.le_refl _),
    wr_get _ _ _ _ _ (by rw [R.msz]; exact hb) (by rw [R.msz]; exact Nat.le_refl _)]
  split
  · rfl
  · exact hc1m x (by omega)

/-- What `storeAcc n d` promises: the accumulator is stored as the IR stores its value. -/
def StoreAcc (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (n : Nat) (d : Dst) (s0 : GS) (_ : Unit)
    (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → ∀ fr ist tmps s v, Wr Z E n d → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → IR.Sem.rd s.mem Z.acc n = v →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr (dtAfter dt d) s1.regs (IR.Sem.setDst Z.c ist tmps n d v).1 (IR.Sem.setDst Z.c ist tmps n d v).2 s')

theorem rd_wr_other (m : ByteArray) (a n v b k : Nat) (ha : a + n ≤ 65536) (hb : b + k ≤ 65536)
    (h : a + n ≤ b ∨ b + k ≤ a) : IR.Sem.rd (IR.Sem.wr m a n v) b k = IR.Sem.rd m b k :=
  rd_congr _ _ _ _ hb (fun x h1 h2 => wr_get_far _ _ _ _ _ ha (by omega))

theorem storeAcc_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 0 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (s0 : GS) :
    wpg (storeAcc n d) E (StoreAcc Z E base sF dt n d s0) s0 := by
  have hacr := ok.accRam
  unfold storeAcc
  cases d with
  | slot sl =>
    simp only [wpg_bind, killWrite, wpg_setRegs]
    refine wpg_storeNeeded sl n _ _ (fun b hb => ?_)
    -- what the tracker says afterwards: the accumulator holds the slot
    have claims : ∀ (ist : IR.Sem.St) (tmps : Array Nat) (m : ByteArray) (v : Nat), WrSlot Z E n sl →
        ist.mem.size = 65536 → IR.Sem.rd m Z.acc n = v →
        (∀ k o, ({ acc := some (n, Dst.opd (.slot sl)) } : Regs).acc = some (k, o) → Own E o →
          IR.Sem.rd m Z.acc k =
            IR.Sem.opd Z.c { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps k o) ∧
        (∀ k a, ({ acc := some (n, Dst.opd (.slot sl)) } : Regs).acc = some (k, .slot a) → Own E (.slot a) →
          Z.use E.fn.name (a, k)) ∧
        (∀ k o, ({ acc := some (n, Dst.opd (.slot sl)) } : Regs).acc = some (k, o) → k ≤ 8) := by
      intro ist tmps m v W hisz hv
      have hb' := ok.dbound E.fn.name sl n W.dst
      refine ⟨fun k o h hown => ?_, fun k a h hown => ?_, fun k o h => ?_⟩
      · cases h
        show _ = IR.Sem.rd (IR.Sem.wr ist.mem _ n v) _ n
        rw [rd_wr _ _ _ _ (by rw [hisz]; exact hb') (by rw [hisz]; exact Nat.le_refl _), hv, ← hv]
        exact (Nat.mod_eq_of_lt (rd_lt _ _ _)).symm
      · cases h
        exact W.use hown
      · cases h
        exact hn.2
    cases b with
    | true =>
      simp only [if_true, wpg_bind, wpg_ins, wpg_call, wpg_setRegs]
      refine ⟨⟨by simp, List.suffix_refl _, List.suffix_refl _⟩, fun hx fr ist tmps s v W R hat hv => ?_⟩
      obtain ⟨ad0, harea⟩ := W.area
      have hb' := ok.dbound E.fn.name sl n W.dst
      obtain ⟨s', st, at', hsp', hh', hrs', hsz', hfree⟩ := st_run ok F hn hrt hdep
        (s1 := s0) (p := slotVal sl) ⟨hx.out, hx.jumps, hx.labels⟩ R hat
        (fun pc => slot_val ok sl ad0 pc harea) W.ram hb' W.noacc W.nostack
      rw [hv] at hfree
      have hacc_keep : IR.Sem.rd (IR.Sem.wr s.mem (Z.c.layout.addr sl) n v) Z.acc n = v := by
        rw [rd_wr_other _ _ _ _ _ n hb' (by omega) (by rcases W.noacc with h | h; exact Or.inl h; exact Or.inr (by omega))]
        exact hv
      obtain ⟨c1, c2, c3⟩ := claims ist tmps (IR.Sem.wr s.mem (Z.c.layout.addr sl) n v) v W R.isz hacc_keep
      have Rs : Rel Z E fr dt { acc := some (n, Dst.opd (.slot sl)) }
          { ist with mem := IR.Sem.wr ist.mem (Z.c.layout.addr sl) n v } tmps
          { s with mem := IR.Sem.wr s.mem (Z.c.layout.addr sl) n v } :=
        Rel.wr_slot ok hT R W v rfl rfl rfl rfl (fun o ho => by cases ho) (fun o ho => by cases ho)
          (fun a h => by cases h) (fun a h => by cases h) c1 c2 c3
      refine ⟨s', st, by simpa [pushL] using at', ?_⟩
      exact Rel.dt_mono (Rs.free_stack ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun a h => by cases h) (fun a h => by cases h) (fun k o h => h))
        (fun t ht => by rcases ht with h | h; exact h; cases h)
    | false =>
      simp only [Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _⟩, fun hx fr ist tmps s v W R hat hv => ?_⟩
      obtain ⟨harea, lv, hlive, hall⟩ := hb rfl
      obtain ⟨c1, c2, c3⟩ := claims ist tmps s.mem v W R.isz hv
      refine ⟨s, Steps.refl _, hat, ?_⟩
      exact Rel.dt_mono (Rel.wr_dead ok R W v (W.dead harea lv hlive hall) (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun a h => by cases h) (fun a h => by cases h) c1 c2 c3)
        (fun t ht => by rcases ht with h | h; exact h; cases h)
  | tmp t =>
    simp only [wpg_bind]
    refine wpg_tmpSlot t _ _ ?_
    have claims : ∀ (ist : IR.Sem.St) (tmps : Array Nat) (m : ByteArray) (v : Nat), WrTmp E n t →
        tmps.size = E.fn.tmps.size → IR.Sem.rd m Z.acc n = v →
        (∀ k o, ({ acc := some (n, Dst.opd (.tmp t)) } : Regs).acc = some (k, o) → Own E o →
          IR.Sem.rd m Z.acc k = IR.Sem.opd Z.c ist (tmps.setIfInBounds t (IR.modN n v)) k o) ∧
        (∀ k a, ({ acc := some (n, Dst.opd (.tmp t)) } : Regs).acc = some (k, .slot a) → Own E (.slot a) →
          Z.use E.fn.name (a, k)) ∧
        (∀ k o, ({ acc := some (n, Dst.opd (.tmp t)) } : Regs).acc = some (k, o) → k ≤ 8) := by
      intro ist tmps m v W htsz hv
      have hlt : t < tmps.size := by rw [htsz]; exact W.lt
      refine ⟨fun k o h hown => ?_, fun k a h hown => ?_, fun k o h => ?_⟩
      · cases h
        show _ = IR.modN n ((tmps.setIfInBounds t (IR.modN n v)).getD t 0)
        have hvl : v < 2 ^ (8 * n) := by rw [← hv]; exact rd_lt _ _ _
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hlt, IR.modN, hv,
          Nat.mod_eq_of_lt hvl]
      · cases h
      · cases h
        exact hn.2
    by_cases hsp : E.spilled[t]! = true
    · simp only [hsp, if_true, wpg_bind, wpg_ins, wpg_call, wpg_setRegs]
      refine ⟨⟨by simp, List.suffix_refl _, List.suffix_refl _⟩, fun hx fr ist tmps s v W R hat hv => ?_⟩
      obtain ⟨ad0, harea⟩ := hT.area
      have hb' : tmpAddr Z E t + n ≤ 65536 := by have := hT.bound t hsp; rw [W.size] at this; exact this
      obtain ⟨s', st, at', hsp', hh', hrs', hsz', hfree⟩ := st_run ok F hn hrt hdep
        (s1 := s0) (p := slotVal { area := tmpArea E.fn.name, off := E.tmpOff[t]! })
        ⟨hx.out, hx.jumps, hx.labels⟩ R hat
        (fun pc => slot_val ok { area := tmpArea E.fn.name, off := E.tmpOff[t]! } ad0 pc harea) (hT.ram t hsp) hb'
        (by have := hT.noacc t hsp; rw [W.size] at this; exact this)
        (by have := hT.nostack t hsp; rw [W.size] at this; exact this)
      rw [hv] at hfree
      have hna := hT.noacc t hsp
      rw [W.size] at hna
      have hacc_keep : IR.Sem.rd (IR.Sem.wr s.mem (tmpAddr Z E t) n v) Z.acc n = v := by
        rw [rd_wr_other _ _ _ _ _ n hb' (by omega) (by rcases hna with h | h; exact Or.inl h; exact Or.inr (by omega))]
        exact hv
      obtain ⟨c1, c2, c3⟩ := claims ist tmps (IR.Sem.wr s.mem (tmpAddr Z E t) n v) v W R.tsz hacc_keep
      have Rs : Rel Z E fr (dtAfter dt (.tmp t)) { acc := some (n, Dst.opd (.tmp t)) } ist
          (tmps.setIfInBounds t (IR.modN n v)) { s with mem := IR.Sem.wr s.mem (tmpAddr Z E t) n v } :=
        Rel.wr_tmp ok hT R W v (by rw [if_pos hsp]) rfl rfl rfl (fun o ho => by cases ho)
          (fun o ho => by cases ho) (fun a h => by cases h) (fun a h => by cases h) c1 c2 c3
      refine ⟨s', st, by simpa [pushL] using at', ?_⟩
      exact Rs.free_stack ok hT hfree hsz' hrs' hh' hsp' (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun a h => by cases h) (fun a h => by cases h) (fun k o h => h)
    · simp only [hsp, Bool.false_eq_true, if_false, wpg_pure, wpg_setRegs]
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _⟩, fun hx fr ist tmps s v W R hat hv => ?_⟩
      obtain ⟨c1, c2, c3⟩ := claims ist tmps s.mem v W R.tsz hv
      exact ⟨s, Steps.refl _, hat, Rel.wr_tmp ok hT R W v (by rw [if_neg hsp]) rfl rfl rfl (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun a h => by cases h) (fun a h => by cases h) c1 c2 c3⟩

/-- **`mov` of a wide value.** -/
theorem movW_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {n : Nat} (hn : 2 < n ∧ n ≤ 8)
    (hrt : RtW Z n) (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (d : Dst) (src : Opd) (s0 : GS) :
    wpg (genInstr (.mov n d src)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.mov n d src) (RdW Z E dt n src ∧ Wr Z E n d) s0) s0 := by
  have h1 : (n == 1) = false := by simp; omega
  have h2 : (n == 2) = false := by simp; omega
  simp only [genInstr, Codegen.load, store, wpg_bind, h1, h2, Bool.false_eq_true, if_false]
  refine wpg_mono (loadAcc_ok (dt := dt) ok hT F ⟨by omega, hn.2⟩ hrt hdep src s0) ?_
  intro _ s1 ⟨hx1, hacc1, hl⟩
  refine wpg_mono (storeAcc_ok (dt := dt) ok hT F ⟨by omega, hn.2⟩ hrt hdep d s1) ?_
  intro _ s2 ⟨hx2, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hrd, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1⟩ := hl (hx2.trans hxF) fr ist tmps s hrd R hat
  obtain ⟨s'', st2, at2, R2⟩ := hs hxF fr ist tmps s' _ hwr R1 at1 (R1.racc n src hacc1 (Rd.own_w hrd))
  exact ⟨s'', st1.trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
