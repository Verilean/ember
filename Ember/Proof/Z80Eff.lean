import Ember.Proof.Z80After
import Ember.Proof.Z80Mul

/-!
# Ember.Proof.Z80Eff — effects (plan M7.3)

The code of an effect loads its argument and calls the effect's routine
of the runtime; the routine is taken with a specification (`RtEff`): it
does to the machine what `IR.Sem.effect` does to the world.  So after
the code the machine stands for the world after the effect.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)
open Ember.Lang (Effect)

/-- The effects covered, with their arguments and results. -/
def effCov : Effect → List (Nat × Opd) → Option (Nat × Dst) → Bool
  | .outByte, [(1, _)], none | .drop, [(1, _)], none | .outEnd, [], none => true
  | .inputNext, [], r | .ringPop, [], r => (r.map (·.1 == 2)).getD true
  | _, _, _ => false

theorem opd_world (c : IR.Ctx) (ist : IR.Sem.St) (wd : Ember.Lang.World) (tmps : Array Nat) (n : Nat) (o : Opd) :
    IR.Sem.opd c { ist with world := wd } tmps n o = IR.Sem.opd c ist tmps n o := by
  cases o <;> rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- The relation does not look at the world. -/
theorem Rel.world {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu} (R : Rel Z E fr dt regs ist tmps s)
    (wd : Ember.Lang.World) : Rel Z E fr dt regs { ist with world := wd } tmps s :=
  ⟨R.img, R.run, R.mem, R.tmp, R.rs, R.msz, R.isz, R.tsz, R.sp, R.room, R.stk, R.out,
    fun o ho hown => by rw [opd_world]; exact R.ra o ho hown,
    fun o ho hown => by rw [opd_world]; exact R.rhl o ho hown,
    fun n o h hown => by rw [opd_world]; exact R.racc n o h hown, R.ina, R.inhl, R.inacc, R.nacc⟩

/-- **The call of an effect's routine**, from states that agree with the
arguments in place: the machine stands for the world after the effect. -/
theorem eff_call (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {s0 s1 : GS} {e : Effect} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins ⟨.call, [.imm (.sym (effectRoutine e))]⟩)) (hrt : RtEff Z e)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hat : At Z.addrs (base + s0.out.size) s) (w : Z.W)
    (hw : Z.wrel ist.world w) (vs : List Nat) (hargs : EffArgs e vs s) :
    ∃ s' w', WSteps Z (s, w) (s', w') ∧ At Z.addrs (base + s1.out.size) s' ∧
      Z.wrel (IR.Sem.effect Z.c ist.world e vs).2 w' ∧
      Rel Z E fr dt {} { ist with world := (IR.Sem.effect Z.c ist.world e vs).2 } tmps s' ∧
      ∀ r, (IR.Sem.effect Z.c ist.world e vs).1 = some r → s'.hl.toNat = r := by
  obtain ⟨entry, hsym, hent, hspec⟩ := hrt
  have hroom := R.room
  have hstk := ok.stack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  obtain ⟨c1, st1, cs, hpc1, I1, hh1, hrs1, hback⟩ :=
    call_step ok (F.emitted hx ho) hsym hent hat R.img R.run R.rs R.msz (by omega) (by omega)
  have hc1sp : c1.sp.toNat = s.sp.toNat - 2 := by rw [cs.sp]; exact sub2_toNat _ (by omega)
  have hargs1 : EffArgs e vs c1 := by
    unfold EffArgs at hargs ⊢
    cases e <;> first | exact hargs | (rw [cs.a]; exact hargs)
  obtain ⟨s', w', st2, hpc', hsp', hh', hrs', hsz', hfree, hw', hres⟩ :=
    hspec c1 w ist.world vs hpc1 I1 hh1 (by rw [hrs1]; exact R.rs) (by rw [cs.size]; exact R.msz) (by omega)
      (by omega) hw hargs1
  have hmem : FreeStack Z s s' := by
    intro x hx' hnrt
    rw [hfree x (by omega) hnrt, cs.mem x (by omega)]
  refine ⟨s', w', (Steps.lift ok st1 w).trans st2, ?_, hw', ?_, hres⟩
  · have := hback s' (by rw [hpc', cpu_rd16 _ _ (by omega), hc1sp])
    rw [ho, Array.size_push, ← Nat.add_assoc]
    exact this
  · refine (R.free_stack ok hT hmem hsz' (by rw [hrs', hrs1]) (by rw [hh', R.run]) ?_
      (fun o ho => by cases ho) (fun o ho => by cases ho) (fun sl h => by cases h) (fun sl h => by cases h)
      (fun n o h => by cases h)).world _
    rw [hsp', cs.sp]
    exact UInt16.sub_add_cancel _ _

/-- **An effect**: the argument loaded by `m`, the routine called, the result stored. -/
theorem eff_core (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (e : Effect) (hk : effKnown e = true) (args : List (Nat × Opd))
    (ret : Option (Nat × Dst))
    (hret : ∀ n d, ret = some (n, d) → n = 2 ∧ ∀ wd vs, ∃ r, (IR.Sem.effect Z.c wd e vs).1 = some r)
    (H : Prop) (m : GM Unit) (s0 : GS)
    (hm : wpg m E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → H → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          EffArgs e (args.map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2) s')) s0) :
    wpg (do m; call (effectRoutine e); killAll; retStore ret) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → H ∧ (∀ n d, ret = some (n, d) → Wr Z E n d) → ∀ fr ist tmps s w,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s → Z.wrel ist.world w →
        MAfter Z E base fr dt (.eff e args ret) s1 ist tmps s w (IR.Sem.step Z.c ist tmps (.eff e args ret)))) s0 := by
  simp only [wpg_bind]
  refine wpg_mono hm ?_
  intro _ s1 ⟨hx1, hl⟩
  simp only [wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (retStore_ok (dt := dt) ok hT F hrt.wide hdep ret (fun n d h => Or.inr (Or.inl (hret n d h).1)) _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (effectRoutine e))]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hx1.trans (hmid.trans hx2), fun hx ⟨hH, hwr⟩ fr ist tmps s w R hat hw => ?_⟩
  obtain ⟨s', st1, at1, R1, hargs⟩ := hl (hmid.trans (hx2.trans hx)) hH fr ist tmps s R hat
  obtain ⟨s'', w', st2, at2, hw', R2, hres⟩ := eff_call ok hT F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (effectRoutine e))]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hx)) rfl (hrt.eff e hk) hdep R1 at1 w hw _ hargs
  obtain ⟨s3, st3, at3, R3⟩ := hs hx hwr fr _ tmps s''
    (IR.Sem.effect Z.c ist.world e (args.map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2)).1 R2 at2 (by
      intro n d hnd
      obtain ⟨h2, hsome⟩ := hret n d hnd
      obtain ⟨r, hr⟩ := hsome ist.world (args.map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2)
      subst h2
      refine ⟨fun h => (by cases h), fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hr]
      exact hres r hr)
  refine ⟨s3, w', ((Steps.lift ok st1 w).trans st2).trans (Steps.lift ok st3 w'), ?_, at3, R3⟩
  rw [setRet_world]
  exact hw'

/-- What an effect needs of the program. -/
def EffNeed (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (args : List (Nat × Opd)) (ret : Option (Nat × Dst)) : Prop :=
  (∀ o, args = [(1, o)] → Rd Z E dt 1 o) ∧ ∀ n d, ret = some (n, d) → Wr Z E n d

/-- What the generator promises for an effect. -/
def EffPost (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (e : Effect) (args : List (Nat × Opd))
    (ret : Option (Nat × Dst)) (s0 : GS) (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → EffNeed Z E dt args ret → ∀ fr ist tmps s w, Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → Z.wrel ist.world w →
      MAfter Z E base fr dt (.eff e args ret) s1 ist tmps s w (IR.Sem.step Z.c ist tmps (.eff e args ret)))

/-- An effect with a byte in `A`: `out.byte`, `drop`. -/
theorem eff_byte (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (e : Effect) (he : e = .outByte ∨ e = .drop) (o : Opd) (s0 : GS) :
    wpg (genInstr (.eff e [(1, o)] none)) E (EffPost Z E base sF dt e [(1, o)] none s0) s0 := by
  have hm : wpg (loadA o) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → Rd Z E dt 1 o → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          EffArgs e ([(1, o)].map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2) s')) s0 := by
    refine wpg_mono (loadA_ok (dt := dt) ok F o s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine ⟨hx1, fun hx hrd fr ist tmps s R hat => ?_⟩
    obtain ⟨s', st, at', R', _, hA⟩ := hl hx fr ist tmps s hrd R hat
    refine ⟨s', st, at', R', ?_⟩
    rcases he with rfl | rfl
    · show [IR.Sem.opd Z.c ist tmps 1 o] = [s'.a.toNat]
      rw [hA]
    · show [IR.Sem.opd Z.c ist tmps 1 o] = [s'.a.toNat]
      rw [hA]
  have hk : effKnown e = true := by rcases he with rfl | rfl <;> rfl
  have core := eff_core (dt := dt) ok hT F hrt hdep e hk [(1, o)] none (fun n d h => by cases h) (Rd Z E dt 1 o)
    (loadA o) s0 hm
  rcases he with rfl | rfl
  · exact wpg_mono core (fun _ s1 ⟨hx, h⟩ => ⟨hx, fun hxF hN => h hxF ⟨hN.1 o rfl, hN.2⟩⟩)
  · exact wpg_mono core (fun _ s1 ⟨hx, h⟩ => ⟨hx, fun hxF hN => h hxF ⟨hN.1 o rfl, hN.2⟩⟩)

/-- An effect without arguments: `out.end`, `input.next`, `ring.pop`. -/
theorem eff_none (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (e : Effect) (he : e = .outEnd ∨ e = .inputNext ∨ e = .ringPop)
    (ret : Option (Nat × Dst))
    (hret : ∀ n d, ret = some (n, d) → n = 2 ∧ ∀ wd vs, ∃ r, (IR.Sem.effect Z.c wd e vs).1 = some r) (s0 : GS) :
    wpg (genInstr (.eff e [] ret)) E (EffPost Z E base sF dt e [] ret s0) s0 := by
  have hm : wpg (pure () : GM Unit) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → True → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          EffArgs e (([] : List (Nat × Opd)).map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2) s')) s0 := by
    refine ⟨GExt.refl _, fun _ _ fr ist tmps s R hat => ⟨s, Steps.refl _, hat, R, ?_⟩⟩
    rcases he with rfl | rfl | rfl <;> rfl
  have hk : effKnown e = true := by rcases he with rfl | rfl | rfl <;> rfl
  have core := eff_core (dt := dt) ok hT F hrt hdep e hk [] ret hret True (pure ()) s0 hm
  have conv : wpg (do (pure () : GM Unit); call (effectRoutine e); killAll; retStore ret) E
      (EffPost Z E base sF dt e [] ret s0) s0 :=
    wpg_mono core (fun _ s1 ⟨hx, h⟩ => ⟨hx, fun hxF hN => h hxF ⟨trivial, hN.2⟩⟩)
  rcases he with rfl | rfl | rfl <;> cases ret <;> exact conv

/-- **Every covered effect.** -/
theorem eff_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (e : Effect) (args : List (Nat × Opd)) (ret : Option (Nat × Dst))
    (hcov : effCov e args ret = true) (s0 : GS) :
    wpg (genInstr (.eff e args ret)) E (EffPost Z E base sF dt e args ret s0) s0 := by
  unfold effCov at hcov
  split at hcov
  · exact eff_byte ok hT F hrt hdep _ (Or.inl rfl) _ s0
  · exact eff_byte ok hT F hrt hdep _ (Or.inr rfl) _ s0
  · exact eff_none ok hT F hrt hdep _ (Or.inl rfl) none (fun n d h => by cases h) s0
  · refine eff_none ok hT F hrt hdep _ (Or.inr (Or.inl rfl)) _ (fun n d h => ?_) s0
    subst h
    exact ⟨by simpa using hcov, fun wd vs => ⟨_, rfl⟩⟩
  · refine eff_none ok hT F hrt hdep _ (Or.inr (Or.inr rfl)) _ (fun n d h => ?_) s0
    subst h
    exact ⟨by simpa using hcov, fun wd vs => ⟨_, rfl⟩⟩
  · cases hcov

end

end Ember.Proof.Z80Gen
