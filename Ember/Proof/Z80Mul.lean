import Ember.Proof.Z80Alu

/-!
# Ember.Proof.Z80Mul — one-byte `mul`, `div`, `mod` (plan M7.3)

These are routines of the runtime: `A := A op E`.  `RtOK` is what the
proofs take of the runtime — one specification per routine, of the kind
`ember-z80 rt-check` tests.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin)

/-- `rt_bound`: returns with the registers as they were when `HL < BC`;
if not, the CPU gets to `rt_trap`. -/
def RtBound (Z : ZCtx) : Prop :=
  ∃ entry, Z.sym "rt_bound" entry ∧ entry < 65536 ∧
    ∀ c : Cpu, c.pc.toNat = entry → Img Z.a 0 c → c.halted = false → c.ramStart.toNat = Z.ramStart →
      c.mem.size = 65536 → Z.stackLo + Z.rtK ≤ c.sp.toNat → c.sp.toNat + 2 ≤ Z.stackHi →
      ∃ s', Steps c s' ∧ s'.halted = false ∧ s'.ramStart = c.ramStart ∧ s'.mem.size = 65536 ∧
        FreeStack Z c s' ∧ s'.a = c.a ∧ s'.de = c.de ∧
        (if c.hl.toNat < c.bc.toNat then s'.pc = c.rd16 c.sp ∧ s'.sp = c.sp + 2 ∧ s'.hl = c.hl
         else ∃ j : Nat, Z.items[j]? = some (Item.label "rt_trap") ∧ At Z.addrs j s')

/-- The effects whose routines are specified so far. -/
def effKnown : Ember.Lang.Effect → Bool
  | .inputNext | .ringPop | .outByte | .outEnd | .drop | .note => true
  | _ => false

/-- The arguments of an effect, where its routine finds them: a byte in
`A`, and for a note its value in the accumulator. -/
def EffArgs (Z : ZCtx) (e : Ember.Lang.Effect) (vs : List Nat) (c : Cpu) : Prop :=
  match e with
  | .outByte | .drop => vs = [c.a.toNat]
  | .note => vs = [c.a.toNat, IR.Sem.rd c.mem Z.acc 4]
  | _ => vs = []

/-- **The routine of an effect**: it returns, having done to the machine
what the effect does to the world; the result in `HL`. -/
def RtEff (Z : ZCtx) (e : Ember.Lang.Effect) : Prop :=
  ∃ entry, Z.sym (effectRoutine e) entry ∧ entry < 65536 ∧
    ∀ (c : Cpu) (w : Z.W) (wd : Ember.Lang.World) (vs : List Nat), c.pc.toNat = entry → Img Z.a 0 c →
      c.halted = false → c.ramStart.toNat = Z.ramStart → c.mem.size = 65536 → Z.stackLo + Z.rtK ≤ c.sp.toNat →
      c.sp.toNat + 2 ≤ Z.stackHi → Z.wrel wd w → EffArgs Z e vs c →
      ∃ c' w', WSteps Z (c, w) (c', w') ∧ c'.pc = c.rd16 c.sp ∧ c'.sp = c.sp + 2 ∧ c'.halted = false ∧
        c'.ramStart = c.ramStart ∧ c'.mem.size = 65536 ∧ FreeStack Z c c' ∧
        Z.wrel (IR.Sem.effect Z.c wd e vs).2 w' ∧ ∀ r, (IR.Sem.effect Z.c wd e vs).1 = some r → c'.hl.toNat = r

/-- The routines on values of `n` bytes in the accumulator. -/
structure RtW (Z : ZCtx) (n : Nat) : Prop where
  /-- accumulator := the `n` bytes at `HL` -/
  ld : RtAcc Z s!"rt_ld{bits n}" (fun _ => True)
    (fun s s' => IR.Sem.rd s'.mem Z.acc n = IR.Sem.rd s.mem s.hl.toNat n)
  /-- the `n` bytes at `HL` (in RAM) := accumulator -/
  st : ∃ entry, Z.sym s!"rt_st{bits n}" entry ∧ entry < 65536 ∧
    Routine Z entry Z.rtK (fun s => Z.ramStart ≤ s.hl.toNat ∧ s.hl.toNat + n ≤ 65536)
      (fun s s' => ∀ x, x < Z.stackLo ∨ s.sp.toNat ≤ x → ¬ Z.rt x →
        s'.mem.get! x = (IR.Sem.wr s.mem s.hl.toNat n (IR.Sem.rd s.mem Z.acc n)).get! x)
  /-- accumulator := accumulator `op` the `n` bytes at `HL` -/
  bin : ∀ op, RtAcc Z (routineW op n) (fun _ => True)
    (fun s s' => IR.Sem.rd s'.mem Z.acc n = IR.binOp op n (IR.Sem.rd s.mem Z.acc n) (IR.Sem.rd s.mem s.hl.toNat n))
  /-- the flags of accumulator − the `n` bytes at `HL` -/
  cmp : RtPure Z s!"rt_cmp{bits n}"
    (fun s s' => s'.flag FZ = (IR.Sem.rd s.mem Z.acc n == IR.Sem.rd s.mem s.hl.toNat n) ∧
      s'.flag FC = decide (IR.Sem.rd s.mem Z.acc n < IR.Sem.rd s.mem s.hl.toNat n))

/-- **What is taken of the runtime.** -/
structure RtOK (Z : ZCtx) : Prop where
  bound : RtBound Z
  wide : RtW Z 4
  /-- accumulator := `A`, := `HL`, zero-extended to its eight bytes -/
  accA : RtAcc Z "rt_acc_a" (fun _ => True) (fun s s' => IR.Sem.rd s'.mem Z.acc 8 = s.a.toNat)
  accHL : RtAcc Z "rt_acc_hl" (fun _ => True) (fun s s' => IR.Sem.rd s'.mem Z.acc 8 = s.hl.toNat)
  eff : ∀ e, effKnown e = true → RtEff Z e
  shl8 : RtPure Z "rt_shl8" (fun s s' => s'.a.toNat = s.a.toNat * 2 ^ s.b.toNat % 256 ∧ s'.hl = s.hl)
  shr8 : RtPure Z "rt_shr8" (fun s s' => s'.a.toNat = s.a.toNat / 2 ^ s.b.toNat ∧ s'.hl = s.hl)
  shl16 : RtPure Z "rt_shl16" (fun s s' => s'.hl.toNat = s.hl.toNat * 2 ^ s.b.toNat % 65536 ∧ s'.a = s.a)
  shr16 : RtPure Z "rt_shr16" (fun s s' => s'.hl.toNat = s.hl.toNat / 2 ^ s.b.toNat ∧ s'.a = s.a)
  mul8 : RtPure Z "rt_mul8" (fun s s' => s'.a.toNat = s.a.toNat * s.e.toNat % 256 ∧ s'.hl = s.hl)
  div8 : RtPure Z "rt_div8"
    (fun s s' => s'.a.toNat = (if s.e.toNat = 0 then 0 else s.a.toNat / s.e.toNat) ∧ s'.hl = s.hl)
  mod8 : RtPure Z "rt_mod8"
    (fun s s' => s'.a.toNat = (if s.e.toNat = 0 then 0 else s.a.toNat % s.e.toNat) ∧ s'.hl = s.hl)
  not16 : RtPure Z "rt_not16" (fun s s' => s'.hl.toNat = 65535 - s.hl.toNat)
  neg16 : RtPure Z "rt_neg16" (fun s s' => s'.hl.toNat = (65536 - s.hl.toNat) % 65536)
  mul16 : RtPure Z "rt_mul16" (fun s s' => s'.hl.toNat = s.hl.toNat * s.de.toNat % 65536)
  div16 : RtPure Z "rt_div16"
    (fun s s' => s'.hl.toNat = (if s.de.toNat = 0 then 0 else s.hl.toNat / s.de.toNat))
  mod16 : RtPure Z "rt_mod16"
    (fun s s' => s'.hl.toNat = (if s.de.toNat = 0 then 0 else s.hl.toNat % s.de.toNat))

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- The states agree when `A` and `HL` are as they were. -/
theorem Rel.keep {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s s' : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hS : Sys s s') (ha : s'.a = s.a) (hhl : s'.hl = s.hl) :
    Rel Z E fr dt regs ist tmps s' :=
  R.regs_only hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 (fun o ho hown => by rw [ha]; exact R.ra o ho hown)
    (fun o ho hown => by rw [hhl]; exact R.rhl o ho hown) R.ina R.inhl (fun n o h => h)

/-- What `loadE a b` promises, `A` holding `a`: `b` in `E`. -/
def LoadE (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (a b : Opd) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.a = s0.regs.a ∧ (∀ o, o ∈ s1.regs.hl → o ∈ s0.regs.hl) ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.a = s.a ∧ s'.e.toNat = IR.Sem.opd Z.c ist tmps 1 b)

theorem loadE_ok (ok : Z.OK) (F : GFinal Z base sF) (a b : Opd) (s0 : GS) :
    wpg (loadE a b) E (LoadE Z E base sF dt a b s0) s0 := by
  unfold loadE
  -- one instruction that sets `E`
  have one : ∀ (b : Opd) (i : Instr) (f : Cpu → Cpu), (∀ env s inp, exec env i s inp = some (f s)) → i.falls = true →
      (∀ s, Sys s (f s)) → (∀ s, (f s).io = .none) → (∀ s, (f s).hl = s.hl) → (∀ s, (f s).a = s.a) →
      (∀ (s : Cpu) (ist : IR.Sem.St) (tmps : Array Nat), s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
        (f s).e.toNat = IR.Sem.opd Z.c ist tmps 1 b) →
      LoadE Z E base sF dt a b s0 () { s0 with out := s0.out.push (.ins i) } := by
    intro b i f hexec hfalls hsys hio hhl ha hval
    refine ⟨GExt.of_out (by simp) rfl rfl, rfl, fun o ho => ho, fun hx fr ist tmps s hrd R hat hA => ?_⟩
    obtain ⟨hst, hat', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (f s) (fun ad _ => hexec _ _ _) hfalls (hsys s)
      (hio s)
    exact ⟨_, hst, hat', R.keep (hsys s) (ha s) (hhl s), ha s, hval s ist tmps hA⟩
  have mem_case : ∀ b : Opd, (∀ v, b ≠ .const v) →
      wpg (if (a == b) = true then ins .ld [.e, .a]
        else do
          let p ← addrOf b
          ins .ld [.hl, .imm p]
          ins .ld [.e, .mhl]
          setRegs fun r => { r with hl := [] }) E (LoadE Z E base sF dt a b s0) s0 := by
    intro b hc
    by_cases hab : (a == b) = true
    · rw [if_pos hab, wpg_ins]
      have hab' : a = b := by simpa using hab
      subst hab'
      refine one _ ⟨.ld, [.e, .a]⟩ (fun s => ((op1 s).setReg .hl 3 ((op1 s).reg .hl 7)).tick 4) (fun _ _ _ => rfl) rfl
        (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
        (fun s ist tmps hA => by simp only [zsim]; exact hA)
    · rw [if_neg hab]
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok b s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1⟩
      subst hp
      simp only [wpg_ins, wpg_setRegs]
      refine ⟨GExt.of_out (by simp [ho1]) hj1 hl1, (by show s1.regs.a = s0.regs.a; rw [hr1]),
        (fun o ho => by cases ho), fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩).toNat = opdAddr Z E b :=
        immW_toNat _ _ _ _ rfl hv (by omega)
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1)
        (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (((GExt.push _ _).trans (GExt.regs _ _)).trans hx) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩)
        (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          intro _
          rfl) rfl (by simp only [Sys, zsim, and_self])
      obtain ⟨st2, at2, _⟩ := run_reg ok F
        (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (s1 := { s1 with out := (s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).push (.ins ⟨.ld, [.e, .mhl]⟩) })
        ((GExt.regs _ _).trans hx) rfl M1 at1
        (((op1 (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)).setReg .hl 3
          ((op1 (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)).rd
            (op1 (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)).hl)).tick 7)
        (fun ad' _ => rfl) rfl (by simp only [Sys, zsim, and_self])
      refine ⟨_, st1.trans st2, at2, ?_, by simp only [zsim], ?_⟩
      · refine R.regs_only (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim]) (by simp only [zsim])
          (fun o ho hown => ?_) (fun o ho => by cases ho) (fun sl hsl => R.ina sl (by rw [← hr1]; exact hsl))
          (fun sl hsl => by cases hsl) (fun n o h => by rw [← hr1]; exact h)
        simp only [zsim]
        exact R.ra o (by rw [← hr1]; exact ho) hown
      · simp only [zsim]
        show (s.mem.get! _).toNat = _
        rw [hnn, ← rd_one _ _ (by omega)]
        exact opd_mem hrd hsp hc R
  cases b with
  | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
  | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)
  | const v =>
    simp only [wpg_ins]
    refine one _ ⟨.ld, [.e, n8 v]⟩ (fun s => ((skip (op1 s) 1).setReg .hl 3 (byteOf (Int.ofNat (v % 256)))).tick 7)
      (fun _ _ _ => rfl) rfl (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
      (fun s => by simp only [zsim]) (fun s ist tmps _ => ?_)
    simp only [zsim]
    rw [byteOf_toNat, opd_const]
    show (((v % 256 : Nat) : Int) % 256).toNat = v % 256
    omega

theorem RtPure.mono {name : String} {rel rel' : Cpu → Cpu → Prop} (h : RtPure Z name rel)
    (hm : ∀ s s', rel s s' → rel' s s') : RtPure Z name rel' := by
  obtain ⟨entry, h1, h2, hR⟩ := h
  refine ⟨entry, h1, h2, fun s a1 a2 a3 a4 a5 a6 a7 a8 => ?_⟩
  obtain ⟨s', b1, b2, b3, b4, b5, b6, b7, b8⟩ := hR s a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨s', b1, b2, b3, b4, b5, b6, hm _ _ b7, b8⟩

/-- The routine of a one-byte `mul`, `div` or `mod`. -/
def rt8name (op : Bin) : String :=
  match op with
  | .mul => "rt_mul8" | .div => "rt_div8" | _ => "rt_mod8"

theorem rt8 (hrt : RtOK Z) {op : Bin} (hop : aluK op = none) :
    RtPure Z (rt8name op) (fun s s' => s'.a.toNat = IR.binOp op 1 s.a.toNat s.e.toNat ∧ s'.hl = s.hl) := by
  cases op <;> first | (cases hop; done) | skip
  · refine hrt.mul8.mono (fun s s' ⟨h1, h2⟩ => ⟨?_, h2⟩)
    rw [h1]
    rfl
  · refine hrt.div8.mono (fun s s' ⟨h1, h2⟩ => ⟨?_, h2⟩)
    rw [h1]
    have ha := s.a.toNat_lt
    show _ = (if (s.e.toNat == 0) = true then 0 else s.a.toNat / s.e.toNat) % 2 ^ (8 * 1)
    by_cases he : s.e.toNat = 0
    · simp [he]
    · have : s.a.toNat / s.e.toNat ≤ s.a.toNat := Nat.div_le_self _ _
      simp only [he, if_false, beq_iff_eq]
      exact (Nat.mod_eq_of_lt (by omega : s.a.toNat / s.e.toNat < 2 ^ (8 * 1))).symm
  · refine hrt.mod8.mono (fun s s' ⟨h1, h2⟩ => ⟨?_, h2⟩)
    rw [h1]
    have ha := s.a.toNat_lt
    show _ = (if (s.e.toNat == 0) = true then 0 else s.a.toNat % s.e.toNat) % 2 ^ (8 * 1)
    by_cases he : s.e.toNat = 0
    · simp [he]
    · have : s.a.toNat % s.e.toNat ≤ s.a.toNat := Nat.mod_le _ _
      simp only [he, if_false, beq_iff_eq]
      exact (Nat.mod_eq_of_lt (by omega : s.a.toNat % s.e.toNat < 2 ^ (8 * 1))).symm

theorem hl_congr {s s' : Cpu} (h : s'.h = s.h) (l : s'.l = s.l) : s'.hl = s.hl := by
  simp only [Cpu.hl, h, l]

theorem bin8Rt_call (op : Bin) (a b : Opd) :
    bin8Rt op a b = (do
      let r := (← get).regs
      if r.a.contains b && a != b then do
        ins .ld [.e, .a]
        loadA a
      else do
        loadA a
        loadE a b
      call (rt8name op)) := rfl

theorem bin8Rt_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {op : Bin} (hop : aluK op = none)
    (a b : Opd) (s0 : GS) :
    wpg (do bin8Rt op a b; setRegs fun r => { r with a := [] }) E
      (Bin8 Z E base sF dt op a b (RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s0 := by
  rw [bin8Rt_call]
  -- the call, from a state with the operands in `A` and `E`
  have fin : ∀ (s1 : GS), GExt s0 s1 → ∀ (pre : GS → Prop),
      (∀ s2, GExt s2 sF → pre s2 → ∀ fr ist tmps s, Rd Z E dt 1 a → Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 a ∧ s'.e.toNat = IR.Sem.opd Z.c ist tmps 1 b) →
      (∀ s2, GExt s1 s2 → pre s2) →
      wpg (do call (rt8name op); setRegs fun r => { r with a := [] }) E
        (Bin8 Z E base sF dt op a b (RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s1 := by
    intro s1 hx1 pre hpre hmono
    simp only [wpg_bind, wpg_call, wpg_setRegs]
    refine ⟨hx1.trans ((GExt.push _ _).trans (GExt.regs _ _)), fun hx ⟨hrt, hdep⟩ fr ist tmps s hra hrb R hat0 => ?_⟩
    obtain ⟨s2, st2, at2, R2, hA, hE⟩ := hpre _ hx (hmono _ ((GExt.push _ _).trans (GExt.regs _ _))) fr ist tmps s hra hrb R hat0
    obtain ⟨c1, s', cs, st3, at3, ⟨hval, hhl⟩, hRel⟩ := rt_call ok hT F (s0 := s1)
      (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (rt8name op))]⟩) })
      ((GExt.regs _ _).trans hx) rfl (rt8 hrt hop) hdep R2 at2
    refine ⟨s', st2.trans st3, at3, hRel _ (fun o ho => by cases ho) (fun o ho hown => ?_)
      (fun sl hsl => by cases hsl) (fun sl hsl => R2.inhl sl hsl) (fun n o h => h), ?_⟩
    · rw [hhl, hl_congr cs.h cs.l]
      exact R2.rhl o ho hown
    · rw [hval, cs.a, cs.e, hA, hE]
  simp only [wpg_bind, wpg_get]
  by_cases hat : (s0.regs.a.contains b && a != b) = true
  · simp only [hat, if_true, wpg_bind, wpg_ins]
    have hbmem : b ∈ s0.regs.a := by
      simp only [Bool.and_eq_true] at hat
      simpa using hat.1
    refine wpg_mono (loadA_ok (dt := dt) ok F a _) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine fin s1 ((GExt.push _ _).trans hx1) (fun s2 => GExt s1 s2) (fun s2 hx2 hp fr ist tmps s hra hrb R hat0 => ?_)
      (fun s2 h => h)
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.e, .a]⟩) })
      ((hx1.trans hp).trans hx2) rfl R.mach hat0
      (((op1 s).setReg .hl 3 ((op1 s).reg .hl 7)).tick 4) (fun ad _ => rfl) rfl (by simp only [Sys, zsim, and_self])
    have R1 : Rel Z E fr dt s0.regs ist tmps (((op1 s).setReg .hl 3 ((op1 s).reg .hl 7)).tick 4) :=
      R.keep (by simp only [Sys, zsim, and_self]) (by simp only [zsim]) (by simp only [zsim])
    obtain ⟨s2', st2, at2, R2, hk2, hA2⟩ := hl (hp.trans hx2) fr ist tmps _ hra R1 at1
    refine ⟨s2', st1.trans st2, at2, R2, hA2, ?_⟩
    rw [hk2.2.2.2.1]
    simp only [zsim]
    exact R.ra b hbmem hrb.own
  · simp only [hat, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, _, _, hl⟩
    refine wpg_mono (loadE_ok (dt := dt) ok F a b s1) ?_
    intro _ s2 ⟨hx2, _, _, he⟩
    refine fin s2 (hx1.trans hx2) (fun s3 => GExt s2 s3) (fun s3 hx3 hp fr ist tmps s hra hrb R hat0 => ?_)
      (fun s3 h => h)
    obtain ⟨s1', st1, at1, R1, _, hA1⟩ := hl (hx2.trans (hp.trans hx3)) fr ist tmps s hra R hat0
    obtain ⟨s2', st2, at2, R2, ha2, hE2⟩ := he (hp.trans hx3) fr ist tmps s1' hrb R1 at1 hA1
    exact ⟨s2', st1.trans st2, at2, R2, by rw [ha2, hA1], hE2⟩

theorem bin8_rt (op : Bin) (hop : aluK op = none) (a b : Opd) :
    bin8 op a b = (do bin8Rt op a b; setRegs fun r => { r with a := [] }) := by
  cases op <;> first | (cases hop; done) | rfl

/-- **The code of a one-byte `bin` does what the IR's instruction does.** -/
theorem bin1_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (op : Bin) (d : Dst) (a b : Opd) (s0 : GS) :
    wpg (genInstr (.bin op 1 d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.bin op 1 d a b)
        (Rd Z E dt 1 a ∧ Rd Z E dt 1 b ∧ Wr Z E 1 d ∧ RtOK Z ∧ Z.rtK + 2 ≤ Z.depth E.fn.name) s0) s0 := by
  cases hk : aluK op with
  | some k =>
    refine wpg_mono (bin1_alu_ok (dt := dt) ok hT F hk d a b s0) ?_
    intro _ s1 ⟨hx, h⟩
    exact ⟨hx, fun hxF ⟨h1, h2, h3, _⟩ => h hxF ⟨h1, h2, h3⟩⟩
  | none =>
    simp only [genInstr, genBin, store, wpg_bind, beq_self_eq_true, if_true]
    rw [bin8_rt op hk]
    refine wpg_mono (bin8Rt_ok (dt := dt) ok hT F hk a b s0) ?_
    intro _ s1 ⟨hx1, h⟩
    refine wpg_mono (storeA_ok (dt := dt) ok hT F d s1) ?_
    intro _ s2 ⟨hx2, _, _, hs⟩
    refine ⟨hx1.trans hx2, fun hxF ⟨hra, hrb, hwr, hrt, hdep⟩ fr ist tmps s R hat => ?_⟩
    obtain ⟨s', st1, at1, R1, hA⟩ := h (hx2.trans hxF) ⟨hrt, hdep⟩ fr ist tmps s hra hrb R hat
    obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' _ hwr R1 at1 (by
      rw [hA, Nat.mod_eq_of_lt (binOp_lt _ 1 _ _)])
    exact ⟨s'', st1.trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
