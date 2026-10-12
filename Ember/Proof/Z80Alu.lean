import Ember.Proof.Z80Call

/-!
# Ember.Proof.Z80Alu — one-byte arithmetic (plan M7.3)

`add`, `sub`, `and`, `or`, `xor` of one byte are one instruction on `A`
with the second operand in a register, as an immediate or in memory
(`Codegen.alu8`); the result is the IR's `binOp` (`alu_val`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin)

/-- The code of an operation in the opcodes of the accumulator group. -/
def aluK : Bin → Option UInt8
  | .add => some 0 | .sub => some 2 | .and => some 4 | .xor => some 5 | .or => some 6
  | _ => none

/-- The instruction `alu8` emits. -/
def aluIns (op : Bin) (x : Arg) : Instr :=
  match op with
  | .add => ⟨.add, [.a, x]⟩
  | .sub => ⟨.sub, [x]⟩
  | .and => ⟨.and, [x]⟩
  | .or => ⟨.or, [x]⟩
  | _ => ⟨.xor, [x]⟩

theorem wpg_alu8 {E : GEnv} {s : GS} {op : Bin} {k : UInt8} (hk : aluK op = some k) (x : Arg)
    (Q : Unit → GS → Prop) :
    wpg (alu8 op x) E Q s ↔ Q () { s with out := s.out.push (.ins (aluIns op x)) } := by
  cases op <;> first | (cases hk; done) | exact Iff.rfl

theorem aluIns_falls (op : Bin) (x : Arg) : (aluIns op x).falls = true := by
  cases op <;> rfl

/-- **The accumulator operations are the IR's.** -/
theorem alu_val {op : Bin} {k : UInt8} (hk : aluK op = some k) (s : Cpu) (v : UInt8) :
    (s.alu k v).a.toNat = IR.binOp op 1 s.a.toNat v.toNat := by
  have ha := s.a.toNat_lt
  have hv := v.toNat_lt
  cases op <;> simp only [aluK, Option.some.injEq, reduceCtorEq] at hk <;> subst hk
  · -- add
    show ((s.a.toUInt16 + v.toUInt16 + 0).toUInt8).toNat = (s.a.toNat + v.toNat) % 2 ^ (8 * 1)
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_add, UInt8.toNat_toUInt16]
    show ((s.a.toNat + v.toNat) % 65536 + 0) % 65536 % 256 = _
    omega
  · -- sub
    show ((s.a.toUInt16 - v.toUInt16 - 0).toUInt8).toNat = (s.a.toNat + 2 ^ (8 * 1) - v.toNat) % 2 ^ (8 * 1)
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16]
    show (2 ^ 16 - 0 + (2 ^ 16 - v.toNat + s.a.toNat) % 2 ^ 16) % 2 ^ 16 % 256 = _
    omega
  · -- and
    show (s.a &&& v).toNat = (s.a.toNat &&& v.toNat) % 2 ^ (8 * 1)
    rw [UInt8.toNat_and, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)]
  · -- or
    show (s.a ||| v).toNat = (s.a.toNat ||| v.toNat) % 2 ^ (8 * 1)
    rw [UInt8.toNat_or, Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hv)]
  · -- xor
    show (s.a ^^^ v).toNat = (s.a.toNat ^^^ v.toNat) % 2 ^ (8 * 1)
    rw [UInt8.toNat_xor, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hv)]

section
variable (env : Env) (s : Cpu) (inp : UInt16 → UInt8)

theorem exec_alu_reg {op : Bin} {k : UInt8} (hk : aluK op = some k) {x : Arg} {z : UInt8} (hz : r8? x = some z) :
    exec env (aluIns op x) s inp = some (((op1 s).alu k ((op1 s).reg .hl z)).tick 4) := by
  cases op <;> simp only [aluK, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;>
    cases x <;> simp only [r8?, Option.some.injEq, reduceCtorEq] at hz <;> subst hz <;> rfl

theorem exec_alu_imm {op : Bin} {k : UInt8} (hk : aluK op = some k) (v : Nat) :
    exec env (aluIns op (n8 v)) s inp =
      some (((skip (op1 s) 1).alu k (byteOf (Int.ofNat (v % 256)))).tick 7) := by
  cases op <;> simp only [aluK, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;> rfl

theorem exec_alu_mhl {op : Bin} {k : UInt8} (hk : aluK op = some k) :
    exec env (aluIns op .mhl) s inp = some (((op1 s).alu k ((op1 s).rd (op1 s).hl)).tick 7) := by
  cases op <;> simp only [aluK, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;> rfl

end

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- The machine is running the image. -/
def Mach (Z : ZCtx) (s : Cpu) : Prop := Img Z.a 0 s ∧ s.halted = false

theorem Rel.mach {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu} (R : Rel Z E fr dt regs ist tmps s) :
    Mach Z s := ⟨R.img, R.run⟩

/-- Memory, the start of RAM, the stack pointer and `halted` are as they were. -/
def Sys (s s' : Cpu) : Prop :=
  s'.mem = s.mem ∧ s'.ramStart = s.ramStart ∧ s'.halted = s.halted ∧ s'.sp = s.sp

theorem Sys.refl (s : Cpu) : Sys s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Sys.trans {s s' s'' : Cpu} (h1 : Sys s s') (h2 : Sys s' s'') : Sys s s'' :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem Mach.sys {s s' : Cpu} (M : Mach Z s) (h : Sys s s') : Mach Z s' :=
  ⟨M.1.congr h.2.1 h.1, by rw [h.2.2.1]; exact M.2⟩

/-- One instruction that leaves memory alone, emitted and run. -/
theorem run_reg (ok : Z.OK) (F : GFinal Z base sF) {s0 s1 : GS} {i : Instr} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins i)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs (base + s0.out.size) s)
    (s' : Cpu) (hexec : ∀ ad, Z.addrs[base + s0.out.size]? = some ad → ∀ {inp}, exec (Z.a.env ad) i s inp = some s')
    (hf : i.falls = true) (hS : Sys s s') (hio : s'.io = .none := by first | rfl | simp only [zsim]) :
    Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Mach Z s' := by
  obtain ⟨h1, h2⟩ := run_ins ok F hx ho M.1 M.2 hat (fun ad had => hexec ad had) hf hio
  exact ⟨h1, h2, M.sys hS⟩

/-- The states agree when only registers changed and the tracker claims nothing of `A`. -/
theorem Rel.of_sys {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s s' : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hS : Sys s s') (ha : regs'.a = [])
    (hsub : ∀ o, o ∈ regs'.hl → o ∈ regs.hl)
    (hhl : ∀ o, o ∈ regs'.hl → Own E o → s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o)
    (hacc : ∀ n o, regs'.acc = some (n, o) → regs.acc = some (n, o)) :
    Rel Z E fr dt regs' ist tmps s' :=
  R.regs_only hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 (fun o ho => by rw [ha] at ho; cases ho) hhl
    (fun sl hsl => by rw [ha] at hsl; cases hsl) (fun sl hsl => R.inhl sl (hsub _ hsl)) hacc

/-- What `alu8Opd op a b` promises, `A` holding the first operand. -/
def AluOpd (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (op : Bin) (a b : Opd) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧ s1.regs.a = s0.regs.a ∧ (∀ o, o ∈ s1.regs.hl → o ∈ s0.regs.hl) ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt { s1.regs with a := [] } ist tmps s' ∧
        s'.a.toNat = IR.binOp op 1 (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b))

theorem opd_const (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (n v : Nat) :
    IR.Sem.opd c ist tmps n (.const v) = v % 2 ^ (8 * n) := rfl

theorem bin_beq {x y : Bin} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem binOp_lt (op : Bin) (n x y : Nat) : IR.binOp op n x y < 2 ^ (8 * n) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem alu8Opd_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (a b : Opd) (s0 : GS) : wpg (alu8Opd op a b) E (AluOpd Z E base sF dt op a b s0) s0 := by
  unfold alu8Opd
  -- an instruction on `A` alone, with the value it leaves
  have one : ∀ (i : Instr) (f : Cpu → Cpu), (∀ env s inp, exec env i s inp = some (f s)) → i.falls = true →
      (∀ s, Sys s (f s)) → (∀ s, (f s).io = .none) → (∀ s, (f s).hl = s.hl) →
      (∀ (s : Cpu) (ist : IR.Sem.St) (tmps : Array Nat),
        s.a.toNat = IR.Sem.opd Z.c ist tmps 1 a →
        (f s).a.toNat = IR.binOp op 1 (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b)) →
      AluOpd Z E base sF dt op a b s0 () { s0 with out := s0.out.push (.ins i) } := by
    intro i f hexec hfalls hsys hio hhl hval
    refine ⟨GExt.of_out (by simp) rfl rfl, rfl, fun o ho => ho, fun hx fr ist tmps s hrd R hat hA => ?_⟩
    obtain ⟨hst, hat', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat (f s) (fun ad _ => hexec _ _ _) hfalls (hsys s)
      (hio s)
    exact ⟨_, hst, hat', R.of_sys (hsys s) rfl (fun o ho => ho) (fun o ho hown => by rw [hhl]; exact R.rhl o ho hown)
      (fun n o h => h), hval s ist tmps hA⟩
  have incA : ∀ s : Cpu, (((op1 s).inc8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).inc8 ((op1 s).reg .hl 7)).1 |>.tick 4).a.toNat
      = (s.a.toNat + 1) % 256 := by
    intro s
    simp only [zsim]
    rw [UInt8.toNat_add]
    rfl
  have decA : ∀ s : Cpu, (((op1 s).dec8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).dec8 ((op1 s).reg .hl 7)).1 |>.tick 4).a.toNat
      = (s.a.toNat + 255) % 256 := by
    intro s
    simp only [zsim]
    rw [UInt8.toNat_sub]
    show (2 ^ 8 - 1 + s.a.toNat) % 2 ^ 8 = _
    omega
  -- the second operand in memory, or the first again
  have mem_case : ∀ b : Opd, (∀ v, b ≠ .const v) →
      wpg (if (a == b) = true then alu8 op .a
        else do
          let p ← addrOf b
          ins .ld [.hl, .imm p]
          alu8 op .mhl
          setRegs fun r => { r with hl := [] }) E (AluOpd Z E base sF dt op a b s0) s0 := by
    intro b hc
    by_cases hab : (a == b) = true
    · rw [if_pos hab, wpg_alu8 hk]
      have hab' : a = b := by simpa using hab
      subst hab'
      refine ⟨GExt.of_out (by simp) rfl rfl, rfl, fun o ho => ho, fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨hst, hat', _⟩ := run_reg ok F (s0 := s0) hx rfl R.mach hat
        (((op1 s).alu k ((op1 s).reg .hl 7)).tick 4) (fun ad _ => exec_alu_reg _ _ _ hk rfl) (aluIns_falls _ _)
        (by simp only [Sys, zsim, and_self])
      refine ⟨_, hst, hat', R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o ho => ho)
        (fun o ho hown => by simp only [zsim]; exact R.rhl o ho hown) (fun n o h => h), ?_⟩
      simp only [zsim]
      rw [alu_val hk]
      simp only [zsim]
      rw [hA]
    · rw [if_neg hab]
      simp only [wpg_bind]
      refine wpg_mono (addrOf_ok b s0) ?_
      intro p s1 ⟨ho1, hr1, hp, hsp, _, hj1, hl1⟩
      subst hp
      simp only [wpg_ins, wpg_alu8 hk, wpg_setRegs]
      refine ⟨GExt.of_out (by simp [ho1]) hj1 hl1, (by show s1.regs.a = s0.regs.a; rw [hr1]),
        (fun o ho => by cases ho), fun hx fr ist tmps s hrd R hat hA => ?_⟩
      obtain ⟨ad, had, hpc⟩ := hat
      obtain ⟨hv, hb⟩ := opd_val ok hrd hsp hc ad
      have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩).toNat = opdAddr Z E b :=
        immW_toNat _ _ _ _ rfl hv (by omega)
      -- `ld hl,nn`
      obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s1)
        (s1 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (((GExt.push _ _).trans (GExt.regs _ _)).trans hx) rfl R.mach (by rw [ho1]; exact ⟨ad, had, hpc⟩)
        (((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).tick 10)
        (fun ad' had' => by
          rw [ho1, had] at had'
          cases had'
          intro _
          rfl) rfl (by simp only [Sys, zsim, and_self])
      -- the operation, with `(hl)`
      obtain ⟨st2, at2, _⟩ := run_reg ok F
        (s0 := { s1 with out := s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩) })
        (s1 := { s1 with out := (s1.out.push (.ins ⟨.ld, [.hl, .imm (opdVal E b)]⟩)).push (.ins (aluIns op .mhl)) })
        ((GExt.regs _ _).trans hx) rfl M1 at1 _ (fun ad' _ => exec_alu_mhl _ _ _ hk) (aluIns_falls _ _)
        (by simp only [Sys, zsim, and_self])
      refine ⟨_, st1.trans st2, at2, R.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o ho => by cases ho)
        (fun o ho => by cases ho) (fun n o h => by rw [← hr1]; exact h), ?_⟩
      simp only [zsim]
      rw [alu_val hk]
      simp only [zsim]
      rw [hA]
      congr 1
      show (s.mem.get! _).toNat = _
      rw [hnn, ← rd_one _ _ (by omega)]
      exact opd_mem hrd hsp hc R
  cases b with
  | const v =>
    simp only []
    by_cases h1 : (op == .add && v % 256 == 1) = true
    · simp only [h1, if_true, wpg_ins]
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨hop, hv⟩ := h1
      obtain rfl := bin_beq hop
      refine one _ (fun s => ((op1 s).inc8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).inc8 ((op1 s).reg .hl 7)).1 |>.tick 4)
        (fun _ _ _ => rfl) rfl (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
        (fun s ist tmps hA => ?_)
      rw [incA, opd_const, ← hA]
      show _ = (s.a.toNat + v % 2 ^ (8 * 1)) % 2 ^ (8 * 1)
      rw [show v % 2 ^ (8 * 1) = 1 from hv]
      try omega
    · simp only [h1, Bool.false_eq_true, if_false]
      by_cases h2 : (op == .sub && v % 256 == 1) = true
      · simp only [h2, if_true, wpg_ins]
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        obtain ⟨hop, hv⟩ := h2
        obtain rfl := bin_beq hop
        refine one _ (fun s => ((op1 s).dec8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).dec8 ((op1 s).reg .hl 7)).1 |>.tick 4)
          (fun _ _ _ => rfl) rfl (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
          (fun s ist tmps hA => ?_)
        rw [decA, opd_const, ← hA]
        show _ = (s.a.toNat + 2 ^ (8 * 1) - v % 2 ^ (8 * 1)) % 2 ^ (8 * 1)
        rw [show v % 2 ^ (8 * 1) = 1 from hv]
        try omega
      · simp only [h2, Bool.false_eq_true, if_false]
        by_cases h3 : (op == .add && v % 256 == 255) = true
        · simp only [h3, if_true, wpg_ins]
          simp only [Bool.and_eq_true, beq_iff_eq] at h3
          obtain ⟨hop, hv⟩ := h3
          obtain rfl := bin_beq hop
          refine one _ (fun s => ((op1 s).dec8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).dec8 ((op1 s).reg .hl 7)).1 |>.tick 4)
            (fun _ _ _ => rfl) rfl (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
            (fun s ist tmps hA => ?_)
          rw [decA, opd_const, ← hA]
          show _ = (s.a.toNat + v % 2 ^ (8 * 1)) % 2 ^ (8 * 1)
          rw [show v % 2 ^ (8 * 1) = 255 from hv]
          try omega
        · simp only [h3, Bool.false_eq_true, if_false]
          by_cases h4 : (op == .sub && v % 256 == 255) = true
          · simp only [h4, if_true, wpg_ins]
            simp only [Bool.and_eq_true, beq_iff_eq] at h4
            obtain ⟨hop, hv⟩ := h4
            obtain rfl := bin_beq hop
            refine one _ (fun s => ((op1 s).inc8 ((op1 s).reg .hl 7)).2.setReg .hl 7 ((op1 s).inc8 ((op1 s).reg .hl 7)).1 |>.tick 4)
              (fun _ _ _ => rfl) rfl (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim]) (fun s => by simp only [zsim])
              (fun s ist tmps hA => ?_)
            rw [incA, opd_const, ← hA]
            show _ = (s.a.toNat + 2 ^ (8 * 1) - v % 2 ^ (8 * 1)) % 2 ^ (8 * 1)
            rw [show v % 2 ^ (8 * 1) = 255 from hv]
            try omega
          · simp only [h4, Bool.false_eq_true, if_false]
            rw [wpg_alu8 hk]
            refine one _ (fun s => ((skip (op1 s) 1).alu k (byteOf (Int.ofNat (v % 256 % 256)))).tick 7)
              (fun _ _ _ => exec_alu_imm _ _ _ hk _) (aluIns_falls _ _) (fun s => by simp only [Sys, zsim, and_self]) (fun s => by simp only [zsim])
              (fun s => by simp only [zsim]) (fun s ist tmps hA => ?_)
            simp only [zsim]
            rw [alu_val hk, opd_const, ← hA, byteOf_toNat]
            simp only [zsim]
            have : (Int.ofNat (v % 256 % 256) % 256).toNat = v % 2 ^ (8 * 1) := by
              show (((v % 256 % 256 : Nat) : Int) % 256).toNat = v % 256
              omega
            rw [this]
  | slot sl => exact mem_case (.slot sl) (fun v h => by cases h)
  | tmp t => exact mem_case (.tmp t) (fun v h => by cases h)

/-- Two states that agree with the IR have the same start of RAM, and both run. -/
theorem Rel.sys_of {regs regs' : Regs} {ist ist' : IR.Sem.St} {tmps tmps' : Array Nat} {dt' : Nat → Prop}
    {s s' : Cpu} (R : Rel Z E fr dt regs ist tmps s) (R' : Rel Z E fr dt' regs' ist' tmps' s')
    (hm : s'.mem = s.mem) : Sys s s' :=
  ⟨hm, UInt16.toNat_inj.mp (by rw [R.rs, R'.rs]), by rw [R.run, R'.run], by rw [R.sp, R'.sp]⟩

/-- What the one-byte operations in `A` promise, before the tracker forgets `A`. -/
def Bin8A (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (op : Bin) (a b : Opd) (s0 : GS)
    (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧ (∀ o, o ∈ s1.regs.hl → o ∈ s0.regs.hl) ∧
    (GExt s1 sF → ∀ fr ist tmps s, Rd Z E dt 1 a → Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧
        Rel Z E fr dt { s1.regs with a := [] } ist tmps s' ∧
        s'.a.toNat = IR.binOp op 1 (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b))

theorem bin8Alu_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (a b : Opd) (s0 : GS) : wpg (bin8Alu op a b) E (Bin8A Z E base sF dt op a b s0) s0 := by
  unfold bin8Alu
  simp only [wpg_bind, wpg_get]
  by_cases hat : (s0.regs.a.contains b && a != b) = true
  · simp only [hat, if_true, wpg_bind, wpg_ins, wpg_setRegs]
    have hbmem : b ∈ s0.regs.a := by
      simp only [Bool.and_eq_true] at hat
      simpa using hat.1
    refine wpg_mono (loadA_ok (dt := dt) ok F a _) ?_
    intro _ s1 ⟨hx1, hhl1, _, hl⟩
    rw [wpg_alu8 hk]
    refine ⟨((GExt.push _ _).trans (GExt.regs _ _)).trans (hx1.trans (GExt.push _ _)),
      fun o ho => by rw [hhl1] at ho; exact ho, fun hx fr ist tmps s hra hrb R hat0 => ?_⟩
    -- `ld c,a`: the second operand, which is at hand
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0)
      (s1 := { s0 with out := s0.out.push (.ins ⟨.ld, [.c, .a]⟩) })
      (((GExt.regs _ _).trans (hx1.trans (GExt.push _ _))).trans hx) rfl R.mach hat0
      (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4) (fun ad _ => rfl) rfl (by simp only [Sys, zsim, and_self])
    have hS1 : Sys s (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4) := by simp only [Sys, zsim, and_self]
    have hc : (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4).c.toNat = IR.Sem.opd Z.c ist tmps 1 b := by
      simp only [zsim]
      exact R.ra b hbmem hrb.own
    have R1 : Rel Z E fr dt { s0.regs with a := [] } ist tmps (((op1 s).setReg .hl 1 ((op1 s).reg .hl 7)).tick 4) :=
      R.of_sys hS1 rfl (fun o ho => ho) (fun o ho hown => by simp only [zsim]; exact R.rhl o ho hown) (fun n o h => h)
    -- the first operand into `A`
    obtain ⟨s2, st2, at2, R2, hk2, hA2⟩ := hl ((GExt.push _ _).trans hx) fr ist tmps _ hra R1 at1
    have hS2 := R1.sys_of R2 hk2.2.2.2.2.2.2.2
    -- the operation, with `c`
    obtain ⟨st3, at3, _⟩ := run_reg ok F (s0 := s1) hx rfl R2.mach at2
      (((op1 s2).alu k ((op1 s2).reg .hl 1)).tick 4) (fun ad _ => exec_alu_reg _ _ _ hk rfl) (aluIns_falls _ _)
      (by simp only [Sys, zsim, and_self])
    refine ⟨_, (st1.trans st2).trans st3, at3, R2.of_sys (by simp only [Sys, zsim, and_self]) rfl (fun o ho => ho)
      (fun o ho hown => by simp only [zsim]; exact R2.rhl o ho hown) (fun n o h => h), ?_⟩
    simp only [zsim]
    rw [alu_val hk]
    simp only [zsim]
    rw [hA2, hk2.2.1, hc]
  · simp only [hat, Bool.false_eq_true, if_false, wpg_bind]
    refine wpg_mono (loadA_ok (dt := dt) ok F a s0) ?_
    intro _ s1 ⟨hx1, hhl1, _, hl⟩
    refine wpg_mono (alu8Opd_ok (dt := dt) ok F hk a b s1) ?_
    intro _ s2 ⟨hx2, _, hhl2, hop⟩
    refine ⟨hx1.trans hx2, fun o ho => by rw [← hhl1]; exact hhl2 o ho, fun hx fr ist tmps s hra hrb R hat0 => ?_⟩
    obtain ⟨s1', st1, at1, R1, hk1, hA1⟩ := hl (hx2.trans hx) fr ist tmps s hra R hat0
    obtain ⟨s2', st2, at2, R2, hA2⟩ := hop hx fr ist tmps s1' hrb R1 at1 hA1
    exact ⟨s2', st1.trans st2, at2, R2, hA2⟩

/-- What a one-byte operation promises: the result in `A`. -/
def Bin8 (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (dt : Nat → Prop) (op : Bin) (a b : Opd) (H : Prop)
    (s0 : GS) (_ : Unit) (s1 : GS) : Prop :=
  GExt s0 s1 ∧
    (GExt s1 sF → H → ∀ fr ist tmps s, Rd Z E dt 1 a → Rd Z E dt 1 b → Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s →
      ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
        s'.a.toNat = IR.binOp op 1 (IR.Sem.opd Z.c ist tmps 1 a) (IR.Sem.opd Z.c ist tmps 1 b))

theorem bin8_alu (op : Bin) {k : UInt8} (hk : aluK op = some k) (a b : Opd) :
    bin8 op a b = (do bin8Alu op a b; setRegs fun r => { r with a := [] }) := by
  cases op <;> first | (cases hk; done) | rfl

theorem bin8_alu_ok (ok : Z.OK) (F : GFinal Z base sF) {op : Bin} {k : UInt8} (hk : aluK op = some k)
    (a b : Opd) (s0 : GS) : wpg (bin8 op a b) E (Bin8 Z E base sF dt op a b True s0) s0 := by
  rw [bin8_alu op hk, wpg_bind]
  refine wpg_mono (bin8Alu_ok (dt := dt) ok F hk a b s0) ?_
  intro _ s1 ⟨hx1, hsub, h⟩
  rw [wpg_setRegs]
  refine ⟨hx1.trans (GExt.regs _ _), fun hx _ fr ist tmps s hra hrb R hat0 => ?_⟩
  obtain ⟨s', st, at', R', hA⟩ := h ((GExt.regs _ _).trans hx) fr ist tmps s hra hrb R hat0
  exact ⟨s', st, at', R', hA⟩

/-- The code of a one-byte `add`, `sub`, `and`, `or` or `xor` does what the IR's instruction does. -/
theorem bin1_alu_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {op : Bin} {k : UInt8}
    (hk : aluK op = some k) (d : Dst) (a b : Opd) (s0 : GS) :
    wpg (genInstr (.bin op 1 d a b)) E
      (InsPost Z E base sF dt (dtAfter dt d) (.bin op 1 d a b)
        (Rd Z E dt 1 a ∧ Rd Z E dt 1 b ∧ Wr Z E 1 d) s0) s0 := by
  simp only [genInstr, genBin, store, wpg_bind, beq_self_eq_true, if_true]
  refine wpg_mono (bin8_alu_ok (dt := dt) ok F hk a b s0) ?_
  intro _ s1 ⟨hx1, h⟩
  refine wpg_mono (storeA_ok (dt := dt) ok hT F d s1) ?_
  intro _ s2 ⟨hx2, _, _, hs⟩
  refine ⟨hx1.trans hx2, fun hxF ⟨hra, hrb, hwr⟩ fr ist tmps s R hat => ?_⟩
  obtain ⟨s', st1, at1, R1, hA⟩ := h (hx2.trans hxF) trivial fr ist tmps s hra hrb R hat
  obtain ⟨s'', st2, at2, R2, _⟩ := hs hxF fr ist tmps s' _ hwr R1 at1 (by
    rw [hA, Nat.mod_eq_of_lt (binOp_lt _ 1 _ _)])
  exact ⟨s'', st1.trans st2, at2, R2⟩

end

end Ember.Proof.Z80Gen
