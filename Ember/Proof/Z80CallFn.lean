import Ember.Proof.Z80Ret
import Ember.Proof.Z80Call

/-!
# Ember.Proof.Z80CallFn — a call of a function of the program (plan M7.3)

* `Entry`: the CPU is at a function's entry, the shared bytes as in the
  IR's state, the argument that travels in a register in `A` or `HL`;
* `Outcome`: what the function then does, for the result the IR's
  semantics gives — it returns (`RetSt`), or the CPU gets to `rt_trap`;
* `Callee`: the function called has that outcome (the theorem about
  functions gives it, by induction on the fuel);
* `call_ok`: the code of the IR's `call`, given `Callee`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The IR's state once the function has the argument `v` passed in a register. -/
def stArg (c : IR.Ctx) (gf : IR.Fn) (st : IR.Sem.St) (v : Nat) : IR.Sem.St :=
  match gf.regParam with
  | some (n, sl) => { st with mem := IR.Sem.wr st.mem (c.layout.addr sl) n v }
  | none => st

/-- The CPU is at the entry of `gf`: the return address on the stack,
the argument `v` in its register. -/
structure Entry (Z : ZCtx) (gf : IR.Fn) (st : IR.Sem.St) (v : Nat) (s : Cpu) : Prop where
  pc : ∃ ad, Z.sym (fnLabel gf.name) ad ∧ s.pc.toNat = ad
  img : Img Z.a 0 s
  run : s.halted = false
  rs : s.ramStart.toNat = Z.ramStart
  msz : s.mem.size = 65536
  isz : st.mem.size = 65536
  mem : ∀ x, Z.data x → s.mem.get! x = st.mem.get! x
  room : Z.stackLo + Z.depth gf.name ≤ s.sp.toNat ∧ s.sp.toNat + 2 ≤ Z.stackHi
  arg : ∀ n sl, gf.regParam = some (n, sl) → ResIn n v s

/-- What the function does from `s`, for the result the IR gives. -/
def Outcome (Z : ZCtx) (f : IR.Fn) (fr : Fr) (s : Cpu) : IR.Sem.Res → Prop
  | .ok r st' => ∃ s' v, Steps s s' ∧ IR.Instr.ret v ∈ f.body.toList ∧ RetSt Z f fr st' (v.map (·.1)) r s'
  | .trap st' => ∃ s', Steps s s' ∧ Trapped Z st' s'
  | _ => True

/-- The function `g`, entered with the IR in the state `st1` (its
argument stored), has the outcome of the result `res`. -/
def Callee (Z : ZCtx) (g : String) (st1 : IR.Sem.St) (res : IR.Sem.Res) : Prop :=
  ∀ gf st v s, Z.c.prog.fn? g = some gf → st1 = stArg Z.c gf st v → Entry Z gf st v s →
    Outcome Z gf ⟨s.sp, s.mem⟩ s res

/-- What a call needs of the program. -/
structure CallNeed (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (g : String) (ret : Option (Nat × Dst))
    (reg : Option (Nat × Opd)) : Prop where
  fn : ∃ gf, Z.c.prog.fn? g = some gf
  /-- The argument in a register is the parameter in a register, of that size. -/
  regSz : ∀ gf, Z.c.prog.fn? g = some gf → reg.map (·.1) = gf.regParam.map (·.1)
  rd : ∀ n o, reg = some (n, o) → Rd Z E dt n o
  wr : ∀ n d, ret = some (n, d) → Wr Z E n d
  /-- The result is of the size the function returns. -/
  retSz : ∀ n d, ret = some (n, d) → ∀ gf v, Z.c.prog.fn? g = some gf → IR.Instr.ret v ∈ gf.body.toList →
    ∃ o, v = some (n, o)
  label : ∃ j : Nat, Z.items[j]? = some (Item.label (fnLabel g))
  depth : Z.depth g + 2 ≤ Z.depth E.fn.name
  /-- What the function called may write, the caller may; not the caller's temporaries. -/
  sub : ∀ x, Z.wr g x → Z.wr E.fn.name x
  tmps : ∀ t, E.spilled[t]! = true → ∀ j, j < E.fn.tmps[t]! → ¬ Z.wr g (tmpAddr Z E t + j)

/-- What follows a call, for the result of the function called. -/
def AfterCall (Z : ZCtx) (E : GEnv) (fr : Fr) (dt' : Nat → Prop) (regs' : Regs) (k' : Nat) (tmps : Array Nat)
    (ret : Option (Nat × Dst)) (s : Cpu) : IR.Sem.Res → Prop
  | .ok r st2 => ∃ s', Steps s s' ∧ At Z.addrs k' s' ∧
      Rel Z E fr dt' regs' (IR.Sem.setRet Z.c st2 tmps ret r).1 (IR.Sem.setRet Z.c st2 tmps ret r).2 s'
  | .trap st2 => ∃ s', Steps s s' ∧ Trapped Z st2 s'
  | _ => True

/-- The temporaries assigned once the result of a call is. -/
def dtRet (dt : Nat → Prop) : Option (Nat × Dst) → Nat → Prop
  | some (_, d) => dtAfter dt d
  | none => dt

/-- The state of the IR the function called starts in. -/
def callSt (c : IR.Ctx) (ist : IR.Sem.St) (tmps : Array Nat) (g : String) (reg : Option (Nat × Opd)) :
    IR.Sem.St :=
  match reg, c.prog.fn? g with
  | some (n, o), some gf =>
    match gf.regParam with
    | some (_, sl) => { ist with mem := IR.Sem.wr ist.mem (c.layout.addr sl) n (IR.Sem.opd c ist tmps n o) }
    | none => ist
  | _, _ => ist

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

theorem add2_sub2 (x : UInt16) : x - 2 + 2 = x := UInt16.sub_add_cancel _ _

/-- The call itself and the return, from states that agree with the
argument in its register: the states agree again, nothing in the registers. -/
theorem call_fn (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {s0 s1 : GS} {g : String}
    {ret : Option (Nat × Dst)} {reg : Option (Nat × Opd)} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins ⟨.call, [.imm (.sym (fnLabel g))]⟩)) (N : CallNeed Z E dt g ret reg)
    {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu} (R : Rel Z E fr dt regs ist tmps s)
    (hat : At Z.addrs (base + s0.out.size) s)
    (harg : ∀ n o, reg = some (n, o) → (n = 1 → s.a.toNat = IR.Sem.opd Z.c ist tmps n o) ∧
      (n = 2 → s.hl.toNat = IR.Sem.opd Z.c ist tmps n o))
    (res : IR.Sem.Res) (hc : Callee Z g (callSt Z.c ist tmps g reg) res) :
    match res with
    | .ok r st2 => ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt {} st2 tmps s' ∧
        ∀ n d, ret = some (n, d) → ResIn n (r.getD 0) s'
    | .trap st2 => ∃ s', Steps s s' ∧ Trapped Z st2 s'
    | _ => True := by
  obtain ⟨gf, hgf⟩ := N.fn
  obtain ⟨j, hj⟩ := N.label
  obtain ⟨T, _, hsym, hTlt⟩ := label_at ok hj R.img
  have hroom := R.room
  have hstk := ok.stack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  have hdep := N.depth
  obtain ⟨c1, st1, cs, hpc1, I1, hh1, hrs1, hback⟩ :=
    call_step ok (F.emitted hx ho) hsym hTlt hat R.img R.run R.rs R.msz (by omega) (by omega)
  have hc1sp : c1.sp.toNat = s.sp.toNat - 2 := by rw [cs.sp]; exact sub2_toNat _ (by omega)
  -- the argument, and the state of the IR at the entry
  have hreg := N.regSz gf hgf
  have hv : ∃ v, callSt Z.c ist tmps g reg = stArg Z.c gf ist v ∧
      ∀ n sl, gf.regParam = some (n, sl) → ResIn n v s := by
    cases hr : reg with
    | none =>
      rw [hr] at hreg
      cases hp : gf.regParam with
      | none => exact ⟨0, by simp [callSt, stArg, hp], fun n sl h => by cases h⟩
      | some p => rw [hp] at hreg; cases hreg
    | some p =>
      obtain ⟨n, o⟩ := p
      rw [hr] at hreg
      cases hp : gf.regParam with
      | none => rw [hp] at hreg; cases hreg
      | some q =>
        obtain ⟨n', sl⟩ := q
        rw [hp] at hreg
        have hn : n = n' := by simpa using hreg
        subst hn
        refine ⟨IR.Sem.opd Z.c ist tmps n o, by simp [callSt, stArg, hp, hgf], fun m sl' h => ?_⟩
        cases h
        exact harg n o hr
  obtain ⟨v, hst1, hargv⟩ := hv
  have hname : gf.name = g := by
    have := List.find?_some hgf
    simpa using this
  have ent : Entry Z gf ist v c1 := by
    refine ⟨⟨T, ?_, hpc1⟩, I1, hh1, by rw [hrs1]; exact R.rs, by rw [cs.size]; exact R.msz, R.isz, fun x hxd => ?_,
      ⟨by rw [hname]; omega, by omega⟩, fun n sl h => ?_⟩
    · rw [hname]
      exact hsym
    · rw [cs.mem x (by have := ok.nostack x hxd; omega)]
      exact R.mem x hxd
    · obtain ⟨h1, h2⟩ := hargv n sl h
      exact ⟨fun e => by rw [cs.a]; exact h1 e, fun e => by rw [hl_congr cs.h cs.l]; exact h2 e⟩
  have hout := hc gf ist v c1 hgf hst1 ent
  cases res with
  | fuel => trivial
  | bad => trivial
  | trap st2 =>
    obtain ⟨s', st2', htr⟩ := hout
    exact ⟨s', st1.trans st2', htr⟩
  | ok r st2 =>
    obtain ⟨s', rv, st2', hrv, hret⟩ := hout
    have hfr : ∀ x, x < Z.stackLo ∨ Z.stackHi ≤ x → ¬ Z.wr g x → s'.mem.get! x = s.mem.get! x := by
      intro x hx1 hx2
      rw [hret.out x (by rw [hname]; exact hx2)]
      exact cs.mem x (by omega)
    have hstk' : ∀ x, fr.sp.toNat ≤ x → x < Z.stackHi → s'.mem.get! x = s.mem.get! x := by
      intro x h1 h2
      rw [hret.stk x (by show c1.sp.toNat ≤ x; omega) h2]
      exact cs.mem x (by omega)
    refine ⟨s', st1.trans st2', ?_, ?_, ?_⟩
    · rw [ho, Array.size_push, ← Nat.add_assoc]
      refine hback s' ?_
      rw [hret.pc]
      show IR.Sem.rd c1.mem c1.sp.toNat 2 = _
      rw [hc1sp]
    · refine ⟨hret.img, hret.run, hret.mem, fun t h1 h2 => ?_, hret.rs, hret.msz, hret.isz, R.tsz, ?_, R.room,
    fun x h1 h2 => ?_, fun x hxw => ?_, fun o ho => (by cases ho), fun o ho => (by cases ho),
        fun n o h => (by cases h), fun sl h => (by cases h), fun sl h => (by cases h), fun n sl h => (by cases h),
        fun n o h => (by cases h)⟩
      · rw [← R.tmp t h1 h2]
        refine rd_congr _ _ _ _ (hT.bound t h2) (fun x hx1 hx2 => hfr x ?_ ?_)
        · have := hT.nostack t h2
          omega
        · have := N.tmps t h2 (x - tmpAddr Z E t) (by omega)
          rwa [show tmpAddr Z E t + (x - tmpAddr Z E t) = x by omega] at this
      · rw [hret.sp]
        show c1.sp + 2 = fr.sp
        rw [cs.sp, add2_sub2, R.sp]
      · rw [hstk' x h1 h2]
        exact R.stk x h1 h2
      · have hng : ¬ Z.wr g x := fun h => hxw (N.sub x h)
        rw [hfr x ?_ hng]
        · exact R.out x hxw
        · rcases Nat.lt_or_ge x Z.stackLo with h | h
          · exact Or.inl h
          · rcases Nat.lt_or_ge x Z.stackHi with h' | h'
            · exact absurd (ok.wrStack _ x h h') hxw
            · exact Or.inr h'
    · intro n d hnd
      obtain ⟨o, ho'⟩ := N.retSz n d hnd gf rv hgf hrv
      exact hret.res n (by rw [ho']; rfl)

/-! ## The code of `call` -/

/-- The argument in a register, loaded. -/
def argLoad : Option (Nat × Opd) → GM Unit
  | some (n, o) => Codegen.load n o
  | none => pure ()

/-- The result, stored. -/
def retStore : Option (Nat × Dst) → GM Unit
  | some (n, d) => store n d
  | none => pure ()

theorem genCall_eq (g : String) (ret : Option (Nat × Dst)) (reg : Option (Nat × Opd)) :
    genInstr (.call g ret reg) = (do argLoad reg; call (fnLabel g); killAll; retStore ret) := by
  cases reg <;> cases ret <;> rfl

theorem argLoad_ok (ok : Z.OK) (F : GFinal Z base sF) (reg : Option (Nat × Opd))
    (hsz : ∀ n o, reg = some (n, o) → n = 1 ∨ n = 2) (s0 : GS) :
    wpg (argLoad reg) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → (∀ n o, reg = some (n, o) → Rd Z E dt n o) → ∀ fr ist tmps s,
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          ∀ n o, reg = some (n, o) → (n = 1 → s'.a.toNat = IR.Sem.opd Z.c ist tmps n o) ∧
            (n = 2 → s'.hl.toNat = IR.Sem.opd Z.c ist tmps n o))) s0 := by
  cases reg with
  | none =>
    exact ⟨GExt.refl _, fun _ _ fr ist tmps s R hat => ⟨s, Steps.refl _, hat, R, fun n o h => by cases h⟩⟩
  | some p =>
    obtain ⟨n, o⟩ := p
    rcases hsz n o rfl with rfl | rfl
    · simp only [argLoad, Codegen.load, beq_self_eq_true, if_true]
      refine wpg_mono (loadA_ok (dt := dt) ok F o s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine ⟨hx1, fun hx hrd fr ist tmps s R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, _, hA⟩ := hl hx fr ist tmps s (hrd 1 o rfl) R hat
      refine ⟨s', st1, at1, R1, fun n' o' h => ?_⟩
      cases h
      exact ⟨fun _ => hA, fun e => (by cases e)⟩
    · simp only [argLoad, Codegen.load, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
        beq_self_eq_true, if_true]
      refine wpg_mono (loadHL_ok (dt := dt) ok F o s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      refine ⟨hx1, fun hx hrd fr ist tmps s R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, _, hHL⟩ := hl hx fr ist tmps s (hrd 2 o rfl) R hat
      refine ⟨s', st1, at1, R1, fun n' o' h => ?_⟩
      cases h
      exact ⟨fun e => (by cases e), fun _ => hHL⟩

theorem retStore_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (ret : Option (Nat × Dst))
    (hsz : ∀ n d, ret = some (n, d) → n = 1 ∨ n = 2) (s1 : GS) :
    wpg (retStore ret) E (fun _ s2 => GExt s1 s2 ∧
      (GExt s2 sF → (∀ n d, ret = some (n, d) → Wr Z E n d) → ∀ fr ist tmps s r,
        Rel Z E fr dt s1.regs ist tmps s → At Z.addrs (base + s1.out.size) s →
        (∀ n d, ret = some (n, d) → ResIn n (Option.getD r 0) s) →
        ∃ s', Steps s s' ∧ At Z.addrs (base + s2.out.size) s' ∧
          Rel Z E fr (dtRet dt ret) s2.regs (IR.Sem.setRet Z.c ist tmps ret r).1
            (IR.Sem.setRet Z.c ist tmps ret r).2 s')) s1 := by
  cases ret with
  | none =>
    exact ⟨GExt.refl _, fun _ _ fr ist tmps s r R hat _ => ⟨s, Steps.refl _, hat, R⟩⟩
  | some p =>
    obtain ⟨n, d⟩ := p
    rcases hsz n d rfl with rfl | rfl
    · simp only [retStore, store, beq_self_eq_true, if_true]
      refine wpg_mono (storeA_ok (dt := dt) ok hT F d s1) ?_
      intro _ s2 ⟨hx2, _, _, hs⟩
      refine ⟨hx2, fun hx hwr fr ist tmps s r R hat hres => ?_⟩
      have hA := (hres 1 d rfl).1 rfl
      obtain ⟨s', st, at', R', _⟩ := hs hx fr ist tmps s (r.getD 0) (hwr 1 d rfl) R hat (by
        have := s.a.toNat_lt
        rw [← hA]
        omega)
      exact ⟨s', st, at', R'⟩
    · simp only [retStore, store, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
        beq_self_eq_true, if_true]
      refine wpg_mono (storeHL_ok (dt := dt) ok hT F d s1) ?_
      intro _ s2 ⟨hx2, _, _, hs⟩
      refine ⟨hx2, fun hx hwr fr ist tmps s r R hat hres => ?_⟩
      have hHL := (hres 2 d rfl).2 rfl
      obtain ⟨s', st, at', R', _⟩ := hs hx fr ist tmps s (r.getD 0) (hwr 2 d rfl) R hat (by
        have := s.hl.toNat_lt
        rw [← hHL]
        omega)
      exact ⟨s', st, at', R'⟩

/-- **`call`**: the argument loaded, the function called, its result stored. -/
theorem call_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (g : String) (ret : Option (Nat × Dst))
    (reg : Option (Nat × Opd)) (hreg : ∀ n o, reg = some (n, o) → n = 1 ∨ n = 2)
    (hret : ∀ n d, ret = some (n, d) → n = 1 ∨ n = 2) (s0 : GS) :
    wpg (genInstr (.call g ret reg)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → CallNeed Z E dt g ret reg → ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s →
        At Z.addrs (base + s0.out.size) s → ∀ res, Callee Z g (callSt Z.c ist tmps g reg) res →
        AfterCall Z E fr (dtRet dt ret) s1.regs (base + s1.out.size) tmps ret s res)) s0 := by
  rw [genCall_eq]
  simp only [wpg_bind]
  refine wpg_mono (argLoad_ok (dt := dt) ok F reg hreg s0) ?_
  intro _ s1 ⟨hx1, hl⟩
  simp only [wpg_call, killAll, wpg_setRegs]
  refine wpg_mono (retStore_ok (dt := dt) ok hT F ret hret _) ?_
  intro _ s2 ⟨hx2, hs⟩
  have hmid : GExt s1 { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (fnLabel g))]⟩), regs := {} } :=
    ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩
  refine ⟨hx1.trans (hmid.trans hx2), fun hx N fr ist tmps s R hat res hc => ?_⟩
  obtain ⟨s', st1, at1, R1, harg⟩ := hl (hmid.trans (hx2.trans hx)) N.rd fr ist tmps s R hat
  have hcall := call_fn ok hT F (s0 := s1)
    (s1 := { s1 with out := s1.out.push (.ins ⟨.call, [.imm (.sym (fnLabel g))]⟩) })
    ((GExt.regs _ _).trans (hx2.trans hx)) rfl N R1 at1 harg res hc
  cases res with
  | fuel => trivial
  | bad => trivial
  | trap st2 =>
    obtain ⟨s'', st2', htr⟩ := hcall
    exact ⟨s'', st1.trans st2', htr⟩
  | ok r st2 =>
    obtain ⟨s'', st2', at2, R2, hres⟩ := hcall
    obtain ⟨s3, st3, at3, R3⟩ := hs hx N.wr fr st2 tmps s'' r R2 at2 hres
    exact ⟨s3, (st1.trans st2').trans st3, at3, R3⟩

end

end Ember.Proof.Z80Gen
