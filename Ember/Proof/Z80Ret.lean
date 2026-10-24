import Ember.Proof.Z80Ctl
import Ember.Proof.Z80Acc

/-!
# Ember.Proof.Z80Ret — the end of a function: `ret` and `trap` (plan M7.3)

`RetSt`: the state a function returns in, as its caller finds it — the
program counter at the return address, the stack pointer after it, the
shared bytes as the IR left them, nothing written but what the function
may write, the result in `A` or `HL`.  `Trapped`: the CPU is at the
runtime's `rt_trap`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The result of `n` bytes, where the caller finds it: `A`, `HL`, or the accumulator. -/
def ResIn (Z : ZCtx) (n v : Nat) (s : Cpu) : Prop :=
  (n = 1 → s.a.toNat = v) ∧ (n = 2 → s.hl.toNat = v) ∧ (2 < n → IR.Sem.rd s.mem Z.acc n = v)

/-- The function `f`, entered with the stack `fr`, has returned: `ist`
is the IR's state, `r` its result (of `sz` bytes). -/
structure RetSt (Z : ZCtx) (f : IR.Fn) (fr : Fr) (ist : IR.Sem.St) (sz : Option Nat) (r : Option Nat)
    (s' : Cpu) : Prop where
  pc : s'.pc.toNat = IR.Sem.rd fr.mem fr.sp.toNat 2
  sp : s'.sp = fr.sp + 2
  img : Img Z.a 0 s'
  run : s'.halted = false
  rs : s'.ramStart.toNat = Z.ramStart
  msz : s'.mem.size = 65536
  isz : ist.mem.size = 65536
  mem : ∀ x, Z.data x → s'.mem.get! x = ist.mem.get! x
  stk : ∀ x, fr.sp.toNat ≤ x → x < Z.stackHi → s'.mem.get! x = fr.mem.get! x
  out : ∀ x, ¬ Z.wr f.name x → s'.mem.get! x = fr.mem.get! x
  res : ∀ n, sz = some n → ResIn Z n (r.getD 0) s'

/-- The CPU is at `rt_trap`, the shared bytes as the IR left them, the image in ROM (what stepping on from
the label needs). -/
def Trapped (Z : ZCtx) (ist : IR.Sem.St) (s' : Cpu) : Prop :=
  ∃ j, Z.items[j]? = some (Item.label "rt_trap") ∧ At Z.addrs j s' ∧ s'.halted = false ∧
    (∀ x, Z.data x → s'.mem.get! x = ist.mem.get! x) ∧ Img Z.a 0 s'

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- The `ret` item, from states that agree. -/
theorem ret_step (ok : Z.OK) (F : GFinal Z base sF) {s0 s1 : GS} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins ⟨.ret, []⟩)) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hat : At Z.addrs (base + s0.out.size) s) (sz r : Option Nat)
    (hres : ∀ n, sz = some n → ResIn Z n (r.getD 0) s) : ∃ s', Steps s s' ∧ RetSt Z E.fn fr ist sz r s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := fun inp => (step_item ok.placed R.img (F.emitted hx ho) had hpc R.run (inp := inp)
    (s' := (retTo (op1 s)).tick 10) rfl).1
  have hroom := R.room
  have hstk := ok.stack
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  refine ⟨_, Steps.one hst rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, R.isz, ?_, ?_, ?_, ?_⟩⟩
  · have h1 : ((retTo (op1 s)).tick 10).pc = s.rd16 s.sp := by simp only [retTo, zsim]
    rw [h1, cpu_rd16 _ _ (by omega), hspv]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => R.stk x h1 (by omega))
  · simp only [retTo, zsim]
    rw [R.sp]
  · exact R.img.congr (by simp only [retTo, zsim]) (by simp only [retTo, zsim])
  · simp only [retTo, zsim]
    exact R.run
  · simp only [retTo, zsim]
    exact R.rs
  · simp only [retTo, zsim]
    exact R.msz
  · intro x hxd
    simp only [retTo, zsim]
    exact R.mem x hxd
  · intro x h1 h2
    simp only [retTo, zsim]
    exact R.stk x h1 h2
  · intro x hxw
    simp only [retTo, zsim]
    exact R.out x hxw
  · intro n hn
    obtain ⟨h1, h2, h3⟩ := hres n hn
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp only [retTo, zsim]
      exact h1 e
    · simp only [retTo, zsim]
      exact h2 e
    · simp only [retTo, zsim]
      exact h3 e

/-- **`ret`**: the result loaded, the function returns. -/
theorem ret_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtW Z 4)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (v : Option (Nat × Opd))
    (hsz : ∀ n o, v = some (n, o) → n = 1 ∨ n = 2 ∨ n = 4) (s0 : GS) :
    wpg (genInstr (.ret v)) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → (∀ n o, v = some (n, o) → RdN Z E dt n o) →
        ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧
          RetSt Z E.fn fr ist (v.map (·.1)) (v.map fun a => IR.Sem.opd Z.c ist tmps a.1 a.2) s')) s0 := by
  cases v with
  | none =>
    simp only [genInstr, wpg_bind, wpg_ins, wpg_modify]
    refine ⟨GExt.of_out (by simp) rfl rfl, fun hx _ fr ist tmps s R hat => ?_⟩
    exact ret_step ok F hx rfl R hat none none (fun n hn => by cases hn)
  | some p =>
    obtain ⟨n, o⟩ := p
    simp only [genInstr, wpg_bind]
    by_cases h1 : n = 1
    · subst h1
      simp only [Codegen.load, beq_self_eq_true, if_true]
      refine wpg_mono (loadA_ok (dt := dt) ok F o s0) ?_
      intro _ s1 ⟨hx1, _, _, hl⟩
      simp only [wpg_ins, wpg_modify]
      refine ⟨hx1.trans (GExt.of_out (by simp) rfl rfl), fun hx hv fr ist tmps s R hat => ?_⟩
      obtain ⟨s', st1, at1, R1, _, hA⟩ :=
        hl ((show GExt s1 { s1 with out := s1.out.push (.ins ⟨.ret, []⟩), dead := true } from
          ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩).trans hx) fr ist tmps s (hv 1 o rfl) R hat
      obtain ⟨s'', st2, hret⟩ := ret_step ok F hx rfl R1 at1 (some 1) (some (IR.Sem.opd Z.c ist tmps 1 o))
        (fun n hn => by cases hn; exact ⟨fun _ => hA, fun e => (by cases e), fun e => absurd e (by decide)⟩)
      exact ⟨s'', st1.trans st2, hret⟩
    · by_cases h2 : n = 2
      · subst h2
        simp only [Codegen.load, show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true, if_false,
          beq_self_eq_true, if_true]
        refine wpg_mono (loadHL_ok (dt := dt) ok F o s0) ?_
        intro _ s1 ⟨hx1, _, _, hl⟩
        simp only [wpg_ins, wpg_modify]
        refine ⟨hx1.trans (GExt.of_out (by simp) rfl rfl), fun hx hv fr ist tmps s R hat => ?_⟩
        obtain ⟨s', st1, at1, R1, _, hHL⟩ :=
          hl ((show GExt s1 { s1 with out := s1.out.push (.ins ⟨.ret, []⟩), dead := true } from
          ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩).trans hx) fr ist tmps s (hv 2 o rfl) R hat
        obtain ⟨s'', st2, hret⟩ := ret_step ok F hx rfl R1 at1 (some 2) (some (IR.Sem.opd Z.c ist tmps 2 o))
          (fun n hn => by cases hn; exact ⟨fun e => (by cases e), fun _ => hHL, fun e => absurd e (by decide)⟩)
        exact ⟨s'', st1.trans st2, hret⟩
      · have h4 : n = 4 := by
          rcases hsz n o rfl with h | h | h
          · exact absurd h h1
          · exact absurd h h2
          · exact h
        subst h4
        simp only [Codegen.load, show ((4 : Nat) == 1) = false from rfl, show ((4 : Nat) == 2) = false from rfl,
          Bool.false_eq_true, if_false]
        refine wpg_mono (loadAcc_ok (dt := dt) ok hT F (by omega) hrt hdep o s0) ?_
        intro _ s1 ⟨hx1, hacc1, hl⟩
        simp only [wpg_ins, wpg_modify]
        refine ⟨hx1.trans (GExt.of_out (by simp) rfl rfl), fun hx hv fr ist tmps s R hat => ?_⟩
        obtain ⟨s', st1, at1, R1⟩ :=
          hl ((show GExt s1 { s1 with out := s1.out.push (.ins ⟨.ret, []⟩), dead := true } from
          ⟨by simp, List.suffix_refl _, List.suffix_refl _⟩).trans hx) fr ist tmps s (hv 4 o rfl) R hat
        obtain ⟨s'', st2, hret⟩ := ret_step ok F hx rfl R1 at1 (some 4) (some (IR.Sem.opd Z.c ist tmps 4 o))
          (fun n hn => by
            cases hn
            exact ⟨fun e => (by cases e), fun e => (by cases e),
              fun _ => R1.racc 4 o hacc1 (Rd.own_w (dt := dt) (n := 4) (hv 4 o rfl))⟩)
        exact ⟨s'', st1.trans st2, hret⟩

/-- **`trap`**: the CPU is at `rt_trap`. -/
theorem trap_ok (ok : Z.OK) (F : GFinal Z base sF) (s0 : GS) :
    wpg (genInstr .trap) E (fun _ s1 => GExt s0 s1 ∧
      (GExt s1 sF → ∀ j : Nat, Z.items[j]? = some (Item.label "rt_trap") →
        ∀ fr ist tmps s, Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps s s' ∧ Trapped Z ist s')) s0 := by
  simp only [genInstr, wpg_bind, wpg_ins, wpg_modify]
  refine ⟨GExt.of_out (by simp) rfl rfl, fun hx j hlab fr ist tmps s R hat => ?_⟩
  have hk : Z.items[base + s0.out.size]? = some (.ins ⟨.jp, [.imm (.sym "rt_trap")]⟩) :=
    F.at hx (by simp)
  obtain ⟨s', st, at', M', hS, _⟩ := jp_step ok hk hlab R.mach hat
  exact ⟨s', st, j, hlab, at', M'.2, fun x hxd => by rw [hS.1]; exact R.mem x hxd, M'.1⟩

end

end Ember.Proof.Z80Gen
