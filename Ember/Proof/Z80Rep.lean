import Ember.Proof.Z80Mul
import Ember.Proof.Z80Bits

/-!
# Ember.Proof.Z80Rep — an instruction repeated (plan M7.3)

`Codegen.rep k (ins …)` emits one instruction `k` times; run, it is the
instruction's effect iterated (`run_rep`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin)

/-- `f`, `k` times. -/
def iter {α : Type} : Nat → (α → α) → α → α
  | 0, _, s => s
  | k + 1, f, s => iter k f (f s)

/-- `it` emitted `k` times. -/
def pushK (it : Item) : Nat → GS → GS
  | 0, s => s
  | k + 1, s => pushK it k { s with out := s.out.push it }

theorem pushK_size (it : Item) : ∀ (k : Nat) (s : GS), (pushK it k s).out.size = s.out.size + k
  | 0, _ => rfl
  | k + 1, s => by rw [pushK, pushK_size it k, Array.size_push]; omega

theorem pushK_regs (it : Item) : ∀ (k : Nat) (s : GS), (pushK it k s).regs = s.regs
  | 0, _ => rfl
  | k + 1, s => by rw [pushK, pushK_regs it k]

theorem pushK_ext (it : Item) : ∀ (k : Nat) (s : GS), GExt s (pushK it k s)
  | 0, s => GExt.refl s
  | k + 1, s => (GExt.push s it).trans (pushK_ext it k _)

theorem wpg_rep_ins {E : GEnv} (op : Op) (args : List Arg) (Q : Unit → GS → Prop) :
    ∀ (k : Nat) (s : GS), wpg (rep k (ins op args)) E Q s ↔ Q () (pushK (.ins { op, args }) k s)
  | 0, _ => Iff.rfl
  | k + 1, s => by
    rw [rep, wpg_bind, wpg_ins, wpg_rep_ins op args Q k]
    rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- **An instruction repeated**: its effect, iterated. -/
theorem run_rep (ok : Z.OK) (F : GFinal Z base sF) {i : Instr} (f : Cpu → Cpu)
    (hexec : ∀ env s inp, exec env i s inp = some (f s)) (hf : i.falls = true) (hS : ∀ s, Sys s (f s)) :
    ∀ (k : Nat) (s0 : GS) (s : Cpu), GExt (pushK (.ins i) k s0) sF → Mach Z s →
      At Z.addrs (base + s0.out.size) s →
      Steps Z.inp s (iter k f s) ∧ At Z.addrs (base + (pushK (.ins i) k s0).out.size) (iter k f s) ∧ Mach Z (iter k f s)
  | 0, s0, s, _, M, hat => ⟨Steps.refl _ _, hat, M⟩
  | k + 1, s0, s, hx, M, hat => by
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins i) })
      ((pushK_ext _ k _).trans hx) rfl M hat (f s) (fun ad _ => hexec _ _ _) hf (hS s)
    obtain ⟨st2, at2, M2⟩ := run_rep ok F f hexec hf hS k _ (f s) hx M1 at1
    exact ⟨st1.trans st2, at2, M2⟩

/-- Instructions emitted one after the other. -/
def pushL : List Instr → GS → GS
  | [], s => s
  | i :: r, s => pushL r { s with out := s.out.push (.ins i) }

theorem pushL_size : ∀ (l : List Instr) (s : GS), (pushL l s).out.size = s.out.size + l.length
  | [], _ => rfl
  | i :: r, s => by rw [pushL, pushL_size r, Array.size_push, List.length_cons]; omega

theorem pushL_regs : ∀ (l : List Instr) (s : GS), (pushL l s).regs = s.regs
  | [], _ => rfl
  | i :: r, s => by rw [pushL, pushL_regs r]

theorem pushL_ext : ∀ (l : List Instr) (s : GS), GExt s (pushL l s)
  | [], s => GExt.refl s
  | i :: r, s => (GExt.push s _).trans (pushL_ext r _)

/-- Their effects, one after the other. -/
def runL : List (Cpu → Cpu) → Cpu → Cpu
  | [], s => s
  | f :: r, s => runL r (f s)

/-- An instruction with what it does, whatever the labels are. -/
structure Does (i : Instr) (f : Cpu → Cpu) : Prop where
  exec : ∀ env s inp, exec env i s inp = some (f s)
  falls : i.falls = true
  sys : ∀ s, Sys s (f s)

/-- **Instructions one after the other**, each leaving memory alone. -/
theorem run_list (ok : Z.OK) (F : GFinal Z base sF) :
    ∀ (l : List (Instr × (Cpu → Cpu))), (∀ p, p ∈ l → Does p.1 p.2) → ∀ (s0 : GS) (s : Cpu),
      GExt (pushL (l.map (·.1)) s0) sF → Mach Z s → At Z.addrs (base + s0.out.size) s →
      Steps Z.inp s (runL (l.map (·.2)) s) ∧
        At Z.addrs (base + (pushL (l.map (·.1)) s0).out.size) (runL (l.map (·.2)) s) ∧
        Mach Z (runL (l.map (·.2)) s) ∧ Sys s (runL (l.map (·.2)) s)
  | [], _, s0, s, _, M, hat => ⟨Steps.refl _ _, hat, M, Sys.refl s⟩
  | (i, f) :: r, h, s0, s, hx, M, hat => by
    have hd := h (i, f) (by simp)
    obtain ⟨st1, at1, M1⟩ := run_reg ok F (s0 := s0) (s1 := { s0 with out := s0.out.push (.ins i) })
      ((pushL_ext _ _).trans hx) rfl M hat (f s) (fun ad _ => hd.exec _ _ _) hd.falls (hd.sys s)
    obtain ⟨st2, at2, M2, S2⟩ := run_list ok F r (fun p hp => h p (by simp [hp])) _ (f s) hx M1 at1
    exact ⟨st1.trans st2, at2, M2, (hd.sys s).trans S2⟩

theorem iter_inv {α : Type} (f : α → α) (P : α → α → Prop) (hrefl : ∀ s, P s s)
    (htrans : ∀ s s' s'', P s s' → P s' s'' → P s s'') (h : ∀ s, P s (f s)) : ∀ (k : Nat) (s : α), P s (iter k f s)
  | 0, s => hrefl s
  | k + 1, s => htrans _ _ _ (h s) (iter_inv f P hrefl htrans h k (f s))

/-- The states agree when registers changed, `HL` is no longer tracked,
and `A` is as it was or no longer tracked either. -/
theorem Rel.hl_gone {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s s' : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hS : Sys s s') (hhl : regs'.hl = [])
    (ha : regs'.a = [] ∨ (regs'.a = regs.a ∧ s'.a = s.a))
    (hacc : ∀ n o, regs'.acc = some (n, o) → regs.acc = some (n, o)) : Rel Z E fr dt regs' ist tmps s' := by
  refine R.regs_only hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 (fun o ho hown => ?_) (fun o ho => by rw [hhl] at ho; cases ho)
    (fun sl hsl hown => ?_) (fun sl hsl => by rw [hhl] at hsl; cases hsl) hacc
  · rcases ha with h | ⟨h1, h2⟩
    · rw [h] at ho; cases ho
    · rw [h2]; exact R.ra o (h1 ▸ ho) hown
  · rcases ha with h | ⟨h1, _⟩
    · rw [h] at hsl; cases hsl
    · exact R.ina sl (h1 ▸ hsl) hown

end

end Ember.Proof.Z80Gen
