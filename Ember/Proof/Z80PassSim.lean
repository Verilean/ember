import Ember.Proof.Z80PassLocal
import Ember.Proof.Z80Rel
import Ember.Proof.Z80Rep
import Ember.Proof.Z80Bin16
import Ember.Proof.Z80Shift
import Ember.Proof.Z80Ext

/-!
# Ember.Proof.Z80PassSim — two images side by side on the machine of the proofs (plan M7.3)

`Z80PassLocal` has the rewrites of the passes on `Asm.exec`, from one CPU
state.  Here the same rewrites are steps of the machine the proofs run
(`wstep`: the CPU stepped on the bytes of its image, the I/O bus and the
devices around it), in two images at once — the image without the
passes (`A`) and one with them (`B`) — each from its own state.

The setting is the harness's, and only it: `Machine.step` is `wstep` in
harness mode with no byte on the wire, no RDRF and no tick pending
(`Z80Machine.step_sim`), so no interrupt is taken; the code is in ROM,
below `ramStart`, where a write does nothing (`Cpu.wr`), so it is the
image's bytes at every step (`Img`).

`Regs`: two CPUs equal but for the program counter, `R`, the T-states
and memory — what the relation between the two machines asks of the
registers where they are known.  `packHigh_steps`: from such states at
the rewrite, four steps of `A` and two of `B` leave such states at the
items after it, memory, the stack pointer and the devices as they were.

What is not here: the relation of the whole images (the code and the
data after a rewrite are at other addresses, so are the return
addresses on the stack), and the theorem about the image as built by
default.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

/-- An image: its items, as the assembler placed them. -/
structure Code where
  items : List Item
  a : Assembled
  addrs : List Nat
  placed : Placed items 0 a addrs

/-- The machine around the CPU: its state, what the bus answers, what I/O does to it; an
instruction without I/O leaves it as it is. -/
structure Dev where
  W : Type
  bus : W → UInt16 → UInt8
  dev : W → IoEvent → W
  quiet : ∀ w, dev w .none = w

/-- One step of the machine (`wstep`). -/
def mstep (D : Dev) (x : Cpu × D.W) : Cpu × D.W :=
  (x.1.step (D.bus x.2), D.dev x.2 (x.1.step (D.bus x.2)).io)

def mrun (D : Dev) : Nat → Cpu × D.W → Cpu × D.W
  | 0, x => x
  | n + 1, x => mrun D n (mstep D x)

theorem mrun_add (D : Dev) : ∀ (n m : Nat) (x : Cpu × D.W), mrun D (n + m) x = mrun D m (mrun D n x)
  | 0, m, x => by simp [mrun]
  | n + 1, m, x => by rw [show n + 1 + m = (n + m) + 1 by omega, mrun, mrun, mrun_add D n m]

/-- The machine of a setting of the proofs. -/
def ZCtx.dev (Z : ZCtx) (ok : Z.OK) : Dev := ⟨Z.W, Z.bus, Z.dev, ok.quiet⟩

theorem wrun_eq (Z : ZCtx) (ok : Z.OK) : ∀ (n : Nat) (x : Cpu × Z.W), wrun Z n x = mrun (ZCtx.dev Z ok) n x
  | 0, _ => rfl
  | n + 1, x => wrun_eq Z ok n (wstep Z x)

/-- The CPU runs the image: its bytes in ROM, not halted. -/
def Loaded (C : Code) (s : Cpu) : Prop := Img C.a 0 s ∧ s.halted = false

/-- The items `l` from index `k` on. -/
def Has (C : Code) (k : Nat) (l : List Item) : Prop := ∀ j it, l[j]? = some it → C.items[k + j]? = some it

theorem Has.get {C : Code} {k : Nat} {l : List Item} (h : Has C k l) (j : Nat) {it : Item} (hj : l[j]? = some it) :
    C.items[k + j]? = some it := h j it hj

/-- **An instruction that goes on, without I/O**: one step of the machine
is what it does, the devices as they were. -/
theorem does_step (D : Dev) {C : Code} {k : Nat} {i : Instr} {f : Cpu → Cpu} (hd : Does i f)
    (hk : C.items[k]? = some (.ins i)) {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    mstep D (s, w) = (f s, w) ∧ At C.addrs (k + 1) (f s) ∧ Loaded C (f s) ∧ Sys s (f s) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := step_item C.placed L.1 hk had hpc L.2 (inp := D.bus w) (hd.exec _ s _)
  have hS := hd.sys s
  refine ⟨?_, hst.2 hd.falls, ⟨L.1.congr hS.2.1 hS.1, by rw [hS.2.2.1]; exact L.2⟩, hS⟩
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hst.1, hd.io s, D.quiet]

/-- Two CPUs equal but for the program counter, `R`, the T-states and memory. -/
def Regs (s t : Cpu) : Prop :=
  { s with pc := 0, r := 0, cycles := 0, mem := .empty } = { t with pc := 0, r := 0, cycles := 0, mem := .empty }

theorem Regs.refl (s : Cpu) : Regs s s := rfl
theorem Regs.symm {s t : Cpu} (h : Regs s t) : Regs t s := Eq.symm h
theorem Regs.trans {s t u : Cpu} (h1 : Regs s t) (h2 : Regs t u) : Regs s u := Eq.trans h1 h2

theorem Regs.sp {s t : Cpu} (h : Regs s t) : s.sp = t.sp := by
  have := congrArg Cpu.sp h; exact this

theorem Regs.halted {s t : Cpu} (h : Regs s t) : s.halted = t.halted := by
  have := congrArg Cpu.halted h; exact this

theorem Regs.ramStart {s t : Cpu} (h : Regs s t) : s.ramStart = t.ramStart := by
  have := congrArg Cpu.ramStart h; exact this

theorem Regs.io {s t : Cpu} (h : Regs s t) : s.io = t.io := by
  have := congrArg Cpu.io h; exact this

/-! ## `packHigh`, on the machine -/

/-- The four instructions `packHigh` replaces, one after the other. -/
def fromF (s : Cpu) : Cpu := ldL0 (ldRR 4 5 (ldH0 (ldRA 5 s)))
/-- The two it writes instead. -/
def toF (s : Cpu) : Cpu := ldL0 (ldRA 4 s)

theorem from_regs (s : Cpu) : Regs (fromF s) { s with h := s.a, l := 0, io := .none, eiDelay := false } := by
  cases s
  simp [Regs, fromF, ldL0, ldRR, ldH0, ldRA, op1, Cpu.bumpR, skip, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.idxGet, Cpu.idxSet, Cpu.setHL, Cpu.hl, UInt16.add_assoc]
  rfl

theorem to_regs (s : Cpu) : Regs (toF s) { s with h := s.a, l := 0, io := .none, eiDelay := false } := by
  cases s
  simp [Regs, toF, ldL0, ldRA, op1, Cpu.bumpR, skip, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.idxGet, Cpu.idxSet, Cpu.setHL, Cpu.hl, UInt16.add_assoc]
  rfl

/-- **`packHigh` on the machine**: in `A` the four items of the rewrite
from `kA`, in `B` the two from `kB`; from states equal but for the
program counter, `R`, the T-states and memory, at those items and
running their images, four steps of `A` and two of `B` get to the items
after the rewrite, in states equal in the same way, each with its memory,
stack pointer and devices as they were. -/
theorem packHigh_steps (D : Dev) {A B : Code} {kA kB : Nat}
    (hA : Has A kA (packHighFrom.map .ins)) (hB : Has B kB (packHighTo.map .ins))
    {s t : Cpu} (LA : Loaded A s) (LB : Loaded B t) (atA : At A.addrs kA s) (atB : At B.addrs kB t)
    (hr : Regs s t) (w v : D.W) :
    ∃ s' t', mrun D 4 (s, w) = (s', w) ∧ mrun D 2 (t, v) = (t', v) ∧
      At A.addrs (kA + 4) s' ∧ At B.addrs (kB + 2) t' ∧ Loaded A s' ∧ Loaded B t' ∧ Regs s' t' ∧
      s'.mem = s.mem ∧ t'.mem = t.mem ∧ s'.sp = s.sp ∧ t'.sp = t.sp := by
  obtain ⟨e1, a1, L1, S1⟩ := does_step D does_ld_l_a (hA.get 0 rfl) LA atA w
  obtain ⟨e2, a2, L2, S2⟩ := does_step D does_ld_h_0 (hA.get 1 rfl) L1 a1 w
  obtain ⟨e3, a3, L3, S3⟩ := does_step D does_ld_h_l (hA.get 2 rfl) L2 a2 w
  obtain ⟨e4, a4, L4, S4⟩ := does_step D does_ld_l_0 (hA.get 3 rfl) L3 a3 w
  obtain ⟨f1, b1, M1, T1⟩ := does_step D does_ld_h_a (hB.get 0 rfl) LB atB v
  obtain ⟨f2, b2, M2, T2⟩ := does_step D does_ld_l_0 (hB.get 1 rfl) M1 b1 v
  refine ⟨fromF s, toF t, ?_, ?_, a4, b2, L4, M2, ?_, ?_, ?_, ?_, ?_⟩
  · show mrun D 3 (mstep D (s, w)) = _
    rw [e1]; show mrun D 2 (mstep D _) = _
    rw [e2]; show mrun D 1 (mstep D _) = _
    rw [e3]; show mrun D 0 (mstep D _) = _
    rw [e4]; rfl
  · show mrun D 1 (mstep D (t, v)) = _
    rw [f1]; show mrun D 0 (mstep D _) = _
    rw [f2]; rfl
  · refine (from_regs s).trans (Regs.trans ?_ (to_regs t).symm)
    revert hr; cases s; cases t
    simp only [Regs, Cpu.mk.injEq]
    intros; subst_vars; simp_all
  · exact (S1.trans S2 |>.trans S3 |>.trans S4).1
  · exact (T1.trans T2).1
  · exact (S1.trans S2 |>.trans S3 |>.trans S4).2.2.2
  · exact (T1.trans T2).2.2.2

/-- info: 'Ember.Proof.PassSim.packHigh_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms packHigh_steps

end Ember.Proof.PassSim
