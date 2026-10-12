import Ember.Proof.Z80LoopHSpec
import Ember.Z80.Machine

/-!
# Ember.Proof.Z80Machine — the machine the tests run, and the machine of the proofs (plan M7.3)

The proofs about the test harness run the CPU model in a machine that is
the IR's world behind ports (`hbus`, `hdev`).  The tests run
`Ember.Z80.Machine`.  Here the two are tied: `Sim` relates a `Machine`
in harness mode — nothing on the serial line, no interrupt pending — to
a world and a latch, and `step_sim` says one `Machine.step` is one step
of the proofs' machine, the relation kept.
-/

namespace Ember.Proof.Z80Gen.LoopH
open Ember Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Proof.Refine (callN)
open Ember.Lang (World)
open Ember.Trace (Input)

/-- Where the next item of input is: exhausted chunks skipped. -/
def normPos (inputs : Array Input) (pos off : Nat) : Nat × Nat :=
  if h : pos < inputs.size then
    match inputs[pos] with
    | .rx b => if off ≥ b.size then normPos inputs (pos + 1) 0 else (pos, off)
    | .tick => (pos, off)
  else (pos, off)
termination_by inputs.size - pos

theorem mnorm : ∀ (n : Nat) (m : Machine), n = m.inputs.size - m.ipos →
    m.normalize = { m with ipos := (normPos m.inputs m.ipos m.ioff).1, ioff := (normPos m.inputs m.ipos m.ioff).2 } := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m hn
    rw [Machine.normalize, normPos]
    by_cases h : m.ipos < m.inputs.size
    · simp only [h, dite_true]
      cases hx : m.inputs[m.ipos] with
      | tick => rfl
      | rx b =>
        simp only
        by_cases ho : m.ioff ≥ b.size
        · simp only [ho, if_true]
          rw [ih (m.inputs.size - (m.ipos + 1)) (by omega) { m with ipos := m.ipos + 1, ioff := 0 } rfl]
        · simp only [ho, if_false]
    · simp only [h, dite_false]

theorem wnorm : ∀ (n : Nat) (w : World), n = w.inputs.size - w.pos → w.framed = false →
    w.normalize = { w with pos := (normPos w.inputs w.pos w.off).1, off := (normPos w.inputs w.pos w.off).2 } := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hn hf
    obtain ⟨inputs, pos, off, cur, events, frame, mmio, framed⟩ := w
    simp only at hf hn
    subst hf
    rw [World.normalize, normPos]
    simp only [Bool.false_eq_true, if_false]
    by_cases h : pos < inputs.size
    · simp only [h, dite_true]
      cases hx : inputs[pos] with
      | tick => rfl
      | rx b =>
        simp only
        by_cases ho : off ≥ b.size
        · simp only [ho, if_true]
          rw [ih (inputs.size - (pos + 1)) (by omega) _ rfl rfl]
        · simp only [ho, if_false]
    · simp only [h, dite_false]

/-- An event the harness recorded, as the IR's world has it: a drop by
the name of its reason.  (Notes and the trap are not followed.) -/
def evOf (c : IR.Ctx) : HEvent → Option Trace.Event
  | .tx b => some (.tx b)
  | .drop k => some (.drop (c.dropReasons.getD k.toNat s!"code-{k.toNat}"))
  | _ => none

def evsOf (c : IR.Ctx) (es : Array (Nat × HEvent)) : Array (Nat × Trace.Event) :=
  es.filterMap fun e => (evOf c e.2).map fun x => (e.1, x)

/-- **The relation**: a `Machine` in harness mode with nothing on the
serial line and no interrupt pending, and the world and latch it stands
for. -/
structure Sim (c : IR.Ctx) (m : Machine) (w : World × UInt8) : Prop where
  harness : m.harness = true
  noRx : m.rxQueue.size ≤ m.rxPos
  rdrf : m.rdrf = false
  tick : m.tickPending = false
  prog : m.program = 0
  inputs : m.inputs = w.1.inputs
  pos : m.ipos = w.1.pos
  off : m.ioff = w.1.off
  cur : m.cur = w.1.cur
  latch : m.latch = w.2
  frame : m.frame = w.1.frame
  framed : w.1.framed = false
  events : evsOf c m.events = w.1.events

/-- The world with its position moved, an item taken. -/
def wTook (w : World) (x : Nat) (p : Nat × Nat) : World := { w with cur := x, pos := p.1, off := p.2 }
def wAt (w : World) (p : Nat × Nat) : World := { w with pos := p.1, off := p.2 }

/-- `World.next`, by where the next item is. -/
theorem next_eq (w : World) (hf : w.framed = false) :
    w.next =
      (if h : (normPos w.inputs w.pos w.off).1 < w.inputs.size then
        match w.inputs[(normPos w.inputs w.pos w.off).1] with
        | .tick => (0x0100, wTook w (normPos w.inputs w.pos w.off).1
            (normPos w.inputs ((normPos w.inputs w.pos w.off).1 + 1) 0))
        | .rx b => ((b.get! (normPos w.inputs w.pos w.off).2).toUInt16, wTook w (normPos w.inputs w.pos w.off).1
            (normPos w.inputs (normPos w.inputs w.pos w.off).1 ((normPos w.inputs w.pos w.off).2 + 1)))
      else (0xFFFF, wAt w (normPos w.inputs w.pos w.off))) := by
  unfold World.next wTook wAt
  simp only
  rw [wnorm _ w rfl hf]
  simp only
  by_cases h : (normPos w.inputs w.pos w.off).1 < w.inputs.size
  · simp only [h, dite_true]
    cases hx : w.inputs[(normPos w.inputs w.pos w.off).1] with
    | tick =>
      simp only
      congr 1
      exact wnorm _ _ rfl hf
    | rx b =>
      simp only
      congr 1
      exact wnorm _ _ rfl hf
  · simp only [h, dite_false]

def mTook (m : Machine) (x : Nat) (l : UInt8) (p : Nat × Nat) : Machine := { m with cur := x, latch := l, ipos := p.1, ioff := p.2 }
def mAt (m : Machine) (p : Nat × Nat) : Machine := { m with ipos := p.1, ioff := p.2 }

theorem peek_eq (m : Machine) :
    m.peekInput =
      (if h : (normPos m.inputs m.ipos m.ioff).1 < m.inputs.size then
        match m.inputs[(normPos m.inputs m.ipos m.ioff).1] with
        | .tick => ((1 : UInt8), (0 : UInt8))
        | .rx b => (0, b[(normPos m.inputs m.ipos m.ioff).2]!)
      else (2, 0)) := by
  unfold Machine.peekInput
  simp only
  rw [mnorm _ m rfl]
  simp only
  by_cases h : (normPos m.inputs m.ipos m.ioff).1 < m.inputs.size
  · simp only [h, dite_true, ge_iff_le, Nat.not_le.mpr h, if_false, getElem!_pos]
    cases hx : m.inputs[(normPos m.inputs m.ipos m.ioff).1] <;> rfl
  · simp only [h, dite_false, ge_iff_le, Nat.le_of_not_lt h, if_true]

theorem take_eq (m : Machine) :
    m.takeInput =
      (if h : (normPos m.inputs m.ipos m.ioff).1 < m.inputs.size then
        match m.inputs[(normPos m.inputs m.ipos m.ioff).1] with
        | .tick => mTook m (normPos m.inputs m.ipos m.ioff).1 m.latch
            (normPos m.inputs ((normPos m.inputs m.ipos m.ioff).1 + 1) 0)
        | .rx b => mTook m (normPos m.inputs m.ipos m.ioff).1 b[(normPos m.inputs m.ipos m.ioff).2]!
            (normPos m.inputs (normPos m.inputs m.ipos m.ioff).1 ((normPos m.inputs m.ipos m.ioff).2 + 1))
      else mAt m (normPos m.inputs m.ipos m.ioff)) := by
  unfold Machine.takeInput mTook mAt
  simp only
  rw [mnorm _ m rfl]
  simp only
  by_cases h : (normPos m.inputs m.ipos m.ioff).1 < m.inputs.size
  · simp only [h, dite_true, ge_iff_le, Nat.not_le.mpr h, if_false, getElem!_pos]
    cases hx : m.inputs[(normPos m.inputs m.ipos m.ioff).1] with
    | tick =>
      simp only
      exact mnorm _ _ rfl
    | rx b =>
      simp only
      exact mnorm _ _ rfl
  · simp only [h, dite_false, ge_iff_le, Nat.le_of_not_lt h, if_true]

theorem ba_getElem! (b : ByteArray) (i : Nat) : b[i]! = b.get! i := by
  obtain ⟨bs⟩ := b
  by_cases h : i < bs.size
  · have h' : i < (ByteArray.mk bs).size := h
    rw [getElem!_pos (ByteArray.mk bs) i h']
    simp [ByteArray.get!, h]
    rfl
  · have h' : ¬ i < (ByteArray.mk bs).size := h
    rw [getElem!_neg (ByteArray.mk bs) i h']
    simp [ByteArray.get!, h]

theorem u8_to16_lt (b : UInt8) : b.toUInt16.toNat < 256 := by
  rw [UInt8.toNat_toUInt16]
  exact b.toNat_lt

/-- What the machine answers at `0xD1` is what the proofs' machine answers. -/
theorem kind_sim {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) : m.peekInput.1 = kindOf w.1 := by
  rw [peek_eq]
  unfold kindOf
  rw [next_eq _ S.framed]
  simp only [S.inputs, S.pos, S.off]
  by_cases h : (normPos w.1.inputs w.1.pos w.1.off).1 < w.1.inputs.size
  · simp only [h, dite_true]
    cases hx : w.1.inputs[(normPos w.1.inputs w.1.pos w.1.off).1] with
    | tick => rfl
    | rx b =>
      simp only
      have hlt := u8_to16_lt (b.get! (normPos w.1.inputs w.1.pos w.1.off).2)
      have h1 : (b.get! (normPos w.1.inputs w.1.pos w.1.off).2).toUInt16 ≠ 0xFFFF := by
        intro e
        rw [e] at hlt
        exact absurd hlt (by decide)
      have h2 : (b.get! (normPos w.1.inputs w.1.pos w.1.off).2).toUInt16 ≠ 0x0100 := by
        intro e
        rw [e] at hlt
        exact absurd hlt (by decide)
      simp only [h1, h2, if_false]
  · simp only [h, dite_false]
    rfl

/-- A read of `0xD1`: the machine takes the next item as the proofs' machine does. -/
theorem take_sim {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) :
    Sim c m.takeInput (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2) := by
  rw [take_eq, next_eq _ S.framed]
  simp only [S.inputs, S.pos, S.off]
  by_cases h : (normPos w.1.inputs w.1.pos w.1.off).1 < w.1.inputs.size
  · simp only [h, dite_true]
    cases hx : w.1.inputs[(normPos w.1.inputs w.1.pos w.1.off).1] with
    | tick =>
      simp only
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, rfl, S.latch, S.frame, S.framed, S.events⟩
    | rx b =>
      simp only
      refine ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, rfl, ?_, S.frame, S.framed, S.events⟩
      simp only [u8_to16_lt, if_true]
      show b[(normPos w.1.inputs w.1.pos w.1.off).2]! = lo (b.get! _).toUInt16
      apply UInt8.toNat_inj.mp
      show _ = (b.get! _).toUInt16.toUInt8.toNat
      rw [UInt16.toNat_toUInt8, UInt8.toNat_toUInt16]
      have := (b.get! (normPos w.1.inputs w.1.pos w.1.off).2).toNat_lt
      rw [Nat.mod_eq_of_lt (by omega), ba_getElem!]
  · simp only [h, dite_false]
    exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, S.cur, S.latch, S.frame, S.framed, S.events⟩

/-- The relation does not look at the CPU, the ACIA's registers or the debug port. -/
theorem Sim.of_eq {c : IR.Ctx} {m m' : Machine} {w : World × UInt8} (S : Sim c m w) (h1 : m'.harness = m.harness)
    (h2 : m'.rxQueue = m.rxQueue) (h3 : m'.rxPos = m.rxPos) (h4 : m'.rdrf = false) (h5 : m'.tickPending = false)
    (h6 : m'.program = m.program) (h7 : m'.inputs = m.inputs) (h8 : m'.ipos = m.ipos) (h9 : m'.ioff = m.ioff)
    (h10 : m'.cur = m.cur) (h11 : m'.latch = m.latch) (h12 : m'.frame = m.frame) (h13 : m'.events = m.events) :
    Sim c m' w :=
  ⟨by rw [h1]; exact S.harness, by rw [h2, h3]; exact S.noRx, h4, h5, by rw [h6]; exact S.prog,
    by rw [h7]; exact S.inputs, by rw [h8]; exact S.pos, by rw [h9]; exact S.off, by rw [h10]; exact S.cur,
    by rw [h11]; exact S.latch, by rw [h12]; exact S.frame, S.framed, by rw [h13]; exact S.events⟩

theorem bus_sim {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) :
    (fun p : UInt16 =>
      match p.toUInt8 with
      | 0xD0 => if m.peekInput.1 == 2 then 0 else 1
      | 0xD1 => m.peekInput.1
      | 0xD2 => m.latch
      | 0xD8 => m.program
      | _ => 0xFF) = hbus w := by
  funext p
  rw [kind_sim S, S.latch, S.prog]
  unfold hbus
  show _ = (if p.toUInt8 = 0xD0 then _ else if p.toUInt8 = 0xD1 then _ else if p.toUInt8 = 0xD2 then _
    else if p.toUInt8 = 0xD8 then _ else _)
  split <;> simp_all

theorem evsOf_push (c : IR.Ctx) (es : Array (Nat × HEvent)) (i : Nat) (e : HEvent) :
    evsOf c (es.push (i, e)) = match evOf c e with
      | some x => (evsOf c es).push (i, x)
      | none => evsOf c es := by
  unfold evsOf
  cases h : evOf c e <;> simp [Array.filterMap_push, h]

theorem ofNat_toNat_mod (v : UInt8) : UInt8.ofNat (v.toNat % 256) = v := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  have := v.toNat_lt
  omega

/-- The machine after the CPU's step, before what the step did on the bus is applied. -/
def afterCpu (m : Machine) (w : World × UInt8) : Machine := { m with cpu := m.cpu.step (hbus w) }

theorem step_eq {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) :
    m.step = (afterCpu m w).applyIo := by
  have hrx : m.rxDue = false := by
    simp [Machine.rxDue, Nat.not_lt.mpr S.noRx]
  have hirq : m.irq = false := by simp [Machine.irq, S.rdrf, S.tick]
  have hlt : decide (m.rxPos < m.rxQueue.size) = false := by simp [Nat.not_lt.mpr S.noRx]
  unfold Machine.step
  simp only [hrx, Bool.false_eq_true, if_false, hirq, Bool.false_and, hlt, Bool.and_false, S.harness, if_true]
  unfold Machine.modifyCpu afterCpu
  simp only
  congr 3
  funext p
  rw [kind_sim S, S.latch, S.prog]
  unfold hbus
  have hl : lo p = p.toUInt8 := rfl
  rw [hl]
  split <;> simp_all

/-- What the CPU did on the bus does to the machine what it does to the proofs' machine. -/
theorem io_sim {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) (c' : Cpu) :
    Sim c ({ m with cpu := c' } : Machine).applyIo (hdev c w c'.io) := by
  have S' : Sim c ({ m with cpu := c' } : Machine) w := S.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl
  unfold Machine.applyIo
  simp only
  cases hio : c'.io with
  | none => exact S'
  | read port =>
    simp only
    have hl : lo port = port.toUInt8 := rfl
    split
    · rename_i h
      have : hdev c w (.read port) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl rfl S.tick rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h
      have : hdev c w (.read port) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h
      have : hdev c w (.read port) = (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2) := by
        simp [hdev, hl, h]
      rw [this]
      exact take_sim S'
    · rename_i h1 h2 h3
      have : hdev c w (.read port) = w := by
        simp only [hdev, hl]
        rw [if_neg (fun e => h3 e)]
      rw [this]
      exact S'
  | write port v =>
    simp only
    have hl : lo port = port.toUInt8 := rfl
    split
    · -- 0xD3: a byte of the frame
      rename_i h
      have : hdev c w (.write port v) = ((IR.Sem.effect c w.1 .outByte [v.toNat]).2, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, by
        show m.frame.push v = w.1.frame.push (UInt8.ofNat (v.toNat % 256))
        rw [ofNat_toNat_mod, S.frame], S.framed, S.events⟩
    · -- 0xD4: the end of the frame
      rename_i h
      have : hdev c w (.write port v) = ((IR.Sem.effect c w.1 .outEnd []).2, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, rfl, S.framed, by
        show evsOf c (m.events.push (m.cur, .tx m.frame)) = w.1.events.push (w.1.cur, .tx w.1.frame)
        rw [evsOf_push]
        show (evsOf c m.events).push (m.cur, .tx m.frame) = _
        rw [S.events, S.cur, S.frame]⟩
    · -- 0xD5: a drop
      rename_i h
      have : hdev c w (.write port v) = ((IR.Sem.effect c w.1 .drop [v.toNat]).2, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .drop v)) =
          w.1.events.push (w.1.cur, .drop (c.dropReasons.getD v.toNat s!"code-{v.toNat}"))
        rw [evsOf_push]
        show (evsOf c m.events).push (m.cur, .drop _) = _
        rw [S.events, S.cur]⟩
    · -- 0xD6: a note (not followed)
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .note v)) = _
        rw [evsOf_push]
        exact S.events⟩
    · -- 0xD7: the trap (not followed)
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .trap)) = _
        rw [evsOf_push]
        exact S.events⟩
    · -- the ACIA's control register
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      split
      · exact S'.of_eq rfl rfl rfl rfl S.tick rfl rfl rfl rfl rfl rfl rfl rfl
      · exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl
    · -- the ACIA's data register
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl
    · -- the debug port
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h1 h2 h3 h4 h5 h6 h7 h8
      have : hdev c w (.write port v) = w := by
        simp only [hdev, hl]
        rw [if_neg (fun e => h1 e), if_neg (fun e => h2 e), if_neg (fun e => h3 e)]
      rw [this]
      exact S'

/-- **One step of the machine the tests run is one step of the proofs'
machine**, the relation kept: the CPU steps with the same answers on the
bus, and what it did on the bus does the same to both. -/
theorem step_sim {c : IR.Ctx} {m : Machine} {w : World × UInt8} (S : Sim c m w) :
    m.step.cpu = m.cpu.step (hbus w) ∧ Sim c m.step (hdev c w (m.cpu.step (hbus w)).io) := by
  rw [step_eq S]
  refine ⟨?_, io_sim S _⟩
  unfold afterCpu Machine.applyIo
  simp only
  split
  · rfl
  · split <;> first | rfl | (simp only [take_eq]; split <;> first | rfl | (split <;> rfl))
  · split <;> first | rfl | (split <;> rfl)


/-! ## Runs -/

/-- `n` steps of the machine the tests run. -/
def mrun : Nat → Machine → Machine
  | 0, m => m
  | n + 1, m => mrun n m.step

/-- **A run of the machine the tests run is a run of the proofs' machine.** -/
theorem run_sim (a : Assembled) (addrs : List Nat) : ∀ (n : Nat) (m : Machine) (w : World × UInt8), Sim img.ctx m w →
    (mrun n m).cpu = (wrun (Zof a addrs) n (m.cpu, w)).1 ∧
      Sim img.ctx (mrun n m) (wrun (Zof a addrs) n (m.cpu, w)).2
  | 0, _, _, S => ⟨rfl, S⟩
  | n + 1, m, w, S => by
    obtain ⟨hc, S1⟩ := step_sim S
    obtain ⟨h1, h2⟩ := run_sim a addrs n m.step _ S1
    have e : wstep (Zof a addrs) (m.cpu, w) = (m.step.cpu, hdev img.ctx w (m.cpu.step (hbus w)).io) := by
      show (m.cpu.step (hbus w), hdev img.ctx w (m.cpu.step (hbus w)).io) = _
      rw [hc]
    show (mrun n m.step).cpu = (wrun (Zof a addrs) n (wstep (Zof a addrs) (m.cpu, w))).1 ∧
      Sim img.ctx (mrun n m.step) (wrun (Zof a addrs) n (wstep (Zof a addrs) (m.cpu, w))).2
    rw [e]
    exact ⟨h1, h2⟩

/-- The machine as the tests set it up for a run of the harness: the
CPU at reset with the image in ROM, the input given, nothing recorded,
nothing on the serial line. -/
structure Reset (a : Assembled) (inputs : Array Input) (m : Machine) : Prop where
  pc : m.cpu.pc.toNat = 0
  img : Img a 0 m.cpu
  run : m.cpu.halted = false
  rs : m.cpu.ramStart.toNat = 0x8000
  msz : m.cpu.mem.size = 65536
  harness : m.harness = true
  noRx : m.rxQueue.size ≤ m.rxPos
  rdrf : m.rdrf = false
  tick : m.tickPending = false
  prog : m.program = 0
  inputs : m.inputs = inputs
  pos : m.ipos = 0
  off : m.ioff = 0
  cur : m.cur = 0
  latch : m.latch = 0
  frame : m.frame = ByteArray.empty
  events : m.events = #[]

/-- **The loopback image on the machine the tests run.**  `Machine.step`
from reset, for any input: `j` calls of `main` end in the Ember
semantics, and after some number of steps the machine stands for their
world (`Sim`: the input position, the frame, the events recorded — a
drop by the name of its reason) with the CPU at the head of the loop;
or it stopped (`di; halt`) after `i ≤ j` calls, standing for the world
of those, the input used up or the loop's count of idle calls full. -/
theorem loopH_machine (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (m : Machine), Reset a inputs m →
        ∀ j : Nat, ∃ (st' : Lang.Sem.St) (n : Nat) (w' : World × UInt8),
          callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧ Sim img.ctx (mrun n m) w' ∧
          ((At addrs 176 (mrun n m).cpu ∧ (mrun n m).cpu.sp = 0 ∧ w'.1 = st'.world) ∨
           (∃ i sti, i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
              (mrun n m).cpu.halted = true ∧ (mrun n m).cpu.iff1 = false ∧ w'.1 = sti.world ∧
              (sti.world.next.1 = 0xFFFF ∨ Idle sti.world))) := by
  obtain ⟨a, addrs, ha, hspec⟩ := loopH_spec p S
  refine ⟨a, addrs, ha, fun inputs m R j => ?_⟩
  have S0 : Sim img.ctx m ((st0 inputs).world, 0) :=
    ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.frame, rfl, by
      rw [R.events]
      rfl⟩
  obtain ⟨st', hj, hcase⟩ := hspec inputs m.cpu R.pc R.img R.run R.rs R.msz j
  rcases hcase with ⟨s', w', ⟨n, hn⟩, hat, hsp, hw⟩ | ⟨i, sti, s', w', hi, hci, ⟨n, hn⟩, hh, hif, hw, hwhy⟩
  · obtain ⟨hc, Sn⟩ := run_sim a addrs n m _ S0
    rw [hn] at hc Sn
    exact ⟨st', n, w', hj, Sn, Or.inl ⟨by rw [hc]; exact hat, by rw [hc]; exact hsp, hw⟩⟩
  · obtain ⟨hc, Sn⟩ := run_sim a addrs n m _ S0
    rw [hn] at hc Sn
    exact ⟨st', n, w', hj, Sn, Or.inr ⟨i, sti, hi, hci, by rw [hc]; exact hh, by rw [hc]; exact hif, hw, hwhy⟩⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_machine

/-! ## The machine as the tests build it -/

theorem load_fold (bytes : ByteArray) (m0 : ByteArray) (h0 : m0.size = 65536) :
    ∀ n, n ≤ bytes.size → n ≤ 65536 →
      ((List.range n).foldl (fun m k => if 0 + k < 65536 then m.set! (0 + k) bytes[k]! else m) m0).size = 65536 ∧
      ∀ x, x < n →
        ((List.range n).foldl (fun m k => if 0 + k < 65536 then m.set! (0 + k) bytes[k]! else m) m0).get! x =
          bytes.get! x
  | 0, _, _ => ⟨h0, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  | n + 1, h1, h2 => by
    obtain ⟨hsz, hget⟩ := load_fold bytes m0 h0 n (by omega) (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add]
    rw [if_pos (by omega)]
    refine ⟨by rw [set_size]; simpa using hsz, fun x hx => ?_⟩
    by_cases hxn : x = n
    · rw [hxn, getBang_same _ _ _ (by simp only [Nat.zero_add] at hsz; omega), ba_getElem!]
    · rw [getBang_set _ _ _ _ (fun e => hxn e.symm)]
      simpa using hget x (by omega)

/-- The machine `Ember.Tools.Z80.machineOf` builds of an image, set up
as `Target.runHarness` sets it up for the first program of the image. -/
def harnessMachine (a : Assembled) (inputs : Array Input) : Machine :=
  { cpu := { (({} : Cpu).load 0 a.bytes) with ramStart := 0x8000 }, harness := true, inputs := inputs, program := 0 }

theorem harness_reset (a : Assembled) (inputs : Array Input) (hsz : a.bytes.size ≤ 0x8000) :
    Reset a inputs (harnessMachine a inputs) := by
  have hm0 : (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).size = 65536 := by simp [ByteArray.size]
  obtain ⟨hs, hg⟩ := load_fold a.bytes _ hm0 a.bytes.size (Nat.le_refl _) (by omega)
  refine ⟨rfl, ⟨by show 0 + a.bytes.size ≤ (0x8000 : UInt16).toNat; simpa using hsz, fun x b hx => ?_⟩, rfl, rfl, hs,
    rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlt : x < a.bytes.size := by
    rcases Nat.lt_or_ge x a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [Nat.zero_add]
  refine Eq.trans (hg x hlt) ?_
  clear hg hs
  generalize a.bytes = B at hx hlt
  obtain ⟨bs⟩ := B
  have hlt' : x < bs.size := hlt
  simp only [ByteArray.get!]
  rw [Array.getElem?_eq_getElem hlt'] at hx
  cases hx
  simp [hlt']

/-- **The loopback image, loaded and run as the tests do.**  The image
`assemble` makes of `LoopH.items`, loaded into the CPU model at 0 with
RAM from `0x8000`, in `Ember.Z80.Machine` in harness mode with any
input: what `loopH_machine` says of `Machine.step` from there. -/
theorem loopH_harness (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (j : Nat), ∃ (st' : Lang.Sem.St) (n : Nat) (w' : World × UInt8),
        callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧
        Sim img.ctx (mrun n (harnessMachine a inputs)) w' ∧
        ((At addrs 176 (mrun n (harnessMachine a inputs)).cpu ∧ w'.1 = st'.world) ∨
         (∃ i sti, i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
            (mrun n (harnessMachine a inputs)).cpu.halted = true ∧ w'.1 = sti.world ∧
            (sti.world.next.1 = 0xFFFF ∨ Idle sti.world))) := by
  obtain ⟨a, addrs, ha, hm⟩ := loopH_machine p S
  have hsz : a.bytes.size ≤ 0x8000 := by
    have h : (match assemble items with | .ok a => decide (a.bytes.size ≤ 0x8000) | .error _ => false) = true := by
      decide +kernel
    have ha' : assemble items = .ok a := ha
    rw [ha'] at h
    simpa using h
  refine ⟨a, addrs, ha, fun inputs j => ?_⟩
  obtain ⟨st', n, w', hj, Sn, hcase⟩ := hm inputs _ (harness_reset a inputs hsz) j
  refine ⟨st', n, w', hj, Sn, ?_⟩
  rcases hcase with ⟨hat, _, hw⟩ | ⟨i, sti, hi, hci, hh, _, hw, hwhy⟩
  · exact Or.inl ⟨hat, hw⟩
  · exact Or.inr ⟨i, sti, hi, hci, hh, hw, hwhy⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_harness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_harness

end Ember.Proof.Z80Gen.LoopH
