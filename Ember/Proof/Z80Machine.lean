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

/-- An event the harness recorded, as the IR's world has it: a drop by
the name of its reason, a note by its name and with its value.  (A trap
is no event of the world: the world records it in `trapped`, and `Sim`
ties that to `trapIn`.) -/
def evOf (c : IR.Ctx) : HEvent → Option Trace.Event
  | .tx b => some (.tx b)
  | .drop k => some (.drop (c.dropReasons.getD k.toNat s!"code-{k.toNat}"))
  | .note k x => some (.note s!"{c.notes.getD k.toNat s!"note-{k.toNat}"} {x}")
  | .trap => none

def evsOf (c : IR.Ctx) (es : Array (Nat × HEvent)) : Array (Nat × Trace.Event) :=
  es.filterMap fun e => (evOf c e.2).map fun x => (e.1, x)

/-- Whether the harness recorded a trap. -/
def trapIn (es : Array (Nat × HEvent)) : Bool := es.any fun e => e.2 matches .trap

theorem trapIn_push (es : Array (Nat × HEvent)) (i : Nat) (e : HEvent) :
    trapIn (es.push (i, e)) = (trapIn es || e matches .trap) := by
  simp [trapIn, Array.any_push]

/-- **The relation**: a `Machine` in harness mode with nothing on the
serial line and no interrupt pending, and the world and latch it stands
for. -/
structure Sim (c : IR.Ctx) (m : Machine) (w : HW) : Prop where
  harness : m.harness = true
  noRx : m.rxQueue.size ≤ m.rxPos
  rdrf : m.rdrf = false
  tick : m.tickPending = false
  prog : m.program = 0
  inputs : m.inputs = w.1.inputs
  pos : m.ipos = w.1.pos
  off : m.ioff = w.1.off
  cur : m.cur = w.1.cur
  latch : m.latch = w.2.1
  mark : m.mark = w.2.2.1
  frame : m.frame = w.1.frame
  framed : w.1.framed = false
  events : evsOf c m.events = w.1.events
  nval : m.nval = w.2.2.2
  /-- The world says a trap was recorded when the harness recorded one. -/
  trapped : w.1.trapped = trapIn m.events

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
theorem kind_sim {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) : m.peekInput.1 = kindOf w.1 := by
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
theorem take_sim {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) :
    Sim c m.takeInput (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2.1, w.2.2) := by
  rw [take_eq, next_eq _ S.framed]
  simp only [S.inputs, S.pos, S.off]
  by_cases h : (normPos w.1.inputs w.1.pos w.1.off).1 < w.1.inputs.size
  · simp only [h, dite_true]
    cases hx : w.1.inputs[(normPos w.1.inputs w.1.pos w.1.off).1] with
    | tick =>
      simp only
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, rfl, S.latch, S.mark, S.frame, S.framed, S.events, S.nval, S.trapped⟩
    | rx b =>
      simp only
      refine ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, rfl, ?_, S.mark, S.frame, S.framed, S.events, S.nval, S.trapped⟩
      simp only [u8_to16_lt, if_true]
      show b[(normPos w.1.inputs w.1.pos w.1.off).2]! = lo (b.get! _).toUInt16
      apply UInt8.toNat_inj.mp
      show _ = (b.get! _).toUInt16.toUInt8.toNat
      rw [UInt16.toNat_toUInt8, UInt8.toNat_toUInt16]
      have := (b.get! (normPos w.1.inputs w.1.pos w.1.off).2).toNat_lt
      rw [Nat.mod_eq_of_lt (by omega), ba_getElem!]
  · simp only [h, dite_false]
    exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, rfl, rfl, S.cur, S.latch, S.mark, S.frame, S.framed, S.events, S.nval, S.trapped⟩

/-- The relation does not look at the CPU, the ACIA's registers or the debug port. -/
theorem Sim.of_eq {c : IR.Ctx} {m m' : Machine} {w : HW} (S : Sim c m w) (h1 : m'.harness = m.harness)
    (h2 : m'.rxQueue = m.rxQueue) (h3 : m'.rxPos = m.rxPos) (h4 : m'.rdrf = false) (h5 : m'.tickPending = false)
    (h6 : m'.program = m.program) (h7 : m'.inputs = m.inputs) (h8 : m'.ipos = m.ipos) (h9 : m'.ioff = m.ioff)
    (h10 : m'.cur = m.cur) (h11 : m'.latch = m.latch) (h12 : m'.frame = m.frame) (h13 : m'.events = m.events)
    (h14 : m'.mark = m.mark) (h15 : m'.nval = m.nval) :
    Sim c m' w :=
  ⟨by rw [h1]; exact S.harness, by rw [h2, h3]; exact S.noRx, h4, h5, by rw [h6]; exact S.prog,
    by rw [h7]; exact S.inputs, by rw [h8]; exact S.pos, by rw [h9]; exact S.off, by rw [h10]; exact S.cur,
    by rw [h11]; exact S.latch, by rw [h14]; exact S.mark, by rw [h12]; exact S.frame, S.framed,
    by rw [h13]; exact S.events, by rw [h15]; exact S.nval, by rw [h13]; exact S.trapped⟩

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
def afterCpu (m : Machine) (w : HW) : Machine := { m with cpu := m.cpu.step (hbus w) }

theorem step_eq {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) :
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
  rw [kind_sim S, S.latch, S.prog, S.pos, S.off, S.mark]
  unfold hbus
  have hl : lo p = p.toUInt8 := rfl
  rw [hl]
  split <;> simp_all

/-- What the CPU did on the bus does to the machine what it does to the proofs' machine. -/
theorem io_sim {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) (c' : Cpu) :
    Sim c ({ m with cpu := c' } : Machine).applyIo (hdev c w c'.io) := by
  have S' : Sim c ({ m with cpu := c' } : Machine) w := S.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      exact S'.of_eq rfl rfl rfl rfl S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h
      have : hdev c w (.read port) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h
      have : hdev c w (.read port) =
          (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2.1, w.2.2) := by
        simp [hdev, hl, h]
      rw [this]
      exact take_sim S'
    · -- 0xD9: the mark
      rename_i h
      have : hdev c w (.read port) = (w.1, w.2.1, (w.1.pos, w.1.off), w.2.2.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, by
        show (m.ipos, m.ioff) = (w.1.pos, w.1.off)
        rw [S.pos, S.off], S.frame, S.framed, S.events, S.nval, S.trapped⟩
    · rename_i h1 h2 h3 h4
      have : hdev c w (.read port) = w := by
        simp only [hdev, hl]
        rw [if_neg (fun e => h3 e), if_neg (fun e => h4 e)]
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
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, by
        show m.frame.push v = w.1.frame.push (UInt8.ofNat (v.toNat % 256))
        rw [ofNat_toNat_mod, S.frame], S.framed, S.events, S.nval, S.trapped⟩
    · -- 0xD4: the end of the frame
      rename_i h
      have : hdev c w (.write port v) = ((IR.Sem.effect c w.1 .outEnd []).2, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, rfl, S.framed, by
        show evsOf c (m.events.push (m.cur, .tx m.frame)) = w.1.events.push (w.1.cur, .tx w.1.frame)
        rw [evsOf_push]
        show (evsOf c m.events).push (m.cur, .tx m.frame) = _
        rw [S.events, S.cur, S.frame], S.nval, by
        show w.1.trapped = trapIn (m.events.push (m.cur, .tx m.frame))
        simp [trapIn_push, S.trapped]⟩
    · -- 0xD5: a drop
      rename_i h
      have : hdev c w (.write port v) = ((IR.Sem.effect c w.1 .drop [v.toNat]).2, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .drop v)) =
          w.1.events.push (w.1.cur, .drop (c.dropReasons.getD v.toNat s!"code-{v.toNat}"))
        rw [evsOf_push]
        show (evsOf c m.events).push (m.cur, .drop _) = _
        rw [S.events, S.cur], S.nval, by
        show w.1.trapped = trapIn (m.events.push (m.cur, .drop v))
        simp [trapIn_push, S.trapped]⟩
    · -- 0xD6: a note, with the value written before it
      rename_i h
      have : hdev c w (.write port v) =
          ((IR.Sem.effect c w.1 .note [v.toNat, w.2.2.2.1]).2, w.2.1, w.2.2.1, (0, 0)) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .note v m.nval.1)) =
          w.1.events.push (w.1.cur, .note s!"{c.notes.getD v.toNat s!"note-{v.toNat}"} {w.2.2.2.1}")
        rw [evsOf_push]
        show (evsOf c m.events).push (m.cur, .note _) = _
        rw [S.events, S.cur, S.nval], rfl, by
        show w.1.trapped = trapIn (m.events.push (m.cur, .note v m.nval.1))
        simp [trapIn_push, S.trapped]⟩
    · -- 0xDA: a byte of the value of the note to come
      rename_i h
      have : hdev c w (.write port v) =
          (w.1, w.2.1, w.2.2.1, (w.2.2.2.1 + v.toNat * 2 ^ (8 * w.2.2.2.2), w.2.2.2.2 + 1)) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, S.frame, S.framed,
        S.events, by
        show (m.nval.1 + v.toNat * 2 ^ (8 * m.nval.2), m.nval.2 + 1) = _
        rw [S.nval], S.trapped⟩
    · -- 0xD7: the trap, recorded in the world (`trapped`; no line of its own)
      rename_i h
      have : hdev c w (.write port v) = ({ w.1 with trapped := true }, w.2) := by simp [hdev, hl, h]
      rw [this]
      exact ⟨S.harness, S.noRx, S.rdrf, S.tick, S.prog, S.inputs, S.pos, S.off, S.cur, S.latch, S.mark, S.frame, S.framed, by
        show evsOf c (m.events.push (m.cur, .trap)) = _
        rw [evsOf_push]
        exact S.events, S.nval, by
        show true = trapIn (m.events.push (m.cur, .trap))
        simp [trapIn_push]⟩
    · -- the ACIA's control register
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      split
      · exact S'.of_eq rfl rfl rfl rfl S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · -- the ACIA's data register
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · -- the debug port
      rename_i h
      have : hdev c w (.write port v) = w := by simp [hdev, hl, h]
      rw [this]
      exact S'.of_eq rfl rfl rfl S.rdrf S.tick rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9
      have : hdev c w (.write port v) = w := by
        simp only [hdev, hl]
        rw [if_neg (fun e => h1 e), if_neg (fun e => h2 e), if_neg (fun e => h3 e), if_neg (fun e => h5 e),
          if_neg (fun e => h4 e), if_neg (fun e => h6 e)]
      rw [this]
      exact S'

/-- **One step of the machine the tests run is one step of the proofs'
machine**, the relation kept: the CPU steps with the same answers on the
bus, and what it did on the bus does the same to both. -/
theorem step_sim {c : IR.Ctx} {m : Machine} {w : HW} (S : Sim c m w) :
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

/-- **A run of the machine the tests run is a run of the proofs' machine**, for any image. -/
theorem run_sim_of (I : ImgIn) (a : Assembled) (addrs : List Nat) : ∀ (n : Nat) (m : Machine) (w : HW),
    Sim I.ctx m w →
    (mrun n m).cpu = (wrun (I.ZH a addrs (0, 0)) n (m.cpu, w)).1 ∧
      Sim I.ctx (mrun n m) (wrun (I.ZH a addrs (0, 0)) n (m.cpu, w)).2
  | 0, _, _, S => ⟨rfl, S⟩
  | n + 1, m, w, S => by
    obtain ⟨hc, S1⟩ := step_sim S
    obtain ⟨h1, h2⟩ := run_sim_of I a addrs n m.step _ S1
    have e : wstep (I.ZH a addrs (0, 0)) (m.cpu, w) = (m.step.cpu, hdev I.ctx w (m.cpu.step (hbus w)).io) := by
      show (m.cpu.step (hbus w), hdev I.ctx w (m.cpu.step (hbus w)).io) = _
      rw [hc]
    show (mrun n m.step).cpu = (wrun (I.ZH a addrs (0, 0)) n (wstep (I.ZH a addrs (0, 0)) (m.cpu, w))).1 ∧
      Sim I.ctx (mrun n m.step) (wrun (I.ZH a addrs (0, 0)) n (wstep (I.ZH a addrs (0, 0)) (m.cpu, w))).2
    rw [e]
    exact ⟨h1, h2⟩

theorem run_sim (a : Assembled) (addrs : List Nat) (n : Nat) (m : Machine) (w : HW) (S : Sim img.ctx m w) :
    (mrun n m).cpu = (wrun (Zof a addrs (0, 0)) n (m.cpu, w)).1 ∧
      Sim img.ctx (mrun n m) (wrun (Zof a addrs (0, 0)) n (m.cpu, w)).2 :=
  run_sim_of img a addrs n m w S

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
  mark : m.mark = (0, 0)
  frame : m.frame = ByteArray.empty
  events : m.events = #[]
  nval : m.nval = (0, 0)

/-- **The loopback image on the machine the tests run.**  `Machine.step`
from reset, for any input: `j` calls of `main` end in the Ember
semantics, and after some number of steps the machine stands for their
world (`Sim`: the input position, the frame, the events recorded — a
drop by the name of its reason) with the CPU at the head of the loop;
or it stopped (`di; halt`) after `i ≤ j` calls, standing for the world
of those, the input used up. -/
theorem loopH_machine (p : Lang.Prog) (S : LoopSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Input) (m : Machine), Reset a inputs m →
        ∀ j : Nat, ∃ (st' : Lang.Sem.St) (n : Nat) (w' : HW),
          callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧ Sim img.ctx (mrun n m) w' ∧
          ((At addrs 174 (mrun n m).cpu ∧ (mrun n m).cpu.sp = 0 ∧ w'.1 = st'.world) ∨
           (∃ i sti, i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
              (mrun n m).cpu.halted = true ∧ (mrun n m).cpu.iff1 = false ∧ w'.1 = sti.world ∧
              sti.world.next.1 = 0xFFFF)) := by
  obtain ⟨a, addrs, ha, hspec⟩ := loopH_spec p S
  refine ⟨a, addrs, ha, fun inputs m R j => ?_⟩
  have S0 : Sim img.ctx m ((st0 inputs).world, 0, (0, 0), (0, 0)) :=
    ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
      rw [R.events]
      rfl, R.nval, by rw [R.events]; show false = _; simp [trapIn]⟩
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
    rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      ∀ (inputs : Array Input) (j : Nat), ∃ (st' : Lang.Sem.St) (n : Nat) (w' : HW),
        callN 366 p "main" j (Lang.Sem.initial p inputs) = some st' ∧
        Sim img.ctx (mrun n (harnessMachine a inputs)) w' ∧
        ((At addrs 174 (mrun n (harnessMachine a inputs)).cpu ∧ w'.1 = st'.world) ∨
         (∃ i sti, i ≤ j ∧ callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧
            (mrun n (harnessMachine a inputs)).cpu.halted = true ∧ w'.1 = sti.world ∧
            sti.world.next.1 = 0xFFFF)) := by
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

/-- **The loopback image, loaded and run as the tests do, processes all
its input and stops.**  For any input: after some number of
`Machine.step`s the CPU is halted (`di; halt`), and the machine stands
for the world that some number of calls of `main` leave in the Ember
semantics — the input position, the frame, the events recorded — with no
input left. -/
theorem loopH_halts (p : Lang.Prog) (S : LoopSrc p) :
    ∃ a : Assembled, assemble items = .ok a ∧
      ∀ inputs : Array Input, ∃ (i : Nat) (sti : Lang.Sem.St) (n : Nat) (w' : HW),
        callN 366 p "main" i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF ∧
        (mrun n (harnessMachine a inputs)).cpu.halted = true ∧
        Sim img.ctx (mrun n (harnessMachine a inputs)) w' ∧ w'.1 = sti.world := by
  obtain ⟨a, addrs, ha, hspec⟩ := loopH_spec_halt p S
  have hsz : a.bytes.size ≤ 0x8000 := by
    have h : (match assemble items with | .ok a => decide (a.bytes.size ≤ 0x8000) | .error _ => false) = true := by
      decide +kernel
    have ha' : assemble items = .ok a := ha
    rw [ha'] at h
    simpa using h
  refine ⟨a, ha, fun inputs => ?_⟩
  have R := harness_reset a inputs hsz
  have S0 : Sim img.ctx (harnessMachine a inputs) ((st0 inputs).world, 0, (0, 0), (0, 0)) :=
    ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
      rw [R.events]
      rfl, R.nval, by rw [R.events]; show false = _; simp [trapIn]⟩
  obtain ⟨i, sti, s', w', hi, hex, ⟨n, hn⟩, hh, _, hw⟩ := hspec inputs _ R.pc R.img R.run R.rs R.msz
  obtain ⟨hc, Sn⟩ := run_sim a addrs n _ _ S0
  rw [hn] at hc Sn
  exact ⟨i, sti, n, w', hi, hex, by rw [hc]; exact hh, Sn, hw⟩

/-- info: 'Ember.Proof.Z80Gen.LoopH.loopH_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopH_halts

end Ember.Proof.Z80Gen.LoopH
