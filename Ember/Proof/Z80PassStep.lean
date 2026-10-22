import Ember.Proof.Z80PassSim
import Ember.Proof.IRMem

/-!
# Ember.Proof.Z80PassStep — one ordinary instruction in two machines (plan M7.3)

The two images (without the passes and with them) are run side by side;
where they run the same instruction, from states that agree, they are
to agree after it.  `Eqv lo hi`: two CPUs equal but for the program
counter, `R`, the T-states, memory and the stack pointer, and their memories equal on
`[lo, hi)` (the RAM below the stack: what the two keep the same; the
ROM differs, so does the stack, which holds return addresses).

`Form`: the forms of the instructions of the stack's images that neither
jump, call, return nor touch the stack (the others have relations of
their own); `ord_eqv`: such an instruction, with the same operands, from states
that agree, gives states that agree — provided the bytes it reads or
writes through `HL`, `DE` or its operand address are in `[lo, hi)`
(a hypothesis: in the image it is a fact about the address, which the
proofs of the image know, not one this lemma can see).

The instruction's operands are the same in both: for an operand that is
a number, or a symbol of the RAM, which both images place alike.  An
operand that is an address in ROM (a literal, the initial values) is not
the same in both; nor is a jump's target.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc

/-- Two CPUs equal but for `pc`, `R`, the T-states, memory and the stack pointer (where the stacks
of the two machines are, and what is on them, is a relation of its own: a call the passes made a
jump leaves one return address less on the stack of the image with the passes). -/
def RegsS (s t : Cpu) : Prop :=
  { s with pc := 0, r := 0, cycles := 0, mem := .empty, sp := 0 } =
    { t with pc := 0, r := 0, cycles := 0, mem := .empty, sp := 0 }

/-- Two CPUs equal but for `pc`, `R`, the T-states, memory and the stack pointer; memories equal on
`[lo, hi)`, of one size. -/
structure Eqv (lo hi : Nat) (s t : Cpu) : Prop where
  regs : RegsS s t
  mem : ∀ x, lo ≤ x → x < hi → s.mem.get! x = t.mem.get! x
  msz : s.mem.size = t.mem.size

theorem regs_iff {s t : Cpu} :
    RegsS s t ↔ t = { s with pc := t.pc, r := t.r, cycles := t.cycles, mem := t.mem, sp := t.sp } := by
  constructor
  · intro h; cases s; cases t; simp only [RegsS, Cpu.mk.injEq] at h ⊢; simp_all
  · intro h; rw [h]; rfl

theorem regs_ex {s t : Cpu} (h : RegsS s t) :
    ∃ p r c m q, t = { s with pc := p, r := r, cycles := c, mem := m, sp := q } :=
  ⟨t.pc, t.r, t.cycles, t.mem, t.sp, regs_iff.mp h⟩

theorem RegsS.ramStart {s t : Cpu} (h : RegsS s t) : s.ramStart = t.ramStart := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h; rfl
theorem RegsS.io {s t : Cpu} (h : RegsS s t) : s.io = t.io := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h; rfl
theorem RegsS.halted {s t : Cpu} (h : RegsS s t) : s.halted = t.halted := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h; rfl
theorem RegsS.hl {s t : Cpu} (h : RegsS s t) : s.hl = t.hl := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h; rfl
theorem RegsS.de {s t : Cpu} (h : RegsS s t) : s.de = t.de := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h; rfl
theorem RegsS.of_regs {s t : Cpu} (h : Regs s t) : RegsS s t := by
  revert h; cases s; cases t; simp only [Regs, RegsS, Cpu.mk.injEq]; intro h; simp_all

/-- The forms of the ordinary instructions of the stack's images (`v`: the operand, a number or a symbol). -/
inductive Form where
  | adcAM
  | sbcAM
  | andM
  | cpM
  | orM
  | incM
  | stA (v : Val)
  | stHL (v : Val)
  | stDEA
  | stHLA
  | stHLN (v : Val)
  | ldAN (v : Val)
  | ldADE
  | ldAHL
  | ldDENN (v : Val)
  | ldHLNN (v : Val)
  | addAC
  | addHLBC
  | addHLDE
  | addHLHL
  | andC
  | andL
  | andN (v : Val)
  | cpC
  | cpN (v : Val)
  | cpl
  | decA
  | decB
  | decBC
  | decC
  | decHL
  | di
  | exDEHL
  | halt
  | inA (v : Val)
  | incA
  | incB
  | incC
  | incDE
  | incHL
  | ldAB
  | ldAC
  | ldAH
  | ldAL
  | ldAI (v : Val)
  | ldBI (v : Val)
  | ldBCI (v : Val)
  | ldCA
  | ldCI (v : Val)
  | ldDH
  | ldDEI (v : Val)
  | ldEL
  | ldHA
  | ldHL2
  | ldHI (v : Val)
  | ldHLI (v : Val)
  | ldLA
  | ldLI (v : Val)
  | orA
  | orC
  | orD
  | orE
  | orH
  | orL
  | orN (v : Val)
  | outA (v : Val)
  | rla
  | rrL
  | sbcHLDE
  | srlA
  | srlH
  | subC
  | xorA
  | xorN (v : Val)
  deriving BEq, Repr

/-- The instruction of a form. -/
def Form.instr : Form → Instr
  | .adcAM => ⟨.adc, [.a, .mhl]⟩
  | .sbcAM => ⟨.sbc, [.a, .mhl]⟩
  | .andM => ⟨.and, [.mhl]⟩
  | .cpM => ⟨.cp, [.mhl]⟩
  | .orM => ⟨.or, [.mhl]⟩
  | .incM => ⟨.inc, [.mhl]⟩
  | .stA v => ⟨.ld, [.mem v, .a]⟩
  | .stHL v => ⟨.ld, [.mem v, .hl]⟩
  | .stDEA => ⟨.ld, [.mde, .a]⟩
  | .stHLA => ⟨.ld, [.mhl, .a]⟩
  | .stHLN v => ⟨.ld, [.mhl, .imm v]⟩
  | .ldAN v => ⟨.ld, [.a, .mem v]⟩
  | .ldADE => ⟨.ld, [.a, .mde]⟩
  | .ldAHL => ⟨.ld, [.a, .mhl]⟩
  | .ldDENN v => ⟨.ld, [.de, .mem v]⟩
  | .ldHLNN v => ⟨.ld, [.hl, .mem v]⟩
  | .addAC => ⟨.add, [.a, .c]⟩
  | .addHLBC => ⟨.add, [.hl, .bc]⟩
  | .addHLDE => ⟨.add, [.hl, .de]⟩
  | .addHLHL => ⟨.add, [.hl, .hl]⟩
  | .andC => ⟨.and, [.c]⟩
  | .andL => ⟨.and, [.l]⟩
  | .andN v => ⟨.and, [.imm v]⟩
  | .cpC => ⟨.cp, [.c]⟩
  | .cpN v => ⟨.cp, [.imm v]⟩
  | .cpl => ⟨.cpl, []⟩
  | .decA => ⟨.dec, [.a]⟩
  | .decB => ⟨.dec, [.b]⟩
  | .decBC => ⟨.dec, [.bc]⟩
  | .decC => ⟨.dec, [.c]⟩
  | .decHL => ⟨.dec, [.hl]⟩
  | .di => ⟨.di, []⟩
  | .exDEHL => ⟨.ex, [.de, .hl]⟩
  | .halt => ⟨.halt, []⟩
  | .inA v => ⟨.in, [.a, .mem v]⟩
  | .incA => ⟨.inc, [.a]⟩
  | .incB => ⟨.inc, [.b]⟩
  | .incC => ⟨.inc, [.c]⟩
  | .incDE => ⟨.inc, [.de]⟩
  | .incHL => ⟨.inc, [.hl]⟩
  | .ldAB => ⟨.ld, [.a, .b]⟩
  | .ldAC => ⟨.ld, [.a, .c]⟩
  | .ldAH => ⟨.ld, [.a, .h]⟩
  | .ldAL => ⟨.ld, [.a, .l]⟩
  | .ldAI v => ⟨.ld, [.a, .imm v]⟩
  | .ldBI v => ⟨.ld, [.b, .imm v]⟩
  | .ldBCI v => ⟨.ld, [.bc, .imm v]⟩
  | .ldCA => ⟨.ld, [.c, .a]⟩
  | .ldCI v => ⟨.ld, [.c, .imm v]⟩
  | .ldDH => ⟨.ld, [.d, .h]⟩
  | .ldDEI v => ⟨.ld, [.de, .imm v]⟩
  | .ldEL => ⟨.ld, [.e, .l]⟩
  | .ldHA => ⟨.ld, [.h, .a]⟩
  | .ldHL2 => ⟨.ld, [.h, .l]⟩
  | .ldHI v => ⟨.ld, [.h, .imm v]⟩
  | .ldHLI v => ⟨.ld, [.hl, .imm v]⟩
  | .ldLA => ⟨.ld, [.l, .a]⟩
  | .ldLI v => ⟨.ld, [.l, .imm v]⟩
  | .orA => ⟨.or, [.a]⟩
  | .orC => ⟨.or, [.c]⟩
  | .orD => ⟨.or, [.d]⟩
  | .orE => ⟨.or, [.e]⟩
  | .orH => ⟨.or, [.h]⟩
  | .orL => ⟨.or, [.l]⟩
  | .orN v => ⟨.or, [.imm v]⟩
  | .outA v => ⟨.out, [.mem v, .a]⟩
  | .rla => ⟨.rla, []⟩
  | .rrL => ⟨.rr, [.l]⟩
  | .sbcHLDE => ⟨.sbc, [.hl, .de]⟩
  | .srlA => ⟨.srl, [.a]⟩
  | .srlH => ⟨.srl, [.h]⟩
  | .subC => ⟨.sub, [.c]⟩
  | .xorA => ⟨.xor, [.a]⟩
  | .xorN v => ⟨.xor, [.imm v]⟩

/-- Does the form read or write memory through `HL`, `DE` or its operand address? -/
def Form.mem : Form → Bool
  | .adcAM => true
  | .sbcAM => true
  | .andM => true
  | .cpM => true
  | .orM => true
  | .incM => true
  | .stA _ => true
  | .stHL _ => true
  | .stDEA => true
  | .stHLA => true
  | .stHLN _ => true
  | .ldAN _ => true
  | .ldADE => true
  | .ldAHL => true
  | .ldDENN _ => true
  | .ldHLNN _ => true
  | .addAC => false
  | .addHLBC => false
  | .addHLDE => false
  | .addHLHL => false
  | .andC => false
  | .andL => false
  | .andN _ => false
  | .cpC => false
  | .cpN _ => false
  | .cpl => false
  | .decA => false
  | .decB => false
  | .decBC => false
  | .decC => false
  | .decHL => false
  | .di => false
  | .exDEHL => false
  | .halt => false
  | .inA _ => false
  | .incA => false
  | .incB => false
  | .incC => false
  | .incDE => false
  | .incHL => false
  | .ldAB => false
  | .ldAC => false
  | .ldAH => false
  | .ldAL => false
  | .ldAI _ => false
  | .ldBI _ => false
  | .ldBCI _ => false
  | .ldCA => false
  | .ldCI _ => false
  | .ldDH => false
  | .ldDEI _ => false
  | .ldEL => false
  | .ldHA => false
  | .ldHL2 => false
  | .ldHI _ => false
  | .ldHLI _ => false
  | .ldLA => false
  | .ldLI _ => false
  | .orA => false
  | .orC => false
  | .orD => false
  | .orE => false
  | .orH => false
  | .orL => false
  | .orN _ => false
  | .outA _ => false
  | .rla => false
  | .rrL => false
  | .sbcHLDE => false
  | .srlA => false
  | .srlH => false
  | .subC => false
  | .xorA => false
  | .xorN _ => false

/-- **An ordinary instruction in two machines**: from CPUs that agree
(`Eqv lo hi`), with the same operands and the same answers of the bus,
the bytes it may read or write at `HL`, `DE` and its operand address in
`[lo, hi)` (in RAM), the instruction gives CPUs that agree. -/
theorem ord_eqv (lo hi : Nat) (hhi : hi ≤ 65536) (f : Form)
    (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (s t : Cpu) (E : Eqv lo hi s t)
    (hhl : f.mem = true → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi) (hde : f.mem = true → lo ≤ s.de.toNat ∧ s.de.toNat < hi)
    (hnn : f.mem = true → lo ≤ nn.toNat ∧ nn.toNat + 1 < hi)
    (s' : Cpu) (hs : execI f.instr n nn s inp = some s') :
    ∃ t', execI f.instr n nn t inp = some t' ∧ Eqv lo hi s' t' := by
  obtain ⟨hr, hm, hsz⟩ := E
  obtain ⟨p, r, c, m, q, rfl⟩ := regs_ex hr
  cases s with
  | mk a f0 b c0 d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r0 iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  cases f
  all_goals
    simp +decide only [Form.instr, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?, Option.some.injEq,
      Option.map_some, if_true, if_false] at hs ⊢
    subst hs
    refine ⟨_, rfl, ?_⟩
  all_goals
    first
    | (have hhl := hhl rfl; have hde := hde rfl; have hnn := hnn rfl
       simp only [Cpu.hl, Cpu.de] at hhl hde
       have e1 : m.get! (mk16 h l).toNat = mem.get! (mk16 h l).toNat := (hm _ hhl.1 hhl.2).symm
       have e4 : m.get! (mk16 d e).toNat = mem.get! (mk16 d e).toNat := (hm _ hde.1 hde.2).symm
       have e2 : m.get! nn.toNat = mem.get! nn.toNat := (hm _ hnn.1 (by omega)).symm
       have e3 : m.get! (nn + 1).toNat = mem.get! (nn + 1).toNat := by
         have : (nn + 1).toNat = nn.toNat + 1 := by rw [UInt16.toNat_add]; simp; omega
         rw [this]; exact (hm _ (by omega) hnn.2).symm
       simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp,
         Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.rd, Cpu.wr, Cpu.wr16, Cpu.rd16, Cpu.de, Cpu.flag, Cpu.inc8,
         e1, e2, e3, e4]
       (repeat' split) <;> refine ⟨?_, ?_, ?_⟩ <;>
         first
         | exact rfl
         | exact hm
         | exact hsz
         | (intro x h1 h2; simp only [Ember.Proof.IRSim.get_set, Ember.Proof.IRSim.size_set, hsz]
            (repeat' split) <;> first | rfl | exact hm x h1 h2 | omega)
         | simp only [Ember.Proof.IRSim.size_set, hsz])
    | (simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp, Cpu.rp,
         Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.add16, Cpu.sbc16, Cpu.bc, Cpu.de, Cpu.flag, Cpu.inc8, Cpu.dec8,
         Cpu.rot]
       (repeat' split) <;> exact ⟨rfl, hm, hsz⟩)

/-- An ordinary instruction always does something; it leaves the start of RAM, the size of memory and,
when what it writes is in RAM, the bytes below `ramStart` (the ROM) as they were; only `halt` halts. -/
theorem ord_rom (f : Form) (n : UInt8) (nn : UInt16) (inp : UInt16 → UInt8) (s : Cpu)
    (hhl : f.mem = true → s.ramStart.toNat ≤ s.hl.toNat) (hde : f.mem = true → s.ramStart.toNat ≤ s.de.toNat)
    (hnn : f.mem = true → s.ramStart.toNat ≤ nn.toNat ∧ nn.toNat < 65535) :
    ∃ s', execI f.instr n nn s inp = some s' ∧ s'.ramStart = s.ramStart ∧ s'.mem.size = s.mem.size ∧
      (∀ x, x < s.ramStart.toNat → s'.mem.get! x = s.mem.get! x) ∧ (f ≠ .halt → s'.halted = s.halted) := by
  cases s with
  | mk a f0 b c0 d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r0 iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  cases f
  all_goals
    simp +decide only [Form.instr, execI, exec1, exec2, ldI, aluI, incI, decI, rotI, simpleI, rr?, r8?,
      Option.map_some, if_true, if_false]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  all_goals
    try simp only [op1, op2, skip, Cpu.bumpR, Cpu.tick, Cpu.setReg, Cpu.reg, Cpu.setHL, Cpu.hl, Cpu.setRp,
      Cpu.idxGet, Cpu.idxSet, Cpu.alu, Cpu.add16, Cpu.sbc16, Cpu.rd, Cpu.wr, Cpu.wr16, Cpu.rd16, Cpu.de, Cpu.flag,
      Cpu.inc8, Cpu.dec8, Cpu.rot, Cpu.setBC, Cpu.setDE, Cpu.rp, Ember.Proof.IRSim.size_set]
  all_goals
    first
    | trivial
    | (intro _; trivial)
    | (intro _ _; trivial)
    | (intro _; rfl)
    | (intro hne; exact absurd rfl hne)
    | (((repeat' split) <;> simp only [Ember.Proof.IRSim.size_set]) <;> done)
    | ((repeat' split) <;> first | (intro _; trivial) | (intro _; rfl))
    | (have hhl := hhl rfl; have hde := hde rfl; have hnn := hnn rfl
       simp only [Cpu.hl, Cpu.de] at hhl hde
       intro x hx
       (repeat' split) <;> simp only [Ember.Proof.IRSim.get_set] <;> (repeat' split) <;>
         first | rfl | (simp only [UInt16.lt_iff_toNat_lt, UInt16.toNat_add] at *; omega))
    | ((repeat' split) <;> intro x hx <;> rfl)

theorem ord_falls (f : Form) : f.instr.falls = true := by
  cases f <;> rfl

/-- What a step leaves of the image: the same start of RAM and the same ROM. -/
theorem Loaded.keep {C : Code} {s s' : Cpu} (L : Loaded C s) (hr : s'.ramStart = s.ramStart)
    (hm : ∀ x, x < s.ramStart.toNat → s'.mem.get! x = s.mem.get! x) (hh : s'.halted = false) : Loaded C s' := by
  refine ⟨⟨by rw [hr]; exact L.1.rom, fun x b hb => ?_⟩, hh⟩
  have hlt : x < C.a.bytes.size := by
    rcases Nat.lt_or_ge x C.a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hb; cases hb
  have := L.1.rom
  rw [hm _ (by omega)]
  exact L.1.bytes x b hb

/-- **An ordinary instruction, a step of each machine**: in `A` at item
`kA` and in `B` at item `kB` the same instruction of a form of `Form`,
with the same operand in both (`hop`: a number, or a symbol both images
place alike); from CPUs that agree (`Eqv lo hi`, `lo` in RAM), running
their images, the bytes the instruction reads or writes in `[lo, hi)`:
one step of each machine, the devices in the same state, gives CPUs
that agree, at the items after, running their images (not `halt`). -/
theorem ord_mstep (D : Dev) {A B : Code} {kA kB : Nat} (f : Form) (hnh : f ≠ .halt) (lo hi : Nat)
    (hhi : hi ≤ 65536) (hA : A.items[kA]? = some (.ins f.instr)) (hB : B.items[kB]? = some (.ins f.instr))
    (hop : ∀ pa pb, f.instr.immB (A.a.env pa) = f.instr.immB (B.a.env pb) ∧
      f.instr.immW (A.a.env pa) = f.instr.immW (B.a.env pb))
    {s t : Cpu} (LA : Loaded A s) (LB : Loaded B t) (atA : At A.addrs kA s) (atB : At B.addrs kB t)
    (E : Eqv lo hi s t) (hlo : s.ramStart.toNat ≤ lo)
    (hhl : f.mem = true → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi) (hde : f.mem = true → lo ≤ s.de.toNat ∧ s.de.toNat < hi)
    (hnn : ∀ pa, f.mem = true → lo ≤ (f.instr.immW (A.a.env pa)).toNat ∧ (f.instr.immW (A.a.env pa)).toNat + 1 < hi)
    (w : D.W) :
    ∃ s' t' w', mstep D (s, w) = (s', w') ∧ mstep D (t, w) = (t', w') ∧ Eqv lo hi s' t' ∧
      At A.addrs (kA + 1) s' ∧ At B.addrs (kB + 1) t' ∧ Loaded A s' ∧ Loaded B t' := by
  obtain ⟨pa, hpa, hpcA⟩ := atA
  obtain ⟨pb, hpb, hpcB⟩ := atB
  have hrsT : t.ramStart = s.ramStart := (RegsS.ramStart E.regs).symm
  have hhlT : t.hl = s.hl := (RegsS.hl E.regs).symm
  have hdeT : t.de = s.de := (RegsS.de E.regs).symm
  have hnA := hnn pa
  obtain ⟨s', hs', hrs', _, hrom', hh'⟩ := ord_rom f (f.instr.immB (A.a.env pa)) (f.instr.immW (A.a.env pa))
    (D.bus w) s (fun h => by have := hhl h; omega) (fun h => by have := hde h; omega)
    (fun h => by have := hnA h; omega)
  obtain ⟨t', ht', E'⟩ := ord_eqv lo hi hhi f _ _ (D.bus w) s t E hhl hde (hnn pa) s' hs'
  obtain ⟨t'', ht'', hrsT', _, hromT', hhT'⟩ := ord_rom f (f.instr.immB (A.a.env pa)) (f.instr.immW (A.a.env pa))
    (D.bus w) t (fun h => by have := hhl h; rw [hhlT, hrsT]; omega) (fun h => by have := hde h; rw [hdeT, hrsT]; omega)
    (fun h => by have := hnA h; rw [hrsT]; omega)
  rw [ht'] at ht''
  cases ht''
  have exA : exec (A.a.env pa) f.instr s (D.bus w) = some s' := hs'
  have exB : exec (B.a.env pb) f.instr t (D.bus w) = some t' := by
    show execI f.instr (f.instr.immB (B.a.env pb)) (f.instr.immW (B.a.env pb)) t (D.bus w) = some t'
    rw [← (hop pa pb).1, ← (hop pa pb).2]; exact ht'
  have stA := step_item A.placed LA.1 hA hpa hpcA LA.2 exA
  have stB := step_item B.placed LB.1 hB hpb hpcB LB.2 exB
  have hio : t'.io = s'.io := (RegsS.io E'.regs).symm
  refine ⟨s', t', D.dev w s'.io, ?_, ?_, E', stA.2 (ord_falls f), stB.2 (ord_falls f),
    LA.keep hrs' hrom' (by rw [hh' hnh]; exact LA.2), LB.keep hrsT' hromT' (by rw [hhT' hnh]; exact LB.2)⟩
  · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
    rw [stA.1]
  · show (t.step (D.bus w), D.dev w (t.step (D.bus w)).io) = _
    rw [stB.1, hio]

/-- info: 'Ember.Proof.PassSim.ord_eqv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ord_eqv


/-- info: 'Ember.Proof.PassSim.ord_rom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ord_rom

/-- info: 'Ember.Proof.PassSim.ord_mstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_mstep

end Ember.Proof.PassSim
