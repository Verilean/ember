import Ember.Proof.Z80PassStep
import Ember.Proof.Z80Jump
import Ember.Proof.Z80Call

/-!
# Ember.Proof.Z80PassCtl — jumps, calls and returns, as steps of the machine (plan M7.3)

One image at a time (`Code`, stepped by `mstep`): what `jp`, `jr`
(either with a condition), `call` and `ret` to a label do, as the state
after the step and the item the CPU is then at.  A jump changes no
register but the program counter (`op1`: `R`, and what fetching an
opcode resets); a call pushes the address after it; a return pops one.
The two images' steps are put side by side in `Z80PassRun`.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

-- `c` here is a count of T-states, not the register
set_option linter.constructorNameAsVariable false

/-- A label is where its item is: the address the assembler gives it. -/
theorem label_addr {C : Code} {s : Cpu} (L : Loaded C s) {j : Nat} {l : String}
    (hj : C.items[j]? = some (.label l)) :
    ∃ T, C.addrs[j]? = some T ∧ (∀ pc, (C.a.env pc).val (.sym l 0) = Int.ofNat T) ∧ T < 65536 := by
  obtain ⟨ad, bs, h1, _, _, _, _, hb, h6⟩ := C.placed.2 j _ hj
  refine ⟨ad, h1, fun pc => ?_, by have := L.1.rom; have := s.ramStart.toNat_lt; omega⟩
  rw [val_sym _ _ _ (Int.ofNat ad) (by simp [Assembled.env, h6 l rfl])]
  simp

/-- The state after a jump: the opcode fetched, the program counter set. -/
def jumped (s : Cpu) (p : UInt16) (c : UInt64) : Cpu := { op1 s with pc := p, cycles := c }

theorem step_of {D : Dev} {C : Code} {k : Nat} {i : Instr} (hk : C.items[k]? = some (.ins i)) {s : Cpu}
    (L : Loaded C s) {ad : Nat} (had : C.addrs[k]? = some ad) (hpc : s.pc.toNat = ad) (w : D.W) {s' : Cpu}
    (hx : exec (C.a.env ad) i s (D.bus w) = some s') :
    s.step (D.bus w) = s' ∧ (i.falls = true → At C.addrs (k + 1) s') :=
  step_item C.placed L.1 hk had hpc L.2 hx

/-- Is the jump taken: always without a condition, else when the condition holds. -/
def taken (cc : Option Arg) (s : Cpu) : Bool :=
  match cc with
  | none => true
  | some c => s.cond ((cc? c).getD 0)

/-- **A jump to a label** (`jp`, `jr`; with a condition or not): the state after it is `jumped`,
memory as it was; the CPU is at the label when the jump is taken (`cc`: the condition, by its code;
`none`: always), at the next item when not. -/
theorem jump_mstep (D : Dev) {C : Code} {k j : Nat} {op : Op} {cc : Option Arg} {l : String}
    (hop : op = .jp ∨ op = .jr) (hcc : ∀ c, cc = some c → op = .jr → c = .nz ∨ c = .z ∨ c = .nc ∨ c = .c)
    (hcc' : ∀ c, cc = some c → (cc? c).isSome)
    (hk : C.items[k]? = some (.ins ⟨op, (cc.toList) ++ [.imm (.sym l 0)]⟩))
    (hj : C.items[j]? = some (.label l)) {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    ∃ p c, mstep D (s, w) = (jumped s p c, w) ∧ Loaded C (jumped s p c) ∧
      (if taken cc s then At C.addrs j (jumped s p c) else At C.addrs (k + 1) (jumped s p c)) := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hval, hTlt⟩ := label_addr L hj
  obtain ⟨bs, hbs, hnext, hlt⟩ := C.placed.next L.1 hk had
  have hL : ∀ p c, Loaded C (jumped s p c) := fun p c => ⟨L.1.congr rfl rfl, L.2⟩
  -- the displacement of a `jr`, which the assembler checked
  have hrel : op = .jr → -128 ≤ Int.ofNat T - (Int.ofNat ad + 2) ∧ Int.ofNat T - (Int.ofNat ad + 2) ≤ 127 ∧
      bs.length = 2 := by
    intro hjr
    subst hjr
    have h' := encode_run hbs
    have hpcv : (C.a.env ad).pc = Int.ofNat ad := rfl
    cases cc with
    | none =>
      have he' : ((rel (.sym l 0)).run (C.a.env ad)).bind _ = Except.ok bs := h'
      obtain ⟨lst, hl, hb⟩ := bind_ok he'
      obtain ⟨r1, r2⟩ := rel_range hl rfl
      rw [hval, hpcv] at r1 r2
      have := rel_bytes hl
      subst this; cases hb
      exact ⟨r1, r2, rfl⟩
    | some c =>
      rcases hcc c rfl rfl with rfl | rfl | rfl | rfl <;>
      (have he' : ((rel (.sym l 0)).run (C.a.env ad)).bind _ = Except.ok bs := h'
       obtain ⟨lst, hl, hb⟩ := bind_ok he'
       obtain ⟨r1, r2⟩ := rel_range hl rfl
       rw [hval, hpcv] at r1 r2
       have := rel_bytes hl
       subst this; cases hb
       exact ⟨r1, r2, rfl⟩)
  have hjp : op = .jp → bs.length = 3 := by
    intro hjp
    subst hjp
    cases cc with
    | none => exact jp_len hbs
    | some c =>
      have h' := encode_run hbs
      obtain ⟨kk, hkk⟩ := Option.isSome_iff_exists.mp (hcc' c rfl)
      cases c <;> simp only [cc?, reduceCtorEq] at hkk <;>
      (have he' : ((imm16 (.sym l 0)).run (C.a.env ad)).bind _ = Except.ok bs := h'
       obtain ⟨lst, hl, hb⟩ := bind_ok he'
       obtain rfl := imm16_bytes hl
       cases hb
       rfl)
  have hpcT : (UInt16.ofNat T).toNat = T := ofNat_toNat16 hTlt
  have hpcN : ∀ n : Nat, bs.length = n + 1 → ((op1 s).pc + UInt16.ofNat n).toNat = ad + (n + 1) := by
    intro n hn
    have hlt' := hlt (by intro e; rw [e] at hn; cases hn)
    simp only [op1, Cpu.bumpR]
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc, ofNat_toNat16 (by omega)]
    simp only [UInt16.toNat_one]
    omega
  rcases hop with rfl | rfl
  · cases cc with
    | none =>
      have hx := exec_jp_to (C.a.env ad) (.sym l 0) T (hval ad) hTlt s (D.bus w)
      obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
      refine ⟨UInt16.ofNat T, (op1 s).cycles + 10, ?_, hL _ _, ?_⟩
      · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
        rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
      · simp only [taken, if_true]
        exact ⟨T, hT, by simp only [jumped, hpcT]⟩
    | some c =>
      obtain ⟨kk, hkk⟩ := Option.isSome_iff_exists.mp (hcc' c rfl)
      have hx := exec_jpcc_to (C.a.env ad) c kk hkk (.sym l 0) T (hval ad) hTlt s (D.bus w)
      obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
      have hc : (op1 s).cond kk = s.cond kk := rfl
      simp only [taken, hkk, Option.getD_some]
      by_cases hcd : s.cond kk = true
      · rw [hc, if_pos hcd] at hs1
        refine ⟨UInt16.ofNat T, (op1 s).cycles + 10, ?_, hL _ _, ?_⟩
        · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
          rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
        · rw [if_pos hcd]; exact ⟨T, hT, by simp only [jumped, hpcT]⟩
      · rw [hc, if_neg hcd] at hs1
        refine ⟨(op1 s).pc + 2, (op1 s).cycles + 10, ?_, hL _ _, ?_⟩
        · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
          rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
        · rw [if_neg hcd]
          refine ⟨ad + bs.length, hnext, ?_⟩
          rw [hjp rfl]
          exact hpcN 2 (hjp rfl)
  · obtain ⟨d0, d1, hlen⟩ := hrel rfl
    have hpcv : (C.a.env ad).pc = Int.ofNat s.pc.toNat := by rw [hpc]; rfl
    cases cc with
    | none =>
      have hx := exec_jr_to (C.a.env ad) (.sym l 0) T (hval ad) hTlt s (D.bus w) hpcv
        (by rw [show (C.a.env ad).pc = Int.ofNat ad from rfl]; exact d0)
        (by rw [show (C.a.env ad).pc = Int.ofNat ad from rfl]; exact d1)
      obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
      refine ⟨UInt16.ofNat T, (op1 s).cycles + 12, ?_, hL _ _, ?_⟩
      · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
        rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
      · simp only [taken, if_true]
        exact ⟨T, hT, by simp only [jumped, hpcT]⟩
    | some c =>
      obtain ⟨kk, hkk⟩ := Option.isSome_iff_exists.mp (hcc' c rfl)
      have hk3 : kk ≤ 3 := by
        rcases hcc c rfl rfl with rfl | rfl | rfl | rfl <;> simp only [cc?, Option.some.injEq] at hkk <;>
          subst hkk <;> decide
      have hx := exec_jrcc_to (C.a.env ad) c kk hkk hk3 (.sym l 0) T (hval ad) hTlt s (D.bus w) hpcv
        (by rw [show (C.a.env ad).pc = Int.ofNat ad from rfl]; exact d0)
        (by rw [show (C.a.env ad).pc = Int.ofNat ad from rfl]; exact d1)
      obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
      have hc : (op1 s).cond kk = s.cond kk := rfl
      simp only [taken, hkk, Option.getD_some]
      by_cases hcd : s.cond kk = true
      · rw [hc, if_pos hcd] at hs1
        refine ⟨UInt16.ofNat T, (op1 s).cycles + 12, ?_, hL _ _, ?_⟩
        · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
          rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
        · rw [if_pos hcd]; exact ⟨T, hT, by simp only [jumped, hpcT]⟩
      · rw [hc, if_neg hcd] at hs1
        refine ⟨(op1 s).pc + 1, (op1 s).cycles + 7, ?_, hL _ _, ?_⟩
        · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
          rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
        · rw [if_neg hcd]
          refine ⟨ad + bs.length, hnext, ?_⟩
          rw [hlen]
          exact hpcN 1 hlen

/-! ## Calls and returns -/

/-- The state after `call nn`: the address after the call's three bytes pushed. -/
def called (s : Cpu) (nn : UInt16) : Cpu := (callTo (skip (op1 s) 2) nn).tick 17

theorem called_sp (s : Cpu) (nn : UInt16) : (called s nn).sp = s.sp - 2 := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  all_goals ((repeat' split) <;> rfl)
theorem called_pc (s : Cpu) (nn : UInt16) : (called s nn).pc = nn := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  all_goals ((repeat' split) <;> rfl)
theorem called_ramStart (s : Cpu) (nn : UInt16) : (called s nn).ramStart = s.ramStart := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  all_goals ((repeat' split) <;> rfl)
theorem called_halted (s : Cpu) (nn : UInt16) : (called s nn).halted = s.halted := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  all_goals ((repeat' split) <;> rfl)
theorem called_io (s : Cpu) (nn : UInt16) : (called s nn).io = .none := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  all_goals ((repeat' split) <;> rfl)

/-- What a call writes: the return address, low byte first, at the new stack pointer; nothing else. -/
theorem called_mem (s : Cpu) (nn : UInt16) (hsz : s.mem.size = 65536)
    (hr : s.ramStart.toNat ≤ (s.sp - 2).toNat) (hw : (s.sp - 2).toNat + 1 < 65536) (x : Nat) :
    (called s nn).mem.get! x =
      if x = (s.sp - 2).toNat then (s.pc + 3).toUInt8
      else if x = (s.sp - 2).toNat + 1 then ((s.pc + 3) >>> 8).toUInt8 else s.mem.get! x := by
  have h1 : (s.sp - 2 + 1).toNat = (s.sp - 2).toNat + 1 := by
    rw [UInt16.toNat_add]; simp only [UInt16.toNat_one]; omega
  have hnl : ¬ (s.sp - 2) < s.ramStart := by rw [UInt16.lt_iff_toNat_lt]; omega
  have hnl' : ¬ (s.sp - 2 + 1) < s.ramStart := by rw [UInt16.lt_iff_toNat_lt, h1]; omega
  have hp : s.pc + 1 + 2 = s.pc + 3 := by rw [UInt16.add_assoc]; rfl
  have hm : (called s nn).mem = (s.mem.set! (s.sp - 2).toNat (s.pc + 3).toUInt8).set! ((s.sp - 2).toNat + 1)
      ((s.pc + 3) >>> 8).toUInt8 := by
    simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR, hnl, hnl', if_false, h1, hp]
  rw [hm, Ember.Proof.IRSim.get_set, Ember.Proof.IRSim.get_set, Ember.Proof.IRSim.size_set, hsz]
  by_cases hx : x = (s.sp - 2).toNat
  · subst hx
    have : ¬ ((s.sp - 2).toNat + 1 = (s.sp - 2).toNat) := by omega
    simp only [this, false_and, if_false, true_and, if_true]
    rw [if_pos (by omega)]
  · by_cases hx' : x = (s.sp - 2).toNat + 1
    · subst hx'
      have : ¬ ((s.sp - 2).toNat + 1 = (s.sp - 2).toNat) := by omega
      simp only [true_and, if_true, this, if_false]
      rw [if_pos (by omega)]
    · have a1 : ¬ ((s.sp - 2).toNat + 1 = x ∧ (s.sp - 2).toNat + 1 < 65536) := fun h => hx' h.1.symm
      have a2 : ¬ ((s.sp - 2).toNat = x ∧ (s.sp - 2).toNat < 65536) := fun h => hx h.1.symm
      simp only [hx, hx', a1, a2, if_false]

theorem called_size (s : Cpu) (nn : UInt16) : (called s nn).mem.size = s.mem.size := by
  simp only [called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  split <;> split <;> simp

/-- **`call` to a label**: the step is `called`, to the label's address. -/
theorem call_mstep (D : Dev) {C : Code} {k j : Nat} {l : String}
    (hk : C.items[k]? = some (.ins ⟨.call, [.imm (.sym l 0)]⟩)) (hj : C.items[j]? = some (.label l))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    ∃ T ad, C.addrs[j]? = some T ∧ C.addrs[k + 1]? = some (ad + 3) ∧ s.pc.toNat = ad ∧ ad + 3 < 65536 ∧
      mstep D (s, w) = (called s (UInt16.ofNat T), w) ∧ At C.addrs j (called s (UInt16.ofNat T)) := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hval, hTlt⟩ := label_addr L hj
  obtain ⟨bs, hbs, hnext, hlt⟩ := C.placed.next L.1 hk had
  have hlen : bs.length = 3 := call_len hbs
  have hw : Instr.immW (C.a.env ad) ⟨.call, [.imm (.sym l 0)]⟩ = UInt16.ofNat T := by
    apply UInt16.toNat_inj.mp
    rw [immW_toNat _ _ _ T rfl (hval ad) hTlt, ofNat_toNat16 hTlt]
  have hx : exec (C.a.env ad) ⟨.call, [.imm (.sym l 0)]⟩ s (D.bus w) = some (called s (UInt16.ofNat T)) := by
    show execI _ _ (Instr.immW (C.a.env ad) _) _ _ = _
    rw [hw]; rfl
  obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
  refine ⟨T, ad, hT, by rw [hnext, hlen], hpc, by have := hlt (by intro e; rw [e] at hlen; cases hlen); omega,
    ?_, ⟨T, hT, by rw [called_pc, ofNat_toNat16 hTlt]⟩⟩
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hs1, called_io, D.quiet]

/-- The state after `ret` (taken). -/
def returned (s : Cpu) (c : UInt64) : Cpu := { retTo (op1 s) with cycles := c }

theorem returned_pc (s : Cpu) (c : UInt64) : (returned s c).pc = s.rd16 s.sp := rfl
theorem returned_sp (s : Cpu) (c : UInt64) : (returned s c).sp = s.sp + 2 := rfl
theorem returned_mem (s : Cpu) (c : UInt64) : (returned s c).mem = s.mem := rfl

/-- **`ret`, or `ret cc`**: taken (always for `ret`), the state is `returned`; not taken, the CPU
goes on to the next item with nothing changed but `R` and the T-states (`jumped`). -/
theorem ret_mstep (D : Dev) {C : Code} {k : Nat} {cc : Option Arg} (hcc : ∀ c, cc = some c → (cc? c).isSome)
    (hk : C.items[k]? = some (.ins ⟨.ret, cc.toList⟩)) {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s)
    (w : D.W) :
    if taken cc s then ∃ c, mstep D (s, w) = (returned s c, w)
    else ∃ p c, mstep D (s, w) = (jumped s p c, w) ∧ At C.addrs (k + 1) (jumped s p c) := by
  obtain ⟨ad, had, hpc⟩ := hat
  cases cc with
  | none =>
    have hx : exec (C.a.env ad) ⟨.ret, []⟩ s (D.bus w) = some (returned s ((op1 s).cycles + 10)) := rfl
    obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
    simp only [taken, if_true]
    refine ⟨(op1 s).cycles + 10, ?_⟩
    show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
    rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
  | some c =>
    obtain ⟨kk, hkk⟩ := Option.isSome_iff_exists.mp (hcc c rfl)
    have hx := exec_retcc (C.a.env ad) c kk hkk s (D.bus w)
    obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
    obtain ⟨bs, hbs, hnext, hlt⟩ := C.placed.next L.1 hk had
    have hlen : bs.length = 1 := by
      have h' := encode_run hbs
      have henc : ∀ c' : Arg, (cc? c').isSome = true → ∃ b, (encode' ⟨.ret, [c']⟩).run (C.a.env ad) = .ok [b] := by
        intro c' h; cases c' <;> simp [cc?] at h <;> exact ⟨_, rfl⟩
      obtain ⟨b, hb⟩ := henc c (hcc c rfl)
      have h'' : (encode' ⟨.ret, [c]⟩).run (C.a.env ad) = .ok bs := h'
      rw [hb] at h''; cases h''; rfl
    have hc : (op1 s).cond kk = s.cond kk := rfl
    simp only [taken, hkk, Option.getD_some]
    by_cases hcd : s.cond kk = true
    · rw [hc, if_pos hcd] at hs1
      rw [if_pos hcd]
      refine ⟨(op1 s).cycles + 11, ?_⟩
      show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
      rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
    · rw [hc, if_neg hcd] at hs1
      rw [if_neg hcd]
      refine ⟨(op1 s).pc, (op1 s).cycles + 5, ?_, ad + bs.length, hnext, ?_⟩
      · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
        rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
      · have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
        simp only [jumped, op1, Cpu.bumpR, hlen]
        rw [UInt16.toNat_add, hpc]; simp only [UInt16.toNat_one]; omega

/-! ## `djnz`, `halt`, `ld sp,nn` -/

/-- The state after `djnz`: `B` one less, then a jump or not. -/
def djnzed (s : Cpu) (p : UInt16) (c : UInt64) : Cpu := { op1 s with b := s.b - 1, pc := p, cycles := c }

/-- **`djnz` to a label**: `B` one less; at the label when it is not zero, at the next item when it is. -/
theorem djnz_mstep (D : Dev) {C : Code} {k j : Nat} {l : String}
    (hk : C.items[k]? = some (.ins ⟨.djnz, [.imm (.sym l 0)]⟩)) (hj : C.items[j]? = some (.label l))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    ∃ p c, mstep D (s, w) = (djnzed s p c, w) ∧ Loaded C (djnzed s p c) ∧
      (if (s.b - 1 != 0) = true then At C.addrs j (djnzed s p c) else At C.addrs (k + 1) (djnzed s p c)) := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hval, hTlt⟩ := label_addr L hj
  obtain ⟨bs, hbs, hnext, hlt⟩ := C.placed.next L.1 hk had
  have h' := encode_run hbs
  have he' : ((rel (.sym l 0)).run (C.a.env ad)).bind _ = Except.ok bs := h'
  obtain ⟨lst, hl, hb⟩ := bind_ok he'
  obtain ⟨r1, r2⟩ := rel_range hl rfl
  have hlst := rel_bytes hl
  subst hlst; cases hb
  have hpcv : (C.a.env ad).pc = Int.ofNat ad := rfl
  rw [hval, hpcv] at r1 r2
  have hlt' := hlt (by intro e; cases e)
  simp only [List.length_append, List.length_cons, List.length_nil] at hlt' hnext
  have himm : Instr.immB (C.a.env ad) ⟨.djnz, [.imm (.sym l 0)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
    show byteOf ((C.a.env ad).val (.sym l 0) - ((C.a.env ad).pc + 2)) = _
    rw [hval]; rfl
  have hs := sext_val _ r1 r2
  have eT : s.pc + 1 + 1 + Cpu.sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) = UInt16.ofNat T := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, ofNat_toNat16 hTlt, hpc]
    simp only [UInt16.toNat_one, Int.ofNat_eq_natCast] at hs r1 r2 ⊢
    omega
  have hL : ∀ p c, Loaded C (djnzed s p c) := fun p c => ⟨L.1.congr rfl rfl, L.2⟩
  by_cases hb : (s.b - 1 != 0) = true
  · have hx : exec (C.a.env ad) ⟨.djnz, [.imm (.sym l 0)]⟩ s (D.bus w) =
        some (djnzed s (UInt16.ofNat T) ((op1 s).cycles + 13)) := by
      show execI _ (Instr.immB (C.a.env ad) _) _ _ _ = _
      rw [himm]
      simp only [execI, exec1, op1, Cpu.bumpR, skip, Cpu.tick, djnzed]
      rw [if_pos hb]
      simp only [eT]
    obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
    refine ⟨UInt16.ofNat T, (op1 s).cycles + 13, ?_, hL _ _, ?_⟩
    · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
      rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
    · rw [if_pos hb]; exact ⟨T, hT, by simp only [djnzed, ofNat_toNat16 hTlt]⟩
  · have hx : exec (C.a.env ad) ⟨.djnz, [.imm (.sym l 0)]⟩ s (D.bus w) =
        some (djnzed s (s.pc + 1 + 1) ((op1 s).cycles + 8)) := by
      show execI _ (Instr.immB (C.a.env ad) _) _ _ _ = _
      simp only [execI, exec1, op1, Cpu.bumpR, skip, Cpu.tick, djnzed]
      rw [if_neg hb]
    obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
    refine ⟨s.pc + 1 + 1, (op1 s).cycles + 8, ?_, hL _ _, ?_⟩
    · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
      rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)
    · rw [if_neg hb]
      refine ⟨ad + 2, hnext, ?_⟩
      simp only [djnzed]
      rw [UInt16.toNat_add, UInt16.toNat_add, hpc]; simp only [UInt16.toNat_one]; omega

/-- **`halt`**: the CPU halted, nothing else of note changed. -/
theorem halt_mstep (D : Dev) {C : Code} {k : Nat} (hk : C.items[k]? = some (.ins ⟨.halt, []⟩))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    mstep D (s, w) = ((({ op1 s with halted := true }) : Cpu).tick 4, w) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hx : exec (C.a.env ad) ⟨.halt, []⟩ s (D.bus w) = some ((({ op1 s with halted := true }) : Cpu).tick 4) := rfl
  obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)

/-- **`ld sp,nn`**: the stack pointer `nn`, the CPU at the next item. -/
theorem ldsp_mstep (D : Dev) {C : Code} {k : Nat} (n : Nat) (hn : n < 65536)
    (hk : C.items[k]? = some (.ins ⟨.ld, [.sp, .imm (.num (Int.ofNat n))]⟩))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    ∃ p c, mstep D (s, w) = ({ op1 s with sp := UInt16.ofNat n, pc := p, cycles := c }, w) ∧
      At C.addrs (k + 1) { op1 s with sp := UInt16.ofNat n, pc := p, cycles := c } ∧
      Loaded C { op1 s with sp := UInt16.ofNat n, pc := p, cycles := c } := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hw : Instr.immW (C.a.env ad) ⟨.ld, [.sp, .imm (.num (Int.ofNat n))]⟩ = UInt16.ofNat n := by
    apply UInt16.toNat_inj.mp
    rw [immW_toNat _ _ (.num (Int.ofNat n)) n rfl rfl hn, ofNat_toNat16 hn]
  have hx : exec (C.a.env ad) ⟨.ld, [.sp, .imm (.num (Int.ofNat n))]⟩ s (D.bus w) =
      some { op1 s with sp := UInt16.ofNat n, pc := s.pc + 1 + 2, cycles := (op1 s).cycles + 10 } := by
    show execI _ _ (Instr.immW (C.a.env ad) _) _ _ = _
    rw [hw]; rfl
  obtain ⟨hs1, hat'⟩ := step_of hk L had hpc w hx
  refine ⟨_, _, ?_, hat' rfl, ⟨L.1.congr rfl rfl, L.2⟩⟩
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)

/-! ## `push af`, `pop af` -/

/-- The state after `push af`. -/
def pushedAF (s : Cpu) : Cpu := ((op1 s).push (op1 s).af).tick 11

/-- The state after `pop af`. -/
def poppedAF (s : Cpu) : Cpu :=
  ({ ({ op1 s with sp := s.sp + 2 } : Cpu) with a := hi (s.rd16 s.sp), f := lo (s.rd16 s.sp) } : Cpu).tick 10

theorem push_af_mstep (D : Dev) {C : Code} {k : Nat} (hk : C.items[k]? = some (.ins ⟨.push, [.af]⟩))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    mstep D (s, w) = (pushedAF s, w) ∧ At C.addrs (k + 1) (pushedAF s) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hx : exec (C.a.env ad) ⟨.push, [.af]⟩ s (D.bus w) = some (pushedAF s) := rfl
  obtain ⟨hs1, hat'⟩ := step_of hk L had hpc w hx
  refine ⟨?_, hat' rfl⟩
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hs1]
  have : (pushedAF s).io = .none := by
    simp only [pushedAF, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, op1, Cpu.bumpR]; (repeat' split) <;> rfl
  rw [this, D.quiet]

theorem pop_af_mstep (D : Dev) {C : Code} {k : Nat} (hk : C.items[k]? = some (.ins ⟨.pop, [.af]⟩))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    mstep D (s, w) = (poppedAF s, w) ∧ At C.addrs (k + 1) (poppedAF s) ∧ Loaded C (poppedAF s) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hx : exec (C.a.env ad) ⟨.pop, [.af]⟩ s (D.bus w) = some (poppedAF s) := rfl
  obtain ⟨hs1, hat'⟩ := step_of hk L had hpc w hx
  refine ⟨?_, hat' rfl, ⟨L.1.congr rfl rfl, L.2⟩⟩
  show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
  rw [hs1]; exact congrArg (Prod.mk _) (D.quiet w)

/-! ## `ldir` -/

/-- One round of `ldir`, from the state after its two opcode bytes are fetched: a byte from `(HL)`
to `(DE)` (not in ROM), both one up, `BC` one down, the flags of the block instructions; the
program counter back at the `ldir` while `BC` is not zero. -/
def ldirF (e : Cpu) : Cpu :=
  let v := e.rd e.hl
  let w := e.wr e.de v
  let w := (w.setHL (w.hl + 1)).setDE (w.de + 1)
  let w := w.setBC (w.bc - 1)
  let more : Bool := w.bc != 0
  let n : UInt8 := w.a + v
  let w := { w with f := (w.f &&& (FS ||| FZ ||| FC)) ||| bit more FPV ||| (n &&& FX) ||| bit (n &&& 2 != 0) FY }
  if more then ({ w with pc := w.pc - 2 }).tick 21 else w.tick 16

theorem execBlock_ldir (e : Cpu) (inp : UInt16 → UInt8) : e.execBlock inp 6 0 = ldirF e := rfl

/-- `ldirF`, written field by field. -/
def ldirG (x : Cpu) : Cpu :=
  let v := x.mem.get! x.hl.toNat
  let m := if x.de < x.ramStart then x.mem else x.mem.set! x.de.toNat v
  let bc' := x.bc - 1
  let more : Bool := bc' != 0
  let n : UInt8 := x.a + v
  let f' : UInt8 := (x.f &&& (FS ||| FZ ||| FC)) ||| bit more FPV ||| (n &&& FX) ||| bit (n &&& 2 != 0) FY
  let w : Cpu :=
    { x with mem := m, h := hi (x.hl + 1), l := lo (x.hl + 1), d := hi (x.de + 1), e := lo (x.de + 1),
             b := hi bc', c := lo bc', f := f' }
  if more then { w with pc := x.pc - 2, cycles := x.cycles + 21 } else { w with cycles := x.cycles + 16 }

set_option linter.unusedSimpArgs false in
theorem ldirF_eq (e : Cpu) : ldirF e = ldirG e := by
  cases e with
  | mk a f b c d e h l a' f' b' c' d' e' h' l' ix iy sp pc i r iff1 iff2 im halted eiDelay cycles io ramStart mem =>
  by_cases hd : mk16 d e < ramStart
  · simp only [ldirF, ldirG, Cpu.wr, Cpu.rd, Cpu.setHL, Cpu.setDE, Cpu.setBC, Cpu.hl, Cpu.de, Cpu.bc, Cpu.tick,
      Ember.Proof.Z80Gen.hi_mk16, Ember.Proof.Z80Gen.lo_mk16, Ember.Proof.Z80Gen.mk16_hi_lo, hd, if_true]
  · simp only [ldirF, ldirG, Cpu.wr, Cpu.rd, Cpu.setHL, Cpu.setDE, Cpu.setBC, Cpu.hl, Cpu.de, Cpu.bc, Cpu.tick,
      Ember.Proof.Z80Gen.hi_mk16, Ember.Proof.Z80Gen.lo_mk16, Ember.Proof.Z80Gen.mk16_hi_lo, hd, if_false]

/-- One round of `ldir` from the state before its opcode is fetched. -/
def ldirS (s : Cpu) : Cpu := ldirG (op2 s)

theorem ldir_mstep (D : Dev) {C : Code} {k : Nat} (hk : C.items[k]? = some (.ins ⟨.ldir, []⟩))
    {s : Cpu} (L : Loaded C s) (hat : At C.addrs k s) (w : D.W) :
    mstep D (s, w) = (ldirS s, w) ∧
      (if (s.bc - 1 != 0) = true then At C.addrs k (ldirS s) else At C.addrs (k + 1) (ldirS s)) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hx : exec (C.a.env ad) ⟨.ldir, []⟩ s (D.bus w) = some (ldirS s) := by
    show some ((op2 s).execBlock (D.bus w) 6 0) = _
    rw [execBlock_ldir, ldirF_eq]; rfl
  obtain ⟨hs1, _⟩ := step_of hk L had hpc w hx
  obtain ⟨bs, hbs, hnext, hlt⟩ := C.placed.next L.1 hk had
  have hlen : bs.length = 2 := by
    have h' : encode ⟨.ldir, []⟩ (C.a.env ad) = .ok bs := hbs
    have h'' := encode_run h'
    have : (encode' ⟨.ldir, []⟩).run (C.a.env ad) = .ok [0xED, 0xB0] := rfl
    rw [this] at h''; cases h''; rfl
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have hbc : (op2 s).bc = s.bc := rfl
  refine ⟨?_, ?_⟩
  · show (s.step (D.bus w), D.dev w (s.step (D.bus w)).io) = _
    rw [hs1]
    have : (ldirS s).io = .none := by
      simp only [ldirS, ldirG]; split <;> rfl
    rw [this, D.quiet]
  · simp only [ldirS, ldirG, hbc]
    by_cases hb : (s.bc - 1 != 0) = true
    · rw [if_pos hb, if_pos hb]
      refine ⟨ad, had, ?_⟩
      show (s.pc + 1 + 1 - 2).toNat = ad
      rw [show s.pc + 1 + 1 - 2 = s.pc by
        apply UInt16.toNat_inj.mp
        simp only [UInt16.toNat_sub, UInt16.toNat_add, UInt16.toNat_one, show (2 : UInt16).toNat = 2 from rfl]
        omega]
      exact hpc
    · rw [if_neg hb, if_neg hb]
      refine ⟨ad + 2, by rw [hnext, hlen], ?_⟩
      show (s.pc + 1 + 1).toNat = ad + 2
      rw [UInt16.toNat_add, UInt16.toNat_add, hpc]; simp only [UInt16.toNat_one]; omega

end Ember.Proof.PassSim
