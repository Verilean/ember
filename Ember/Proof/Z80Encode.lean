import Ember.Z80.AsmSem

/-!
# Ember.Proof.Z80Encode — the CPU does what the assembler wrote (plan M7.4)

`Ember.Z80.Cpu.step` decodes bytes as it executes them; `Ember.Z80.Asm`
encodes instructions; `Ember.Z80.AsmSem.exec` says what an instruction
does without going through bytes.  `step_encode`: **if the encoding of
an instruction is in memory at the program counter, one step of the CPU
is what `exec` says the instruction does** — the whole state, T-states
and `R` included.  This is "decode ∘ encode = id" for a CPU model whose
decoder is its interpreter.

For every form `exec` covers: all that `Asm.encode` accepts without an
index register (`IX`, `IY`), which neither the back end nor its runtime
uses.

The proof is by cases on the mnemonic and the operands.  With those
fixed, the encoding computes to bytes (an immediate operand apart, which
`imm8_bytes`, `imm16_bytes` and `rel_bytes` give), the CPU's decoding of
those bytes computes, and the two sides are equal by `rfl`.
-/

namespace Ember.Proof.Z80Enc
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm

/-- The bytes `bs` are in memory at the program counter. -/
def Code (s : Cpu) (bs : List UInt8) : Prop := ∀ k b, bs[k]? = some b → s.rd (s.pc + UInt16.ofNat k) = b

section
variable {s : Cpu} {b0 b1 b2 b3 : UInt8} {t : List UInt8}

theorem code0 (h : Code s (b0 :: t)) : s.rd s.pc = b0 := by
  have := h 0 b0 rfl
  rwa [show s.pc + UInt16.ofNat 0 = s.pc from UInt16.add_zero _] at this

theorem code1 (h : Code s (b0 :: b1 :: t)) : s.rd (s.pc + 1) = b1 := h 1 b1 rfl

theorem code2 (h : Code s (b0 :: b1 :: b2 :: t)) : s.rd (s.pc + 1 + 1) = b2 := by
  rw [UInt16.add_assoc]
  exact h 2 b2 rfl

theorem code3 (h : Code s (b0 :: b1 :: b2 :: b3 :: t)) : s.rd (s.pc + 1 + 1 + 1) = b3 := by
  rw [UInt16.add_assoc, UInt16.add_assoc]
  exact h 3 b3 rfl

end

/-! ## One step, by the page of its opcode -/

theorem step_main (s : Cpu) (inp : UInt16 → UInt8) (op : UInt8) (hh : s.halted = false) (h0 : s.rd s.pc = op)
    (hp : (op == 0xDD || op == 0xFD || op == 0xED || op == 0xCB) = false) :
    s.step inp = execMain (op1 s) inp op .hl := by
  simp only [Bool.or_eq_false_iff] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  subst h0
  unfold Cpu.step
  simp only [hh, Bool.false_eq_true, if_false, Cpu.fetch, Cpu.rd] at h1 h2 h3 h4 ⊢
  simp only [h1, h2, h3, h4, Bool.or_self, Bool.false_eq_true, if_false, op1, hh]

theorem step_ed (s : Cpu) (inp : UInt16 → UInt8) (op : UInt8) (hh : s.halted = false) (h0 : s.rd s.pc = 0xED)
    (h1 : s.rd (s.pc + 1) = op) : s.step inp = edOp (op2 s) inp op := by
  have h : s.step inp = execED (op1 s) inp := by
    unfold Cpu.step
    simp only [Cpu.rd] at h0
    simp [hh, Cpu.fetch, Cpu.rd, h0, op1]
  rw [h, ← h1]
  rfl

theorem step_cb (s : Cpu) (inp : UInt16 → UInt8) (op : UInt8) (hh : s.halted = false) (h0 : s.rd s.pc = 0xCB)
    (h1 : s.rd (s.pc + 1) = op) : s.step inp = cbOp (op2 s) op := by
  have h : s.step inp = execCB (op1 s) .hl := by
    unfold Cpu.step
    simp only [Cpu.rd] at h0
    simp [hh, Cpu.fetch, Cpu.rd, h0, op1]
  rw [h, ← h1]
  rfl

/-! ## Operands -/

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem imm8_bytes {env : Env} {v : Val} {l : List UInt8} (h : (imm8 v).run env = .ok l) :
    l = [byteOf (env.val v)] := by
  simp only [Env.val]
  simp only [imm8, ReaderT.run, bind, ReaderT.bind, Except.bind] at h ⊢
  cases hv : value v env with
  | error e => simp [hv] at h
  | ok n =>
    simp only [hv] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

theorem imm16_bytes {env : Env} {v : Val} {l : List UInt8} (h : (imm16 v).run env = .ok l) :
    l = [byteOf (env.val v), byteOf (env.val v / 256)] := by
  simp only [Env.val]
  simp only [imm16, ReaderT.run, bind, ReaderT.bind, Except.bind] at h ⊢
  cases hv : value v env with
  | error e => simp [hv] at h
  | ok n =>
    simp only [hv] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

theorem rel_bytes {env : Env} {v : Val} {l : List UInt8} (h : (rel v).run env = .ok l) :
    l = [byteOf (env.val v - (env.pc + 2))] := by
  simp only [Env.val]
  simp only [rel, ReaderT.run, bind, ReaderT.bind, Except.bind] at h ⊢
  cases hv : value v env with
  | error e => simp [hv] at h
  | ok n =>
    simp only [hv] at h ⊢
    have hr : (read : Enc Env) env = Except.ok env := rfl
    simp only [hr] at h
    split at h
    · cases h
    · cases h
      rfl

/-! ## The instructions -/

section
variable {env : Env} {s s' : Cpu} {inp : UInt16 → UInt8} {bs : List UInt8}

/- The tactics below work on a goal `s.step inp = s'` with
`he : (encode' i).run env = .ok bs`, `hc : Code s bs`, `hh : s.halted = false`
and `hx : exec env i s inp = some s'`, the operands of `i` being
constructors.  The encoding computes; so does the CPU on its opcode. -/

theorem wr_pc (s : Cpu) (a : UInt16) (v : UInt8) : (s.wr a v).pc = s.pc := by
  unfold Cpu.wr
  split <;> rfl

set_option hygiene false in
macro "pc_fin" : tactic =>
  `(tactic| first
    | rfl
    | (show s.pc + 1 + 1 = _; rw [UInt16.add_assoc]; rfl)
    | (show s.pc + 1 + 2 = _; rw [UInt16.add_assoc]; rfl)
    | (show s.pc + 1 + 1 + 2 = _; rw [UInt16.add_assoc, UInt16.add_assoc]; rfl))

set_option hygiene false in
/-- Where the program counter is after an instruction that goes on. -/
macro "enc_pc" : tactic =>
  `(tactic| (intro hf; first
    | (cases hf; done)
    | (simp only [Cpu.tick, Cpu.push, Cpu.wr16, Cpu.setHL, Cpu.setBC, Cpu.setDE, wr_pc]; pc_fin)
    | pc_fin))

set_option hygiene false in
/-- No immediate operand, main page. -/
macro "enc_main" : tactic =>
  `(tactic| (cases he; cases hx; refine ⟨by rw [step_main _ _ _ hh (code0 hc) rfl]; rfl, ?_⟩; enc_pc))

set_option hygiene false in
macro "enc_ed" : tactic =>
  `(tactic| (cases he; cases hx; refine ⟨by rw [step_ed _ _ _ hh (code0 hc) (code1 hc)]; rfl, ?_⟩; enc_pc))

set_option hygiene false in
macro "enc_cb" : tactic =>
  `(tactic| (cases he; cases hx; refine ⟨by rw [step_cb _ _ _ hh (code0 hc) (code1 hc)]; rfl, ?_⟩; enc_pc))

set_option hygiene false in
/-- A byte after the opcode. -/
macro "enc_i8" : tactic =>
  `(tactic| (
    have he' : ((imm8 _).run _).bind _ = Except.ok _ := he
    obtain ⟨l, hl, hb⟩ := bind_ok he'
    obtain rfl := imm8_bytes hl
    cases hb
    have c1 := code1 hc
    unfold exec at hx
    generalize hB : Instr.immB env _ = nB at hx
    have hnB : nB = s.rd (s.pc + 1) := by rw [← hB, c1]; rfl
    subst hnB
    cases hx
    refine ⟨by rw [step_main _ _ _ hh (code0 hc) rfl]; rfl, ?_⟩
    enc_pc))

set_option hygiene false in
/-- A displacement after the opcode. -/
macro "enc_rel" : tactic =>
  `(tactic| (
    have he' : ((rel _).run _).bind _ = Except.ok _ := he
    obtain ⟨l, hl, hb⟩ := bind_ok he'
    obtain rfl := rel_bytes hl
    cases hb
    have c1 := code1 hc
    unfold exec at hx
    generalize hB : Instr.immB env _ = nB at hx
    have hnB : nB = s.rd (s.pc + 1) := by rw [← hB, c1]; rfl
    subst hnB
    cases hx
    refine ⟨by rw [step_main _ _ _ hh (code0 hc) rfl]; rfl, ?_⟩
    enc_pc))

set_option hygiene false in
/-- A word after the opcode. -/
macro "enc_i16" : tactic =>
  `(tactic| (
    have he' : ((imm16 _).run _).bind _ = Except.ok _ := he
    obtain ⟨l, hl, hb⟩ := bind_ok he'
    obtain rfl := imm16_bytes hl
    cases hb
    have c1 := code1 hc
    have c2 := code2 hc
    unfold exec at hx
    generalize hW : Instr.immW env _ = nW at hx
    have hnW : nW = w16 (s.rd (s.pc + 1)) (s.rd (s.pc + 1 + 1)) := by rw [← hW, c1, c2]; rfl
    subst hnW
    cases hx
    refine ⟨by rw [step_main _ _ _ hh (code0 hc) rfl]; rfl, ?_⟩
    enc_pc))

set_option hygiene false in
/-- A word after `ED` and the opcode. -/
macro "enc_i16ed" : tactic =>
  `(tactic| (
    have he' : ((imm16 _).run _).bind _ = Except.ok _ := he
    obtain ⟨l, hl, hb⟩ := bind_ok he'
    obtain rfl := imm16_bytes hl
    cases hb
    have c2 := code2 hc
    have c3 := code3 hc
    unfold exec at hx
    generalize hW : Instr.immW env _ = nW at hx
    have hnW : nW = w16 (s.rd (s.pc + 1 + 1)) (s.rd (s.pc + 1 + 1 + 1)) := by rw [← hW, c2, c3]; rfl
    subst hnW
    cases hx
    refine ⟨by rw [step_ed _ _ _ hh (code0 hc) (code1 hc)]; rfl, ?_⟩
    enc_pc))

set_option hygiene false in
macro "enc_any" : tactic =>
  `(tactic| first | (cases hx; done) | enc_main | enc_ed | enc_cb | enc_i8 | enc_i16 | enc_i16ed | enc_rel)

set_option maxHeartbeats 0 in
theorem arity0_ok (op : Op) (he : (encode' ⟨op, []⟩).run env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env ⟨op, []⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨op, []⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases op <;> enc_any

set_option maxHeartbeats 0 in
theorem rst_ok (x : Arg) (he : (encode' ⟨.rst, [x]⟩).run env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env ⟨.rst, [x]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.rst, [x]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> try (cases hx; done)
  rename_i v
  cases v with
  | sym l o => cases hx
  | num a =>
    by_cases ha : 0 ≤ a ∧ a ≤ 56 ∧ a % 8 = 0
    · have : a = 0 ∨ a = 8 ∨ a = 16 ∨ a = 24 ∨ a = 32 ∨ a = 40 ∨ a = 48 ∨ a = 56 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> enc_main
    · simp [exec, execI, exec1, ha] at hx

set_option maxHeartbeats 0 in
theorem im_ok (x : Arg) (he : (encode' ⟨.im, [x]⟩).run env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env ⟨.im, [x]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.im, [x]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> try (cases hx; done)
  rename_i v
  cases v with
  | sym l o => cases hx
  | num a =>
    cases a with
    | negSucc m => cases hx
    | ofNat m =>
      rcases m with _ | _ | _ | m
      · enc_ed
      · enc_ed
      · enc_ed
      · cases hx

set_option maxHeartbeats 0 in
theorem arity1_ok (op : Op) (x : Arg) (he : (encode' ⟨op, [x]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨op, [x]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨op, [x]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases op <;>
    first
      | (cases hx; done)
      | exact rst_ok x he hc hh hx
      | exact im_ok x he hc hh hx
      | (cases x <;> first | enc_any | (rename_i v; cases v <;> enc_any))

set_option maxHeartbeats 0 in
/-- `bit`, `res` and `set`. -/
theorem bit_ok (op : Op) (hop : op = .bit ∨ op = .res ∨ op = .set) (x y : Arg)
    (he : (encode' ⟨op, [x, y]⟩).run env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env ⟨op, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨op, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> try (rcases hop with rfl | rfl | rfl <;> cases hx; done)
  rename_i v
  cases v with
  | sym l o => rcases hop with rfl | rfl | rfl <;> cases hx
  | num b =>
    by_cases hb : 0 ≤ b ∧ b ≤ 7
    · have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hop with rfl | rfl | rfl <;>
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases y <;> enc_any
    · rcases hop with rfl | rfl | rfl <;> simp [exec, execI, exec2, bitNo?, hb] at hx

set_option maxHeartbeats 0 in
theorem ex2_ok (x y : Arg) (he : (encode' ⟨.ex, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.ex, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.ex, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem add2_ok (x y : Arg) (he : (encode' ⟨.add, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.add, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.add, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem adc2_ok (x y : Arg) (he : (encode' ⟨.adc, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.adc, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.adc, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem sbc2_ok (x y : Arg) (he : (encode' ⟨.sbc, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.sbc, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.sbc, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem jp2_ok (x y : Arg) (he : (encode' ⟨.jp, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.jp, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.jp, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem jr2_ok (x y : Arg) (he : (encode' ⟨.jr, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.jr, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.jr, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem call2_ok (x y : Arg) (he : (encode' ⟨.call, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.call, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.call, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem in2_ok (x y : Arg) (he : (encode' ⟨.in, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.in, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.in, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem out2_ok (x y : Arg) (he : (encode' ⟨.out, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.out, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.out, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

set_option maxHeartbeats 0 in
theorem ld_ok (x y : Arg) (he : (encode' ⟨.ld, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨.ld, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨.ld, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases x <;> first | (cases hx; done) | (cases y <;> enc_any)

theorem arity2_ok (op : Op) (x y : Arg) (he : (encode' ⟨op, [x, y]⟩).run env = .ok bs) (hc : Code s bs)
    (hh : s.halted = false) (hx : exec env ⟨op, [x, y]⟩ s inp = some s') : s.step inp = s' ∧ (Instr.falls ⟨op, [x, y]⟩ = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  cases op <;>
    first
      | (cases hx; done)
      | exact bit_ok _ (Or.inl rfl) x y he hc hh hx
      | exact bit_ok _ (Or.inr (Or.inl rfl)) x y he hc hh hx
      | exact bit_ok _ (Or.inr (Or.inr rfl)) x y he hc hh hx
      | exact ld_ok x y he hc hh hx
      | exact ex2_ok x y he hc hh hx
      | exact add2_ok x y he hc hh hx
      | exact adc2_ok x y he hc hh hx
      | exact sbc2_ok x y he hc hh hx
      | exact jp2_ok x y he hc hh hx
      | exact jr2_ok x y he hc hh hx
      | exact call2_ok x y he hc hh hx
      | exact in2_ok x y he hc hh hx
      | exact out2_ok x y he hc hh hx

/-- **The CPU does what the assembler wrote.**  If `bs` is the encoding
of the instruction `i` (its labels resolved by `env`) and `bs` is in
memory at the program counter of a CPU that is not halted, one step of
the CPU is what `Asm.exec` says `i` does; and unless `i` is a jump, a
call, a return or a block instruction, the program counter is
then after `bs`. -/
theorem step_encode' (i : Instr) (he : (encode' i).run env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env i s inp = some s') : s.step inp = s' ∧ (Instr.falls i = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  obtain ⟨op, args⟩ := i
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · exact arity0_ok op he hc hh hx
  · exact arity1_ok op x he hc hh hx
  · exact arity2_ok op x y he hc hh hx
  · cases hx

theorem step_encode (i : Instr) (he : encode i env = .ok bs) (hc : Code s bs) (hh : s.halted = false)
    (hx : exec env i s inp = some s') : s.step inp = s' ∧ (Instr.falls i = true → s'.pc = s.pc + UInt16.ofNat bs.length) := by
  refine step_encode' i ?_ hc hh hx
  unfold encode at he
  split at he
  · rename_i bs' hb
    cases he
    exact hb
  · cases he

end

/-- info: 'Ember.Proof.Z80Enc.step_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_encode

end Ember.Proof.Z80Enc
