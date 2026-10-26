import Ember.Proof.Z80PassBlockRom

/-!
# Ember.Proof.Z80PassCert — what the checker of the two images looks at, and what it means (plan M7.3)

The pieces the checker of the two images (`A` without the passes, `B`
with them) is made of, each a computation the kernel can run on the
two images' items and labels, with the fact it stands for:

* `Form.ofInstr?`: the form of an ordinary instruction (`ofInstr?_instr`);
* `valSameB`: an operand the same number in both images, from their
  tables of labels (`valSame_of`: the value under any address of either);
  `hop_of`: then the immediates of a form's instruction are the same.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

/-! ## The form of an instruction -/

/-- The operand value of an instruction: its first immediate or address (a number if none). -/
def argVal (i : Instr) : Val := i.immVal?.getD (.num 0)

/-- The forms an instruction may be, with its operand value. -/
def Form.cands (v : Val) : List Form :=
  [.adcAM, .sbcAM, .andM, .cpM, .orM, .incM, .stA v, .stHL v, .stDEA, .stHLA, .stHLN v, .ldAN v, .ldADE,
    .ldAHL, .ldDENN v, .ldHLNN v, .addAC, .addHLBC, .addHLDE, .addHLHL, .andC, .andL, .andN v, .cpC, .cpN v,
    .cpl, .decA, .decB, .decBC, .decC, .decHL, .di, .exDEHL, .halt, .inA v, .incA, .incB, .incC, .incDE,
    .incHL, .ldAB, .ldAC, .ldAH, .ldAL, .ldAI v, .ldBI v, .ldBCI v, .ldCA, .ldCI v, .ldDH, .ldDEI v, .ldEL,
    .ldHA, .ldHL2, .ldHI v, .ldHLI v, .ldLA, .ldLI v, .orA, .orC, .orD, .orE, .orH, .orL, .orN v, .outA v,
    .rla, .rrL, .sbcHLDE, .srlA, .srlH, .subC, .xorA, .xorN v]

/-- **The form of an ordinary instruction**, if it is one. -/
def Form.ofInstr? (i : Instr) : Option Form := (Form.cands (argVal i)).find? fun f => decide (f.instr = i)

theorem ofInstr?_instr {i : Instr} {f : Form} (h : Form.ofInstr? i = some f) : f.instr = i := by
  have := List.find?_some h
  simpa using this

/-- No form is a relative jump. -/
theorem Form.op_ne (f : Form) : f.instr.op ≠ .jr ∧ f.instr.op ≠ .djnz := by
  cases f <;> simp [Form.instr]

/-! ## Operands the same in both images -/

/-- The value of a symbol in an image: its label (or `equ`), as the assembler resolves it. -/
def symVal (a : Assembled) (s : String) : Option Int := (a.labels.reverse.lookup s).map Int.ofNat

/-- An operand the same number in both images: a number, or a symbol with the same value in both. -/
def valSameB (a b : Assembled) : Val → Bool
  | .num _ => true
  | .sym s _ => symVal a s == symVal b s

theorem env_resolve (a : Assembled) (pc : Nat) (s : String) : (a.env pc).resolve s = symVal a s := rfl

theorem env_val_none (env : Env) (s : String) (off : Int) (h : env.resolve s = none) (hs : env.sizing = false) :
    env.val (.sym s off) = 0 := by
  have hr : (readThe Env : Enc Env) env = Except.ok env := rfl
  simp only [Env.val, value, bind, ReaderT.bind, ReaderT.run, read, Except.bind, hr, h, hs]
  rfl

theorem valSame_of {A B : Code} {v : Val} (h : valSameB A.a B.a v = true) :
    ∀ pa pb, (A.a.env pa).val v = (B.a.env pb).val v := by
  intro pa pb
  cases v with
  | num n => rfl
  | sym s off =>
    have e : symVal A.a s = symVal B.a s := by simpa [valSameB] using h
    cases hs : symVal A.a s with
    | none =>
      rw [env_val_none _ s off (by rw [env_resolve, hs]) rfl,
        env_val_none _ s off (by rw [env_resolve, ← e, hs]) rfl]
    | some n =>
      rw [val_sym _ s off n (by rw [env_resolve, hs]), val_sym _ s off n (by rw [env_resolve, ← e, hs])]

/-- The immediates of a form's instruction the same in both images, when its operand is. -/
theorem hop_of {A B : Code} (f : Form) (h : valSameB A.a B.a (argVal f.instr) = true) :
    ∀ pa pb, f.instr.immB (A.a.env pa) = f.instr.immB (B.a.env pb) ∧
      f.instr.immW (A.a.env pa) = f.instr.immW (B.a.env pb) := by
  cases hv : f.instr.immVal? with
  | some v =>
    have h' : valSameB A.a B.a v = true := by simpa [argVal, hv] using h
    exact imm_same _ v hv (Form.op_ne f) (valSame_of h')
  | none =>
    intro pa pb
    have e : f.instr.immInt (A.a.env pa) = f.instr.immInt (B.a.env pb) := by simp only [Instr.immInt, hv]
    refine ⟨?_, ?_⟩
    · have : (f.instr.op == .jr || f.instr.op == .djnz) = false := by
        obtain ⟨h1, h2⟩ := Form.op_ne f
        revert h1 h2
        cases f.instr.op <;> decide
      simp only [Instr.immB, e, this]; rfl
    · simp only [Instr.immW, e]

/-- info: 'Ember.Proof.PassSim.hop_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hop_of

end Ember.Proof.PassSim
