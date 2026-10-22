import Ember.Proof.Z80Rel

/-!
# Ember.Proof.Z80PassLocal — the passes on the assembly, instruction by instruction (plan M7.3)

`Codegen.build` runs passes on the assembled items unless `passes :=
false` (`retThreading`, `sweep`, `peephole`, `packHigh`, then `Asm.relax`);
the proofs of M7.3 are of the image without them.  The passes change
the code in a few ways only, each a rewrite of a few items:

| pass | rewrite | what it needs |
|---|---|---|
| `packHigh` | `ld l,a; ld h,0; ld h,l; ld l,0` → `ld h,a; ld l,0` | the two do the same but for `pc`, `R`, the T-states (`packHigh_agree`) |
| `Asm.relax` | `jp nn` / `jp cc,nn` → `jr` (`cc` of `nz z nc c`) | the same target, flags kept |
| `retThreading` | `jp l` / `jp cc,l` → `ret` / `ret cc` where `l` is a `ret` | the jump then the `ret` is the `ret` |
| `sweep` | local labels nothing refers to, items after `ret`/`jp`/`jr` up to a label | not reached |
| `peephole` | `call f; ret` → `jp f` (labels between kept); `jp cc,l; ret; l:` → `ret !cc` | a tail call: one return address less on the stack while `f` runs |

Every pass moves the code after it, and the data after the code (the
literals are read through `ld hl,lit…` and a routine of the runtime).
Here, the first step: the relation the two machines keep between the
rewrites (`Agree`: everything but `pc`, `R` and the T-states) and the
rewrite of `packHigh` under it.
-/

namespace Ember.Proof.PassLocal
open Ember.Z80 Ember.Z80.Asm

/-- Two CPUs that agree but for the program counter, `R` and the T-states. -/
def Agree (s t : Cpu) : Prop :=
  { s with pc := 0, r := 0, cycles := 0 } = { t with pc := 0, r := 0, cycles := 0 }

theorem Agree.refl (s : Cpu) : Agree s s := rfl

theorem Agree.symm {s t : Cpu} (h : Agree s t) : Agree t s := Eq.symm h

theorem Agree.trans {s t u : Cpu} (h1 : Agree s t) (h2 : Agree t u) : Agree s u := Eq.trans h1 h2

/-- Instructions in a row that each go on to the next: the state after them. -/
def run (env : Int → Env) : List Instr → Cpu → Option Cpu
  | [], s => some s
  | i :: r, s => (exec (env s.pc.toNat) i s).bind (run env r)

def ldr (x y : Arg) : Instr := { op := .ld, args := [x, y] }
def ld0 (x : Arg) : Instr := { op := .ld, args := [x, .imm (.num 0)] }

/-- What `packHigh` rewrites, and what it writes instead. -/
def packHighFrom : List Instr := [ldr .l .a, ld0 .h, ldr .h .l, ld0 .l]
def packHighTo : List Instr := [ldr .h .a, ld0 .l]

/-- **`packHigh`**: the four instructions and the two do the same — `H`
the accumulator, `L` zero, nothing else but the program counter (past
their 6 and 3 bytes), `R` and the T-states. -/
theorem packHigh_from (env : Int → Env) (s : Cpu) : ∃ r c,
    run env packHighFrom s = some { s with h := s.a, l := 0, io := .none, eiDelay := false, pc := s.pc + 6, r, cycles := c } := by
  cases s
  simp [run, packHighFrom, ldr, ld0, exec, execI, exec2, ldI, op1, Cpu.bumpR, skip, Cpu.tick, Cpu.setReg, Cpu.reg,
    Cpu.idxGet, Cpu.idxSet, Cpu.setHL, Cpu.hl, r8?, rr?, Instr.immB, Instr.immInt, Instr.immVal?, Env.val, value,
    UInt16.add_assoc]
  rfl

theorem packHigh_to (env : Int → Env) (s : Cpu) : ∃ r c,
    run env packHighTo s = some { s with h := s.a, l := 0, io := .none, eiDelay := false, pc := s.pc + 3, r, cycles := c } := by
  cases s
  simp [run, packHighTo, ldr, ld0, exec, execI, exec2, ldI, op1, Cpu.bumpR, skip, Cpu.tick, Cpu.setReg, Cpu.reg,
    Cpu.idxGet, Cpu.idxSet, Cpu.setHL, Cpu.hl, r8?, rr?, Instr.immB, Instr.immInt, Instr.immVal?, Env.val, value,
    UInt16.add_assoc]
  rfl

/-- The two agree from CPUs that agree. -/
theorem packHigh_agree (envA envB : Int → Env) (s t : Cpu) (h : Agree s t) :
    ∃ s' t', run envA packHighFrom s = some s' ∧ run envB packHighTo t = some t' ∧ Agree s' t' ∧
      s'.pc = s.pc + 6 ∧ t'.pc = t.pc + 3 := by
  obtain ⟨r1, c1, h1⟩ := packHigh_from envA s
  obtain ⟨r2, c2, h2⟩ := packHigh_to envB t
  refine ⟨_, _, h1, h2, ?_, rfl, rfl⟩
  revert h; cases s; cases t
  simp only [Agree, Cpu.mk.injEq]
  intros; subst_vars; simp_all

/-- info: 'Ember.Proof.PassLocal.packHigh_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms packHigh_agree

-- the rewrite is `packHigh`'s
#guard Codegen.packHigh (packHighFrom.map .ins) == packHighTo.map .ins

end Ember.Proof.PassLocal
