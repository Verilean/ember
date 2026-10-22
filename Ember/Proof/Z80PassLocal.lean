import Ember.Proof.Z80Jump

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
Here, the first step, the rewrites one at a time, from the same CPU
(the relation the two machines keep, and the moved code, are not here):
`packHigh_from`/`packHigh_to` (and `Agree`: everything but `pc`, `R`
and the T-states); `exec_jp_to`, `exec_jr_to`, `exec_jpcc_to`,
`exec_jrcc_to` (`relax`: the same target); `jp_ret`, `jpcc_ret`
(`retThreading`; with `exec_retcc` and `cond_invert`, `peephole`'s
`jp cc,l; ret; l:`).  Not yet: `sweep` (what is not reached), the tail
call of `peephole`, and the theorem that the image as built by default
does what the image without the passes does.
-/

namespace Ember.Proof.PassLocal
open Ember.Z80 Ember.Z80.Asm Ember.Proof.Z80Gen

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

/-! ## `Asm.relax`: `jp` → `jr` -/

theorem ofNat_toNat16 {x : Nat} (hx : x < 65536) : (UInt16.ofNat x).toNat = x := by
  show x % 2 ^ 16 = x
  exact Nat.mod_eq_of_lt hx

/-- `jp nn` goes to `nn`. -/
theorem exec_jp_to (env : Env) (v : Val) (x : Nat) (hv : env.val v = Int.ofNat x) (hx : x < 65536) (s : Cpu)
    (inp : UInt16 → UInt8) :
    exec env ⟨.jp, [.imm v]⟩ s inp = some { op1 s with pc := UInt16.ofNat x, cycles := (op1 s).cycles + 10 } := by
  have hw := immW_toNat env ⟨.jp, [.imm v]⟩ v x rfl hv hx
  have e : Instr.immW env ⟨.jp, [.imm v]⟩ = UInt16.ofNat x := by
    apply UInt16.toNat_inj.mp; rw [hw, ofNat_toNat16 hx]
  simp only [exec, execI, exec1, skip, Cpu.tick, e]

/-- `jr e` at its address goes where the `jp` would, the target within reach. -/
theorem exec_jr_to (env : Env) (v : Val) (x : Nat) (hv : env.val v = Int.ofNat x) (hx : x < 65536) (s : Cpu)
    (inp : UInt16 → UInt8) (hpc : env.pc = Int.ofNat s.pc.toNat)
    (d0 : -128 ≤ Int.ofNat x - (env.pc + 2)) (d1 : Int.ofNat x - (env.pc + 2) ≤ 127) :
    exec env ⟨.jr, [.imm v]⟩ s inp = some { op1 s with pc := UInt16.ofNat x, cycles := (op1 s).cycles + 12 } := by
  have hb : Instr.immB env ⟨.jr, [.imm v]⟩ = byteOf (Int.ofNat x - (env.pc + 2)) := by
    simp only [Instr.immB, Instr.immInt, Instr.immVal?, List.findSome?, hv]; rfl
  have hs := sext_val _ d0 d1
  have e : s.pc + 1 + 1 + Cpu.sext (byteOf (Int.ofNat x - (env.pc + 2))) = UInt16.ofNat x := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, ofNat_toNat16 hx]
    have := s.pc.toNat_lt
    rw [hpc] at hs d0 d1 ⊢
    simp only [UInt16.toNat_one, Int.ofNat_eq_natCast] at hs d0 d1 ⊢
    omega
  simp only [exec, execI, exec1, skip, Cpu.tick, hb, op1, Cpu.bumpR, e]

/-- `jp cc,nn`: to `nn` or past its three bytes. -/
theorem exec_jpcc_to (env : Env) (cc : Arg) (k : UInt8) (hk : cc? cc = some k) (v : Val) (x : Nat)
    (hv : env.val v = Int.ofNat x) (hx : x < 65536) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.jp, [cc, .imm v]⟩ s inp = some (if (op1 s).cond k
      then { op1 s with pc := UInt16.ofNat x, cycles := (op1 s).cycles + 10 }
      else { op1 s with pc := (op1 s).pc + 2, cycles := (op1 s).cycles + 10 }) := by
  have hw := immW_toNat env ⟨.jp, [cc, .imm v]⟩ v x (by cases cc <;> first | rfl | cases hk) hv hx
  have e : Instr.immW env ⟨.jp, [cc, .imm v]⟩ = UInt16.ofNat x := by
    apply UInt16.toNat_inj.mp; rw [hw, ofNat_toNat16 hx]
  have h2 : exec env ⟨.jp, [cc, .imm v]⟩ s inp = exec2 .jp cc (.imm v) (Instr.immB env ⟨.jp, [cc, .imm v]⟩)
      (Instr.immW env ⟨.jp, [cc, .imm v]⟩) (op1 s) (op2 s) inp := rfl
  rw [h2, e]
  cases cc <;> simp only [cc?, reduceCtorEq] at hk <;> cases hk <;>
    simp only [exec2, cc?, Option.map_some, skip, Cpu.tick] <;> split <;> rfl

/-- `jr cc,e` at its address (`cc` of `nz z nc c`): where the `jp` would go, or past its two bytes. -/
theorem exec_jrcc_to (env : Env) (cc : Arg) (k : UInt8) (hk : cc? cc = some k) (hk3 : k ≤ 3) (v : Val) (x : Nat)
    (hv : env.val v = Int.ofNat x) (hx : x < 65536) (s : Cpu) (inp : UInt16 → UInt8)
    (hpc : env.pc = Int.ofNat s.pc.toNat)
    (d0 : -128 ≤ Int.ofNat x - (env.pc + 2)) (d1 : Int.ofNat x - (env.pc + 2) ≤ 127) :
    exec env ⟨.jr, [cc, .imm v]⟩ s inp = some (if (op1 s).cond k
      then { op1 s with pc := UInt16.ofNat x, cycles := (op1 s).cycles + 12 }
      else { op1 s with pc := (op1 s).pc + 1, cycles := (op1 s).cycles + 7 }) := by
  have hb : Instr.immB env ⟨.jr, [cc, .imm v]⟩ = byteOf (Int.ofNat x - (env.pc + 2)) := by
    have hi : (⟨.jr, [cc, .imm v]⟩ : Instr).immVal? = some v := by cases cc <;> first | rfl | cases hk
    simp only [Instr.immB, Instr.immInt, hi, hv]; rfl
  have hs := sext_val _ d0 d1
  have e : s.pc + 1 + 1 + Cpu.sext (byteOf (Int.ofNat x - (env.pc + 2))) = UInt16.ofNat x := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, ofNat_toNat16 hx]
    have := s.pc.toNat_lt
    rw [hpc] at hs d0 d1 ⊢
    simp only [UInt16.toNat_one, Int.ofNat_eq_natCast] at hs d0 d1 ⊢
    omega
  have h2 : exec env ⟨.jr, [cc, .imm v]⟩ s inp = exec2 .jr cc (.imm v) (Instr.immB env ⟨.jr, [cc, .imm v]⟩)
      (Instr.immW env ⟨.jr, [cc, .imm v]⟩) (op1 s) (op2 s) inp := rfl
  rw [h2, hb]
  have hk' : ¬ k > 3 := by
    intro h; exact absurd hk3 (by simpa [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] using h)
  cases cc <;> simp only [cc?, reduceCtorEq] at hk <;> cases hk <;>
    simp only [exec2, cc?, Option.bind_some, skip, Cpu.tick, op1, Cpu.bumpR, e] at hk' ⊢ <;>
    simp only [hk', if_false] <;> split <;> rfl

/-! ## `retThreading`: a jump to a `ret` returns -/

def retI : Instr := ⟨.ret, []⟩

/-- `ret` pops the program counter. -/
theorem exec_ret (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env retI s inp = some ((retTo (op1 s)).tick 10) := rfl

/-- **`jp l` where `l` is a `ret`, then that `ret`** leaves what the
`ret` in its place leaves, but for `R` and the T-states. -/
theorem jp_ret (envJ envR envB : Env) (v : Val) (x : Nat) (hv : envJ.val v = Int.ofNat x) (hx : x < 65536)
    (s : Cpu) (inp : UInt16 → UInt8) : ∃ r c,
    (exec envJ ⟨.jp, [.imm v]⟩ s inp).bind (fun s1 => exec envR retI s1 inp) =
      some { (retTo (op1 s)) with r, cycles := c } ∧
    exec envB retI s inp = some { (retTo (op1 s)) with cycles := (op1 s).cycles + 10 } := by
  rw [exec_jp_to envJ v x hv hx s inp]
  exact ⟨(Cpu.bumpR (op1 s)).r, (op1 s).cycles + 10 + 10, rfl, rfl⟩

/-- `ret cc`: pops the program counter, or goes on past its byte. -/
theorem exec_retcc (env : Env) (cc : Arg) (k : UInt8) (hk : cc? cc = some k) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.ret, [cc]⟩ s inp =
      some (if (op1 s).cond k then (retTo (op1 s)).tick 11 else (op1 s).tick 5) := by
  cases cc <;> simp only [cc?, reduceCtorEq] at hk <;> cases hk <;> rfl

/-- **`jp cc,l` where `l` is a `ret`**: when it jumps, the jump then the
`ret` leaves what `ret cc` leaves, but for `R` and the T-states; when it
does not, both go on past their code (3 and 1 bytes) with the same state. -/
theorem jpcc_ret (envJ envR envB : Env) (cc : Arg) (k : UInt8) (hk : cc? cc = some k) (v : Val) (x : Nat)
    (hv : envJ.val v = Int.ofNat x) (hx : x < 65536) (s : Cpu) (inp : UInt16 → UInt8) :
    ((op1 s).cond k = true → ∃ r c c',
      (exec envJ ⟨.jp, [cc, .imm v]⟩ s inp).bind (fun s1 => exec envR retI s1 inp) =
        some { (retTo (op1 s)) with r, cycles := c } ∧
      exec envB ⟨.ret, [cc]⟩ s inp = some { (retTo (op1 s)) with cycles := c' }) ∧
    ((op1 s).cond k = false → ∃ c c',
      exec envJ ⟨.jp, [cc, .imm v]⟩ s inp = some { op1 s with pc := s.pc + 3, cycles := c } ∧
      exec envB ⟨.ret, [cc]⟩ s inp = some { op1 s with pc := s.pc + 1, cycles := c' }) := by
  rw [exec_jpcc_to envJ cc k hk v x hv hx s inp, exec_retcc envB cc k hk s inp]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [h, if_true, Option.bind_some]
    exact ⟨(Cpu.bumpR (op1 s)).r, (op1 s).cycles + 10 + 10, (op1 s).cycles + 11, rfl, rfl⟩
  · simp only [h, if_false, Bool.false_eq_true]
    refine ⟨(op1 s).cycles + 10, (op1 s).cycles + 5, ?_, rfl⟩
    simp only [op1, Cpu.bumpR, UInt16.add_assoc]
    rfl

/-- The condition `invert` gives is the other one. -/
theorem cond_invert (cc inv : Arg) (k k' : UInt8) (hk : cc? cc = some k) (hi : Codegen.invert cc = some inv)
    (hk' : cc? inv = some k') (s : Cpu) : s.cond k' = !s.cond k := by
  cases cc <;> simp only [cc?, Codegen.invert, reduceCtorEq] at hk hi <;> cases hk <;> cases hi <;>
    simp only [cc?, Option.some.injEq] at hk' <;> subst hk' <;> simp [Cpu.cond]

/-- info: 'Ember.Proof.PassLocal.packHigh_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms packHigh_agree

/-- info: 'Ember.Proof.PassLocal.exec_jrcc_to' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exec_jrcc_to

/-- info: 'Ember.Proof.PassLocal.jpcc_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms jpcc_ret

/-- info: 'Ember.Proof.PassLocal.cond_invert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cond_invert

-- the rewrite is `packHigh`'s
#guard Codegen.packHigh (packHighFrom.map .ins) == packHighTo.map .ins

end Ember.Proof.PassLocal
