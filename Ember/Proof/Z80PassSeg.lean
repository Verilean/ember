import Ember.Proof.Z80PassTaint
import Ember.Proof.Z80PassCtl
import Ember.Proof.Z80PassRun

/-!
# Ember.Proof.Z80PassSeg — the relation of the two machines, and its segments (plan M7.3)

The machine of the image without the passes (`A`) and that of an image
with them (`B`), each at an item of its own image, are related
(`Sync`) when:

* the CPUs are equal but for the program counter, `R`, the T-states,
  memory and the stack pointer, `H` and `L` free where `th`, `tl` say
  (`EqvT`);
* their memories are equal on `[lo, hi)`, the RAM below the stack;
* their stacks hold the same calls (`Stk`): for each call, `A`'s return
  address (an item of `A`) and `B`'s (an item of `B`) — or, for a call
  that is a jump in `B` (a tail call), `A`'s alone;
* the devices are in the same state.

Each lemma here is a segment of the two runs, from related states to
related states: an ordinary instruction (`seg_ord`), …  Which items of
the two images go together is the match's (`Z80PassCheck`); the lemmas
take the facts they need about the items as hypotheses.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc

/-- What a call pushed on the stacks. -/
inductive Frame where
  /-- A call in both images: `A`'s return point and `B`'s (item indices), and the item of the
  entry of the function called, in `A`. -/
  | ret (rA rB e : Nat)
  /-- A call of `A` that is a jump in `B`: `A`'s return point and the entry; nothing on `B`'s stack. -/
  | tail (rA e : Nat)
  deriving DecidableEq, Repr

/-- Where the stack's top is: `sp`, or the top of memory when `sp` is 0 (the stack empty). -/
def top (sp : UInt16) : Nat := if sp = 0 then 65536 else sp.toNat

/-- The word at `x`, low byte first. -/
def word (m : ByteArray) (x : Nat) : Nat := (m.get! x).toNat + 256 * (m.get! (x + 1)).toNat

/-- **The two stacks**: from `a` (in `A`'s memory) and `b` (in `B`'s) up to the top of memory, the
frames `G`; every byte at or above `lo`. -/
def Stk (A B : Code) (lo : Nat) : List Frame → Nat → Nat → ByteArray → ByteArray → Prop
  | [], a, b, _, _ => a = 65536 ∧ b = 65536
  | .ret rA rB _ :: G, a, b, mA, mB =>
    lo ≤ a ∧ lo ≤ b ∧ A.addrs[rA]? = some (word mA a) ∧ B.addrs[rB]? = some (word mB b) ∧
      Stk A B lo G (a + 2) (b + 2) mA mB
  | .tail rA _ :: G, a, b, mA, mB =>
    lo ≤ a ∧ A.addrs[rA]? = some (word mA a) ∧ Stk A B lo G (a + 2) b mA mB

/-- The stacks depend on the bytes from their tops up only. -/
theorem Stk.congr {A B : Code} {lo : Nat} : ∀ (G : List Frame) (a b : Nat) (mA mB mA' mB' : ByteArray),
    Stk A B lo G a b mA mB → (∀ x, a ≤ x → mA'.get! x = mA.get! x) → (∀ x, b ≤ x → mB'.get! x = mB.get! x) →
    Stk A B lo G a b mA' mB'
  | [], _, _, _, _, _, _, h, _, _ => h
  | .ret rA rB e :: G, a, b, mA, mB, mA', mB', ⟨h1, h2, h3, h4, h5⟩, hA, hB => by
    refine ⟨h1, h2, ?_, ?_, Stk.congr G (a + 2) (b + 2) mA mB mA' mB' h5
      (fun x hx => hA x (by omega)) (fun x hx => hB x (by omega))⟩
    · unfold word; rw [hA a (by omega), hA (a + 1) (by omega)]; exact h3
    · unfold word; rw [hB b (by omega), hB (b + 1) (by omega)]; exact h4
  | .tail rA e :: G, a, b, mA, mB, mA', mB', ⟨h1, h3, h5⟩, hA, hB => by
    refine ⟨h1, ?_, Stk.congr G (a + 2) b mA mB mA' mB' h5 (fun x hx => hA x (by omega)) hB⟩
    unfold word; rw [hA a (by omega), hA (a + 1) (by omega)]; exact h3

/-- The tops are at or above `lo`, and `A`'s is at or below `B`'s (`B` has fewer frames). -/
theorem Stk.bounds {A B : Code} {lo : Nat} : ∀ (G : List Frame) (a b : Nat) (mA mB : ByteArray),
    Stk A B lo G a b mA mB → a ≤ b ∧ b ≤ 65536 ∧ a + 2 * G.length ≤ 65536 ∧ (G ≠ [] → lo ≤ a)
  | [], _, _, _, _, ⟨h1, h2⟩ => ⟨by omega, by omega, by simp; omega, fun h => absurd rfl h⟩
  | .ret _ _ _ :: G, a, b, mA, mB, ⟨h1, _, _, _, h5⟩ => by
    have := Stk.bounds G _ _ _ _ h5
    exact ⟨by omega, by omega, by simp; omega, fun _ => h1⟩
  | .tail _ _ :: G, a, b, mA, mB, ⟨h1, _, h5⟩ => by
    have := Stk.bounds G _ _ _ _ h5
    exact ⟨by omega, by omega, by simp; omega, fun _ => h1⟩

/-- **The relation of the two machines** at items `kA` of `A` and `kB` of `B`, with the frames `G`
on the stacks and `H`, `L` free where `th`, `tl`. -/
structure Sync (D : Dev) (A B : Code) (lo hi : Nat) (G : List Frame) (kA kB : Nat) (th tl : Bool)
    (x y : Cpu × D.W) : Prop where
  atA : At A.addrs kA x.1
  atB : At B.addrs kB y.1
  LA : Loaded A x.1
  LB : Loaded B y.1
  E : EqvT lo hi th tl x.1 y.1
  stk : Stk A B hi G (top x.1.sp) (top y.1.sp) x.1.mem y.1.mem
  msz : x.1.mem.size = 65536
  rs : x.1.ramStart.toNat ≤ lo
  w : y.2 = x.2

theorem mask_de (th tl : Bool) (s t : Cpu) : (mask th tl s t).de = t.de := by cases t; rfl
theorem mask_io (th tl : Bool) (s t : Cpu) : (mask th tl s t).io = t.io := by cases t; rfl
theorem mask_ramStart (th tl : Bool) (s t : Cpu) : (mask th tl s t).ramStart = t.ramStart := by cases t; rfl

/-- Where the frames are: at or above `lo` (the bottom of the stack), or the stack is empty. -/
theorem Stk.top_ge {A B : Code} {lo : Nat} {G : List Frame} {a b : Nat} {mA mB : ByteArray}
    (h : Stk A B lo G a b mA mB) (hlo : lo ≤ 65536) : lo ≤ a ∧ lo ≤ b := by
  obtain ⟨h1, h2, _, h4⟩ := Stk.bounds G a b mA mB h
  cases G with
  | nil => obtain ⟨e1, e2⟩ := h; omega
  | cons _ _ => have := h4 (by simp); omega

/-- **An ordinary instruction, in both machines**: the same instruction of a form of `Form` at
`kA` in `A` and at `kB` in `B`, with the same operand in both, reading none of `H`, `L` that are
free; the bytes it reads or writes in the RAM below the stack.  One step of each machine keeps the
relation, at the items after, `H`, `L` free that were and are not written. -/
theorem seg_ord (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {kA kB : Nat}
    {th tl : Bool} (f : Form) (hnh : f ≠ .halt)
    (hA : A.items[kA]? = some (.ins f.instr)) (hB : B.items[kB]? = some (.ins f.instr))
    (hop : ∀ pa pb, f.instr.immB (A.a.env pa) = f.instr.immB (B.a.env pb) ∧
      f.instr.immW (A.a.env pa) = f.instr.immW (B.a.env pb))
    (hrh : th = true → f.readsH = false) (hrl : tl = true → f.readsL = false)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y)
    (hhl : f.viaHL = true → lo ≤ x.1.hl.toNat ∧ x.1.hl.toNat < hi)
    (hde : f.viaDE = true → lo ≤ x.1.de.toNat ∧ x.1.de.toNat < hi)
    (hnn : ∀ pa, f.viaNN = true → lo ≤ (f.instr.immW (A.a.env pa)).toNat ∧ (f.instr.immW (A.a.env pa)).toNat + 1 < hi) :
    Sync D A B lo hi G (kA + 1) (kB + 1) (th && !f.writesH) (tl && !f.writesL) (mstep D x) (mstep D y) := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  obtain ⟨pa, hpa, hpcA⟩ := S.atA
  obtain ⟨pb, hpb, hpcB⟩ := S.atB
  have E := S.E
  have hnA := hnn pa
  -- the step of `A`
  obtain ⟨s', hs', hrs', hsz', hrom', hh', hsp'⟩ := ord_rom f lo hi hhi (f.instr.immB (A.a.env pa))
    (f.instr.immW (A.a.env pa)) (D.bus w') sA hhl hde hnA
  obtain ⟨t', ht', E'⟩ := ord_eqvT lo hi hhi f th tl hrh hrl _ _ (D.bus w') sA sB E hhl hde hnA s' hs'
  -- what `B` reads and writes is where `A` does
  have hmB : sB.ramStart = sA.ramStart := by
    have := RegsS.ramStart E.regs; rw [mask_ramStart] at this; exact this.symm
  have hhlB : f.viaHL = true → lo ≤ sB.hl.toNat ∧ sB.hl.toNat < hi := by
    intro hv
    have h1 : th = false := by
      cases th
      · rfl
      · have := hrh rfl; rw [Form.viaHL_readsH f hv] at this; cases this
    have h2 : tl = false := by
      cases tl
      · rfl
      · have := hrl rfl; rw [Form.viaHL_readsL f hv] at this; cases this
    subst h1 h2
    have := RegsS.hl E.regs; rw [mask_ff] at this; rw [← this]; exact hhl hv
  have hdeB : f.viaDE = true → lo ≤ sB.de.toNat ∧ sB.de.toNat < hi := by
    intro hv
    have := RegsS.de E.regs; rw [mask_de] at this; rw [← this]; exact hde hv
  obtain ⟨t'', ht'', hrsT, hszT, hromT, hhT, hspT⟩ := ord_rom f lo hi hhi (f.instr.immB (A.a.env pa))
    (f.instr.immW (A.a.env pa)) (D.bus w') sB hhlB hdeB hnA
  rw [ht'] at ht''
  cases ht''
  have exA : exec (A.a.env pa) f.instr sA (D.bus w') = some s' := hs'
  have exB : exec (B.a.env pb) f.instr sB (D.bus w') = some t' := by
    show execI f.instr (f.instr.immB (B.a.env pb)) (f.instr.immW (B.a.env pb)) sB (D.bus w') = some t'
    rw [← (hop pa pb).1, ← (hop pa pb).2]; exact ht'
  have stA := step_item A.placed S.LA.1 hA hpa hpcA S.LA.2 exA
  have stB := step_item B.placed S.LB.1 hB hpb hpcB S.LB.2 exB
  have hio : t'.io = s'.io := by
    have := RegsS.io E'.regs; rw [mask_io] at this; exact this.symm
  have eA : mstep D (sA, w') = (s', D.dev w' s'.io) := by
    show (sA.step (D.bus w'), D.dev w' (sA.step (D.bus w')).io) = _
    rw [stA.1]
  have eB : mstep D (sB, w') = (t', D.dev w' s'.io) := by
    show (sB.step (D.bus w'), D.dev w' (sB.step (D.bus w')).io) = _
    rw [stB.1, hio]
  rw [eA, eB]
  have hrsL : sA.ramStart.toNat ≤ lo := S.rs
  have htop : hi ≤ top sA.sp ∧ hi ≤ top sB.sp := (S.stk).top_ge hhi
  refine ⟨stA.2 (ord_falls f), stB.2 (ord_falls f),
    S.LA.keep hrs' (fun x (hx : x < sA.ramStart.toNat) => hrom' x (Or.inl (by omega))) (by rw [hh' hnh]; exact S.LA.2),
    S.LB.keep hrsT (fun x (hx : x < sB.ramStart.toNat) => hromT x (Or.inl (by rw [hmB] at hx; omega)))
      (by rw [hhT hnh]; exact S.LB.2), E', ?_, by rw [hsz']; exact S.msz, by rw [hrs']; exact S.rs, rfl⟩
  show Stk A B hi G (top s'.sp) (top t'.sp) s'.mem t'.mem
  rw [hsp', hspT]
  exact Stk.congr G _ _ _ _ _ _ S.stk (fun x hx => hrom' x (Or.inr (by omega)))
    (fun x hx => hromT x (Or.inr (by omega)))

/-- info: 'Ember.Proof.PassSim.seg_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_ord

/-! ## Jumps -/

/-- `op1`, then the program counter and the T-states set: the relation is kept. -/
theorem Eqv.jumped {lo hi : Nat} {s u : Cpu} (E : Eqv lo hi s u) (p q : UInt16) (c d : UInt64) :
    Eqv lo hi (jumped s p c) (jumped u q d) := by
  obtain ⟨p', r', c', m', q', e⟩ := regs_ex E.regs
  subst e
  exact ⟨by cases s; rfl, E.mem, E.msz⟩

theorem mask_jumped (th tl : Bool) (s t : Cpu) (p q : UInt16) (c d : UInt64) :
    mask th tl (jumped s p c) (jumped t q d) = jumped (mask th tl s t) q d := by
  cases s; cases t; rfl

theorem EqvT.jumped {lo hi : Nat} {th tl : Bool} {s t : Cpu} (E : EqvT lo hi th tl s t) (p q : UInt16)
    (c d : UInt64) : EqvT lo hi th tl (jumped s p c) (jumped t q d) := by
  unfold EqvT at *
  rw [mask_jumped]
  exact Eqv.jumped E p q c d

theorem EqvT.f {lo hi : Nat} {th tl : Bool} {s t : Cpu} (E : EqvT lo hi th tl s t) : s.f = t.f := by
  obtain ⟨_, _, _, _, _, e⟩ := regs_ex E.regs
  have : (mask th tl s t).f = t.f := by cases t; rfl
  rw [← this, e]

theorem taken_eq {lo hi : Nat} {th tl : Bool} {s t : Cpu} (E : EqvT lo hi th tl s t) (cc : Option Arg) :
    taken cc s = taken cc t := by
  cases cc with
  | none => rfl
  | some c =>
    simp only [taken, Cpu.cond]
    rw [show s.flag = t.flag by funext m; simp only [Cpu.flag, E.f]]

/-- **A jump in both machines**: at `kA` in `A` a `jp` or a `jr` to the label at `jA`, at `kB` in `B`
one to the same label, at `jB`, with the same condition (or none).  One step of each keeps the
relation, both at their labels or both at the items after. -/
theorem seg_jump (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {kA kB jA jB : Nat} {th tl : Bool}
    {opA opB : Op} {cc : Option Arg} {l : String}
    (hopA : opA = .jp ∨ opA = .jr) (hopB : opB = .jp ∨ opB = .jr)
    (hcc : ∀ c, cc = some c → c = .nz ∨ c = .z ∨ c = .nc ∨ c = .c)
    (hA : A.items[kA]? = some (.ins ⟨opA, cc.toList ++ [.imm (.sym l 0)]⟩)) (hjA : A.items[jA]? = some (.label l))
    (hB : B.items[kB]? = some (.ins ⟨opB, cc.toList ++ [.imm (.sym l 0)]⟩)) (hjB : B.items[jB]? = some (.label l))
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) :
    if taken cc x.1 then Sync D A B lo hi G jA jB th tl (mstep D x) (mstep D y)
    else Sync D A B lo hi G (kA + 1) (kB + 1) th tl (mstep D x) (mstep D y) := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  have hcc1 : ∀ op : Op, ∀ c, cc = some c → op = .jr → c = .nz ∨ c = .z ∨ c = .nc ∨ c = .c := fun _ c h _ => hcc c h
  have hcc2 : ∀ c, cc = some c → (cc? c).isSome := by
    intro c h; rcases hcc c h with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨pA, cA, eA, LA, atA⟩ := jump_mstep D hopA (hcc1 opA) hcc2 hA hjA S.LA S.atA w'
  obtain ⟨pB, cB, eB, LB, atB⟩ := jump_mstep D hopB (hcc1 opB) hcc2 hB hjB S.LB S.atB w'
  rw [eA, eB]
  have ht := taken_eq S.E cc
  have E' := S.E.jumped pA pB cA cB
  have stk : Stk A B hi G (top (jumped sA pA cA).sp) (top (jumped sB pB cB).sp) (jumped sA pA cA).mem
      (jumped sB pB cB).mem := S.stk
  simp only at atA atB ht ⊢
  by_cases hc : taken cc sA = true
  · rw [if_pos hc] at atA ⊢
    rw [ht] at hc
    rw [if_pos hc] at atB
    exact ⟨atA, atB, LA, LB, E', stk, S.msz, S.rs, rfl⟩
  · rw [if_neg hc] at atA ⊢
    rw [ht] at hc
    rw [if_neg hc] at atB
    exact ⟨atA, atB, LA, LB, E', stk, S.msz, S.rs, rfl⟩

/-- info: 'Ember.Proof.PassSim.seg_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_jump

end Ember.Proof.PassSim
