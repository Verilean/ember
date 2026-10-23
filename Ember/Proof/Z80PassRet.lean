import Ember.Proof.Z80PassSeg

/-!
# Ember.Proof.Z80PassRet — returns of the image without the passes that the other image has fewer of (plan M7.3)

The passes on the assembly take returns out: a `jp l` to a `ret` becomes
the `ret` (`retThr`), a `jp cc,l` over a return becomes a `ret` on the
other condition (`condRet`), a `call f` before a return becomes a jump
to `f` (`tail`, a frame on `A`'s stack only).  Here are the segments of
the two runs for those: `A` takes the steps of its returns while `B`
takes one.

* `EqvT.shift`: the relation kept by steps that change only `pc`, `R`,
  the T-states, `SP` and the memory outside the RAM kept equal, on each
  side;
* `RetSeq`: a return of `A` (past labels, a `ret`, or a `jp` to one);
  `retseq_A`: its steps;
* `pop_tails`: `A` returns through the frames that are its own, then
  through the frame of a call of both (`seg_retseq`: `B` returns once).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

set_option linter.constructorNameAsVariable false

/-- A state after an instruction: no I/O pending, no `ei` delay. -/
def normIE (s : Cpu) : Cpu := { s with io := .none, eiDelay := false }

theorem regsS_jumped (s : Cpu) (p : UInt16) (c : UInt64) : RegsS (normIE s) (jumped s p c) := by
  cases s; rfl
theorem regsS_returned (s : Cpu) (c : UInt64) : RegsS (normIE s) (returned s c) := by
  cases s; rfl
theorem normIE_jumped (s : Cpu) (p : UInt16) (c : UInt64) : normIE (jumped s p c) = jumped s p c := by
  cases s; rfl
theorem normIE_returned (s : Cpu) (c : UInt64) : normIE (returned s c) = returned s c := by
  cases s; rfl
theorem regsS_normIE {s t : Cpu} (h : RegsS s t) : RegsS (normIE s) (normIE t) := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex h
  cases s; rfl
theorem normIE_normIE (s : Cpu) : normIE (normIE s) = normIE s := by cases s; rfl

theorem mask_normIE (th tl : Bool) (s t : Cpu) (s' t' : Cpu) (hs : RegsS (normIE s) s') (ht : RegsS (normIE t) t') :
    RegsS (normIE (mask th tl s t)) (mask th tl s' t') := by
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex hs
  obtain ⟨_, _, _, _, _, rfl⟩ := regs_ex ht
  cases s; cases t; rfl

/-- **The relation, after steps of each machine that change only `pc`, `R`, the T-states, `SP` and
the memory outside `[lo, hi)`** (and leave no I/O pending, no `ei` delay). -/
theorem EqvT.shift {lo hi : Nat} {th tl : Bool} {s t s' t' : Cpu} (E : EqvT lo hi th tl s t)
    (hs : RegsS (normIE s) s') (hsm : ∀ x, lo ≤ x → x < hi → s'.mem.get! x = s.mem.get! x)
    (hsz : s'.mem.size = s.mem.size)
    (ht : RegsS (normIE t) t') (htm : ∀ x, lo ≤ x → x < hi → t'.mem.get! x = t.mem.get! x)
    (htz : t'.mem.size = t.mem.size) : EqvT lo hi th tl s' t' := by
  unfold EqvT at *
  have hm : RegsS (normIE (mask th tl s t)) (mask th tl s' t') := mask_normIE th tl s t s' t' hs ht
  have hmm : (mask th tl s' t').mem = t'.mem := by cases t'; rfl
  have hmm' : (mask th tl s t).mem = t.mem := by cases t; rfl
  refine ⟨?_, fun x h1 h2 => ?_, ?_⟩
  · exact (hs.symm.trans (regsS_normIE E.regs)).trans hm
  · rw [hmm, hsm x h1 h2, htm x h1 h2, ← hmm']; exact E.mem x h1 h2
  · rw [hmm, hsz, htz, ← hmm']; exact E.msz

/-! ## Labels, and returns of `A` -/

/-- Labels from `k` up to `j`. -/
def LabelsTo (C : Code) (k j : Nat) : Prop :=
  k ≤ j ∧ ∀ i, k ≤ i → i < j → ∃ l, C.items[i]? = some (.label l)

theorem at_labels {C : Code} {k j : Nat} (h : LabelsTo C k j) {s : Cpu} (hat : At C.addrs k s) : At C.addrs j s := by
  obtain ⟨hkj, hl⟩ := h
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
  clear hkj
  induction d with
  | zero => exact hat
  | succ d ih =>
    have h' := ih (fun i h1 h2 => hl i h1 (by omega))
    obtain ⟨l, hi⟩ := hl (k + d) (by omega) (by omega)
    exact at_skip C.placed hi (fun _ => rfl) h'

/-- A `ret` past labels. -/
def RetAt (C : Code) (k : Nat) : Prop := ∃ j, LabelsTo C k j ∧ C.items[j]? = some (.ins ⟨.ret, []⟩)

/-- **A return of `A`**: past labels, a `ret`, or a `jp` to a `ret` (past labels). -/
def RetSeq (C : Code) (k : Nat) : Prop :=
  ∃ j, LabelsTo C k j ∧ (C.items[j]? = some (.ins ⟨.ret, []⟩) ∨
    ∃ l jl, C.items[j]? = some (.ins ⟨.jp, [.imm (.sym l 0)]⟩) ∧ C.items[jl]? = some (.label l) ∧ RetAt C jl)

theorem RetAt.retSeq {C : Code} {k : Nat} (h : RetAt C k) : RetSeq C k := by
  obtain ⟨j, hl, hr⟩ := h
  exact ⟨j, hl, Or.inl hr⟩

/-- **The steps of a return of `A`**: one or two; the state as before but `pc` the word at `SP`, `SP`
two more, `R` and the T-states. -/
theorem retseq_A (D : Dev) {C : Code} {k : Nat} (h : RetSeq C k) {s : Cpu} (L : Loaded C s)
    (hat : At C.addrs k s) (w : D.W) (hsp : s.sp ≠ 0) :
    ∃ n s', 1 ≤ n ∧ mrun D n (s, w) = (s', w) ∧ Loaded C s' ∧ RegsS (normIE s) s' ∧ s'.mem = s.mem ∧
      s'.sp = s.sp + 2 ∧ s'.pc = s.rd16 s.sp ∧ NZ D (s, w) n := by
  obtain ⟨j, hl, hj⟩ := h
  have hat' := at_labels hl hat
  rcases hj with hr | ⟨l, jl, hjp, hlab, hra⟩
  · have st := ret_mstep D (cc := none) (fun _ h => by cases h) hr L hat' w
    simp only [taken, if_true] at st
    obtain ⟨c, e⟩ := st
    exact ⟨1, returned s c, Nat.le_refl _, e, ⟨L.1.congr rfl (returned_mem _ _), L.2⟩, regsS_returned s c, rfl, rfl, rfl,
      NZ.le1 _ _ (Nat.le_refl _)⟩
  · obtain ⟨p, c, e1, L1, at1⟩ := jump_mstep D (op := .jp) (cc := none) (Or.inl rfl) (fun _ h => by cases h)
      (fun _ h => by cases h) hjp hlab L hat' w
    simp only [taken, if_true] at at1
    obtain ⟨j2, hl2, hr2⟩ := hra
    have at2 := at_labels hl2 at1
    have st := ret_mstep D (cc := none) (fun _ h => by cases h) hr2 L1 at2 w
    simp only [taken, if_true] at st
    obtain ⟨c2, e2⟩ := st
    have hm : (returned (jumped s p c) c2).mem = s.mem := by rw [returned_mem]; rfl
    have hsp' : (returned (jumped s p c) c2).sp = s.sp + 2 := by rw [returned_sp]; rfl
    have hpc : (returned (jumped s p c) c2).pc = s.rd16 s.sp := by rw [returned_pc]; rfl
    have h2 := regsS_returned (jumped s p c) c2
    rw [normIE_jumped] at h2
    have L2 : Loaded C (returned (jumped s p c) c2) := ⟨L1.1.congr rfl (returned_mem _ _), L1.2⟩
    have e : mrun D 2 (s, w) = (returned (jumped s p c) c2, w) := by
      show mstep D (mstep D (s, w)) = _
      rw [e1, e2]
    exact ⟨2, returned (jumped s p c) c2, by omega, e, L2, (regsS_jumped s p c).trans h2, hm, hsp', hpc,
      NZ.cons (b := 1) e1 (fun _ => hsp) (NZ.le1 _ _ (Nat.le_refl _))⟩

/-- info: 'Ember.Proof.PassSim.retseq_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retseq_A

/-! ## Returns through `A`'s own frames -/

theorem top_ne {sp : UInt16} (h : top sp + 2 ≤ 65536) : top sp = sp.toNat ∧ sp.toNat + 2 ≤ 65536 := by
  by_cases h0 : sp = 0
  · exfalso; simp only [top, h0, if_true] at h; omega
  · have e : top sp = sp.toNat := by simp only [top, h0, if_false]
    exact ⟨e, by omega⟩

/-- **`A` returns through a frame of its own** (a call that is a jump in `B`): the steps of the return
at `k`, to the frame's return point, the frame popped; `B`'s stack as it was. -/
theorem pop_tail (D : Dev) {A B : Code} {lo : Nat} {k r e b : Nat} {G : List Frame} {mB : ByteArray}
    (hk : RetSeq A k) {s : Cpu} (L : Loaded A s) (hat : At A.addrs k s) (w : D.W)
    (st : Stk A B lo (.tail r e :: G) (top s.sp) b s.mem mB) :
    ∃ n s', 1 ≤ n ∧ mrun D n (s, w) = (s', w) ∧ Loaded A s' ∧ At A.addrs r s' ∧ RegsS (normIE s) s' ∧
      s'.mem = s.mem ∧ top s'.sp = top s.sp + 2 ∧ Stk A B lo G (top s'.sp) b s'.mem mB ∧ NZ D (s, w) n := by
  obtain ⟨n, s', hn, e, L', hr, hm, hsp, hpc, nz⟩ := retseq_A D hk L hat w (Stk.sp_ne st (List.cons_ne_nil _ _))
  obtain ⟨h1, hw, rest⟩ := st
  have bnd := Stk.bounds G _ _ _ _ rest
  obtain ⟨t1, t2⟩ := top_ne (sp := s.sp) (by omega)
  have ht' : top s'.sp = top s.sp + 2 := by rw [hsp, top_add2 _ (by omega), t1]
  refine ⟨n, s', hn, e, L', ⟨_, hw, ?_⟩, hr, hm, ht', by rw [ht', hm]; exact rest, nz⟩
  rw [hpc, t1, rd16_word s (by omega)]

/-- info: 'Ember.Proof.PassSim.pop_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_tail

/-- `A`'s own frames, each `(return point, entry)`. -/
def tails (ts : List (Nat × Nat)) : List Frame := ts.map fun p => .tail p.1 p.2

/-- **`A` returns through its own frames and then through a frame of both, `B` returns once**, from a
state of `A` some steps on (`a`, at a return `k0`: nothing changed but `pc`, `R`, the T-states): `A`
a return there (`RetSeq`), and one at each return point of its own frames; `B` a `ret`.  Then some
steps of `A` and one of `B` reach the return points of the frame of both, that frame popped. -/
theorem seg_retseq_from (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {rA rB e kA kB : Nat}
    {th tl : Bool} {ts : List (Nat × Nat)} {x y : Cpu × D.W} {ccB : Option Arg} (hccB : ∀ c, ccB = some c → (cc? c).isSome)
    (hB : B.items[kB]? = some (.ins ⟨.ret, ccB.toList⟩)) (htB : taken ccB y.1 = true)
    (hts : ∀ p, p ∈ ts → RetSeq A p.1) {G0 : List Frame}
    (S : Sync D A B lo hi G0 kA kB th tl x y)
    {m0 k0 : Nat} {a : Cpu} (em0 : mrun D m0 x = (a, x.2)) (La : Loaded A a) (hat0 : At A.addrs k0 a)
    (hk0 : RetSeq A k0) (hr0 : RegsS (normIE x.1) (normIE a)) (hm0 : a.mem = x.1.mem)
    (hst : Stk A B hi (tails ts ++ .ret rA rB e :: G) (top a.sp) (top y.1.sp) a.mem y.1.mem)
    (hnz0 : NZ D x m0) :
    ∃ n, m0 + 1 ≤ n ∧ Sync D A B lo hi G rA rB th tl (mrun D n x) (mstep D y) ∧ NZ D x n := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  simp only at em0 hr0 hm0 hst htB hnz0
  -- `A` through its own frames: a state at a return, the frame of both on top
  have core : ∀ (ts : List (Nat × Nat)) (k : Nat) (s : Cpu) (m : Nat), (∀ p, p ∈ ts → RetSeq A p.1) →
      RetSeq A k → mrun D m (sA, w') = (s, w') → Loaded A s → At A.addrs k s → RegsS (normIE sA) (normIE s) →
      s.mem = sA.mem → Stk A B hi (tails ts ++ .ret rA rB e :: G) (top s.sp) (top sB.sp) s.mem sB.mem →
      NZ D (sA, w') m →
      ∃ m' s' k', m ≤ m' ∧ mrun D m' (sA, w') = (s', w') ∧ Loaded A s' ∧ At A.addrs k' s' ∧ RetSeq A k' ∧
        RegsS (normIE sA) (normIE s') ∧ s'.mem = sA.mem ∧
        Stk A B hi (.ret rA rB e :: G) (top s'.sp) (top sB.sp) s'.mem sB.mem ∧ NZ D (sA, w') m' := by
    intro ts
    induction ts with
    | nil =>
      intro k s m _ hk em L hat hr hm st nz
      exact ⟨m, s, k, Nat.le_refl _, em, L, hat, hk, hr, hm, st, nz⟩
    | cons p ts ih =>
      intro k s m hts' hk em L hat hr hm st nz
      obtain ⟨n, s', hn, e1, L', at', hr', hm', _, st', nz1⟩ := pop_tail D hk L hat w' st
      have hr2 : RegsS (normIE sA) (normIE s') := by
        have := regsS_normIE hr'; rw [normIE_normIE] at this; exact hr.trans this
      have em' : mrun D (m + n) (sA, w') = (s', w') := by rw [mrun_add, em, e1]
      have nz' : NZ D (sA, w') (m + n) := NZ.pre nz em (fun _ _ => Stk.sp_ne st (by simp [tails])) nz1
      obtain ⟨m', s'', k'', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih p.1 s' (m + n)
        (fun q hq => hts' q (List.mem_cons_of_mem _ hq)) (hts' p (List.mem_cons_self ..)) em' L' at' hr2
        (by rw [hm', hm]) st' nz'
      exact ⟨m', s'', k'', by omega, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨m, s, k, hm0', em, L, hat, hk, hr, hm, st, nzm⟩ := core ts k0 a m0 hts hk0 em0 La hat0 hr0 hm0 hst hnz0
  -- the last return of `A`, the `ret` of `B`
  have hs0 : s.sp ≠ 0 := Stk.sp_ne st (List.cons_ne_nil _ _)
  obtain ⟨n, s', hn, e1, L', hr', hm', hsp, hpc, nzn⟩ := retseq_A D hk L hat w' hs0
  have stB := ret_mstep D hccB hB S.LB S.atB w'
  rw [if_pos htB] at stB
  obtain ⟨cB, eB⟩ := stB
  obtain ⟨h1A, h1B, wA, wB, rest⟩ := st
  have bnd := Stk.bounds G _ _ _ _ rest
  obtain ⟨tA1, tA2⟩ := top_ne (sp := s.sp) (by omega)
  obtain ⟨tB1, tB2⟩ := top_ne (sp := sB.sp) (by omega)
  refine ⟨m + n, by omega, ?_, NZ.pre nzm em (fun _ _ => hs0) nzn⟩
  rw [mrun_add, em, e1, eB]
  have hsz : sA.mem.size = 65536 := S.msz
  have hr2 : RegsS (normIE sA) s' := hr.trans hr'
  have hm2 : s'.mem = sA.mem := by rw [hm', hm]
  have hpA : s'.pc.toNat = word s.mem (top s.sp) := by rw [hpc, tA1, rd16_word s (by omega)]
  have hpB : (returned sB cB).pc.toNat = word sB.mem (top sB.sp) := by
    rw [returned_pc, tB1, rd16_word sB (by omega)]
  have hrs : s'.ramStart = sA.ramStart := (RegsS.ramStart hr2).symm
  refine ⟨⟨_, wA, hpA⟩, ⟨_, wB, hpB⟩, L', ⟨S.LB.1.congr rfl (returned_mem _ _), S.LB.2⟩, ?_, ?_,
    by rw [hm2]; exact hsz, by rw [hrs]; exact S.rs, rfl⟩
  · exact EqvT.shift S.E hr2 (fun x _ _ => by rw [hm2]) (by rw [hm2]) (regsS_returned sB cB)
      (fun x _ _ => by rw [returned_mem]) (by rw [returned_mem])
  · show Stk A B hi G (top s'.sp) (top (returned sB cB).sp) s'.mem (returned sB cB).mem
    rw [hsp, top_add2 _ (by omega), returned_sp, top_add2 _ (by omega), returned_mem, hm', ← tA1, ← tB1]
    exact rest

/-- **`A` returns through its own frames and then through a frame of both, `B` returns once**: `A` a
return at `kA` (`RetSeq`), and one at each return point of its own frames; `B` a `ret`.  Then some
steps of `A` and one of `B` reach the return points of the frame of both, that frame popped. -/
theorem seg_retseq (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {rA rB e kA kB : Nat} {th tl : Bool}
    {ts : List (Nat × Nat)} (hA : RetSeq A kA) (hB : B.items[kB]? = some (.ins ⟨.ret, []⟩))
    (hts : ∀ p, p ∈ ts → RetSeq A p.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) kA kB th tl x y) :
    ∃ n, 1 ≤ n ∧ Sync D A B lo hi G rA rB th tl (mrun D n x) (mstep D y) ∧ NZ D x n :=
  seg_retseq_from D (ccB := none) (fun _ h => by cases h) hB rfl hts S (m0 := 0) rfl S.LA S.atA hA rfl rfl S.stk
    (NZ.le1 _ _ (Nat.zero_le _))

/-- info: 'Ember.Proof.PassSim.seg_retseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_retseq

/-! ## A return on a condition, the jump over a return, the call that is a jump -/

theorem taken_invert {c c' : Arg} (h : Codegen.invert c = some c') (s : Cpu) :
    taken (some c') s = !taken (some c) s := by
  cases c <;> simp [Codegen.invert] at h <;> subst h <;> simp [taken, cc?, Cpu.cond]

/-- **`jp cc,l` in `A` where `l` is a `ret`, `ret cc` in `B`** (`retThr` on a condition): taken,
`A` jumps and returns through its own frames and the frame of both, `B` returns; not taken, both go
on. -/
theorem seg_retThrCC (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {rA rB e kA kB jl : Nat}
    {th tl : Bool} {ts : List (Nat × Nat)} {c : Arg} {l : String}
    (hc : c = .nz ∨ c = .z ∨ c = .nc ∨ c = .c)
    (hA : A.items[kA]? = some (.ins ⟨.jp, [c, .imm (.sym l 0)]⟩)) (hjl : A.items[jl]? = some (.label l))
    (hr : RetAt A jl) (hB : B.items[kB]? = some (.ins ⟨.ret, [c]⟩)) (hts : ∀ p, p ∈ ts → RetSeq A p.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) kA kB th tl x y) :
    if taken (some c) x.1 then ∃ n, 1 ≤ n ∧ Sync D A B lo hi G rA rB th tl (mrun D n x) (mstep D y) ∧ NZ D x n
    else Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) (kA + 1) (kB + 1) th tl (mstep D x) (mstep D y) := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  have hcc : (cc? c).isSome := by rcases hc with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨p, cy, eA, LA1, atA1⟩ := jump_mstep D (op := .jp) (cc := some c) (Or.inl rfl) (fun _ _ h => by cases h)
    (fun _ h => by cases h; exact hcc) hA hjl S.LA S.atA w'
  have stB := ret_mstep D (cc := some c) (fun _ h => by cases h; exact hcc) hB S.LB S.atB w'
  have ht := taken_eq S.E (some c)
  simp only at ht ⊢
  by_cases htk : taken (some c) sA = true
  · rw [if_pos htk] at atA1 ⊢
    obtain ⟨n, hn, S'⟩ := seg_retseq_from D (ccB := some c) (fun _ h => by cases h; exact hcc) hB
      (by rw [← ht]; exact htk) hts S (m0 := 1) (by show mstep D (sA, w') = _; rw [eA]) LA1 atA1 hr.retSeq
      (by rw [normIE_jumped]; exact regsS_jumped sA p cy) rfl S.stk (NZ.le1 _ _ (Nat.le_refl _))
    exact ⟨n, by omega, S'⟩
  · rw [if_neg htk] at atA1 ⊢
    rw [ht] at htk
    rw [if_neg htk] at stB
    obtain ⟨pB, cB, eB, atB⟩ := stB
    rw [eA, eB]
    exact ⟨atA1, atB, LA1, ⟨S.LB.1.congr rfl rfl, S.LB.2⟩, S.E.jumped _ _ _ _, S.stk, S.msz, S.rs, rfl⟩

/-- info: 'Ember.Proof.PassSim.seg_retThrCC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_retThrCC


/-- **`ret cc` in both, a frame of `A`'s own on top**: taken, `A` returns through its own frames and the
frame of both, `B` returns; not taken, both go on. -/
theorem seg_retcc_tails (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {rA rB e kA kB : Nat}
    {th tl : Bool} {p : Nat × Nat} {ts : List (Nat × Nat)} {c : Arg} (hc : (cc? c).isSome)
    (hA : A.items[kA]? = some (.ins ⟨.ret, [c]⟩)) (hB : B.items[kB]? = some (.ins ⟨.ret, [c]⟩))
    (hts : ∀ q, q ∈ p :: ts → RetSeq A q.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails (p :: ts) ++ .ret rA rB e :: G) kA kB th tl x y) :
    if taken (some c) x.1 then ∃ n, 1 ≤ n ∧ Sync D A B lo hi G rA rB th tl (mrun D n x) (mstep D y) ∧ NZ D x n
    else Sync D A B lo hi (tails (p :: ts) ++ .ret rA rB e :: G) (kA + 1) (kB + 1) th tl (mstep D x) (mstep D y) := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  have stA := ret_mstep D (cc := some c) (fun _ h => by cases h; exact hc) hA S.LA S.atA w'
  have stB := ret_mstep D (cc := some c) (fun _ h => by cases h; exact hc) hB S.LB S.atB w'
  have ht := taken_eq S.E (some c)
  simp only at ht ⊢
  by_cases htk : taken (some c) sA = true
  · rw [if_pos htk] at stA ⊢
    obtain ⟨cA, eA⟩ := stA
    have st := S.stk
    simp only [tails, List.map_cons, List.cons_append] at st
    obtain ⟨h1, wA, rest⟩ := st
    have bnd := Stk.bounds _ _ _ _ _ rest
    obtain ⟨t1, t2⟩ := top_ne (sp := sA.sp) (by simp at bnd; omega)
    have hpc : (returned sA cA).pc.toNat = word sA.mem (top sA.sp) := by
      rw [returned_pc, t1, rd16_word sA (by omega)]
    have htop : top (returned sA cA).sp = top sA.sp + 2 := by rw [returned_sp, top_add2 _ (by omega), t1]
    obtain ⟨n, hn, S'⟩ := seg_retseq_from D (x := (sA, w')) (y := (sB, w')) (a := returned sA cA) (ccB := some c)
      (fun _ h => by cases h; exact hc) hB
      (by show taken (some c) sB = true; rw [← ht]; exact htk) (fun q hq => hts q (List.mem_cons_of_mem _ hq)) S (m0 := 1)
      (by show mstep D (sA, w') = _; rw [eA]) ⟨S.LA.1.congr rfl (returned_mem _ _), S.LA.2⟩ ⟨_, wA, hpc⟩
      (hts p (List.mem_cons_self ..)) (by rw [normIE_returned]; exact regsS_returned sA cA) (returned_mem _ _)
      (by rw [htop, returned_mem]; exact rest) (NZ.le1 _ _ (Nat.le_refl _))
    exact ⟨n, by omega, S'⟩
  · rw [if_neg htk] at stA ⊢
    rw [ht] at htk
    rw [if_neg htk] at stB
    obtain ⟨pA, cA, eA, atA⟩ := stA
    obtain ⟨pB, cB, eB, atB⟩ := stB
    rw [eA, eB]
    exact ⟨atA, atB, ⟨S.LA.1.congr rfl rfl, S.LA.2⟩, ⟨S.LB.1.congr rfl rfl, S.LB.2⟩, S.E.jumped _ _ _ _,
      S.stk, S.msz, S.rs, rfl⟩

/-- info: 'Ember.Proof.PassSim.seg_retcc_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_retcc_tails

/-- **`jp cc,l` over a return in `A`, `ret` on the other condition in `B`** (`condRet`; `l` after the
return): when `A` jumps, `B` goes on, both after the return; when it does not, `A` returns (through
its own frames and the frame of both) and so does `B`. -/
theorem seg_condRet (D : Dev) {A B : Code} {lo hi : Nat} {G : List Frame} {rA rB e kA kB jl : Nat}
    {th tl : Bool} {ts : List (Nat × Nat)} {c c' : Arg} {l : String}
    (hc : c = .nz ∨ c = .z ∨ c = .nc ∨ c = .c) (hinv : Codegen.invert c = some c')
    (hA : A.items[kA]? = some (.ins ⟨.jp, [c, .imm (.sym l 0)]⟩)) (hjl : A.items[jl]? = some (.label l))
    (hr : RetSeq A (kA + 1)) (hB : B.items[kB]? = some (.ins ⟨.ret, [c']⟩)) (hts : ∀ p, p ∈ ts → RetSeq A p.1)
    {x y : Cpu × D.W} (S : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) kA kB th tl x y) :
    if taken (some c) x.1 then
      Sync D A B lo hi (tails ts ++ .ret rA rB e :: G) jl (kB + 1) th tl (mstep D x) (mstep D y)
    else ∃ n, 1 ≤ n ∧ Sync D A B lo hi G rA rB th tl (mrun D n x) (mstep D y) ∧ NZ D x n := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  have hcc : (cc? c).isSome := by rcases hc with rfl | rfl | rfl | rfl <;> rfl
  have hcc' : (cc? c').isSome := by
    rcases hc with rfl | rfl | rfl | rfl <;> simp [Codegen.invert] at hinv <;> subst hinv <;> rfl
  obtain ⟨p, cy, eA, LA1, atA1⟩ := jump_mstep D (op := .jp) (cc := some c) (Or.inl rfl) (fun _ _ h => by cases h)
    (fun _ h => by cases h; exact hcc) hA hjl S.LA S.atA w'
  have stB := ret_mstep D (cc := some c') (fun _ h => by cases h; exact hcc') hB S.LB S.atB w'
  have ht := taken_eq S.E (some c)
  have hi := taken_invert hinv sB
  simp only at ht ⊢
  by_cases htk : taken (some c) sA = true
  · rw [if_pos htk] at atA1 ⊢
    have hnB : ¬ taken (some c') sB = true := by rw [hi, ← ht, htk]; decide
    rw [if_neg hnB] at stB
    obtain ⟨pB, cB, eB, atB⟩ := stB
    rw [eA, eB]
    exact ⟨atA1, atB, LA1, ⟨S.LB.1.congr rfl rfl, S.LB.2⟩, S.E.jumped _ _ _ _, S.stk, S.msz, S.rs, rfl⟩
  · rw [if_neg htk] at atA1 ⊢
    have hB' : taken (some c') sB = true := by
      rw [hi, ← ht]; cases h : taken (some c) sA <;> simp_all
    obtain ⟨n, hn, S'⟩ := seg_retseq_from D (ccB := some c') (fun _ h => by cases h; exact hcc') hB hB' hts S
      (m0 := 1) (by show mstep D (sA, w') = _; rw [eA]) LA1 atA1 hr
      (by rw [normIE_jumped]; exact regsS_jumped sA p cy) rfl S.stk (NZ.le1 _ _ (Nat.le_refl _))
    exact ⟨n, by omega, S'⟩

/-- info: 'Ember.Proof.PassSim.seg_condRet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_condRet

theorem regsS_called (s : Cpu) (nn : UInt16) : RegsS (normIE s) (called s nn) := by
  cases s
  simp only [RegsS, normIE, PassSim.called, callTo, Cpu.push, Cpu.wr16, Cpu.wr, Cpu.tick, skip, op1, Cpu.bumpR]
  (repeat' split) <;> rfl

/-- **A call in `A` that is a jump in `B`** (`tail`): room for the return address above the RAM kept
equal.  One step of each, at the entries: a frame on `A`'s stack only (`tail`). -/
theorem seg_tail (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {kA kB eA eB : Nat} {th tl : Bool} {l : String} {opB : Op} (hopB : opB = .jp ∨ opB = .jr)
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym l 0)]⟩)) (heA : A.items[eA]? = some (.label l))
    (hB : B.items[kB]? = some (.ins ⟨opB, [.imm (.sym l 0)]⟩)) (heB : B.items[eB]? = some (.label l))
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    (room : hi + 2 ≤ top x.1.sp) :
    Sync D A B lo hi (.tail (kA + 1) eA :: G) eA eB th tl (mstep D x) (mstep D y) := by
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  simp only at room
  obtain ⟨TA, adA, hTA, hrA, hpcA, hltA, eA', atA⟩ := call_mstep D hA heA S.LA S.atA w'
  obtain ⟨pB, cB, eB', LB1, atB⟩ := jump_mstep D (op := opB) (cc := none) hopB (fun _ h => by cases h)
    (fun _ h => by cases h) hB heB S.LB S.atB w'
  simp only [taken, if_true] at atB
  rw [eA', eB']
  have hrsA : sA.ramStart.toNat ≤ lo := S.rs
  have hszA : sA.mem.size = 65536 := S.msz
  have bnd := Stk.bounds G _ _ _ _ S.stk
  simp only at bnd
  obtain ⟨tA1, tA2⟩ := top_sub2 sA.sp (by omega)
  have rA' : sA.ramStart.toNat ≤ (sA.sp - 2).toNat := by omega
  have aboveA := called_above sA (UInt16.ofNat TA) hszA (by omega) rA'
  have keepA : ∀ x, x < sA.ramStart.toNat → (called sA (UInt16.ofNat TA)).mem.get! x = sA.mem.get! x :=
    fun x hx => aboveA x (Or.inr (by omega))
  have E' : EqvT lo hi th tl (called sA (UInt16.ofNat TA)) (jumped sB pB cB) :=
    EqvT.shift S.E (regsS_called _ _) (fun x _ h2 => aboveA x (Or.inr (by omega))) (called_size _ _)
      (regsS_jumped _ _ _) (fun _ _ _ => rfl) rfl
  refine ⟨atA, atB, S.LA.keep (called_ramStart _ _) keepA (by rw [called_halted]; exact S.LA.2), LB1, E', ?_,
    by rw [called_size]; exact hszA, by rw [called_ramStart]; exact hrsA, rfl⟩
  show Stk A B hi (.tail (kA + 1) eA :: G) (top (called sA _).sp) (top (jumped sB pB cB).sp)
    (called sA _).mem (jumped sB pB cB).mem
  rw [called_sp, tA1, show (jumped sB pB cB).sp = sB.sp from rfl, show (jumped sB pB cB).mem = sB.mem from rfl]
  refine ⟨by omega, ?_, ?_⟩
  · rw [← tA2, word_called sA _ hszA rA' (by omega), hrA]
    congr 1
    rw [UInt16.toNat_add, hpcA]; simp only [show (3 : UInt16).toNat = 3 from rfl]; omega
  · rw [show top sA.sp - 2 + 2 = top sA.sp by omega]
    exact Stk.congr G _ _ _ _ _ _ S.stk (fun x hx => aboveA x (Or.inl hx)) (fun _ _ => rfl)

/-- info: 'Ember.Proof.PassSim.seg_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_tail

end Ember.Proof.PassSim
