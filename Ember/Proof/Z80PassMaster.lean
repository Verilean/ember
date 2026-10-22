import Ember.Proof.Z80PassChkOK
import Ember.Proof.Z80PassTail
import Ember.Proof.Z80PassBlockRom
import Ember.Proof.Z80PassRun

/-!
# Ember.Proof.Z80PassMaster — the two images, run side by side to the end (plan M7.3)

From a certificate the checker accepts (`check`), the two runs keep the
relation (`Inv`): both halted with the same devices, or at a row of the
certificate — `Sync` at its items, `H` and `L` free where the row lets
them be, the frames on the stacks as the rows of their return points
say (`FOK`), the run of `A` some steps from its start.

What `A`'s run does is taken as a hypothesis here, `SafeA`: at every
item it reaches, the stack is above the RAM kept equal (`hi + 4` below
its top), and the bytes it reads or writes through `HL` and `DE` (an
instruction of a form that does, `ldir`, a call of a routine of the
runtime through `HL` not just after `ld hl,lit`) are in that RAM
`[lo, hi)`.  It is about the image without the passes alone.
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

set_option linter.constructorNameAsVariable false

/-! ## What `A`'s run is taken to do -/

/-- **What `A`'s run needs at item `k`** (state `s`): the stack above `hi + 4`; through `HL` and `DE`,
in `[lo, hi)`. -/
def Need (A : Code) (lo hi : Nat) (k : Nat) (s : Cpu) : Prop :=
  hi + 4 ≤ top s.sp ∧
  ∀ i, A.items[k]? = some (.ins i) →
    (∀ f : Form, f.instr = i →
      (f.viaHL = true → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi) ∧ (f.viaDE = true → lo ≤ s.de.toNat ∧ s.de.toNat < hi)) ∧
    (i = ⟨.ldir, []⟩ → lo ≤ s.hl.toNat ∧ s.hl.toNat < hi ∧ lo ≤ s.de.toNat ∧ s.de.toNat < hi) ∧
    (∀ f, i = ⟨.call, [.imm (.sym f 0)]⟩ → (ptrRoutine f).isSome = true →
      (∀ l, 0 < k → A.items[k - 1]? = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) → ∀ j : Nat, A.items[j]? ≠ some (Item.label l)) →
      lo ≤ s.hl.toNat ∧ s.hl.toNat + 4 ≤ hi)

/-- **`A`'s run from `x0` needs no more**: at every item it is at, not halted. -/
def SafeA (D : Dev) (A : Code) (lo hi : Nat) (x0 : Cpu × D.W) : Prop :=
  ∀ n k, At A.addrs k (mrun D n x0).1 → (mrun D n x0).1.halted = false → Need A lo hi k (mrun D n x0).1

/-! ## The relation kept -/

/-- The row of the certificate at `k`. -/
def rowAt (cert : List Row) (k : Nat) : Row := cert[k]?.getD default

/-- The function whose activation the run is in: the entry of the frame on top. -/
def cur : List Frame → Nat
  | [] => topE
  | .ret _ _ e :: _ => e
  | .tail _ e :: _ => e
  | .data :: G => cur G

/-- `H`, `L` free at most where another pair lets them be. -/
def leT (a b : Bool × Bool) : Prop := (a.1 = true → b.1 = true) ∧ (a.2 = true → b.2 = true)

/-- **The frames as the certificate says**: for a call of both, its return points a row of a meeting
point where the function called may return with `H`, `L` free, in the activation of the frames below;
for a call of `A` only, a return at its return point, the function called returning `H`, `L` free at
most as the one below does, which is a function. -/
def FOK (A : Code) (cert : List Row) (tr : List (Nat × Bool × Bool)) : List Frame → Prop
  | [] => True
  | .ret rA rB e :: G =>
    (rowAt cert rA).tag ≠ .none ∧ (rowAt cert rA).kb = rB ∧
      leT (trOf tr e) ((rowAt cert rA).th, (rowAt cert rA).tl) ∧ cur G ∈ (rowAt cert rA).act ∧ FOK A cert tr G
  | .tail rA e :: G => RetSeq A rA ∧ cur G ≠ topE ∧ leT (trOf tr e) (trOf tr (cur G)) ∧ FOK A cert tr G
  | .data :: _ => False

/-- **The relation the two runs keep**: both halted, the same devices; or at a row of the certificate
that is a meeting point (`Sync` at its items, `H`, `L` free as the row says), the activation among
the row's, the frames as the certificate says; `A`'s state some steps from its start. -/
def Inv (D : Dev) (A B : Code) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool))
    (x0 x y : Cpu × D.W) : Prop :=
  Done D x y ∨
    ∃ G k, (rowAt cert k).tag ≠ .none ∧
      Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y ∧
      cur G ∈ (rowAt cert k).act ∧ FOK A cert tr G ∧ ∃ n, x = mrun D n x0

/-! ## `H`, `L` free in more places -/

theorem EqvT.mono {lo hi : Nat} {th tl th' tl' : Bool} {s t : Cpu} (E : EqvT lo hi th tl s t)
    (h1 : th = true → th' = true) (h2 : tl = true → tl' = true) : EqvT lo hi th' tl' s t := by
  have hh : th = false → s.h = t.h := by
    intro e; subst e
    obtain ⟨_, _, _, _, _, e⟩ := regs_ex E.regs
    have : (mask false tl s t).h = t.h := by cases t; rfl
    rw [← this, e]
  have hl : tl = false → s.l = t.l := by
    intro e; subst e
    obtain ⟨_, _, _, _, _, e⟩ := regs_ex E.regs
    have : (mask th false s t).l = t.l := by cases t; rfl
    rw [← this, e]
  have hm : mask th' tl' s t = mask th tl s t := by
    cases th <;> cases tl <;> cases th' <;> cases tl' <;> simp_all [mask]
  unfold EqvT at *
  rw [hm]; exact E

theorem Sync.mono {D : Dev} {A B : Code} {lo hi : Nat} {G : List Frame} {kA kB : Nat} {th tl th' tl' : Bool}
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) (h1 : th = true → th' = true)
    (h2 : tl = true → tl' = true) : Sync D A B lo hi G kA kB th' tl' x y :=
  { S with E := S.E.mono h1 h2 }

/-! ## What the checks at rows say -/

theorem succOK_spec {r : Row} {kb : Nat} {th tl : Bool} {act : List Nat} (h : succOK r kb th tl act = true) :
    r.tag ≠ .none ∧ r.kb = kb ∧ (th = true → r.th = true) ∧ (tl = true → r.tl = true) ∧ ∀ e, e ∈ act → e ∈ r.act := by
  simp only [succOK, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun e => ?_, fun e => ?_, h5⟩
  · rcases h3 with h | h
    · rw [e] at h; cases h
    · exact h
  · rcases h4 with h | h
    · rw [e] at h; cases h
    · exact h

theorem rowAt_of {cert : List Row} {k : Nat} {r : Row} (h : cert[k]? = some r) : rowAt cert k = r := by
  simp [rowAt, h]

theorem rowAt_some {cert : List Row} {k : Nat} (h : (rowAt cert k).tag ≠ .none) : cert[k]? = some (rowAt cert k) := by
  unfold rowAt at h ⊢
  cases e : cert[k]? with
  | none => rw [e] at h; exact absurd rfl h
  | some r => rfl

theorem nextRow_drop (cert : List Row) (k : Nat) : nextRow (cert.drop (k + 1)) = rowAt cert (k + 1) := by
  simp [nextRow, rowAt, List.head?_drop]

theorem rowN_drop (cert : List Row) (k n : Nat) (hn : 1 ≤ n) : rowN (cert.drop (k + 1)) n = rowAt cert (k + n) := by
  simp only [rowN, rowAt, List.drop_drop, List.head?_drop]
  congr 2; omega

theorem drop_cons {xs : List Item} {k : Nat} {it : Item} {rest : List Item} (h : xs.drop k = it :: rest) :
    xs[k]? = some it := by
  have : (xs.drop k)[0]? = some it := by rw [h]; rfl
  simpa using this

theorem drop_cons2 {xs : List Item} {k : Nat} {i0 i1 : Item} {rest : List Item} (h : xs.drop k = i0 :: i1 :: rest) :
    xs[k + 1]? = some i1 := by
  have : (xs.drop k)[1]? = some i1 := by rw [h]; rfl
  simpa using this

theorem valSameL_B {A B : Code} {v : Val} (h : valSameL A.a.labels.reverse B.a.labels.reverse v = true) :
    valSameB A.a B.a v = true := by
  cases v with
  | num n => rfl
  | sym s off => simpa [valSameL, valSameB, symValL, symVal] using h

/-- **An ordinary instruction's row**: the same instruction in both images, of a form not reading
`H`, `L` where they are free, its operand the same, its address in `[lo, hi)`, the next row after. -/
theorem ordOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : ordOK c as bs r rs = true) :
    ∃ (f : Form) (a' b' : List Item), as = .ins f.instr :: a' ∧ bs = .ins f.instr :: b' ∧ f ≠ .halt ∧
      valSameL c.la c.lb (argVal f.instr) = true ∧ (r.th = true → f.readsH = false) ∧
      (r.tl = true → f.readsL = false) ∧ (f.viaNN = true → nnOK c.la c.lo c.hi (argVal f.instr) = true) ∧
      succOK (nextRow rs) (r.kb + 1) (r.th && !f.writesH) (r.tl && !f.writesL) r.act = true := by
  unfold ordOK at h
  split at h
  · rename_i i a' j b'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hij, h⟩ := h
    subst hij
    split at h
    · rename_i f _
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨hfi, hnh⟩, hv⟩, hrh⟩, hrl⟩, hnn⟩, hs⟩ := h
      have hfi' : f.instr = i := of_decide_eq_true hfi
      subst hfi'
      refine ⟨f, a', b', rfl, rfl, (by intro e; subst e; cases hnh), hv, fun e => ?_, fun e => ?_, fun e => ?_, hs⟩
      · rw [e] at hrh; simpa using hrh
      · rw [e] at hrl; simpa using hrl
      · rw [e] at hnn; simpa using hnn
    · cases h
  · cases h

/-- info: 'Ember.Proof.PassSim.ordOK_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms ordOK_spec

theorem viaNN_immVal (f : Form) (h : f.viaNN = true) : f.instr.immVal? = some (argVal f.instr) := by
  cases f <;> simp_all [Form.viaNN, Form.instr, argVal, Instr.immVal?]

/-- The operand address of a form, in `[lo, hi)` with the byte after, as the check says. -/
theorem nnOK_spec {A : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {f : Form} (hf : f.viaNN = true)
    (h : nnOK A.a.labels.reverse lo hi (argVal f.instr) = true) :
    ∀ pa, lo ≤ (f.instr.immW (A.a.env pa)).toNat ∧ (f.instr.immW (A.a.env pa)).toNat + 1 < hi := by
  intro pa
  have hv := viaNN_immVal f hf
  unfold nnOK at h
  split at h
  · rename_i n hn
    simp only [decide_eq_true_eq] at h
    obtain ⟨h0, h1, h2⟩ := h
    have hval' : (A.a.env pa).val (argVal f.instr) = n := by
      generalize argVal f.instr = v at hn
      cases v with
      | num m =>
        simp only [valOf, Option.some.injEq] at hn
        subst hn; rfl
      | sym s off =>
        simp only [valOf, symValL, Option.map_map, Option.map_eq_some_iff] at hn
        obtain ⟨a, ha, he⟩ := hn
        rw [val_sym _ s off (Int.ofNat a) (by simp [env_resolve, symVal, ha]), ← he]
        rfl
    have hval : (A.a.env pa).val (argVal f.instr) = Int.ofNat n.toNat := by
      rw [hval']; exact (Int.toNat_of_nonneg h0).symm
    rw [immW_toNat _ _ _ n.toNat hv hval (by omega)]
    exact ⟨h1, h2⟩
  · cases h

/-! ## The facts the segments take -/

/-- **What the theorem takes, besides the certificate's check**: `A`'s run needs no more than `SafeA`;
the RAM kept equal `[lo, hi)` in the memory; the accumulator of the runtime, the same in both, in it. -/
structure Glob (D : Dev) (A B : Code) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool))
    (x0 : Cpu × D.W) : Prop where
  chk : check A.items B.items A.a B.a lo hi cert tr = true
  safe : SafeA D A lo hi x0
  hlo : lo ≤ hi
  h1 : 1 ≤ hi
  hhi : hi ≤ 65536
  acc : ∃ acc, (∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc) ∧
    (∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc) ∧ lo ≤ acc ∧ acc + 4 ≤ hi

/-- The check at a row of a meeting point. -/
theorem Glob.row {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {k : Nat} (ht : (rowAt cert k).tag ≠ .none) :
    rowOK (mkCtx A.items B.items A.a B.a lo hi cert tr) (prevOf A.items k) (A.items.drop k)
      (B.items.drop (rowAt cert k).kb) (rowAt cert k) (cert.drop (k + 1)) = true :=
  (check_rows Gl.chk).2.2 k _ (rowAt_some ht) ht

/-- What `A`'s run needs at a meeting point. -/
theorem Glob.need {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k kb : Nat} {th tl : Bool}
    {x y : Cpu × D.W} (S : Sync D A B lo hi G k kb th tl x y) (hx : ∃ n, x = mrun D n x0) : Need A lo hi k x.1 := by
  obtain ⟨n, rfl⟩ := hx
  exact Gl.safe n k S.atA S.LA.2

theorem reach_step {D : Dev} {x0 x : Cpu × D.W} (hx : ∃ n, x = mrun D n x0) (a : Nat) :
    ∃ n, mrun D a x = mrun D n x0 := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n + a, by rw [mrun_add]⟩

/-! ## The segments, from a row of each kind -/

/-- **An ordinary instruction**: one step of each, to the next row. -/
theorem step_ord {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .ord)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨f, a', b', hA, hB, hnh, hv, hrh, hrl, hnn, hs⟩ := ordOK_spec hrow
  have hAk := drop_cons hA
  have hBk := drop_cons hB
  have nd := Gl.need S hx
  have hN := nd.2 f.instr hAk
  have S' := seg_ord D Gl.hhi f hnh hAk hBk (hop_of f (valSameL_B hv)) hrh hrl S
    (hN.1 f rfl).1 (hN.1 f rfl).2 (fun pa hf => nnOK_spec Gl.hhi hf (hnn hf) pa)
  rw [nextRow_drop] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  refine ⟨1, 1, Nat.one_pos, Or.inr ⟨G, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩⟩
  rw [s2]
  exact S'.mono s3 s4

/-- info: 'Ember.Proof.PassSim.step_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_ord

/-! ## Labels, conditions -/

theorem ccOK_spec {x : Arg} (h : ccOK (some x) = true) : x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c := by
  cases x <;> simp_all [ccOK]

/-- **A label where the runs meet**, from the table: in both images, its row, `B`'s index there. -/
theorem Glob.lab {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {l : String} {li : LInfo}
    (h : lookupL (mkCtx A.items B.items A.a B.a lo hi cert tr).t l = some li) :
    A.items[li.ia]? = some (.label l) ∧ B.items[li.ib]? = some (.label l) ∧ rowAt cert li.ia = li.row ∧
      li.row.tag = .skipBoth ∧ li.row.kb = li.ib := by
  obtain ⟨_, h1, h2, h3, h4, _⟩ := mkTbl_lookup A.items cert 0 l li h
  rw [Nat.sub_zero] at h1 h2
  have hr := rowAt_of h2
  have hrow := Gl.row (k := li.ia) (by rw [hr, h3]; intro e; cases e)
  rw [hr] at hrow
  simp only [rowOK, h3] at hrow
  unfold skipBothOK at hrow
  have hA : A.items.drop li.ia = .label l :: A.items.drop (li.ia + 1) := by
    rw [List.drop_eq_getElem_cons (by have := (List.getElem?_eq_some_iff.mp h1).1; omega)]
    congr 1
    have := (List.getElem?_eq_some_iff.mp h1).2; exact this
  rw [hA] at hrow
  cases hb : B.items.drop li.row.kb with
  | nil => rw [hb] at hrow; cases hrow
  | cons b bs =>
    rw [hb] at hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    obtain ⟨⟨_, e⟩, _⟩ := hrow
    subst e
    refine ⟨h1, ?_, hr, h3, h4.symm⟩
    rw [h4]; exact drop_cons hb

theorem has_of_take {C : Code} {k : Nat} {l : List Item} (h : l = (C.items.drop k).take l.length) : Has C k l := by
  intro j it hj
  have hj' : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  rw [h] at hj
  simp only [List.getElem?_take, hj', if_true, List.getElem?_drop] at hj
  exact hj

/-! ## Jumps -/

theorem jumpOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : jumpOK c as bs r rs = true) :
    ∃ (opA opB : Op) (cc : Option Arg) (l : String) (li : LInfo) (a' b' : List Item),
      as = .ins ⟨opA, cc.toList ++ [.imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨opB, cc.toList ++ [.imm (.sym l 0)]⟩ :: b' ∧
      (opA = .jp ∨ opA = .jr) ∧ (opB = .jp ∨ opB = .jr) ∧
      (∀ x, cc = some x → x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c) ∧ lookupL c.t l = some li ∧
      succOK li.row li.ib r.th r.tl r.act = true ∧
      (cc.isSome = true → succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act = true) := by
  unfold jumpOK at h
  split at h
  · rename_i opA argsA a' opB argsB b'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hA, hB⟩, hab⟩, h⟩ := h
    subst hab
    split at h
    · rename_i l
      split at h
      · rename_i li hli
        refine ⟨opA, opB, none, l, li, a', b', rfl, rfl, hA, hB, ?_, hli, h, ?_⟩
        · intro _ e; cases e
        · intro e; cases e
      · cases h
    · rename_i x l
      simp only [Bool.and_eq_true] at h
      obtain ⟨hx, h⟩ := h
      split at h
      · rename_i li hli
        simp only [Bool.and_eq_true] at h
        refine ⟨opA, opB, some x, l, li, a', b', rfl, rfl, hA, hB, ?_, hli, h.1, fun _ => h.2⟩
        intro y e; cases e; exact ccOK_spec hx
      · cases h
    · cases h
  · cases h

theorem step_jump {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .jump)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨opA, opB, cc, l, li, a', b', hA, hB, hoA, hoB, hcc, hli, hs1, hs2⟩ := jumpOK_spec hrow
  obtain ⟨hlA, hlB, hrA, _, hkb⟩ := Gl.lab hli
  have S' := seg_jump D hoA hoB hcc (drop_cons hA) hlA (drop_cons hB) hlB S
  refine ⟨1, 1, Nat.one_pos, Or.inr ?_⟩
  by_cases ht : taken cc x.1 = true
  · rw [if_pos ht] at S'
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs1
    refine ⟨G, li.ia, by rw [hrA]; exact s1, ?_, by rw [hrA]; exact s5 _ hcur, hF, reach_step hx 1⟩
    rw [hrA, s2]
    exact S'.mono s3 s4
  · rw [if_neg ht] at S'
    have hsome : cc.isSome = true := by
      cases cc with
      | none => exact absurd rfl ht
      | some _ => rfl
    have hs := hs2 hsome
    rw [nextRow_drop] at hs
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
    refine ⟨G, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩
    rw [s2]
    exact S'.mono s3 s4

/-- info: 'Ember.Proof.PassSim.step_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_jump

end Ember.Proof.PassSim
