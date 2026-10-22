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
meeting point of the certificate it reaches, the stack is above the RAM
kept equal (`hi + 4` below its top), and the bytes it reads or writes
through `HL` and `DE` (an instruction of a form that does, `ldir`, a
call of a routine of the runtime through `HL` not just after
`ld hl,lit`) are in that RAM `[lo, hi)`.  It is about the run of the
image without the passes alone, at the items the certificate lists.
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

/-! ## The relation kept -/

/-- The row of the certificate at `k`. -/
def rowAt (cert : List Row) (k : Nat) : Row := cert[k]?.getD default

/-- **`A`'s run from `x0` needs no more**: at every meeting point of the certificate (`cert`) it is at,
not halted.  Inside the segments that start there — the routines of the runtime, the copies of
literals — nothing is asked: the lemmas of those segments have what they need from their start. -/
def SafeA (D : Dev) (A : Code) (lo hi : Nat) (cert : List Row) (x0 : Cpu × D.W) : Prop :=
  ∀ n k, (rowAt cert k).tag ≠ .none → At A.addrs k (mrun D n x0).1 → (mrun D n x0).1.halted = false →
    Need A lo hi k (mrun D n x0).1

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

/-- **What the theorem takes, besides the certificate's rows checked** (`RowsOK`, from `check` by
`check_rows`, or checked in parts): `A`'s run needs no more than `SafeA`;
the RAM kept equal `[lo, hi)` in the memory; the accumulator of the runtime, the same in both, in it. -/
structure Glob (D : Dev) (A B : Code) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool))
    (x0 : Cpu × D.W) : Prop where
  chk : RowsOK A.items B.items A.a B.a lo hi cert tr
  safe : SafeA D A lo hi cert x0
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
  Gl.chk.2.2 k _ (rowAt_some ht) ht

/-- What `A`'s run needs at a meeting point. -/
theorem Glob.need {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k kb : Nat} {th tl : Bool}
    (ht : (rowAt cert k).tag ≠ .none) {x y : Cpu × D.W} (S : Sync D A B lo hi G k kb th tl x y)
    (hx : ∃ n, x = mrun D n x0) : Need A lo hi k x.1 := by
  obtain ⟨n, rfl⟩ := hx
  exact Gl.safe n k ht S.atA S.LA.2

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
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
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

/-! ## `djnz`, calls, `halt`, `ld sp,0`, `ldir`, `packHigh` -/

theorem djnzOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : djnzOK c as bs r rs = true) :
    ∃ (l : String) (li : LInfo) (a' b' : List Item),
      as = .ins ⟨.djnz, [.imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨.djnz, [.imm (.sym l 0)]⟩ :: b' ∧
      lookupL c.t l = some li ∧ succOK li.row li.ib r.th r.tl r.act = true ∧
      succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act = true := by
  unfold djnzOK at h
  split at h
  · rename_i l a' l' b'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨e, h⟩ := h
    subst e
    split at h
    · rename_i li hli
      simp only [Bool.and_eq_true] at h
      exact ⟨l, li, a', b', rfl, rfl, hli, h.1, h.2⟩
    · cases h
  · cases h

theorem step_djnz {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .djnz)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨l, li, a', b', hA, hB, hli, hs1, hs2⟩ := djnzOK_spec hrow
  obtain ⟨hlA, hlB, hrA, _, hkb⟩ := Gl.lab hli
  have S' := seg_djnz D (drop_cons hA) hlA (drop_cons hB) hlB S
  refine ⟨1, 1, Nat.one_pos, Or.inr ?_⟩
  by_cases ht : (x.1.b - 1 != 0) = true
  · rw [if_pos ht] at S'
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs1
    refine ⟨G, li.ia, by rw [hrA]; exact s1, ?_, by rw [hrA]; exact s5 _ hcur, hF, reach_step hx 1⟩
    rw [hrA, s2]
    exact S'.mono s3 s4
  · rw [if_neg ht] at S'
    rw [nextRow_drop] at hs2
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs2
    refine ⟨G, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩
    rw [s2]
    exact S'.mono s3 s4

theorem callOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : callOK c as bs r rs = true) :
    ∃ (l : String) (li : LInfo) (a' b' : List Item),
      as = .ins ⟨.call, [.imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨.call, [.imm (.sym l 0)]⟩ :: b' ∧
      lookupL c.t l = some li ∧ succOK li.row li.ib r.th r.tl [li.ia] = true ∧
      succOK (nextRow rs) (r.kb + 1) (trOf c.tr li.ia).1 (trOf c.tr li.ia).2 r.act = true := by
  unfold callOK at h
  split at h
  · rename_i l a' l' b'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨e, h⟩ := h
    subst e
    split at h
    · rename_i li hli
      simp only [Bool.and_eq_true] at h
      exact ⟨l, li, a', b', rfl, rfl, hli, h.1, h.2⟩
    · cases h
  · cases h

theorem step_call {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .call)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨l, li, a', b', hA, hB, hli, hs1, hs2⟩ := callOK_spec hrow
  obtain ⟨hlA, hlB, hrA, _, hkb⟩ := Gl.lab hli
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  have S' := seg_call D Gl.hhi (drop_cons hA) hlA (drop_cons hB) hlB S Gl.hlo Gl.h1 (by have := nd.1; omega)
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs1
  rw [nextRow_drop] at hs2
  obtain ⟨t1, t2, t3, t4, t5⟩ := succOK_spec hs2
  refine ⟨1, 1, Nat.one_pos, Or.inr ⟨.ret (k + 1) ((rowAt cert k).kb + 1) li.ia :: G, li.ia,
    by rw [hrA]; exact s1, ?_, ?_, ?_, reach_step hx 1⟩⟩
  · rw [hrA, s2]; exact S'.mono s3 s4
  · rw [hrA]; exact s5 _ (List.mem_singleton_self _)
  · exact ⟨t1, t2, ⟨t3, t4⟩, t5 _ hcur, hF⟩

theorem haltOK_spec {as bs : List Item} (h : haltOK as bs = true) :
    ∃ a' b' : List Item, as = .ins ⟨.halt, []⟩ :: a' ∧ bs = .ins ⟨.halt, []⟩ :: b' := by
  unfold haltOK at h
  split at h
  · rename_i a' b'; exact ⟨a', b', rfl, rfl⟩
  · cases h

theorem step_halt {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .halt)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨a', b', hA, hB⟩ := haltOK_spec hrow
  exact ⟨1, 1, Nat.one_pos, Or.inl (seg_halt D (drop_cons hA) (drop_cons hB) S)⟩

theorem ldspOK_spec {as bs : List Item} {r : Row} {rs : List Row} (h : ldspOK as bs r rs = true) :
    ∃ a' b' : List Item, as = .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: a' ∧ bs = .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: b' ∧
      succOK (nextRow rs) (r.kb + 1) r.th r.tl [topE] = true := by
  unfold ldspOK at h
  split at h
  · rename_i a' b'; exact ⟨a', b', rfl, rfl, h⟩
  · cases h

theorem step_ldsp {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .ldsp)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨a', b', hA, hB, hs⟩ := ldspOK_spec hrow
  have S' := seg_ldsp0 D (drop_cons hA) (drop_cons hB) S
  rw [nextRow_drop] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  refine ⟨1, 1, Nat.one_pos, Or.inr ⟨[], k + 1, s1, ?_, s5 _ (List.mem_singleton_self _), trivial, reach_step hx 1⟩⟩
  rw [s2]; exact S'.mono s3 s4

theorem ldirOK_spec {as bs : List Item} {r : Row} {rs : List Row} (h : ldirOK as bs r rs = true) :
    ∃ a' b' : List Item, as = .ins ⟨.ldir, []⟩ :: a' ∧ bs = .ins ⟨.ldir, []⟩ :: b' ∧ r.th = false ∧ r.tl = false ∧
      succOK (nextRow rs) (r.kb + 1) false false r.act = true := by
  unfold ldirOK at h
  split at h
  · rename_i a' b'
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨a', b', rfl, rfl, h.1.1, h.1.2, h.2⟩
  · cases h

theorem step_ldir {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .ldir)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨a', b', hA, hB, hth, htl, hs⟩ := ldirOK_spec hrow
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  obtain ⟨d1, d2, d3, d4⟩ := (nd.2 _ (drop_cons hA)).2.1 rfl
  rw [hth, htl] at S
  have E := eqv_ff S.E
  have hv : x.1.mem.get! x.1.hl.toNat = y.1.mem.get! y.1.hl.toNat := by
    rw [← RegsS.hl E.regs]; exact E.mem _ d1 d2
  have S' := seg_ldir D Gl.hhi (drop_cons hA) (drop_cons hB) S hv ⟨d3, d4⟩
  refine ⟨1, 1, Nat.one_pos, Or.inr ?_⟩
  by_cases hb : (x.1.bc - 1 != 0) = true
  · rw [if_pos hb] at S'
    refine ⟨G, k, (by rw [htag]; intro h; cases h), (by rw [hth, htl]; exact S'), hcur, hF, reach_step hx 1⟩
  · rw [if_neg hb] at S'
    rw [nextRow_drop] at hs
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
    refine ⟨G, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩
    rw [s2]; exact S'.mono (fun e => by cases e) (fun e => by cases e)

theorem packOK_spec {as bs : List Item} {r : Row} {rs : List Row} (h : packOK as bs r rs = true) :
    packHighFrom.map Item.ins = as.take 4 ∧ packHighTo.map Item.ins = bs.take 2 ∧
      succOK (rowN rs 4) (r.kb + 2) false false r.act = true := by
  simp only [packOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem step_pack {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .pack)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨hA, hB, hs⟩ := packOK_spec hrow
  have S' := seg_pack D (has_of_take (by rw [List.length_map, show packHighFrom.length = 4 from rfl]; exact hA))
    (has_of_take (by rw [List.length_map, show packHighTo.length = 2 from rfl]; exact hB)) S
  rw [rowN_drop _ _ _ (by decide)] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  refine ⟨4, 2, by decide, Or.inr ⟨G, k + 4, s1, ?_, s5 _ hcur, hF, reach_step hx 4⟩⟩
  rw [s2]; exact S'.mono (fun e => by cases e) (fun e => by cases e)


/-! ## Returns -/

theorem retAtB_spec (C : Code) : ∀ (l : List Item) (i : Nat), C.items.drop i = l → retAtB l = true → RetAt C i
  | [], _, _, h => by simp [retAtB] at h
  | it :: rest, i, hd, h => by
    cases it with
    | label l =>
      simp only [retAtB] at h
      have hd' : C.items.drop (i + 1) = rest := by
        have := congrArg List.tail hd; simpa [List.tail_drop] using this
      obtain ⟨j, ⟨hij, hl⟩, hr⟩ := retAtB_spec C rest (i + 1) hd' h
      refine ⟨j, ⟨by omega, fun m h1 h2 => ?_⟩, hr⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; exact ⟨l, drop_cons hd⟩
      · exact hl m (by omega) h2
    | ins ins =>
      obtain ⟨op, args⟩ := ins
      cases op <;> try (simp [retAtB] at h)
      cases args with
      | nil => exact ⟨i, ⟨Nat.le_refl _, fun m h1 h2 => by omega⟩, drop_cons hd⟩
      | cons _ _ => simp [retAtB] at h
    | _ => simp [retAtB] at h

theorem retSeqB_spec (C : Code) : ∀ (l : List Item) (i : Nat), C.items.drop i = l →
    retSeqB (labTbl C.items 0) l = true → RetSeq C i
  | [], _, _, h => by simp [retSeqB] at h
  | it :: rest, i, hd, h => by
    cases it with
    | label l =>
      simp only [retSeqB] at h
      have hd' : C.items.drop (i + 1) = rest := by
        have := congrArg List.tail hd; simpa [List.tail_drop] using this
      obtain ⟨j, ⟨hij, hl⟩, hr⟩ := retSeqB_spec C rest (i + 1) hd' h
      refine ⟨j, ⟨by omega, fun m h1 h2 => ?_⟩, hr⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; exact ⟨l, drop_cons hd⟩
      · exact hl m (by omega) h2
    | ins ins =>
      obtain ⟨op, args⟩ := ins
      cases op <;> try (simp [retSeqB] at h)
      · -- jp
        match args, h with
        | [.imm (.sym l 0)], h =>
          simp only [retSeqB] at h
          split at h
          · rename_i sa hsa
            obtain ⟨jl, hjl, rfl⟩ := sufOf_label hsa
            exact ⟨i, ⟨Nat.le_refl _, fun m h1 h2 => by omega⟩,
              Or.inr ⟨l, jl, drop_cons hd, hjl, retAtB_spec C _ jl rfl h⟩⟩
          · cases h
      · -- ret
        cases args with
        | nil => exact ⟨i, ⟨Nat.le_refl _, fun m h1 h2 => by omega⟩, Or.inl (drop_cons hd)⟩
        | cons _ _ => simp [retSeqB] at h
    | _ => simp [retSeqB] at h

/-- **The frames under a function**: `A`'s own (each a return at its return point), then a call of
both; the function's return taint at most that frame's. -/
theorem frames_split {A : Code} {cert : List Row} {tr : List (Nat × Bool × Bool)} :
    ∀ (G : List Frame), FOK A cert tr G → cur G ≠ topE →
      ∃ ts rA rB e G', G = tails ts ++ .ret rA rB e :: G' ∧ (∀ p, p ∈ ts → RetSeq A p.1) ∧
        FOK A cert tr (.ret rA rB e :: G') ∧ leT (trOf tr (cur G)) (trOf tr e)
  | [], _, h => absurd rfl h
  | .ret rA rB e :: G', hF, _ => ⟨[], rA, rB, e, G', rfl, (fun _ h => absurd h List.not_mem_nil), hF,
      (fun h => h), (fun h => h)⟩
  | .tail rA e :: G', ⟨hr, hne, hle, hF⟩, _ => by
    obtain ⟨ts, rA', rB', e', G'', hG, hts, hF', hle'⟩ := frames_split G' hF hne
    refine ⟨(rA, e) :: ts, rA', rB', e', G'', by rw [hG]; rfl, fun p hp => ?_, hF', ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hr
      · exact hts p hp
    · exact ⟨fun h => hle'.1 (hle.1 h), fun h => hle'.2 (hle.2 h)⟩
  | .data :: _, hF, _ => absurd hF id

theorem retOK_spec {tr : List (Nat × Bool × Bool)} {r : Row} (h : retOK tr r = true) :
    topE ∉ r.act ∧ ∀ e, e ∈ r.act → leT (r.th, r.tl) (trOf tr e) := by
  simp only [retOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h1, fun e he => ?_⟩
  obtain ⟨a, b⟩ := h2 e he
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rcases a with a | a
    · exact absurd (x.symm.trans a) (by decide)
    · exact a
  · rcases b with b | b
    · exact absurd (x.symm.trans b) (by decide)
    · exact b

theorem retRowOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : retRowOK c as bs r rs = true) :
    ∃ (cc : Option Arg) (a' b' : List Item), as = .ins ⟨.ret, cc.toList⟩ :: a' ∧ bs = .ins ⟨.ret, cc.toList⟩ :: b' ∧
      retOK c.tr r = true ∧ (∀ x, cc = some x → x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c) ∧
      (cc.isSome = true → succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act = true) := by
  unfold retRowOK at h
  split at h
  · rename_i cc a' cc' b'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨e, hret⟩, h⟩ := h
    subst e
    split at h
    · refine ⟨none, a', b', rfl, rfl, hret, ?_, ?_⟩
      · intro _ e; cases e
      · intro e; cases e
    · rename_i x
      simp only [Bool.and_eq_true] at h
      refine ⟨some x, a', b', rfl, rfl, hret, ?_, fun _ => h.2⟩
      intro y e; cases e; exact ccOK_spec h.1
    · cases h
  · cases h

theorem cc_some {x : Arg} (h : x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c) : (cc? x).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The relation at the return points of a frame of both, popped. -/
theorem inv_ret {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 x y : Cpu × D.W} {G' : List Frame} {rA rB e : Nat} {th tl : Bool}
    (S : Sync D A B lo hi G' rA rB th tl x y) (hF : FOK A cert tr (.ret rA rB e :: G'))
    (ht : leT (th, tl) (trOf tr e)) (hx : ∃ n, x = mrun D n x0) : Inv D A B lo hi cert tr x0 x y := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := hF
  refine Or.inr ⟨G', rA, f1, ?_, f4, f5, hx⟩
  rw [f2]
  exact S.mono (fun h => f3.1 (ht.1 h)) (fun h => f3.2 (ht.2 h))

theorem step_ret {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .ret)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨cc, a', b', hA, hB, hret, hcc, hs⟩ := retRowOK_spec hrow
  obtain ⟨htop, hle⟩ := retOK_spec hret
  have hne : cur G ≠ topE := fun e => htop (e ▸ hcur)
  obtain ⟨ts, rA, rB, e, G', hG, hts, hF', hle'⟩ := frames_split G hF hne
  have ht : leT ((rowAt cert k).th, (rowAt cert k).tl) (trOf tr e) :=
    ⟨fun h => hle'.1 ((hle _ hcur).1 h), fun h => hle'.2 ((hle _ hcur).2 h)⟩
  subst hG
  cases cc with
  | none =>
    obtain ⟨n, hn, S'⟩ := seg_retseq D (ts := ts) ⟨k, ⟨Nat.le_refl _, fun m h1 h2 => by omega⟩, Or.inl (drop_cons hA)⟩
      (drop_cons hB) hts S
    exact ⟨n, 1, hn, inv_ret S' hF' ht (reach_step hx n)⟩
  | some cnd =>
    have hcx := cc_some (hcc cnd rfl)
    have hfall : ∀ (S' : Sync D A B lo hi (tails ts ++ .ret rA rB e :: G') (k + 1) ((rowAt cert k).kb + 1)
        (rowAt cert k).th (rowAt cert k).tl (mstep D x) (mstep D y)),
        ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
      intro S'
      have hs' := hs rfl
      rw [nextRow_drop] at hs'
      obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs'
      refine ⟨1, 1, Nat.one_pos, Or.inr ⟨_, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩⟩
      rw [s2]; exact S'.mono s3 s4
    cases ts with
    | nil =>
      have S' := seg_ret D (cc := some cnd) (fun _ h => by cases h; exact hcx) (drop_cons hA) (drop_cons hB) S
      by_cases htk : taken (some cnd) x.1 = true
      · rw [if_pos htk] at S'
        exact ⟨1, 1, Nat.one_pos, inv_ret S' hF' ht (reach_step hx 1)⟩
      · rw [if_neg htk] at S'
        exact hfall S'
    | cons p ts =>
      have S' := seg_retcc_tails D hcx (drop_cons hA) (drop_cons hB) hts S
      by_cases htk : taken (some cnd) x.1 = true
      · rw [if_pos htk] at S'
        obtain ⟨n, hn, S''⟩ := S'
        exact ⟨n, 1, hn, inv_ret S'' hF' ht (reach_step hx n)⟩
      · rw [if_neg htk] at S'
        exact hfall S'

/-- info: 'Ember.Proof.PassSim.step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_ret

theorem retThrOK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : retThrOK c as bs r rs = true) :
    ∃ (cc : Option Arg) (l : String) (sa a' b' : List Item),
      as = .ins ⟨.jp, cc.toList ++ [.imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨.ret, cc.toList⟩ :: b' ∧
      retOK c.tr r = true ∧ (∀ x, cc = some x → x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c) ∧
      sufOf c.tA l = some sa ∧ retAtB sa = true ∧
      (cc.isSome = true → succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act = true) := by
  unfold retThrOK at h
  split at h
  · rename_i argsA a' cc b'
    simp only [Bool.and_eq_true] at h
    obtain ⟨hret, h⟩ := h
    split at h
    · rename_i l
      split at h
      · rename_i sa hsa
        refine ⟨none, l, sa, a', b', rfl, rfl, hret, ?_, hsa, h, ?_⟩
        · intro _ e; cases e
        · intro e; cases e
      · cases h
    · rename_i x l x'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨e, hx⟩, h⟩ := h
      subst e
      split at h
      · rename_i sa hsa
        simp only [Bool.and_eq_true] at h
        refine ⟨some x, l, sa, a', b', rfl, rfl, hret, ?_, hsa, h.1, fun _ => h.2⟩
        intro y e; cases e; exact ccOK_spec hx
      · cases h
    · cases h
  · cases h

theorem step_retThr {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .retThr)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨cc, l, sa, a', b', hA, hB, hret, hcc, hsa, hra, hs⟩ := retThrOK_spec hrow
  obtain ⟨jl, hjl, rfl⟩ := sufOf_label hsa
  have hRA := retAtB_spec A _ jl rfl hra
  obtain ⟨htop, hle⟩ := retOK_spec hret
  have hne : cur G ≠ topE := fun e => htop (e ▸ hcur)
  obtain ⟨ts, rA, rB, e, G', hG, hts, hF', hle'⟩ := frames_split G hF hne
  have ht : leT ((rowAt cert k).th, (rowAt cert k).tl) (trOf tr e) :=
    ⟨fun h => hle'.1 ((hle _ hcur).1 h), fun h => hle'.2 ((hle _ hcur).2 h)⟩
  subst hG
  cases cc with
  | none =>
    obtain ⟨n, hn, S'⟩ := seg_retseq D (ts := ts)
      ⟨k, ⟨Nat.le_refl _, fun m h1 h2 => by omega⟩, Or.inr ⟨l, jl, drop_cons hA, hjl, hRA⟩⟩ (drop_cons hB) hts S
    exact ⟨n, 1, hn, inv_ret S' hF' ht (reach_step hx n)⟩
  | some cnd =>
    have S' := seg_retThrCC D (hcc cnd rfl) (drop_cons hA) hjl hRA (drop_cons hB) hts S
    by_cases htk : taken (some cnd) x.1 = true
    · rw [if_pos htk] at S'
      obtain ⟨n, hn, S''⟩ := S'
      exact ⟨n, 1, hn, inv_ret S'' hF' ht (reach_step hx n)⟩
    · rw [if_neg htk] at S'
      have hs' := hs rfl
      rw [nextRow_drop] at hs'
      obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs'
      refine ⟨1, 1, Nat.one_pos, Or.inr ⟨_, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx 1⟩⟩
      rw [s2]; exact S'.mono s3 s4

theorem condRetOK_spec {c : Ctx} {as bs : List Item} {r : Row} (h : condRetOK c as bs r = true) :
    ∃ (x x' : Arg) (l : String) (li : LInfo) (a' b' : List Item),
      as = .ins ⟨.jp, [x, .imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨.ret, [x']⟩ :: b' ∧
      retOK c.tr r = true ∧ (x = .nz ∨ x = .z ∨ x = .nc ∨ x = .c) ∧ Codegen.invert x = some x' ∧
      retSeqB c.tA a' = true ∧ lookupL c.t l = some li ∧ succOK li.row (r.kb + 1) r.th r.tl r.act = true := by
  unfold condRetOK at h
  split at h
  · rename_i x l a' x' b'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hret, hx⟩, hinv⟩, hseq⟩, h⟩ := h
    split at h
    · rename_i li hli
      exact ⟨x, x', l, li, a', b', rfl, rfl, hret, ccOK_spec hx, hinv, hseq, hli, h⟩
    · cases h
  · cases h

theorem step_condRet {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .condRet)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨cnd, cnd', l, li, a', b', hA, hB, hret, hc, hinv, hseq, hli, hs⟩ := condRetOK_spec hrow
  have hRS : RetSeq A (k + 1) := by
    refine retSeqB_spec A a' (k + 1) ?_ hseq
    have := congrArg List.tail hA; simpa [List.tail_drop] using this
  obtain ⟨hlA, _, hrA, _, hkb⟩ := Gl.lab hli
  obtain ⟨htop, hle⟩ := retOK_spec hret
  have hne : cur G ≠ topE := fun e => htop (e ▸ hcur)
  obtain ⟨ts, rA, rB, e, G', hG, hts, hF', hle'⟩ := frames_split G hF hne
  have ht : leT ((rowAt cert k).th, (rowAt cert k).tl) (trOf tr e) :=
    ⟨fun h => hle'.1 ((hle _ hcur).1 h), fun h => hle'.2 ((hle _ hcur).2 h)⟩
  have hF0 := hF
  have hcur0 := hcur
  subst hG
  have S' := seg_condRet D hc hinv (drop_cons hA) hlA hRS (drop_cons hB) hts S
  by_cases htk : taken (some cnd) x.1 = true
  · rw [if_pos htk] at S'
    obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
    refine ⟨1, 1, Nat.one_pos, Or.inr ⟨_, li.ia, by rw [hrA]; exact s1, ?_, by rw [hrA]; exact s5 _ hcur0, hF0,
      reach_step hx 1⟩⟩
    rw [hrA, s2]; exact S'.mono s3 s4
  · rw [if_neg htk] at S'
    obtain ⟨n, hn, S''⟩ := S'
    exact ⟨n, 1, hn, inv_ret S'' hF' ht (reach_step hx n)⟩

theorem tailOK_spec {c : Ctx} {as bs : List Item} {r : Row} (h : tailOK c as bs r = true) :
    ∃ (opB : Op) (l : String) (li : LInfo) (a' b' : List Item),
      as = .ins ⟨.call, [.imm (.sym l 0)]⟩ :: a' ∧ bs = .ins ⟨opB, [.imm (.sym l 0)]⟩ :: b' ∧
      (opB = .jp ∨ opB = .jr) ∧ retSeqB c.tA a' = true ∧ topE ∉ r.act ∧ lookupL c.t l = some li ∧
      succOK li.row li.ib r.th r.tl [li.ia] = true ∧
      ∀ e, e ∈ r.act → leT (trOf c.tr li.ia) (trOf c.tr e) := by
  unfold tailOK at h
  split at h
  · rename_i l a' opB l' b'
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨e, hop⟩, hseq⟩, htop⟩, h⟩ := h
    subst e
    split at h
    · rename_i li hli
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      refine ⟨opB, l, li, a', b', rfl, rfl, hop, hseq, by simpa using htop, hli, h.1, fun e he => ?_⟩
      obtain ⟨a, b⟩ := h.2 e he
      refine ⟨fun x => ?_, fun x => ?_⟩
      · rcases a with a | a
        · exact absurd (x.symm.trans a) (by decide)
        · exact a
      · rcases b with b | b
        · exact absurd (x.symm.trans b) (by decide)
        · exact b
    · cases h
  · cases h

theorem step_tail {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .tail)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨opB, l, li, a', b', hA, hB, hop, hseq, htop, hli, hs, hle⟩ := tailOK_spec hrow
  have hRS : RetSeq A (k + 1) := by
    refine retSeqB_spec A a' (k + 1) ?_ hseq
    have := congrArg List.tail hA; simpa [List.tail_drop] using this
  obtain ⟨hlA, hlB, hrA, _, hkb⟩ := Gl.lab hli
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  have S' := seg_tail D Gl.hhi hop (drop_cons hA) hlA (drop_cons hB) hlB S Gl.hlo Gl.h1 (by have := nd.1; omega)
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  have hne : cur G ≠ topE := fun e => htop (e ▸ hcur)
  refine ⟨1, 1, Nat.one_pos, Or.inr ⟨.tail (k + 1) li.ia :: G, li.ia, by rw [hrA]; exact s1, ?_,
    by rw [hrA]; exact s5 _ (List.mem_singleton_self _), ⟨hRS, hne, hle _ hcur, hF⟩, reach_step hx 1⟩⟩
  rw [hrA, s2]; exact S'.mono s3 s4

/-- info: 'Ember.Proof.PassSim.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_tail

/-! ## Literals, routines of the runtime -/

/-- The byte of a number of a `db`. -/
def dbByte : Val → UInt8
  | .num m => byteOf m
  | _ => 0

def numsOK (vs : List Val) : Bool := vs.all fun v => match v with | .num m => decide (0 ≤ m ∧ m < 256) | _ => false

theorem imm8_num (env : Env) (m : Int) (h0 : 0 ≤ m) (h1 : m < 256) : (imm8 (.num m)).run env = .ok [byteOf m] := by
  have hc : (!env.sizing && (decide (m < -128) || decide (m > 255))) = false := by
    have : decide (m < -128) = false := by simp; omega
    have : decide (m > 255) = false := by simp; omega
    simp_all
  simp only [imm8, value, bind, ReaderT.bind, ReaderT.run, pure, ReaderT.pure, read, readThe, MonadReaderOf.read,
    ReaderT.read, Except.bind, Except.pure]
  rw [hc]; rfl

/-- **A `db` of numbers of 0 … 255**: its bytes, whatever the labels and the address. -/
theorem db_encode : ∀ (vs : List Val), numsOK vs = true → ∀ env, Item.encode (.db vs) env = .ok (vs.map dbByte)
  | [], _, env => rfl
  | v :: vs, h, env => by
    simp only [numsOK, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hv, hvs⟩ := h
    cases v with
    | num m =>
      simp only [decide_eq_true_eq] at hv
      have ih := db_encode vs hvs env
      simp only [Item.encode, List.mapM_cons] at ih ⊢
      generalize hm : (List.mapM imm8 vs).run env = r at ih
      cases r with
      | error e => simp [Except.map] at ih
      | ok bs =>
        simp only [Except.map, Except.ok.injEq] at ih
        simp only [bind, ReaderT.bind, ReaderT.run, Except.bind, pure, ReaderT.pure, Except.pure, Except.map,
          List.map_cons, dbByte]
        have hi : imm8 (.num m) env = .ok [byteOf m] := imm8_num env m hv.1 hv.2
        have hm' : List.mapM imm8 vs env = .ok bs := hm
        rw [hi, hm']
        simp [ih]
    | sym _ _ => simp at hv

theorem litOK_spec {xs ys : List Item} {l : String} {n : Nat} (h : litOK (labTbl xs 0) (labTbl ys 0) l n = true) :
    ∃ dA dB vs, xs[dA]? = some (.label l) ∧ xs[dA + 1]? = some (.db vs) ∧ ys[dB]? = some (.label l) ∧
      ys[dB + 1]? = some (.db vs) ∧ numsOK vs = true ∧ vs.length = n := by
  unfold litOK at h
  split at h
  · rename_i a vs ra b vs' rb hA hB
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨e, hn⟩, hnums⟩ := h
    subst e
    obtain ⟨dA, hdA, hsA⟩ := sufOf_label hA
    obtain ⟨dB, hdB, hsB⟩ := sufOf_label hB
    exact ⟨dA, dB, vs, hdA, drop_cons2 hsA.symm, hdB, drop_cons2 hsB.symm, hnums, hn⟩
  · cases h

theorem labTbl_some : ∀ (xs : List Item) (k j : Nat) (l : String), xs[j]? = some (.label l) →
    ((labTbl xs k).lookup l).isSome = true
  | [], _, _, _, h => by simp at h
  | it :: r, k, j, l, h => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [labTbl]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have ih := labTbl_some r (k + 1) j l h
      cases it with
      | label l' =>
        simp only [labTbl, lookup_cons]
        split <;> simp_all
      | _ => simpa [labTbl] using ih

/-- A symbol the table of `A`'s labels has not is no label of `A`. -/
theorem notLabel_spec {xs : List Item} {l : String} (h : notLabel (labTbl xs 0) l = true) :
    ∀ j : Nat, xs[j]? ≠ some (Item.label l) := by
  intro j hj
  have := labTbl_some xs 0 j l hj
  simp only [notLabel, Option.isNone_iff_eq_none] at h
  rw [h] at this; cases this

/-- **A routine of the runtime through `HL`**: its items in both images. -/
theorem routineOK_spec {xs ys : List Item} {f : String} (h : routineOK (labTbl xs 0) (labTbl ys 0) f = true) :
    ∃ hd its, ptrRoutine f = some (hd, its) ∧ ∃ i j, its = (xs.drop i).take its.length ∧
      its = (ys.drop j).take its.length := by
  unfold routineOK at h
  split at h
  · rename_i hd its hpr
    split at h
    · rename_i sa sb hsa hsb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨i, _, rfl⟩ := sufOf_label hsa
      obtain ⟨j, _, rfl⟩ := sufOf_label hsb
      exact ⟨hd, its, hpr, i, j, h.1, h.2⟩
    · cases h
  · cases h

/-- What the check of a call of a routine of the runtime says of the item before. -/
def prevOK (tA : List (String × Nat × List Item)) (prev : Option Item) : Bool :=
  match prev with
  | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => notLabel tA l
  | _ => true

theorem prevOK_spec {xs : List Item} {k : Nat} (h : prevOK (labTbl xs 0) (prevOf xs k) = true) :
    ∀ l, 0 < k → xs[k - 1]? = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) → ∀ j : Nat, xs[j]? ≠ some (Item.label l) := by
  intro l hk hp
  have : prevOf xs k = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) := by
    simp only [prevOf, show k ≠ 0 by omega, if_false]; exact hp
  rw [this] at h
  exact notLabel_spec h

theorem blkOK_spec {c : Ctx} {prev : Option Item} {as bs : List Item} {r : Row} {rs : List Row}
    (h : blkOK c prev as bs r rs = true) :
    ∃ (f : String) (a' b' : List Item), as = .ins ⟨.call, [.imm (.sym f 0)]⟩ :: a' ∧
      bs = .ins ⟨.call, [.imm (.sym f 0)]⟩ :: b' ∧ r.th = false ∧ r.tl = false ∧ routineOK c.tA c.tB f = true ∧
      prevOK c.tA prev = true ∧ succOK (nextRow rs) (r.kb + 1) false false r.act = true := by
  unfold blkOK at h
  split at h
  · rename_i f a' f' b'
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨e, hth⟩, htl⟩, hr⟩, hp⟩, hs⟩ := h
    subst e
    exact ⟨f, a', b', rfl, rfl, hth, htl, hr, hp, hs⟩
  · cases h

/-- The accumulator of the runtime, as `Glob` has it. -/
theorem Glob.accs {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) :
    ∃ acc, (∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc) ∧
      (∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc) ∧ lo ≤ acc ∧ acc + 4 ≤ hi := Gl.acc

theorem step_blk {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .blk)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨f, a', b', hA, hB, hth, htl, hr, hp, hs⟩ := blkOK_spec hrow
  obtain ⟨hd, its, hpr, i, j, hiA, hjB⟩ := routineOK_spec hr
  have hLA : Has A i its := has_of_take hiA
  have hLB : Has B j its := has_of_take hjB
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  have hfoot := (nd.2 _ (drop_cons hA)).2.2 f rfl (by rw [hpr]; rfl) (prevOK_spec hp)
  have room := nd.1
  obtain ⟨acc, haccA, haccB, hacc⟩ := Gl.accs
  rw [hth, htl] at S
  rw [nextRow_drop] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  have hA' := drop_cons hA
  have hB' := drop_cons hB
  have fin : ∀ n, Sync D A B lo hi G (k + 1) ((rowAt cert k).kb + 1) false false (mrun D n x) (mrun D n y) → 0 < n →
      ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
    intro n S' hn
    refine ⟨n, n, hn, Or.inr ⟨G, k + 1, s1, ?_, s5 _ hcur, hF, reach_step hx n⟩⟩
    rw [s2]; exact S'.mono (fun e => by cases e) (fun e => by cases e)
  unfold ptrRoutine at hpr
  split at hpr <;> (try cases hpr)
  · exact fin 8 (blk_ld32 D Gl.hhi Gl.hlo Gl.h1 hA' hB' hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot)
      (by decide)
  · exact fin 9 (blk_st32 D Gl.hhi Gl.hlo Gl.h1 hA' hB' hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot)
      (by decide)
  · have S' := blk_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "add") 1 (Or.inr rfl) exec_adc_a_m rfl hA' hB' hLA hLB
      haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot
    exact fin _ S' (by simp)
  · have S' := blk_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "sub") 3 (Or.inr rfl) exec_sbc_a_m rfl hA' hB' hLA hLB
      haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot
    exact fin _ S' (by simp)
  · have S' := blk_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "or") 6 (Or.inl rfl) exec_or_m rfl hA' hB' hLA hLB
      haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot
    exact fin _ S' (by simp)
  · exact fin 44 (blk_cmp32 D Gl.hhi Gl.hlo Gl.h1 hA' hB' hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ S (by omega) hfoot)
      (by decide)

/-- info: 'Ember.Proof.PassSim.step_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_blk

theorem tailBlkOK_spec {c : Ctx} {prev : Option Item} {as bs : List Item} {r : Row}
    (h : tailBlkOK c prev as bs r = true) :
    ∃ (f : String) (a' b' : List Item), as = .ins ⟨.call, [.imm (.sym f 0)]⟩ :: a' ∧
      bs = .ins ⟨.jp, [.imm (.sym f 0)]⟩ :: b' ∧ (f = "rt_st32" ∨ f = "rt_or32") ∧ r.th = false ∧ r.tl = false ∧
      routineOK c.tA c.tB f = true ∧ prevOK c.tA prev = true ∧ retSeqB c.tA a' = true ∧ topE ∉ r.act := by
  unfold tailBlkOK at h
  split at h
  · rename_i f a' f' b'
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨e, hf⟩, hth⟩, htl⟩, hr⟩, hp⟩, hseq⟩, htop⟩ := h
    subst e
    exact ⟨f, a', b', rfl, rfl, hf, hth, htl, hr, hp, hseq, by simpa using htop⟩
  · cases h

theorem step_tailBlk {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .tailBlk)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨f, a', b', hA, hB, hf, hth, htl, hr, hp, hseq, htop⟩ := tailBlkOK_spec hrow
  have hRS : RetSeq A (k + 1) := by
    refine retSeqB_spec A a' (k + 1) ?_ hseq
    have := congrArg List.tail hA; simpa [List.tail_drop] using this
  obtain ⟨hd, its, hpr, i, j, hiA, hjB⟩ := routineOK_spec hr
  have hLA : Has A i its := has_of_take hiA
  have hLB : Has B j its := has_of_take hjB
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  have hfoot := (nd.2 _ (drop_cons hA)).2.2 f rfl (by rw [hpr]; rfl) (prevOK_spec hp)
  have room := nd.1
  obtain ⟨acc, haccA, haccB, hacc⟩ := Gl.accs
  have hne : cur G ≠ topE := fun e => htop (e ▸ hcur)
  obtain ⟨ts, rA, rB, e, G', hG, hts, hF', _⟩ := frames_split G hF hne
  subst hG
  rw [hth, htl] at S
  have ht0 : leT (false, false) (trOf tr e) := ⟨(fun h => by cases h), (fun h => by cases h)⟩
  rcases hf with rfl | rfl
  · simp only [ptrRoutine, Option.some.injEq, Prod.mk.injEq] at hpr
    obtain ⟨_, rfl⟩ := hpr
    obtain ⟨n, hn, S'⟩ := blkT_st32 D Gl.hhi Gl.hlo Gl.h1 (drop_cons hA) hRS (drop_cons hB) hLA hLB haccA haccB
      ⟨hacc.1, hacc.2⟩ hts S (by omega) hfoot
    exact ⟨n, 9, hn, inv_ret S' hF' ht0 (reach_step hx n)⟩
  · simp only [ptrRoutine, Option.some.injEq, Prod.mk.injEq] at hpr
    obtain ⟨_, rfl⟩ := hpr
    obtain ⟨n, hn, S'⟩ := blkT_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "or") 6 (Or.inl rfl) exec_or_m rfl
      (drop_cons hA) hRS (drop_cons hB) hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ hts S (by omega) hfoot
    exact ⟨n, _, hn, inv_ret S' hF' ht0 (reach_step hx n)⟩

/-- info: 'Ember.Proof.PassSim.step_tailBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_tailBlk

theorem blkROK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : blkROK c as bs r rs = true) :
    ∃ (l f : String) (a' b' : List Item),
      as = .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.call, [.imm (.sym f 0)]⟩ :: a' ∧
      bs = .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.call, [.imm (.sym f 0)]⟩ :: b' ∧
      f ≠ "rt_st32" ∧ f ≠ "rt_or32" ∧ routineOK c.tA c.tB f = true ∧ litOK c.tA c.tB l 4 = true ∧
      succOK (rowN rs 2) (r.kb + 2) true true r.act = true := by
  unfold blkROK at h
  split at h
  · rename_i l f a' l' f' b'
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨e1, e2⟩, h1⟩, h2⟩, hr⟩, hl⟩, hs⟩ := h
    subst e1 e2
    exact ⟨l, f, a', b', rfl, rfl, h1, h2, hr, hl, hs⟩
  · cases h

theorem step_blkR {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .blkR)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨l, f, a', b', hA, hB, hf1, hf2, hr, hl, hs⟩ := blkROK_spec hrow
  obtain ⟨hd, its, hpr, i, j, hiA, hjB⟩ := routineOK_spec hr
  have hLA : Has A i its := has_of_take hiA
  have hLB : Has B j its := has_of_take hjB
  obtain ⟨dA, dB, vs, hlA, hdA, hlB, hdB, hnums, hlen⟩ := litOK_spec hl
  have hencA : ∀ ad, Item.encode (.db vs) (A.a.env ad) = .ok (vs.map dbByte) := fun ad => db_encode vs hnums _
  have hencB : ∀ ad, Item.encode (.db vs) (B.a.env ad) = .ok (vs.map dbByte) := fun ad => db_encode vs hnums _
  have hbs : (vs.map dbByte).length = 4 := by rw [List.length_map, hlen]
  have nd := Gl.need (by rw [htag]; intro h; cases h) S hx
  have room := nd.1
  obtain ⟨acc, haccA, haccB, hacc⟩ := Gl.accs
  rw [rowN_drop _ _ _ (by decide)] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  have hA0 := drop_cons hA
  have hB0 := drop_cons hB
  have hA1 := drop_cons2 hA
  have hB1 := drop_cons2 hB
  have fin : ∀ n, Sync D A B lo hi G (k + 2) ((rowAt cert k).kb + 2) true true (mrun D n x) (mrun D n y) → 0 < n →
      ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
    intro n S' hn
    refine ⟨n, n, hn, Or.inr ⟨G, k + 2, s1, ?_, s5 _ hcur, hF, reach_step hx n⟩⟩
    rw [s2]; exact S'.mono s3 s4
  unfold ptrRoutine at hpr
  split at hpr <;> (try cases hpr)
  · exact fin 9 (blkR_ld32 D Gl.hhi Gl.hlo Gl.h1 hA0 hB0 hA1 hB1 hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ hlA hdA hlB hdB
      hencA hencB hbs S (by omega)) (by decide)
  · exact absurd rfl hf1
  · have S' := blkR_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "add") 1 (Or.inr rfl) exec_adc_a_m rfl hA0 hB0 hA1 hB1
      hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ hlA hdA hlB hdB hencA hencB hbs S (by omega)
    exact fin _ S' (by simp)
  · have S' := blkR_bytes D Gl.hhi Gl.hlo Gl.h1 (name := "sub") 3 (Or.inr rfl) exec_sbc_a_m rfl hA0 hB0 hA1 hB1
      hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ hlA hdA hlB hdB hencA hencB hbs S (by omega)
    exact fin _ S' (by simp)
  · exact absurd rfl hf2
  · exact fin 45 (blkR_cmp32 D Gl.hhi Gl.hlo Gl.h1 hA0 hB0 hA1 hB1 hLA hLB haccA haccB ⟨hacc.1, hacc.2⟩ hlA hdA hlB hdB
      hencA hencB hbs S (by omega)) (by decide)

/-- info: 'Ember.Proof.PassSim.step_blkR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_blkR

theorem drop_idx {xs l : List Item} {k : Nat} (h : xs.drop k = l) (i : Nat) : xs[k + i]? = l[i]? := by
  rw [← h, List.getElem?_drop]

theorem copyROK_spec {c : Ctx} {as bs : List Item} {r : Row} {rs : List Row} (h : copyROK c as bs r rs = true) :
    ∃ (l g : String) (n d : Int) (a' : List Item),
      as = .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.ld, [.de, .imm (.sym g 0)]⟩ ::
        .ins ⟨.ld, [.bc, .imm (.num n)]⟩ :: .ins ⟨.ldir, []⟩ :: a' ∧
      as.take 4 = bs.take 4 ∧ 1 ≤ n ∧ n < 65536 ∧ litOK c.tA c.tB l n.toNat = true ∧
      valSameL c.la c.lb (.sym g 0) = true ∧ valOf c.la (.sym g 0) = some d ∧ 0 ≤ d ∧ c.lo ≤ d.toNat ∧
      d.toNat + n.toNat ≤ c.hi ∧ succOK (rowN rs 4) (r.kb + 4) true true r.act = true := by
  unfold copyROK at h
  split at h
  · rename_i l g n a'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨htk, hn⟩, hl⟩, hv⟩, hd⟩, hs⟩ := h
    split at hd
    · rename_i d hdv
      simp only [decide_eq_true_eq] at hd
      exact ⟨l, g, n, d, a', rfl, htk, hn.1, hn.2, hl, hv, hdv, hd.1, hd.2.1, hd.2.2, hs⟩
    · cases hd
  · cases h

theorem step_copyR {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {G : List Frame} {k : Nat} {x y : Cpu × D.W}
    (htag : (rowAt cert k).tag = .copyR)
    (S : Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y)
    (hcur : cur G ∈ (rowAt cert k).act) (hF : FOK A cert tr G) (hx : ∃ n, x = mrun D n x0) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  have hrow := Gl.row (k := k) (by rw [htag]; intro h; cases h)
  simp only [rowOK, htag] at hrow
  obtain ⟨l, g, n, d, a', hA, htk, hn1, hn2, hl, hv, hd, hd0, hdlo, hdhi, hs⟩ := copyROK_spec hrow
  obtain ⟨m, hm⟩ : ∃ m : Nat, n = ((m + 1 : Nat) : Int) := ⟨n.toNat - 1, by omega⟩
  subst hm
  have hmn : (((m + 1 : Nat) : Int)).toNat = m + 1 := by omega
  rw [hmn] at hl hdhi
  -- the items of both images
  have iA := drop_idx hA
  have iB : ∀ i, i < 4 → B.items[(rowAt cert k).kb + i]? = A.items[k + i]? := by
    intro i hi'
    rw [List.getElem?_drop.symm, List.getElem?_drop.symm]
    rw [← List.getElem?_take_of_lt hi', ← htk, List.getElem?_take_of_lt hi']
  have hA0 : A.items[k]? = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) := by simpa using iA 0
  have hA1 : A.items[k + 1]? = some (.ins (Form.ldDEI (.sym g 0)).instr) := iA 1
  have hA2 : A.items[k + 2]? = some (.ins (Form.ldBCI (.num (m + 1 : Nat))).instr) := iA 2
  have hA3 : A.items[k + 3]? = some (.ins ⟨.ldir, []⟩) := iA 3
  have hB0 : B.items[(rowAt cert k).kb]? = some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) := by
    have := iB 0 (by decide); simp only [Nat.add_zero] at this; rw [this]; exact hA0
  have hB1 : B.items[(rowAt cert k).kb + 1]? = some (.ins (Form.ldDEI (.sym g 0)).instr) := by
    rw [iB 1 (by decide)]; exact hA1
  have hB2 : B.items[(rowAt cert k).kb + 2]? = some (.ins (Form.ldBCI (.num (m + 1 : Nat))).instr) := by
    rw [iB 2 (by decide)]; exact hA2
  have hB3 : B.items[(rowAt cert k).kb + 3]? = some (.ins ⟨.ldir, []⟩) := by
    rw [iB 3 (by decide)]; exact hA3
  -- the destination
  have hvB := valSameL_B (A := A) (B := B) hv
  simp only [valOf, symValL, Option.map_map, Option.map_eq_some_iff] at hd
  obtain ⟨a, ha, hda⟩ := hd
  simp only [Function.comp_apply, Int.add_zero] at hda
  subst hda
  have ha' : A.a.labels.reverse.lookup g = some a := ha
  have hlo0 : lo ≤ (Int.ofNat a).toNat := hdlo
  have hhi0 : (Int.ofNat a).toNat + (m + 1) ≤ hi := hdhi
  have hta : (Int.ofNat a).toNat = a := rfl
  have hlo' : lo ≤ a := by rw [← hta]; exact hlo0
  have hhi' : a + (m + 1) ≤ hi := by rw [← hta]; exact hhi0
  have hgA : ∀ pa, (A.a.env pa).val (.sym g 0) = Int.ofNat a := fun pa => by
    rw [val_sym _ g 0 (Int.ofNat a) (by simp [env_resolve, symVal, ha'])]; simp
  have hgB : ∀ pb, (B.a.env pb).val (.sym g 0) = Int.ofNat a := fun pb => by
    rw [← valSame_of hvB 0 pb]; exact hgA 0
  -- the literal
  obtain ⟨dA, dB, vs, hlA, hdA, hlB, hdB, hnums, hlen⟩ := litOK_spec hl
  have hencA : ∀ ad, Item.encode (.db vs) (A.a.env ad) = .ok (vs.map dbByte) := fun ad => db_encode vs hnums _
  have hencB : ∀ ad, Item.encode (.db vs) (B.a.env ad) = .ok (vs.map dbByte) := fun ad => db_encode vs hnums _
  have hbs : (vs.map dbByte).length = m + 1 := by rw [List.length_map, hlen]
  have S' := blkR_copy D Gl.hhi hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hgA hgB
    ⟨hlo', by omega⟩ (by omega) hlA hdA hlB hdB hencA hencB hbs S
  rw [rowN_drop _ _ _ (by decide)] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
  refine ⟨m + 4, m + 4, by omega, Or.inr ⟨G, k + 4, s1, ?_, s5 _ hcur, hF, reach_step hx _⟩⟩
  rw [s2]; exact S'.mono s3 s4

/-- info: 'Ember.Proof.PassSim.step_copyR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_copyR

/-! ## Past labels -/

theorem isZero_encode {it : Item} (h : isZero it = true) : ∀ env, it.encode env = .ok [] := by
  cases it <;> simp_all [isZero, Item.encode]

/-- **Rows of items of no bytes**: past them, no step, to a row of another kind. -/
theorem past_zero {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) {x y : Cpu × D.W} {G : List Frame} :
    ∀ (d k : Nat), A.items.length - k = d → (rowAt cert k).tag ≠ .none →
      Sync D A B lo hi G k (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y →
      cur G ∈ (rowAt cert k).act →
      ∃ k', (rowAt cert k').tag ≠ .none ∧ (rowAt cert k').tag ≠ .skipBoth ∧ (rowAt cert k').tag ≠ .skipA ∧
        Sync D A B lo hi G k' (rowAt cert k').kb (rowAt cert k').th (rowAt cert k').tl x y ∧
        cur G ∈ (rowAt cert k').act
  | d, k, hd, ht, S, hcur => by
    by_cases hb : (rowAt cert k).tag = .skipBoth
    · have hrow := Gl.row (k := k) ht
      simp only [rowOK, hb] at hrow
      unfold skipBothOK at hrow
      split at hrow
      · rename_i a as b bs hA hB
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
        obtain ⟨⟨hz, e⟩, hs⟩ := hrow
        subst e
        rw [nextRow_drop] at hs
        obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
        have S1 : Sync D A B lo hi G (k + 1) ((rowAt cert k).kb + 1) (rowAt cert k).th (rowAt cert k).tl x y :=
          { S with
            atA := at_skip A.placed (drop_cons hA) (isZero_encode hz) S.atA
            atB := at_skip B.placed (drop_cons hB) (isZero_encode hz) S.atB }
        have hk : k < A.items.length := by
          have := drop_cons hA; exact (List.getElem?_eq_some_iff.mp this).1
        cases d with
        | zero => omega
        | succ d =>
          exact past_zero Gl d (k + 1) (by omega) s1 (by rw [s2]; exact S1.mono s3 s4) (s5 _ hcur)
      · cases hrow
    by_cases ha : (rowAt cert k).tag = .skipA
    · have hrow := Gl.row (k := k) ht
      simp only [rowOK, ha] at hrow
      unfold skipAOK at hrow
      split at hrow
      · rename_i a as hA
        simp only [Bool.and_eq_true] at hrow
        obtain ⟨hz, hs⟩ := hrow
        rw [nextRow_drop] at hs
        obtain ⟨s1, s2, s3, s4, s5⟩ := succOK_spec hs
        have S1 : Sync D A B lo hi G (k + 1) (rowAt cert k).kb (rowAt cert k).th (rowAt cert k).tl x y :=
          { S with atA := at_skip A.placed (drop_cons hA) (isZero_encode hz) S.atA }
        have hk : k < A.items.length := by
          have := drop_cons hA; exact (List.getElem?_eq_some_iff.mp this).1
        cases d with
        | zero => omega
        | succ d =>
          exact past_zero Gl d (k + 1) (by omega) s1 (by rw [s2]; exact S1.mono s3 s4) (s5 _ hcur)
      · cases hrow
    exact ⟨k, ht, hb, ha, S, hcur⟩

/-! ## The two runs to the end -/

/-- **A segment from any meeting point**: some steps of `A` (at least one), some of `B`, to the relation
again. -/
theorem step_inv {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) (x y : Cpu × D.W)
    (hI : Inv D A B lo hi cert tr x0 x y) (hx : x.1.halted = false) :
    ∃ a b, 0 < a ∧ Inv D A B lo hi cert tr x0 (mrun D a x) (mrun D b y) := by
  rcases hI with hd | ⟨G, k, ht, S, hcur, hF, hr⟩
  · rw [hd.1] at hx; cases hx
  obtain ⟨k', ht', hb, ha, S', hcur'⟩ := past_zero Gl _ k rfl ht S hcur
  cases htag : (rowAt cert k').tag with
  | none => exact absurd htag ht'
  | skipBoth => exact absurd htag hb
  | skipA => exact absurd htag ha
  | ord => exact step_ord Gl htag S' hcur' hF hr
  | jump => exact step_jump Gl htag S' hcur' hF hr
  | djnz => exact step_djnz Gl htag S' hcur' hF hr
  | call => exact step_call Gl htag S' hcur' hF hr
  | ret => exact step_ret Gl htag S' hcur' hF hr
  | halt => exact step_halt Gl htag S'
  | ldsp => exact step_ldsp Gl htag S' hr
  | ldir => exact step_ldir Gl htag S' hcur' hF hr
  | pack => exact step_pack Gl htag S' hcur' hF hr
  | blk => exact step_blk Gl htag S' hcur' hF hr
  | blkR => exact step_blkR Gl htag S' hcur' hF hr
  | copyR => exact step_copyR Gl htag S' hcur' hF hr
  | retThr => exact step_retThr Gl htag S' hcur' hF hr
  | condRet => exact step_condRet Gl htag S' hcur' hF hr
  | tail => exact step_tail Gl htag S' hcur' hF hr
  | tailBlk => exact step_tailBlk Gl htag S' hcur' hF hr

/-- **The image with the passes halts when the one without does, with the same devices.**  From a
certificate the checker accepts for the two images (`Glob.chk`), what `A`'s run is taken to do
(`Glob.safe`, a hypothesis), the RAM kept equal and the accumulator in it, and the two machines
related at their first items with empty stacks (`Sync` at `0`, `0`; `H`, `L` the same): if `A`'s run
halts after `N` steps, `B`'s halts after some `M`, the devices as `A`'s left them. -/
theorem passes_halt {D : Dev} {A B : Code} {lo hi : Nat} {cert : List Row} {tr : List (Nat × Bool × Bool)}
    {x0 y0 : Cpu × D.W} (Gl : Glob D A B lo hi cert tr x0) (S0 : Sync D A B lo hi [] 0 0 false false x0 y0) :
    ∀ N, (mrun D N x0).1.halted = true →
      ∃ M, (mrun D M y0).1.halted = true ∧ (mrun D M y0).2 = (mrun D N x0).2 := by
  intro N hN
  obtain ⟨_, ⟨r, rs, hc, ht, hkb, hth, htl, htop⟩, _⟩ := Gl.chk
  have hr0 : rowAt cert 0 = r := by simp [rowAt, hc]
  have hI : Inv D A B lo hi cert tr x0 x0 y0 := by
    refine Or.inr ⟨[], 0, by rw [hr0]; exact ht, ?_, by rw [hr0]; exact htop, trivial, ⟨0, rfl⟩⟩
    rw [hr0, hkb, hth, htl]; exact S0
  refine sim_halts D (Inv D A B lo hi cert tr x0) (step_inv Gl) ?_ N x0 y0 hI hN
  intro x y hI hx
  rcases hI with hd | ⟨_, _, _, S, _⟩
  · exact ⟨hd.2.1, hd.2.2⟩
  · rw [S.LA.2] at hx; cases hx

/-- info: 'Ember.Proof.PassSim.passes_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms passes_halt

end Ember.Proof.PassSim
