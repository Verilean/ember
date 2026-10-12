import Ember.Proof.Z80Plan

/-!
# Ember.Proof.Z80Check — `FnStatic`, decided on a plan (plan M7.3)

What the theorems about generated code assume of a function
(`FnStatic`: its operands can be read, its destinations written, the
addresses it forms are of shared bytes, the functions it calls are
there, …) as a check on a `Plan` and on the environment the function is
generated in: `fnStaticB`, sound by `fnStaticB_sound`.

Not decided here: a wide constant is in the literal pool (`LitOK` speaks
of the image) — the check refuses a function that reads one.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-! ## Operands -/

def ownB (E : GEnv) (sl : Slot) : Bool :=
  sl.area == .frame E.fn.name || (match sl.area with | .global _ => true | _ => false)

theorem ownB_iff {E : GEnv} {sl : Slot} : ownB E sl = true ↔ Own E (.slot sl) := by
  obtain ⟨ar, off⟩ := sl
  cases ar with
  | global g => simp [ownB, Own]
  | frame f => simp [ownB, Own]

def memLiveB (E : GEnv) (sl : Slot) : Bool :=
  !(sl.area == .frame E.fn.name) || (match E.live with | some lv => lv.getD sl.off true | none => true)

theorem memLiveB_of {E : GEnv} {sl : Slot} (h : MemLive E (.slot sl)) : memLiveB E sl = true := by
  unfold memLiveB
  by_cases ha : sl.area = .frame E.fn.name
  · have := h ha
    cases hl : E.live with
    | none => simp
    | some lv => simp [this lv hl]
  · simp [ha]

/-- The address of the slot of a temporary, in the plan's layout. -/
def tmpAddrP (P : Plan) (E : GEnv) (t : Nat) : Nat :=
  P.c.layout.addr { area := .frame E.fn.name, off := E.tmpOff[t]! }

/-- The temporaries with a slot. -/
def tmpsOf (E : GEnv) : List Nat := (List.range E.spilled.size).filter fun t => E.spilled[t]!

theorem mem_tmpsOf {E : GEnv} {t : Nat} (h : E.spilled[t]! = true) : t ∈ tmpsOf E := by
  have hlt : t < E.spilled.size := by
    rcases Nat.lt_or_ge t E.spilled.size with h' | h'
    · exact h'
    · rw [getElem!_neg E.spilled t (by omega)] at h
      cases h
  rw [getElem!_pos E.spilled t hlt] at h
  simp [tmpsOf, hlt, h]

def rdB (P : Plan) (E : GEnv) (dts : List Nat) (n : Nat) : Opd → Bool
  | .const _ => true
  | .slot sl => (P.c.layout.areaAddr sl.area).isSome && decide (P.c.layout.addr sl + n ≤ 65536) &&
      (!memLiveB E sl || within P.data (P.c.layout.addr sl) n) && ownB E sl &&
      (P.useOf E.fn.name).contains (sl, n)
  | .tmp t => !E.spilled[t]! ||
      (dts.contains t && (P.c.layout.areaAddr (.frame E.fn.name)).isSome &&
        decide (tmpAddrP P E t + E.fn.tmps[t]! ≤ 65536) && decide (n ≤ E.fn.tmps[t]!))

section
variable {P : Plan} {M : Around} {E : GEnv} {dt : Nat → Prop} {dts : List Nat}

theorem rdB_sound (hdt : ∀ t, t ∈ dts → dt t) {n : Nat} {o : Opd} (h : rdB P E dts n o = true) :
    Rd (P.toZ M) E dt n o := by
  cases o with
  | const v => trivial
  | slot sl =>
    simp only [rdB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨h1, h2, fun hlv j hj => ?_, ownB_iff.mp h4, h5⟩
    rcases h3 with h3 | h3
    · rw [memLiveB_of hlv] at h3
      cases h3
    · exact within_spec h3 j hj
  | tmp t =>
    intro hsp
    simp only [rdB, hsp, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.contains_iff_mem, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨hdt t h1, h2, h3, h4⟩

/-- A wide operand: a constant is refused (the literal pool is of the image). -/
def rdWB (P : Plan) (E : GEnv) (dts : List Nat) (n : Nat) : Opd → Bool
  | .const _ => false
  | o => rdB P E dts n o

theorem rdWB_sound (hdt : ∀ t, t ∈ dts → dt t) {n : Nat} {o : Opd} (h : rdWB P E dts n o = true) :
    RdW (P.toZ M) E dt n o := by
  cases o with
  | const v => cases h
  | slot sl => exact rdB_sound (M := M) hdt (o := .slot sl) h
  | tmp t => exact rdB_sound (M := M) hdt (o := .tmp t) h

def rdNB (P : Plan) (E : GEnv) (dts : List Nat) (n : Nat) (o : Opd) : Bool :=
  if n ≤ 2 then rdB P E dts n o else rdWB P E dts n o

theorem rdNB_sound (hdt : ∀ t, t ∈ dts → dt t) {n : Nat} {o : Opd} (h : rdNB P E dts n o = true) :
    RdN (P.toZ M) E dt n o := by
  unfold rdNB at h
  unfold RdN
  split
  · rename_i hn
    rw [if_pos hn] at h
    exact rdB_sound hdt h
  · rename_i hn
    rw [if_neg hn] at h
    exact rdWB_sound hdt h

/-! ## Destinations -/

/-- The generator leaves the store out. -/
def deadB (E : GEnv) (sl : Slot) (n : Nat) : Bool :=
  sl.area == .frame E.fn.name &&
    (match E.live with
     | some lv => (List.range n).all fun k => !lv.getD (sl.off + k) true
     | none => false)

def wrSlotB (P : Plan) (E : GEnv) (n : Nat) (sl : Slot) : Bool :=
  let a := P.c.layout.addr sl
  (P.c.layout.areaAddr sl.area).isSome && (P.dstOf E.fn.name).contains (sl, n) &&
  (!ownB E sl || (P.useOf E.fn.name).contains (sl, n)) &&
  decide (P.ramStart ≤ a) &&
  ((tmpsOf E).all fun t => decide (a + n ≤ tmpAddrP P E t) || decide (tmpAddrP P E t + E.fn.tmps[t]! ≤ a)) &&
  (decide (a + n ≤ P.stackLo) || decide (P.stackHi ≤ a)) &&
  (decide (a + n ≤ P.acc) || decide (P.acc + 8 ≤ a)) &&
  within (P.wrOf E.fn.name) a n &&
  (!deadB E sl n || apartIv P.data a n)

theorem wrB_of_within {f : String} {a n : Nat} (h : within (P.wrOf f) a n = true) (j : Nat) (hj : j < n) :
    P.wrB f (a + j) = true := by
  simp [Plan.wrB, within_spec h j hj]

theorem wrSlotB_sound {n : Nat} {sl : Slot} (h : wrSlotB P E n sl = true) : WrSlot (P.toZ M) E n sl := by
  simp only [wrSlotB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem, Option.isSome_iff_exists, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, fun hown => ?_, h4, fun j hj ⟨t, hsp, hlo, hhi⟩ => ?_, h6, h7, fun j hj => wrB_of_within h8 j hj,
    fun har lv hlv hall j hj => ?_⟩
  · rcases h3 with h3 | h3
    · rw [ownB_iff.mpr hown] at h3
      cases h3
    · exact h3
  · have := h5 t (mem_tmpsOf hsp)
    have e : tmpAddr (P.toZ M) E t = tmpAddrP P E t := rfl
    rw [e] at hlo hhi
    have hlo' : tmpAddrP P E t ≤ P.c.layout.addr sl + j := hlo
    have hhi' : P.c.layout.addr sl + j < tmpAddrP P E t + E.fn.tmps[t]! := hhi
    omega
  · rcases h9 with h9 | h9
    · have : deadB E sl n = true := by
        simp only [deadB, Bool.and_eq_true, beq_iff_eq, har, hlv, List.all_eq_true, List.mem_range,
          Bool.not_eq_true', true_and]
        exact hall
      rw [this] at h9
      cases h9
    · exact apartIv_spec h9 j hj

def wrDB (P : Plan) (E : GEnv) (n : Nat) : Dst → Bool
  | .slot sl => wrSlotB P E n sl
  | .tmp t => decide (t < E.fn.tmps.size) && E.fn.tmps[t]! == n

theorem wrDB_sound {n : Nat} {d : Dst} (h : wrDB P E n d = true) : Wr (P.toZ M) E n d := by
  cases d with
  | slot sl => exact wrSlotB_sound h
  | tmp t =>
    simp only [wrDB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1, h.2⟩

/-! ## The slots of the temporaries -/

def layB (P : Plan) (E : GEnv) : Bool :=
  (P.c.layout.areaAddr (.frame E.fn.name)).isSome &&
  (tmpsOf E).all fun t =>
    let a := tmpAddrP P E t
    let sz := E.fn.tmps[t]!
    decide (a + sz ≤ 65536) && decide (P.ramStart ≤ a) && apartIv P.data a sz &&
    (decide (a + sz ≤ P.stackLo) || decide (P.stackHi ≤ a)) &&
    (decide (a + sz ≤ P.acc) || decide (P.acc + 8 ≤ a)) &&
    within (P.wrOf E.fn.name) a sz && apartIv P.rt a sz &&
    (tmpsOf E).all fun t' => t == t' || decide (tmpAddrP P E t' + E.fn.tmps[t']! ≤ a) ||
      decide (a + sz ≤ tmpAddrP P E t')

theorem layB_sound (h : layB P E = true) : FnLay (P.toZ M) E := by
  simp only [layB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Option.isSome_iff_exists,
    List.all_eq_true, beq_iff_eq] at h
  obtain ⟨h0, h⟩ := h
  have e : ∀ t, tmpAddr (P.toZ M) E t = tmpAddrP P E t := fun _ => rfl
  refine ⟨h0, fun t hsp => ?_, fun t hsp => ?_, fun t hsp j hj => ?_, fun t hsp => ?_, fun t hsp => ?_,
    fun t hsp j hj => ?_, fun t hsp j hj => ?_, fun t t' hne hsp hsp' => ?_⟩
  · exact (h t (mem_tmpsOf hsp)).1.1.1.1.1.1.1
  · exact (h t (mem_tmpsOf hsp)).1.1.1.1.1.1.2
  · exact apartIv_spec (h t (mem_tmpsOf hsp)).1.1.1.1.1.2 j hj
  · exact (h t (mem_tmpsOf hsp)).1.1.1.1.2
  · exact (h t (mem_tmpsOf hsp)).1.1.1.2
  · exact wrB_of_within (h t (mem_tmpsOf hsp)).1.1.2 j hj
  · exact apartIv_spec (h t (mem_tmpsOf hsp)).1.2 j hj
  · rw [e, e]
    rcases (h t (mem_tmpsOf hsp)).2 t' (mem_tmpsOf hsp') with (h1 | h1) | h1
    · exact absurd h1 hne
    · exact Or.inl h1
    · exact Or.inr h1

/-! ## Addresses -/

/-- The index is below this: its length, its bound, what its size holds. -/
def idxMax (x : IR.Index) : Nat :=
  Nat.min (2 ^ (8 * x.size)) (Nat.min (x.len.getD (2 ^ (8 * x.size))) (x.bound.getD (2 ^ (8 * x.size))))

/-- Where the `n` bytes at the address are, whatever the index: from `lo`, `span` bytes. -/
def addrSpan (P : Plan) (p : IR.Addr) (n : Nat) : Option (Nat × Nat) :=
  match p.root with
  | .static sl =>
    match p.idx with
    | none => some (P.c.layout.addr sl + p.off, n)
    | some x => some (P.c.layout.addr sl + p.off, (idxMax x - 1) * x.scale + n)
  | .ptr _ => none

theorem addrSpan_spec {p : IR.Addr} {n lo sp : Nat} (h : addrSpan P p n = some (lo, sp)) (ist : IR.Sem.St)
    (tmps : Array Nat) (a : Nat) (ha : IR.Sem.addr P.c ist tmps p = some a)
    (hb : IR.Sem.inBound P.c ist tmps p = true) : lo ≤ a ∧ a + n ≤ lo + sp := by
  obtain ⟨root, off, idx⟩ := p
  cases root with
  | ptr q => cases h
  | «static» sl =>
    cases idx with
    | none =>
      simp only [addrSpan] at h
      simp only [IR.Sem.addr] at ha
      cases h
      cases ha
      omega
    | some x =>
      simp only [addrSpan] at h
      cases h
      have hi0 := opd_lt P.c ist tmps x.size x.opd
      have hlen : ∀ len, x.len = some len → IR.Sem.opd P.c ist tmps x.size x.opd < len := by
        intro len hl
        simp only [IR.Sem.addr, hl] at ha
        by_cases hc : IR.Sem.opd P.c ist tmps x.size x.opd < len
        · exact hc
        · rw [if_neg hc] at ha
          cases ha
      have hbd : ∀ b, x.bound = some b → IR.Sem.opd P.c ist tmps x.size x.opd < b := by
        intro b hl
        simpa [IR.Sem.inBound, hl] using hb
      have hmax : IR.Sem.opd P.c ist tmps x.size x.opd < idxMax x := by
        unfold idxMax
        refine Nat.lt_min.mpr ⟨hi0, Nat.lt_min.mpr ⟨?_, ?_⟩⟩
        · cases hl : x.len with
          | none => exact hi0
          | some len => exact hlen len hl
        · cases hl : x.bound with
          | none => exact hi0
          | some b => exact hbd b hl
      have hav : a = P.c.layout.addr sl + off + IR.Sem.opd P.c ist tmps x.size x.opd * x.scale := by
        simp only [IR.Sem.addr] at ha
        cases hl : x.len with
        | none =>
          rw [hl] at ha
          exact (Option.some.inj ha).symm
        | some len =>
          rw [hl] at ha
          simp only [if_pos (hlen len hl)] at ha
          exact (Option.some.inj ha).symm
      have hm : IR.Sem.opd P.c ist tmps x.size x.opd * x.scale ≤ (idxMax x - 1) * x.scale :=
        Nat.mul_le_mul_right _ (by omega)
      show P.c.layout.addr sl + off ≤ a ∧ a + n ≤ P.c.layout.addr sl + off + ((idxMax x - 1) * x.scale + n)
      omega

def addrDataB (P : Plan) (p : IR.Addr) (n : Nat) : Bool :=
  match addrSpan P p n with
  | some (lo, sp) => decide (lo + sp ≤ 65536) && within P.data lo sp
  | none => false

theorem addrDataB_sound {p : IR.Addr} {n : Nat} (h : addrDataB P p n = true) : AddrData (P.toZ M) p n := by
  unfold addrDataB at h
  cases hs : addrSpan P p n with
  | none => rw [hs] at h; cases h
  | some q =>
    obtain ⟨lo, sp⟩ := q
    rw [hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    intro ist tmps a ha hb
    obtain ⟨h1, h2⟩ := addrSpan_spec hs ist tmps a ha hb
    refine ⟨by omega, fun j hj => ?_⟩
    have := within_spec h.2 (a - lo + j) (by omega)
    rw [show lo + (a - lo + j) = a + j by omega] at this
    exact this

def addrStoreB (P : Plan) (E : GEnv) (p : IR.Addr) (n : Nat) : Bool :=
  match addrSpan P p n with
  | some (lo, sp) => decide (lo + sp ≤ 65536) && within P.data lo sp && within (P.wrOf E.fn.name) lo sp &&
      (decide (lo + sp ≤ P.acc) || decide (P.acc + 8 ≤ lo))
  | none => false

theorem addrStoreB_sound {p : IR.Addr} {n : Nat} (h : addrStoreB P E p n = true) :
    AddrStore (P.toZ M) E p n := by
  unfold addrStoreB at h
  cases hs : addrSpan P p n with
  | none => rw [hs] at h; cases h
  | some q =>
    obtain ⟨lo, sp⟩ := q
    rw [hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h
    intro ist tmps a ha hb
    obtain ⟨h1, h2⟩ := addrSpan_spec hs ist tmps a ha hb
    refine ⟨by omega, fun j hj => ?_, fun j hj => ?_, ?_⟩
    · have := within_spec h4 (a - lo + j) (by omega)
      rw [show lo + (a - lo + j) = a + j by omega] at this
      exact this
    · have := wrB_of_within h5 (a - lo + j) (by omega)
      rw [show lo + (a - lo + j) = a + j by omega] at this
      exact this
    · show a + n ≤ P.acc ∨ P.acc + 8 ≤ a
      omega

def checkNeedB (P : Plan) (x : IR.Index) (inl : Option Nat) : Bool :=
  match x.len with
  | none => true
  | some len => P.labels.contains "rt_trap" && decide (0 < len) && decide (len ≤ 65536) &&
      (inl.isSome || decide (len < 65536))

/-- The labels of the plan are in the image. -/
def Labels (P : Plan) (M : Around) : Prop := ∀ l, l ∈ P.labels → ∃ j : Nat, M.items[j]? = some (Item.label l)

theorem checkNeedB_sound (hlab : Labels P M) {x : IR.Index} {inl : Option Nat} (h : checkNeedB P x inl = true) :
    CheckNeed (P.toZ M) x inl := by
  unfold checkNeedB at h
  refine ⟨fun len hl => ?_, fun len hl => ?_⟩
  · rw [hl] at h
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    exact hlab _ h.1.1.1
  · rw [hl] at h
    simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, Bool.or_eq_true] at h
    refine ⟨h.1.1.2, h.1.2, fun hn => ?_⟩
    rcases h.2 with h2 | h2
    · rw [hn] at h2
      cases h2
    · exact h2

def addrNeedB (P : Plan) (E : GEnv) (dts : List Nat) (p : IR.Addr) : Bool :=
  match p.root with
  | .ptr _ => true
  | .static sl =>
    (P.c.layout.areaAddr sl.area).isSome &&
    match p.idx with
    | none => decide (P.c.layout.addr sl + p.off < 65536)
    | some x => rdB P E dts x.size x.opd && ((List.range 17).any fun k => x.scale == 2 ^ k) &&
        checkNeedB P x (inlineLen x p.root) &&
        decide (P.c.layout.addr sl + p.off + (inlineLen x p.root).getD 0 < 65536)

theorem addrNeedB_sound (hlab : Labels P M) (hdt : ∀ t, t ∈ dts → dt t) {p : IR.Addr}
    (h : addrNeedB P E dts p = true) : AddrNeed (P.toZ M) E dt p := by
  intro sl hr
  unfold addrNeedB at h
  rw [hr] at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hi : p.idx with
  | none =>
    rw [hi] at h2
    exact (by simpa using h2 : P.c.layout.addr sl + p.off < 65536)
  | some x =>
    rw [hi] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, beq_iff_eq] at h2
    obtain ⟨⟨⟨h3, k, _, h4⟩, h5⟩, h6⟩ := h2
    exact ⟨rdB_sound hdt h3, ⟨k, h4⟩, checkNeedB_sound hlab (by rw [hr]; exact h5), by rw [hr]; exact h6⟩

/-! ## Calls and effects -/

def retSizeB (gf : IR.Fn) (n : Nat) : Bool :=
  gf.body.toList.all fun i =>
    match i with
    | .ret v => (match v with | some (m, _) => m == n | none => false)
    | _ => true

def callNeedB (P : Plan) (E : GEnv) (dts : List Nat) (g : String) (ret : Option (Nat × Dst))
    (reg : Option (Nat × Opd)) : Bool :=
  match P.c.prog.fn? g with
  | none => false
  | some gf =>
    !gf.dead && (reg.map (·.1) == gf.regParam.map (·.1)) &&
    (match reg with | some (n, o) => rdB P E dts n o | none => true) &&
    (match ret with | some (n, d) => wrDB P E n d && retSizeB gf n | none => true) &&
    P.labels.contains (fnLabel g) &&
    decide (P.depthOf g + 2 ≤ P.depthOf E.fn.name) &&
    ((P.wrOf g).all fun iv => decide (iv.2 ≤ iv.1) || within (P.wrOf E.fn.name) iv.1 (iv.2 - iv.1)) &&
    (tmpsOf E).all fun t =>
      let a := tmpAddrP P E t
      let sz := E.fn.tmps[t]!
      apartIv (P.wrOf g) a sz && apartIv P.rt a sz &&
        (decide (a + sz ≤ P.stackLo) || decide (P.stackHi ≤ a)) &&
        (decide (a + sz ≤ P.acc) || decide (P.acc + 8 ≤ a))

theorem callNeedB_sound (hlab : Labels P M) (hdt : ∀ t, t ∈ dts → dt t) {g : String} {ret : Option (Nat × Dst)}
    {reg : Option (Nat × Opd)} (h : callNeedB P E dts g ret reg = true) :
    CallNeed (P.toZ M) E dt g ret reg := by
  unfold callNeedB at h
  cases hg : P.c.prog.fn? g with
  | none => rw [hg] at h; cases h
  | some gf =>
    rw [hg] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq,
      List.all_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    have hgz : (P.toZ M).c.prog.fn? g = some gf := hg
    refine ⟨⟨gf, hgz⟩, fun gf' e => ?_, fun gf' e => ?_, fun n o e => ?_, fun n d e => ?_,
      fun n d e gf' v e' hv => ?_, hlab _ h5, h6, fun x hx => ?_, fun t hsp j hj hw => ?_⟩
    · rw [hgz] at e; cases e; exact h1
    · rw [hgz] at e; cases e; exact h2
    · subst e
      exact rdB_sound hdt h3
    · subst e
      simp only [Bool.and_eq_true] at h4
      exact wrDB_sound h4.1
    · subst e
      rw [hgz] at e'
      cases e'
      simp only [Bool.and_eq_true, retSizeB, List.all_eq_true] at h4
      have := h4.2 _ hv
      cases v with
      | none => cases this
      | some q =>
        obtain ⟨m, o⟩ := q
        simp only [beq_iff_eq] at this
        exact ⟨o, by rw [this]⟩
    · show P.wrB E.fn.name x = true
      have hx' : P.wrB g x = true := hx
      simp only [Plan.wrB, Bool.or_eq_true] at hx' ⊢
      rcases hx' with ((hx' | hx') | hx') | hx'
      · obtain ⟨iv, hm, h9, h10⟩ := inIv_iff.mp hx'
        rcases h7 iv hm with h11 | h11
        · omega
        · have := within_spec h11 (x - iv.1) (by omega)
          rw [show iv.1 + (x - iv.1) = x by omega] at this
          exact Or.inl (Or.inl (Or.inl this))
      · exact Or.inl (Or.inl (Or.inr hx'))
      · exact Or.inl (Or.inr hx')
      · exact Or.inr hx'
    · have hw' : P.wrB g (tmpAddrP P E t + j) = true := hw
      obtain ⟨⟨⟨h9, h10⟩, h11⟩, h12⟩ := h8 t (mem_tmpsOf hsp)
      simp only [Plan.wrB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw'
      rcases hw' with ((hw' | hw') | hw') | hw'
      · exact apartIv_spec h9 j hj hw'
      · omega
      · omega
      · exact apartIv_spec h10 j hj hw'

def effNeedB (P : Plan) (E : GEnv) (dts : List Nat) (args : List (Nat × Opd)) (ret : Option (Nat × Dst)) : Bool :=
  (match args with
   | [a] => a.1 != 1 || rdB P E dts 1 a.2
   | [a, b] => !(a.1 == 1 && b.1 == 4) || (rdB P E dts 1 a.2 && rdWB P E dts 4 b.2)
   | _ => true) &&
  (match ret with | some (n, d) => wrDB P E n d | none => true)

theorem effNeedB_sound (hdt : ∀ t, t ∈ dts → dt t) {args : List (Nat × Opd)} {ret : Option (Nat × Dst)}
    (h : effNeedB P E dts args ret = true) : EffNeed (P.toZ M) E dt args ret := by
  unfold effNeedB at h
  rw [Bool.and_eq_true] at h
  refine ⟨⟨fun o e => ?_, fun o o' e => ?_⟩, fun n d e => ?_⟩
  · subst e
    have := h.1
    simp only [bne_self_eq_false, Bool.false_or] at this
    exact rdB_sound hdt this
  · subst e
    have := h.1
    simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    exact ⟨rdB_sound hdt this.1, rdWB_sound hdt this.2⟩
  · subst e
    exact wrDB_sound h.2

/-! ## Instructions -/

def needB (P : Plan) (E : GEnv) (dts : List Nat) : IR.Instr → Bool
  | .mov n d src => rdNB P E dts n src && wrDB P E n d
  | .bin _ n d a b => rdNB P E dts n a && rdNB P E dts n b && wrDB P E n d
  | .not n d a | .neg n d a => rdB P E dts n a && wrDB P E n d
  | .cmp _ n d a b => rdNB P E dts n a && rdNB P E dts n b && wrDB P E 1 d
  | .ext n d m src => (if m = 4 then isConst src || rdB P E dts 4 src else rdB P E dts m src) && wrDB P E n d
  | .shift _ n d a m amt =>
    (match amt with
     | .const k => rdNB P E dts n a && decide (k < 2 ^ (8 * m)) && wrDB P E n d
     | _ => true)
  | .lea d p => addrNeedB P E dts p && wrDB P E 2 d
  | .load n d p => addrNeedB P E dts p && addrDataB P p n && wrDB P E n d
  | .store n p src => addrNeedB P E dts p && addrStoreB P E p n && rdB P E dts n src
  | .br _ n a b l => rdNB P E dts n a && rdNB P E dts n b && P.labels.contains (lname E l)
  | .jmp _ | .label _ => true
  | .ret v => (match v with | some (n, o) => rdNB P E dts n o | none => true)
  | .trap => P.labels.contains "rt_trap"
  | .call g ret reg => callNeedB P E dts g ret reg
  | .eff _ args ret => effNeedB P E dts args ret
  | _ => false

theorem needB_sound (hlab : Labels P M) (hdt : ∀ t, t ∈ dts → dt t) {i : IR.Instr} (h : needB P E dts i = true) :
    Need (P.toZ M) E dt i := by
  cases i with
  | mov n d src =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨rdNB_sound hdt h.1, wrDB_sound h.2⟩
  | bin op n d a b =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨rdNB_sound hdt h.1.1, rdNB_sound hdt h.1.2, wrDB_sound h.2⟩
  | not n d a =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨rdB_sound hdt h.1, wrDB_sound h.2⟩
  | neg n d a =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨rdB_sound hdt h.1, wrDB_sound h.2⟩
  | cmp op n d a b =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨rdNB_sound hdt h.1.1, rdNB_sound hdt h.1.2, wrDB_sound h.2⟩
  | ext n d m src =>
    simp only [needB, Bool.and_eq_true] at h
    refine ⟨?_, wrDB_sound h.2⟩
    have h1 := h.1
    split
    · rename_i hm
      rw [if_pos hm] at h1
      intro v hv
      rcases Bool.or_eq_true _ _ |>.mp h1 with h2 | h2
      · cases src with
        | const k => trivial
        | slot sl => cases h2
        | tmp t => cases h2
      · exact rdB_sound hdt h2
    · rename_i hm
      rw [if_neg hm] at h1
      exact rdB_sound hdt h1
  | shift l n d a m amt =>
    intro k hk
    subst hk
    simp only [needB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨⟨rdNB_sound hdt h.1.1, h.1.2⟩, wrDB_sound h.2⟩
  | lea d p =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨addrNeedB_sound hlab hdt h.1, wrDB_sound h.2⟩
  | load n d p =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨addrNeedB_sound hlab hdt h.1.1, addrDataB_sound h.1.2, wrDB_sound h.2⟩
  | store n p src =>
    simp only [needB, Bool.and_eq_true] at h
    exact ⟨addrNeedB_sound hlab hdt h.1.1, addrStoreB_sound h.1.2, rdB_sound hdt h.2⟩
  | br op n a b l =>
    simp only [needB, Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨rdNB_sound hdt h.1.1, rdNB_sound hdt h.1.2, hlab _ h.2⟩
  | jmp l => trivial
  | label l => trivial
  | ret v =>
    intro n o e
    subst e
    exact rdNB_sound hdt h
  | trap =>
    simp only [needB, List.contains_iff_mem] at h
    exact hlab _ h
  | call g ret reg => exact callNeedB_sound hlab hdt h
  | eff e args ret => exact effNeedB_sound hdt h
  | _ => cases h

/-! ## The temporaries assigned, as a list -/

def dtAfterL (dts : List Nat) : Dst → List Nat
  | .tmp t => t :: dts
  | _ => dts

def dtRetL (dts : List Nat) : Option (Nat × Dst) → List Nat
  | some (_, d) => dtAfterL dts d
  | none => dts

def dtNextL (dts : List Nat) : IR.Instr → List Nat
  | .label _ => []
  | .mov _ d _ | .bin _ _ d _ _ | .shift _ _ d _ _ _ | .not _ d _ | .neg _ d _ | .ext _ d _ _
  | .cmp _ _ d _ _ | .load _ d _ | .lea d _ => dtAfterL dts d
  | .call _ ret _ | .eff _ _ ret => dtRetL dts ret
  | _ => dts

theorem dtAfterL_sound (hdt : ∀ t, t ∈ dts → dt t) (d : Dst) (t : Nat) (h : t ∈ dtAfterL dts d) :
    dtAfter dt d t := by
  cases d with
  | slot sl => exact Or.inl (hdt t h)
  | tmp x =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (hdt t h)

theorem dtRetL_sound (hdt : ∀ t, t ∈ dts → dt t) (ret : Option (Nat × Dst)) (t : Nat) (h : t ∈ dtRetL dts ret) :
    dtRet dt ret t := by
  cases ret with
  | none => exact hdt t h
  | some q => exact dtAfterL_sound hdt q.2 t h

theorem dtNextL_sound (hdt : ∀ t, t ∈ dts → dt t) (i : IR.Instr) (t : Nat) (h : t ∈ dtNextL dts i) :
    dtNext dt i t := by
  cases i <;>
    first
    | exact dtAfterL_sound hdt _ t h
    | exact dtRetL_sound hdt _ t h
    | exact hdt t h
    | cases h

def dtL (body : Array IR.Instr) : Nat → List Nat
  | 0 => []
  | pc + 1 =>
    match body[pc]? with
    | some i => dtNextL (dtL body pc) i
    | none => dtL body pc

theorem dtL_sound (body : Array IR.Instr) : ∀ (pc t : Nat), t ∈ dtL body pc → dtAt body pc t
  | 0, _, h => by cases h
  | pc + 1, t, h => by
    simp only [dtL, dtAt] at h ⊢
    cases hb : body[pc]? with
    | none =>
      rw [hb] at h
      exact dtL_sound body pc t h
    | some i =>
      rw [hb] at h
      exact dtNextL_sound (dtL_sound body pc) i t h

/-! ## The function -/

def fnStaticB (P : Plan) (E : GEnv) : Bool :=
  shapeB E.fn &&
  ((List.range E.fn.body.size).all fun pc =>
    match E.fn.body[pc]? with
    | some i => needB P (envAt E pc i) (dtL E.fn.body pc) i
    | none => true) &&
  layB P E && decide (P.rtK + 2 ≤ P.depthOf E.fn.name) &&
  (match E.fn.regParam with
   | some (n, sl) => size12 n && wrSlotB P E n sl
   | none => true)

/-- **The check is sound**: a function it accepts has `FnStatic`, in an
image that has the plan's labels. -/
theorem fnStaticB_sound (hlab : Labels P M) (h : fnStaticB P E = true) : FnStatic (P.toZ M) E := by
  simp only [fnStaticB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsh, hneed⟩, hlay⟩, hdep⟩, hreg⟩ := h
  obtain ⟨hcov, hfalls, hne, hlabels⟩ := shapeB_sound hsh
  refine ⟨fun pc i hb => ?_, hcov, hfalls, hne, hlabels, layB_sound hlay, hdep, fun n sl e => ?_⟩
  · have hlt : pc < E.fn.body.size := by
      rcases Nat.lt_or_ge pc E.fn.body.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hb; cases hb
    have := hneed pc hlt
    rw [hb] at this
    exact needB_sound hlab (dtL_sound E.fn.body pc) this
  · rw [e] at hreg
    simp only [Bool.and_eq_true] at hreg
    exact ⟨size12_spec hreg.1, wrSlotB_sound hreg.2⟩

end

/-- info: 'Ember.Proof.Z80Gen.fnStaticB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnStaticB_sound

end Ember.Proof.Z80Gen
