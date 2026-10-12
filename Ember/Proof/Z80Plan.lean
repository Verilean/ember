import Ember.Proof.Z80Shape

/-!
# Ember.Proof.Z80Plan — a layout one can compute with (plan M7.3)

`ZCtx` says what the proofs about generated code need of an image in
predicates: the bytes shared with the IR, the bytes a function may
write, the slots it uses.  A `Plan` gives them as data — intervals of
addresses, lists of slots — and `Plan.toZ` is the `ZCtx` of a plan and
of what is around it (`Around`: the image and what is around the CPU).

`okB` decides what `ZCtx.OK` asks of the plan (`plan_ok`); what it asks
of the image and of the machine stays to be given: the items are placed,
an instruction without I/O leaves the machine alone, the areas and the
accumulator have their symbols.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-! ## Intervals of addresses -/

/-- Intervals `[lo, hi)`. -/
abbrev Ivs := List (Nat × Nat)

def inIv (ivs : Ivs) (x : Nat) : Bool := ivs.any fun iv => decide (iv.1 ≤ x) && decide (x < iv.2)

/-- The `n` bytes at `a` are in one of the intervals. -/
def within (ivs : Ivs) (a n : Nat) : Bool := ivs.any fun iv => decide (iv.1 ≤ a) && decide (a + n ≤ iv.2)

/-- The `n` bytes at `a` are in none of the intervals. -/
def apartIv (ivs : Ivs) (a n : Nat) : Bool := ivs.all fun iv => decide (a + n ≤ iv.1) || decide (iv.2 ≤ a)

theorem inIv_iff {ivs : Ivs} {x : Nat} : inIv ivs x = true ↔ ∃ iv, iv ∈ ivs ∧ iv.1 ≤ x ∧ x < iv.2 := by
  simp [inIv]

theorem within_spec {ivs : Ivs} {a n : Nat} (h : within ivs a n = true) (j : Nat) (hj : j < n) :
    inIv ivs (a + j) = true := by
  simp only [within, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨iv, hm, h1, h2⟩ := h
  exact inIv_iff.mpr ⟨iv, hm, by omega, by omega⟩

theorem apartIv_spec {ivs : Ivs} {a n : Nat} (h : apartIv ivs a n = true) (j : Nat) (hj : j < n) :
    ¬ inIv ivs (a + j) = true := by
  simp only [apartIv, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  intro hin
  obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hin
  have := h iv hm
  omega

/-- Every address of the intervals has the property the check of an interval gives. -/
theorem ivs_all {ivs : Ivs} {p : Nat × Nat → Bool} {Q : Nat → Prop} (h : ivs.all p = true)
    (hp : ∀ iv x, p iv = true → iv.1 ≤ x → x < iv.2 → Q x) (x : Nat) (hx : inIv ivs x = true) : Q x := by
  obtain ⟨iv, hm, h1, h2⟩ := inIv_iff.mp hx
  exact hp iv x (List.all_eq_true.mp h iv hm) h1 h2

/-! ## The plan -/

structure Plan where
  c : IR.Ctx
  ramStart : Nat
  stackLo : Nat
  stackHi : Nat
  acc : Nat
  rtK : Nat
  /-- The stack a function needs below its return address. -/
  depth : List (String × Nat)
  /-- The bytes shared with the IR. -/
  data : Ivs
  /-- The runtime's own bytes. -/
  rt : Ivs
  /-- The bytes a function may write, besides the accumulator, the stack and the runtime's own. -/
  wr : List (String × Ivs)
  /-- The slots a function uses, and those it writes. -/
  use : List (String × List (Slot × Nat))
  dst : List (String × List (Slot × Nat))
  /-- Labels that are in the image. -/
  labels : List String
  /-- Wide constants that are in the image's literal pool: bytes and value. -/
  lits : List (Nat × Nat) := []

def Plan.depthOf (P : Plan) (f : String) : Nat := (P.depth.lookup f).getD 0
def Plan.wrOf (P : Plan) (f : String) : Ivs := (P.wr.lookup f).getD []
def Plan.useOf (P : Plan) (f : String) : List (Slot × Nat) := (P.use.lookup f).getD []
def Plan.dstOf (P : Plan) (f : String) : List (Slot × Nat) := (P.dst.lookup f).getD []

def Plan.wrB (P : Plan) (f : String) (x : Nat) : Bool :=
  inIv (P.wrOf f) x || (decide (P.acc ≤ x) && decide (x < P.acc + 8)) ||
    (decide (P.stackLo ≤ x) && decide (x < P.stackHi)) || inIv P.rt x

/-- The image and the machine around the CPU. -/
structure Around where
  items : List Item
  a : Assembled
  addrs : List Nat
  W : Type
  bus : W → UInt16 → UInt8
  dev : W → IoEvent → W
  wrel : Ember.Lang.World → W → Prop

/-- The setting of the proofs, for a plan and a machine. -/
def Plan.toZ (P : Plan) (M : Around) : ZCtx :=
  { items := M.items, a := M.a, addrs := M.addrs, c := P.c,
    data := fun x => inIv P.data x = true,
    ramStart := P.ramStart,
    use := fun f p => p ∈ P.useOf f,
    dst := fun f p => p ∈ P.dstOf f,
    stackLo := P.stackLo, stackHi := P.stackHi,
    depth := P.depthOf, rtK := P.rtK, acc := P.acc,
    wr := fun f x => P.wrB f x = true,
    rt := fun x => inIv P.rt x = true,
    W := M.W, bus := M.bus, dev := M.dev, wrel := M.wrel }

theorem lookup_mem {α : Type} {l : List (String × α)} {f : String} {v : α} (h : l.lookup f = some v) :
    (f, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [List.lookup_cons] at h
    by_cases hk : (f == k) = true
    · rw [hk] at h
      cases h
      have : f = k := by simpa using hk
      rw [this]
      exact List.mem_cons_self
    · simp only [hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A slot of a function's list is in the list of an entry of the table. -/
theorem mem_of_lookup {α : Type} {l : List (String × List α)} {f : String} {x : α}
    (h : x ∈ (l.lookup f).getD []) : ∃ e, e ∈ l ∧ x ∈ e.2 := by
  cases hl : l.lookup f with
  | none => rw [hl] at h; cases h
  | some v =>
    rw [hl] at h
    exact ⟨(f, v), lookup_mem hl, h⟩

/-! ## What `ZCtx.OK` asks of the plan -/

def okB (P : Plan) : Bool :=
  let L := P.c.layout
  (P.data.all fun iv => decide (iv.2 ≤ iv.1) ||
    (decide (P.ramStart ≤ iv.1) && decide (iv.2 ≤ 65536) &&
      (decide (iv.2 ≤ P.acc) || decide (P.acc + 8 ≤ iv.1)) &&
      (decide (iv.2 ≤ P.stackLo) || decide (P.stackHi ≤ iv.1)) &&
      P.rt.all fun r => decide (iv.2 ≤ r.1) || decide (r.2 ≤ iv.1))) &&
  decide (P.ramStart ≤ P.stackLo) && decide (P.stackHi ≤ 65536) &&
  decide (P.ramStart ≤ P.acc) && decide (P.acc + 8 ≤ 65536) &&
  (decide (P.acc + 8 ≤ P.stackLo) || decide (P.stackHi ≤ P.acc)) &&
  (P.rt.all fun iv => decide (iv.2 ≤ iv.1) ||
    (decide (P.ramStart ≤ iv.1) &&
      (decide (iv.2 ≤ P.acc) || decide (P.acc + 8 ≤ iv.1)) &&
      (decide (iv.2 ≤ P.stackLo) || decide (P.stackHi ≤ iv.1)))) &&
  (P.use.all fun e => e.2.all fun p => decide (L.addr p.1 + p.2 ≤ 65536)) &&
  (P.dst.all fun e => e.2.all fun p => decide (L.addr p.1 + p.2 ≤ 65536)) &&
  (P.use.all fun e => e.2.all fun a => (P.dstOf e.1).all fun b =>
    IR.slotsOverlap a.1 a.2 b.1 b.2 || decide (L.addr a.1 + a.2 ≤ L.addr b.1) ||
      decide (L.addr b.1 + b.2 ≤ L.addr a.1))

/-- **The plan gives `ZCtx.OK`**, with what the image and the machine are to give. -/
theorem plan_ok {P : Plan} (h : okB P = true) (M : Around)
    (placed : Placed M.items 0 M.a M.addrs) (quiet : ∀ w, M.dev w .none = w)
    (areas : ∀ ar ad, P.c.layout.areaAddr ar = some ad → (P.toZ M).sym (areaSym ar) ad)
    (accSym : (P.toZ M).sym "rt_acc" P.acc) : (P.toZ M).OK := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hdata, hs1⟩, hs2⟩, ha1⟩, ha2⟩, has⟩, hrt⟩, hub⟩, hdb⟩, hap⟩ := h
  have hd : ∀ x, inIv P.data x = true → (P.ramStart ≤ x ∧ x < 65536) ∧ (x < P.acc ∨ P.acc + 8 ≤ x) ∧
      (x < P.stackLo ∨ P.stackHi ≤ x) ∧ ¬ inIv P.rt x = true := by
    refine ivs_all hdata (fun iv x hp h1 h2 => ?_)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
    rcases hp with hp | ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩
    · omega
    · refine ⟨by omega, by omega, by omega, fun hin => ?_⟩
      obtain ⟨r, hm, h8, h9⟩ := inIv_iff.mp hin
      have := h7 r hm
      omega
  have hr : ∀ x, inIv P.rt x = true → P.ramStart ≤ x ∧ (x < P.acc ∨ P.acc + 8 ≤ x) ∧
      (x < P.stackLo ∨ P.stackHi ≤ x) := by
    refine ivs_all hrt (fun iv x hp h1 h2 => ?_)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
    omega
  refine
    { placed := placed, quiet := quiet, areas := areas,
      ram := fun x hx => (hd x hx).1,
      stack := ⟨hs1, hs2⟩,
      accSym := accSym,
      accRam := ⟨ha1, ha2⟩,
      accStack := has,
      accData := fun x hx => (hd x hx).2.1,
      accWr := fun f x h1 h2 => ?_,
      wrStack := fun f x h1 h2 => ?_,
      nostack := fun x hx => (hd x hx).2.2.1,
      rtRam := fun x hx => (hr x hx).1,
      rtData := fun x hx => (hd x hx).2.2.2,
      rtStack := fun x hx => (hr x hx).2.2,
      rtAcc := fun x hx => (hr x hx).2.1,
      rtWr := fun f x hx => ?_,
      ubound := fun f a an hu => ?_,
      dbound := fun f b bn hd' => ?_,
      apart := fun f a an b bn hu hd' => ?_ }
  · show P.wrB f x = true
    have h1' : P.acc ≤ x := h1
    have h2' : x < P.acc + 8 := h2
    simp [Plan.wrB, h1', h2']
  · show P.wrB f x = true
    have h1' : P.stackLo ≤ x := h1
    have h2' : x < P.stackHi := h2
    simp [Plan.wrB, h1', h2']
  · show P.wrB f x = true
    have hx' : inIv P.rt x = true := hx
    simp [Plan.wrB, hx']
  · obtain ⟨e, he, hm⟩ := mem_of_lookup (show (a, an) ∈ (P.use.lookup f).getD [] from hu)
    have := List.all_eq_true.mp (List.all_eq_true.mp hub e he) _ hm
    exact (by simpa using this : P.c.layout.addr a + an ≤ 65536)
  · obtain ⟨e, he, hm⟩ := mem_of_lookup (show (b, bn) ∈ (P.dst.lookup f).getD [] from hd')
    have := List.all_eq_true.mp (List.all_eq_true.mp hdb e he) _ hm
    exact (by simpa using this : P.c.layout.addr b + bn ≤ 65536)
  · have hu' : (a, an) ∈ (P.use.lookup f).getD [] := hu
    cases hl : P.use.lookup f with
    | none => rw [hl] at hu'; cases hu'
    | some v =>
      rw [hl] at hu'
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hap (f, v) (lookup_mem hl)) _ hu')
        (b, bn) hd'
      exact (by simpa [or_assoc] using h1 : IR.slotsOverlap a an b bn = true ∨
        P.c.layout.addr a + an ≤ P.c.layout.addr b ∨ P.c.layout.addr b + bn ≤ P.c.layout.addr a)

end Ember.Proof.Z80Gen
