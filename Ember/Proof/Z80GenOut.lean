import Ember.Proof.Z80GenChunks

/-!
# Ember.Proof.Z80GenOut — the generator never reads its output (plan M7.3)

The generator only appends to `GS.out`: nothing it does depends on what
is there already.  `OutFree m`: run from a state, `m` gives what it gives
from the same state with `out` empty, its items after those of the state
(`outFree_genBody`).  So a stretch of a pass is checked from the state
before it with `out` empty (`body_step_out`): the kernel compares the
items of the stretch, not all the items of the function before it.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Codegen Ember.Z80.Asm Ember.Z80.IR

/-- The state with no items. -/
def noItems (s : GS) : GS := { s with out := #[] }

/-- `m` does not read the items already generated: they stay in front of its own. -/
def OutFree {α : Type} (m : GM α) : Prop :=
  ∀ env s, runG m env s = (runG m env (noItems s)).map fun p => (p.1, { p.2 with out := s.out ++ p.2.out })

theorem OutFree.pure {α : Type} (a : α) : OutFree (pure a : GM α) := by
  intro env s
  cases s
  simp [runG, noItems, Except.map]
  rfl

theorem OutFree.throw {α : Type} (e : String) : OutFree (throw e : GM α) := by
  intro env s
  rfl

theorem OutFree.bind {α β : Type} (m : GM α) (k : α → GM β) (hm : OutFree m) (hk : ∀ a, OutFree (k a)) :
    OutFree (m >>= k) := by
  intro env s
  rw [runG_bind, runG_bind, hm]
  cases runG m env (noItems s) with
  | error e => rfl
  | ok p =>
    obtain ⟨a, t⟩ := p
    simp only [Except.map]
    have he : noItems { t with out := s.out ++ t.out } = noItems t := rfl
    rw [hk a env, hk a env t, he]
    cases runG (k a) env (noItems t) with
    | error e => rfl
    | ok q => simp [Except.map, Array.append_assoc]

theorem OutFree.get_bind {α : Type} (k : GS → GM α) (hk : ∀ s, k s = k (noItems s)) (h : ∀ s, OutFree (k s)) :
    OutFree (get >>= k) := by
  intro env s
  have e1 : runG (get >>= k) env s = runG (k s) env s := rfl
  have e2 : runG (get >>= k) env (noItems s) = runG (k (noItems s)) env (noItems s) := rfl
  rw [e1, e2, hk s, h (noItems s) env s]

theorem OutFree.read_bind {α : Type} (k : GEnv → GM α) (h : ∀ e, OutFree (k e)) :
    OutFree (read >>= k) := by
  intro env s
  exact h env env s

theorem OutFree.withReader {α : Type} (f : GEnv → GEnv) (m : GM α) (h : OutFree m) :
    OutFree (withReader f m) := by
  intro env s
  exact h (f env) s

theorem OutFree.modify (f : GS → GS) (hf : ∀ s, f s = { f (noItems s) with out := s.out ++ (f (noItems s)).out }) :
    OutFree (modify f : GM Unit) := by
  intro env s
  show Except.ok ((), f s) = Except.map _ (Except.ok ((), f (noItems s)))
  rw [hf s]
  rfl

theorem OutFree.ite {α : Type} (c : Prop) [Decidable c] (a b : GM α) (ha : OutFree a) (hb : OutFree b) :
    OutFree (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- What `modify` leaves of `out`: a field other than `out` set, or an item pushed. -/
macro "modify_out" : tactic =>
  `(tactic| (intro s; cases s; simp only [noItems]; first | rfl | (simp; done) | (split <;> (dsimp only; simp only [Array.append_empty]; done))))

/-- `OutFree` of what the generator calls, as each is proved (`macro_rules` below). -/
syntax "outfree_lemma" : tactic

macro "outfree_step" : tactic =>
  `(tactic| first
    | (with_reducible exact OutFree.pure _)
    | (with_reducible exact OutFree.throw _)
    | (with_reducible apply OutFree.modify); modify_out
    | (with_reducible refine OutFree.get_bind _ ?_ (fun _ => ?_)); (intro s; rfl)
    | (with_reducible refine OutFree.read_bind _ (fun _ => ?_))
    | (with_reducible refine OutFree.withReader _ _ ?_)
    | (with_reducible refine OutFree.bind _ _ ?_ (fun _ => ?_))
    | (with_reducible refine OutFree.ite _ _ _ ?_ ?_)
    | outfree_lemma
    | split
    | (with_reducible assumption))

/-- Discharges `OutFree` of the generator's code, given `OutFree` of what it calls. -/
macro "outfree" : tactic => `(tactic| repeat' ((try intros); (try dsimp only); outfree_step))

theorem outFree_ins (op : Op) (args : List Arg) : OutFree (ins op args) := by
  unfold ins; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_ins ..)

theorem outFree_call (routine : String) : OutFree (call routine) := by
  unfold call; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_call ..)

theorem outFree_setRegs (f : Regs → Regs) : OutFree (setRegs f) := by
  unfold setRegs; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_setRegs ..)

theorem outFree_rep : ∀ (k : Nat) (m : GM Unit), OutFree m → OutFree (rep k m)
  | 0, _, _ => by unfold rep; outfree
  | k + 1, m, h => by unfold rep; have := outFree_rep k m h; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible refine outFree_rep _ _ ?_)

theorem outFree_noteRead (s : Slot) : OutFree (noteRead s) := by
  unfold noteRead; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_noteRead ..)

theorem outFree_noteAddr (s : Slot) : OutFree (noteAddr s) := by
  unfold noteAddr; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_noteAddr ..)

theorem outFree_storeNeeded (s : Slot) (n : Nat) : OutFree (storeNeeded s n) := by
  unfold storeNeeded; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_storeNeeded ..)

theorem outFree_addrOf (o : Opd) : OutFree (addrOf o) := by
  unfold addrOf; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_addrOf ..)

theorem outFree_ptrOf (n : Nat) (o : Opd) : OutFree (ptrOf n o) := by
  unfold ptrOf; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_ptrOf ..)

theorem outFree_loadA (o : Opd) : OutFree (loadA o) := by
  unfold loadA; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadA ..)

theorem outFree_loadHL (o : Opd) : OutFree (loadHL o) := by
  unfold loadHL; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadHL ..)

theorem outFree_loadDE (o : Opd) : OutFree (loadDE o) := by
  unfold loadDE; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadDE ..)

theorem outFree_loadAcc (n : Nat) (o : Opd) : OutFree (loadAcc n o) := by
  unfold loadAcc; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadAcc ..)

theorem outFree_killWrite (s : Slot) (n : Nat) : OutFree (killWrite s n) := by
  unfold killWrite; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_killWrite ..)

theorem outFree_killSlots  : OutFree (killSlots) := by
  unfold killSlots; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_killSlots ..)

theorem outFree_killAll  : OutFree (killAll) := by
  unfold killAll; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_killAll ..)

theorem outFree_tmpSlot (t : Nat) : OutFree (tmpSlot t) := by
  unfold tmpSlot; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_tmpSlot ..)

theorem outFree_forget (o : Opd) : OutFree (forget o) := by
  unfold forget; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_forget ..)

theorem outFree_storeA (d : Dst) : OutFree (storeA d) := by
  unfold storeA; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_storeA ..)

theorem outFree_storeHL (d : Dst) : OutFree (storeHL d) := by
  unfold storeHL; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_storeHL ..)

theorem outFree_storeAcc (n : Nat) (d : Dst) : OutFree (storeAcc n d) := by
  unfold storeAcc; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_storeAcc ..)

theorem outFree_store (n : Nat) (d : Dst) : OutFree (store n d) := by
  unfold store; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_store ..)

theorem outFree_load (n : Nat) (o : Opd) : OutFree (load n o) := by
  unfold load; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_load ..)

theorem outFree_newLabel : OutFree Codegen.newLabel := by
  intro env s
  have h (t : GS) : runG Codegen.newLabel env t =
      .ok (s!"x_{sanitize env.fn.name}_{t.labels}", { t with labels := t.labels + 1 }) := rfl
  rw [h, h]
  cases s
  simp [noItems, Except.map]

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_newLabel ..)

theorem outFree_localLabel (l : Nat) : OutFree (localLabel l) := by
  unfold localLabel; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_localLabel ..)

theorem outFree_alu8 (op : Bin) (x : Arg) : OutFree (Codegen.alu8 op x) := by
  unfold Codegen.alu8; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_alu8 ..)

theorem outFree_logicConst (op : Bin) (reg : Arg) (m : Nat) : OutFree (logicConst op reg m) := by
  unfold logicConst; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_logicConst ..)

theorem outFree_loadE (a b : Opd) : OutFree (loadE a b) := by
  unfold loadE; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadE ..)

theorem outFree_bin8Rt (op : Bin) (a b : Opd) : OutFree (bin8Rt op a b) := by
  unfold bin8Rt; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin8Rt ..)

theorem outFree_alu8Opd (op : Bin) (a b : Opd) : OutFree (Codegen.alu8Opd op a b) := by
  unfold alu8Opd; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_alu8Opd ..)

theorem outFree_bin8Alu (op : Bin) (a b : Opd) : OutFree (bin8Alu op a b) := by
  unfold bin8Alu; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin8Alu ..)

theorem outFree_bin8 (op : Bin) (a b : Opd) : OutFree (bin8 op a b) := by
  unfold bin8; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin8 ..)

theorem outFree_bin16Const (op : Bin) (v : Nat) : OutFree (bin16Const op v) := by
  unfold bin16Const; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin16Const ..)

theorem outFree_bin16Reg (op : Bin) : OutFree (bin16Reg op) := by
  unfold bin16Reg; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin16Reg ..)

theorem outFree_bin16 (op : Bin) (a b : Opd) : OutFree (bin16 op a b) := by
  unfold bin16; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_bin16 ..)

theorem outFree_binW (op : Bin) (n : Nat) (a b : Opd) : OutFree (binW op n a b) := by
  unfold binW; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_binW ..)

theorem outFree_genBin (op : Bin) (n : Nat) (a b : Opd) : OutFree (genBin op n a b) := by
  unfold genBin; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genBin ..)

theorem outFree_countToB (m : Nat) (amt : Opd) : OutFree (countToB m amt) := by
  unfold countToB; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_countToB ..)

theorem outFree_genShift (left : Bool) (n : Nat) (a : Opd) (m : Nat) (amt : Opd) : OutFree (genShift left n a m amt) := by
  unfold genShift; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genShift ..)

theorem outFree_cp8Opd (a b : Opd) : OutFree (cp8Opd a b) := by
  unfold cp8Opd; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_cp8Opd ..)

theorem outFree_flags8 (op : Cmp) (a b : Opd) : OutFree (flags8 op a b) := by
  unfold flags8; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_flags8 ..)

theorem outFree_eqHL (v : Nat) : OutFree (eqHL v) := by
  unfold eqHL; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_eqHL ..)

theorem outFree_sub16 (a b : Opd) : OutFree (sub16 a b) := by
  unfold sub16; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_sub16 ..)

theorem outFree_flags16 (op : Cmp) (a b : Opd) : OutFree (flags16 op a b) := by
  unfold flags16; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_flags16 ..)

theorem outFree_flagsW (n : Nat) (a b : Opd) : OutFree (flagsW n a b) := by
  unfold flagsW; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_flagsW ..)

theorem outFree_genFlags (op : Cmp) (n : Nat) (a b : Opd) : OutFree (genFlags op n a b) := by
  unfold genFlags; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genFlags ..)

theorem outFree_addOff (k : Nat) : OutFree (addOff k) := by
  unfold addOff; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_addOff ..)

theorem outFree_scaleHL : ∀ (fuel sc : Nat), OutFree (scaleHL fuel sc)
  | 0, _ => by unfold scaleHL; outfree
  | fuel + 1, sc => by unfold scaleHL; have := outFree_scaleHL fuel (sc / 2); outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_scaleHL ..)

theorem outFree_loadHLByte (o : Opd) : OutFree (loadHLByte o) := by
  unfold loadHLByte; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_loadHLByte ..)

theorem outFree_genCheck (x : Index) (inline : Option Nat) : OutFree (genCheck x inline) := by
  unfold genCheck; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genCheck ..)

theorem outFree_genAddr (p : Addr) : OutFree (genAddr p) := by
  unfold genAddr; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genAddr ..)

theorem outFree_jumpTo (l : Nat) : OutFree (jumpTo l) := by
  unfold jumpTo; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_jumpTo ..)

theorem outFree_genLabel (l : Nat) : OutFree (genLabel l) := by
  unfold genLabel; outfree

macro_rules | `(tactic| outfree_lemma) => `(tactic| with_reducible exact outFree_genLabel ..)

theorem outFree_genInstr (i : IR.Instr) : OutFree (genInstr i) := by
  unfold genInstr; outfree

theorem outFree_genBody (f : IR.Fn) (ann : Bool) : ∀ (k : Nat) (l : List IR.Instr), OutFree (genBody f ann k l)
  | _, [] => by unfold genBody; outfree
  | k, i :: r => by
    unfold genBody
    have := outFree_genInstr i
    have := outFree_genBody f ann (k + 1) r
    outfree

theorem outFree_genPre (f : IR.Fn) (isEntry : Bool) : OutFree (genPre f isEntry) := by
  unfold genPre; outfree

/-! ### Stretches by their own items -/

/-- From `s` with any items `o` in front, the body from the `k`-th
instruction ends in `u` with `D` after `o`. -/
def RunsTo (f : IR.Fn) (ann : Bool) (env : GEnv) (l : List IR.Instr) (k : Nat) (s u : GS) (D : Array Item) : Prop :=
  ∀ o, runG (genBody f ann k (l.drop k)) env { s with out := o } = .ok ((), { u with out := o ++ D })

/-- **A stretch, checked from the state before it with no items**, then the rest. -/
theorem body_step_out (f : IR.Fn) (ann : Bool) (env : GEnv) (l : List IR.Instr) (k n : Nat) (s t u : GS)
    (D : Array Item) (hk : k + n ≤ l.length)
    (h1 : runG (genBody f ann k ((l.drop k).take n)) env (noItems s) = .ok ((), t))
    (h2 : RunsTo f ann env l (k + n) t u D) : RunsTo f ann env l k s u (t.out ++ D) := by
  intro o
  rw [← List.take_append_drop n (l.drop k), genBody_append, runG_bind,
    outFree_genBody f ann k _ env { s with out := o }]
  have he : noItems { s with out := o } = noItems s := rfl
  rw [he, h1]
  have hl : ((l.drop k).take n).length = n := by simp; omega
  simp only [Except.map, hl, List.drop_drop]
  rw [h2 (o ++ t.out), Array.append_assoc]

theorem body_end_out (f : IR.Fn) (ann : Bool) (env : GEnv) (l : List IR.Instr) (k : Nat) (s : GS)
    (hk : l.length ≤ k) : RunsTo f ann env l k s s #[] := by
  intro o
  rw [List.drop_eq_nil_of_le hk, Array.append_empty]
  rfl

/-- **A pass of the generator, from its stretches checked by their own items.** -/
theorem genFn_of_out (f : IR.Fn) (spilled : Array Bool) (lits : Array (Nat × Nat)) (isEntry : Bool)
    (live : Option (Array Bool)) (ann : Bool) (s0 u : GS) (D : Array Item)
    (hpre : runG (genPre f isEntry) (fnEnv f spilled live) (fnStart f lits) = .ok ((), s0))
    (hbody : RunsTo f ann (fnEnv f spilled live) f.body.toList 0 s0 u D)
    (hj : jumpsOk u = true) :
    genFn f spilled lits isEntry live ann =
      .ok (s0.out ++ D, u.missed, u.lits, (tmpLayout f spilled).2, if u.addrTaken then none else some u.reads) := by
  have hb := hbody s0.out
  have hs : { s0 with out := s0.out } = s0 := rfl
  rw [hs] at hb
  exact genFn_of f spilled lits isEntry live ann s0 { u with out := s0.out ++ D } hpre hb hj

/-- Items `a` on, cut where `ms` says. -/
def slices {α : Type} (L : List α) : Nat → List Nat → Array α
  | _, [] => #[]
  | a, m :: ms => ⟨(L.drop a).take m⟩ ++ slices L (a + m) ms

theorem slices_toList {α : Type} (L : List α) : ∀ (a : Nat) (ms : List Nat),
    (slices L a ms).toList = (L.drop a).take ms.sum
  | _, [] => by simp [slices]
  | a, m :: ms => by
    simp only [slices, Array.toList_append, slices_toList L (a + m) ms, List.sum_cons, List.take_add,
      List.drop_drop]

/-- `pass2B` from what the pass gives, its items apart. -/
theorem pass2B_of' {p : IR.Prog} {lits : Array (Nat × Nat)} {g : FnPart}
    {r : Array Item × Array Bool × Array (Nat × Nat) × Nat × Option (Array Bool)}
    (hd : g.f.dead = false) (h : genFn g.f g.missed lits (g.f.name == p.entry) g.live false = .ok r)
    (hcode : r.1.toList = g.code)
    (hc : (decide (r.2.2.1 = g.lits) && decide (r.2.2.2.1 = g.size) &&
      ((List.range g.f.tmps.size).find? fun t => r.2.1[t]! && !g.missed[t]!).isNone) = true) :
    pass2B p lits g = true := by
  apply pass2B_of hd h
  simp only [hcode, decide_true, Bool.true_and]
  exact hc

end Ember.Proof.Z80Gen
