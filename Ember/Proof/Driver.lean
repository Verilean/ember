import Ember.Proof.Main

/-!
# Ember.Proof.Driver — `main` called again and again (plan M5.6)
-/

set_option linter.unusedSimpArgs false

namespace Ember.Spec
open Ember Ember.Trace

/-! ## The configuration never changes -/

theorem slipByte_cfg (c : Config) (x : UInt8) : Pres (fun s => s.cfg = c) (slipByte x) := by
  have h1 := frameInput_due (Q := fun _ _ y => y = c)
  unfold slipByte
  pres
  all_goals first | exact h1 _ | with_reducible exact Pres.modifyS (fun _ h => h)

theorem byteInput_cfg (c : Config) (x : UInt8) : Pres (fun s => s.cfg = c) (byteInput x) := by
  have h1 := slipByte_cfg c
  have h2 := tickInput_due (Q := fun _ _ y => y = c)
  unfold byteInput
  pres
  all_goals first | exact h1 _ | exact h2 | with_reducible exact Pres.modifyS (fun _ h => h)

theorem tickArrives_cfg (c : Config) : Pres (fun s => s.cfg = c) tickArrives := by
  have h2 := tickInput_due (Q := fun _ _ y => y = c)
  unfold tickArrives
  pres
  all_goals first | exact h2 | with_reducible exact Pres.modifyS (fun _ h => h)

theorem input_cfg (c : Config) (i : Input) : Pres (fun s => s.cfg = c) (input i) := by
  have h1 := frameInput_due (Q := fun _ _ y => y = c)
  have h2 := byteInput_cfg c
  have h3 := tickArrives_cfg c
  cases i <;> unfold input
  · pres
    all_goals first | exact h1 _ | exact h2 _
  · exact h3

theorem step_cfg (s : State) (i : Input) : (step s i).1.cfg = s.cfg := input_cfg s.cfg i (s, #[]) rfl

end Ember.Spec

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## The Spec: an input is its items -/

/-- The items `main` reads for one input: a tick, or the bytes of a chunk. -/
def itemsOf : Trace.Input → List UInt16
  | .tick => [0x0100]
  | .rx b => b.toList.map (·.toUInt16)

/-- The Spec over a list of items. -/
def runItems (ks : List UInt16) (x : Spec.State × Array Trace.Event) : Spec.State × Array Trace.Event :=
  ks.foldl (fun x k => ((itemM k).run x).2) x

theorem forIn_bytes (l : List UInt8) (x : Spec.State × Array Trace.Event) :
    ((forIn l PUnit.unit fun c (_ : PUnit) =>
        (do Spec.byteInput c; pure (ForInStep.yield PUnit.unit) : Spec.StackM (ForInStep PUnit))).run x).2
      = l.foldl (fun x c => ((Spec.byteInput c).run x).2) x := by
  induction l generalizing x with
  | nil => rfl
  | cons c t ih =>
    rw [List.forIn_cons]
    have h1 : (Spec.byteInput c >>= fun _ => pure (ForInStep.yield PUnit.unit) :
        Spec.StackM (ForInStep PUnit)).run x = (ForInStep.yield PUnit.unit, ((Spec.byteInput c).run x).2) := rfl
    rw [run_bind_eq _ _ _ _ _ h1]
    exact ih _

theorem itemM_byte (c : UInt8) : itemM c.toUInt16 = Spec.byteInput c := by
  have hc := c.toNat_lt
  have h1 : c.toUInt16 ≠ 0xFFFF := by
    intro e
    have := congrArg UInt16.toNat e
    simp at this
    omega
  have h2 : c.toUInt16 ≠ 0x0100 := by
    intro e
    have := congrArg UInt16.toNat e
    simp at this
    omega
  unfold itemM
  rw [if_neg h1, if_neg h2]
  simp

/-- **`Spec.input`, item by item** (SLIP): a tick is `tickArrives`, a
chunk is `byteInput` for each of its bytes. -/
theorem input_items (i : Trace.Input) (s : Spec.State) (es : Array Trace.Event) (hslip : s.cfg.link = .slip) :
    ((Spec.input i).run (s, es)).2 = runItems (itemsOf i) (s, es) := by
  cases i with
  | tick => rfl
  | rx b =>
    unfold Spec.input
    have hg : (Spec.getS).run (s, es) = (s, (s, es)) := rfl
    rw [run_bind_eq _ _ _ _ _ hg]
    simp only [hslip]
    have hfull : ∀ m : Spec.StackM PUnit, m.run (s, es) = (PUnit.unit, (m.run (s, es)).2) := fun _ => rfl
    rw [run_bind_eq _ _ _ _ _ (hfull _), forIn_bytes]
    show _ = (b.toList.map (·.toUInt16)).foldl _ _
    rw [List.foldl_map]
    show List.foldl _ _ _ = _
    congr 1
    funext x c
    rw [itemM_byte]

/-! ## The input oracle: the items left to read -/

/-- The items of input number `i`, with that number. -/
def itemsAt (i : Nat) (x : Trace.Input) : List (Nat × UInt16) := (itemsOf x).map fun k => (i, k)

def laterL : List Trace.Input → Nat → List (Nat × UInt16)
  | [], _ => []
  | x :: t, j => itemsAt j x ++ laterL t (j + 1)

/-- The items of the inputs from number `j` on. -/
def later (inputs : Array Trace.Input) (j : Nat) : List (Nat × UInt16) := laterL (inputs.toList.drop j) j

theorem later_lt (inputs : Array Trace.Input) (j : Nat) (h : j < inputs.size) :
    later inputs j = itemsAt j inputs[j] ++ later inputs (j + 1) := by
  unfold later
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [laterL]

theorem later_ge (inputs : Array Trace.Input) (j : Nat) (h : inputs.size ≤ j) : later inputs j = [] := by
  unfold later
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

/-- The items the oracle has not handed out yet, each with the number of its input. -/
def witems (w : World) : List (Nat × UInt16) :=
  if h : w.pos < w.inputs.size then
    (match w.inputs[w.pos] with
      | .tick => [(w.pos, 0x0100)]
      | .rx b => (b.toList.drop w.off).map fun c => (w.pos, c.toUInt16)) ++ later w.inputs (w.pos + 1)
  else []

/-- Nothing to skip: the oracle is at an item, or at the end. -/
def WNormal (w : World) : Prop :=
  ∀ h : w.pos < w.inputs.size, match w.inputs[w.pos] with
    | .tick => True
    | .rx b => w.off < b.size

theorem toList_length (b : ByteArray) : b.toList.length = b.size := by
  rw [Spec.Slip.toList_eq]
  exact Array.length_toList

theorem witems_start (inputs : Array Trace.Input) (j : Nat) (w : World) (hi : w.inputs = inputs) (hp : w.pos = j)
    (ho : w.off = 0) : witems w = later inputs j := by
  subst hi hp
  unfold witems
  split
  · rename_i h
    rw [later_lt _ _ h]
    congr 1
    split <;> simp [itemsAt, itemsOf, ho, *]
  · rename_i h
    rw [later_ge _ _ (by omega)]

theorem normalize_spec (w : World) (hf : w.framed = false) :
    witems w.normalize = witems w ∧ WNormal w.normalize ∧ w.normalize.inputs = w.inputs ∧
      w.normalize.events = w.events ∧ w.normalize.cur = w.cur ∧ w.normalize.framed = false := by
  fun_induction World.normalize w
  case case1 w h => rw [hf] at h; exact absurd h (by simp)
  case case2 w _ hlt b hx hoff ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih hf
    refine ⟨i1.trans (Eq.trans (witems_start w.inputs (w.pos + 1) _ rfl rfl rfl) ?_), i2, i3, i4, i5, i6⟩
    unfold witems
    rw [dif_pos hlt]
    simp only [hx]
    rw [List.drop_eq_nil_of_le (by rw [toList_length]; exact hoff)]
    rfl
  case case3 w _ hlt b hx hoff =>
    refine ⟨rfl, ?_, rfl, rfl, rfl, hf⟩
    intro h
    simp only [hx]
    omega
  case case4 w _ hlt hx =>
    refine ⟨rfl, ?_, rfl, rfl, rfl, hf⟩
    intro h
    simp only [hx]
  case case5 w _ hlt => exact ⟨rfl, fun h => absurd h hlt, rfl, rfl, rfl, hf⟩

theorem toList_drop (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.toList.drop i = b.get! i :: b.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [toList_length]; exact h)]
  congr 1
  simp [Spec.Slip.toList_eq, ByteArray.get!, h]
  rfl

/-- **`input.next`**: it hands out the first item left (`0xFFFF` when
there is none) and leaves the rest; the events are untouched. -/
theorem next_spec (w : World) (hf : w.framed = false) :
    w.next.2.events = w.events ∧ w.next.2.framed = false ∧
    ((witems w = [] ∧ w.next.1 = 0xFFFF ∧ witems w.next.2 = []) ∨
     (∃ i k, witems w = (i, k) :: witems w.next.2 ∧ w.next.1 = k ∧ w.next.2.cur = i)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := normalize_spec w hf
  rw [← n1, ← n4]
  unfold World.next
  dsimp only
  generalize w.normalize = n at n2 n6 ⊢
  split
  · rename_i h
    have hN := n2 h
    split
    · rename_i hx
      obtain ⟨m1, m2, m3, m4, m5, m6⟩ := normalize_spec
        { n with cur := n.pos, pos := n.pos + 1, off := 0 } n6
      refine ⟨m4, m6, Or.inr ⟨n.pos, 0x0100, ?_, rfl, m5⟩⟩
      dsimp only
      rw [m1, witems_start n.inputs (n.pos + 1) { n with cur := n.pos, pos := n.pos + 1, off := 0 } rfl rfl rfl]
      unfold witems
      rw [dif_pos h]
      simp only [hx]
      rfl
    · rename_i b hx
      simp only [hx] at hN
      obtain ⟨m1, m2, m3, m4, m5, m6⟩ := normalize_spec
        { n with cur := n.pos, off := n.off + 1 } n6
      refine ⟨m4, m6, Or.inr ⟨n.pos, (b.get! n.off).toUInt16, ?_, rfl, m5⟩⟩
      dsimp only
      rw [m1]
      unfold witems
      dsimp only
      rw [dif_pos h, dif_pos h]
      simp only [hx]
      rw [toList_drop b n.off hN]
      rfl
  · rename_i h
    refine ⟨rfl, n6, Or.inl ⟨?_, rfl, ?_⟩⟩ <;> (unfold witems; rw [dif_neg h])

/-! ## `main`, again and again -/

/-- `j` calls of `main`; `none` when one traps or runs out of fuel. -/
def mainIter (fuel : Nat) (p : Prog) : Nat → St → Option St
  | 0, st => some st
  | j + 1, st =>
    match Sem.call fuel p st "main" [] with
    | .ok _ st' => mainIter fuel p j st'
    | _ => none

/-- The lines of a trace that the comparison keeps (transmissions and
drops), each with the number of its input. -/
def kept (w : World) : List (Nat × Trace.Event) := w.events.toList.filter fun e => keep e.2

theorem foldl_emit (X : List Trace.Event) (w : World) :
    X.foldl World.emit w = { w with events := w.events ++ (X.map fun e => (w.cur, e)).toArray } := by
  induction X generalizing w with
  | nil => simp
  | cons e t ih =>
    rw [List.foldl_cons, ih]
    simp [World.emit]

theorem kept_emit (X : List Trace.Event) (w : World) :
    kept (X.foldl World.emit w) = kept w ++ (X.filter keep).map fun e => (w.cur, e) := by
  rw [foldl_emit]
  simp [kept, List.filter_map]
  rfl

/-- The Spec's side while items are consumed: its state, the events of
the input being read (number `tag`), the kept lines of the inputs before. -/
structure Acc where
  s : Spec.State
  es : Array Trace.Event
  tag : Nat
  T : List (Nat × Trace.Event)

/-- The kept lines so far. -/
def Acc.view (a : Acc) : List (Nat × Trace.Event) := a.T ++ (a.es.toList.filter keep).map fun e => (a.tag, e)

/-- One item: an item of a new input starts a new list of events. -/
def accStep (a : Acc) (ik : Nat × UInt16) : Acc :=
  if ik.1 = a.tag then
    { a with s := ((itemM ik.2).run (a.s, a.es)).2.1, es := ((itemM ik.2).run (a.s, a.es)).2.2 }
  else
    { s := ((itemM ik.2).run (a.s, #[])).2.1, es := ((itemM ik.2).run (a.s, #[])).2.2, tag := ik.1, T := a.view }

def runTagged (l : List (Nat × UInt16)) (a : Acc) : Acc := l.foldl accStep a

theorem witems_emit (X : List Trace.Event) (w : World) : witems (X.foldl World.emit w) = witems w := by
  rw [foldl_emit]
  rfl

theorem kept_congr {w w' : World} (h : w'.events = w.events) : kept w' = kept w := by
  unfold kept
  rw [h]

/-- **`j` calls of `main`.**  From `MainInv`, none of them traps; the
state after them satisfies `MainInv` against the Spec after the first
`j` items left in the input; the kept lines of the two traces are the
same, input by input; and those items have been consumed. -/
theorem main_iter (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (mtu : UInt16) (ourIp : UInt32) (N n : Nat) :
    ∀ (j : Nat) (st : St) (a : Acc) (w : TW), MainInv st a.s w mtu ourIp N → st.world.framed = false →
      kept st.world = a.view →
      ∃ (st' : St) (w' : TW), mainIter (n + mtu.toNat + 4420) p j st = some st' ∧
        MainInv st' (runTagged ((witems st.world).take j) a).s w' mtu ourIp N ∧ st'.world.framed = false ∧
        kept st'.world = (runTagged ((witems st.world).take j) a).view ∧
        witems st'.world = (witems st.world).drop j := by
  intro j
  induction j with
  | zero =>
    intro st a w hinv hf hk
    exact ⟨st, w, rfl, hinv, hf, hk, rfl⟩
  | succ j ih =>
    intro st a w hinv hf hk
    obtain ⟨hev, hfr, hcase⟩ := next_spec st.world hf
    rcases hcase with ⟨h0, hk0, h0'⟩ | ⟨i, k, hi, hk1, hc⟩
    · -- nothing left
      obtain ⟨st1, w1, X, hcall, hinv1, hw1, htr⟩ := main_step p hP hR hp st a.s w mtu ourIp N hinv a.es n
      rw [hk0, show itemM 0xFFFF = pure () from if_pos rfl] at hinv1 htr
      have hX : X.filter keep = [] := by
        have : a.es.toList.filter keep = a.es.toList.filter keep ++ X.filter keep := htr
        simpa using this
      have hf1 : st1.world.framed = false := by rw [hw1, foldl_emit]; exact hfr
      have hk1 : kept st1.world = a.view := by
        rw [hw1, kept_emit, hX, List.map_nil, List.append_nil, kept_congr hev]; exact hk
      have hwi : witems st1.world = [] := by rw [hw1, witems_emit]; exact h0'
      obtain ⟨st', w', hit, hinv', hf', hk', hwi'⟩ := ih st1 a w1 hinv1 hf1 hk1
      rw [hwi] at hinv' hk' hwi'
      rw [List.take_nil] at hinv' hk'
      rw [List.drop_nil] at hwi'
      refine ⟨st', w', ?_, ?_, hf', ?_, ?_⟩
      · rw [mainIter, hcall]; exact hit
      · rw [h0, List.take_nil]; exact hinv'
      · rw [h0, List.take_nil]; exact hk'
      · rw [h0, List.drop_nil]; exact hwi'
    · -- an item
      obtain ⟨st1, w1, X, hcall, hinv1, hw1, htr⟩ := main_step p hP hR hp st a.s w mtu ourIp N hinv
        (if i = a.tag then a.es else #[]) n
      rw [hk1] at hinv1 htr
      have hs1 : (accStep a (i, k)).s = ((itemM k).run (a.s, if i = a.tag then a.es else #[])).2.1 := by
        unfold accStep
        split <;> rfl
      have hf1 : st1.world.framed = false := by rw [hw1, foldl_emit]; exact hfr
      have hkv : kept st1.world = (accStep a (i, k)).view := by
        rw [hw1, kept_emit, kept_congr hev, hk, hc]
        unfold accStep
        by_cases hit : i = a.tag
        · rw [if_pos hit] at htr
          simp only [hit, if_true, Acc.view]
          rw [htr, List.map_append, List.append_assoc]
        · rw [if_neg hit] at htr
          simp only [hit, if_false, Acc.view]
          rw [htr]
          simp
      have hwi : witems st1.world = witems st.world.next.2 := by rw [hw1, witems_emit]
      obtain ⟨st', w', hit, hinv', hf', hk', hwi'⟩ := ih st1 (accStep a (i, k)) w1 (by rw [hs1]; exact hinv1) hf1 hkv
      rw [hwi] at hinv' hk' hwi'
      refine ⟨st', w', ?_, ?_, hf', ?_, ?_⟩
      · rw [mainIter, hcall]; exact hit
      · rw [hi]; exact hinv'
      · rw [hi]; exact hk'
      · rw [hi]; exact hwi'

/-- info: 'Ember.Proof.Refine.main_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_iter

/-! ## The Spec, input by input -/

/-- The kept lines of the Spec's trace for the inputs `l` (numbered from
`j`), from the state `s`: what `Spec.step` yields for each. -/
def specKept : List Trace.Input → Nat → Spec.State → List (Nat × Trace.Event)
  | [], _, _ => []
  | x :: t, j, s => ((Spec.step s x).2.filter keep).map (fun e => (j, e)) ++ specKept t (j + 1) (Spec.step s x).1

/-- No event of input `j` has been seen yet. -/
def Fresh (a : Acc) (j : Nat) : Prop := a.tag < j ∨ (a.tag = j ∧ a.es = #[])

theorem runTagged_same (ks : List UInt16) (j : Nat) (a : Acc) (h : a.tag = j) :
    runTagged (ks.map fun k => (j, k)) a
      = { a with s := (runItems ks (a.s, a.es)).1, es := (runItems ks (a.s, a.es)).2 } := by
  induction ks generalizing a with
  | nil => rfl
  | cons k t ih =>
    have e : accStep a (j, k)
        = { a with s := ((itemM k).run (a.s, a.es)).2.1, es := ((itemM k).run (a.s, a.es)).2.2 } := by
      unfold accStep
      rw [if_pos h.symm]
    show runTagged (t.map fun k => (j, k)) (accStep a (j, k)) = _
    rw [e]
    refine Eq.trans (ih { a with s := ((itemM k).run (a.s, a.es)).2.1, es := ((itemM k).run (a.s, a.es)).2.2 } h) ?_
    rfl

/-- The items of one input. -/
theorem runTagged_input (ks : List UInt16) (j : Nat) (a : Acc) (h : Fresh a j) :
    (runTagged (ks.map fun k => (j, k)) a).s = (runItems ks (a.s, #[])).1 ∧
    (runTagged (ks.map fun k => (j, k)) a).view
      = a.view ++ ((runItems ks (a.s, #[])).2.toList.filter keep).map (fun e => (j, e)) ∧
    Fresh (runTagged (ks.map fun k => (j, k)) a) (j + 1) := by
  rcases h with h | ⟨h1, h2⟩
  · cases ks with
    | nil => exact ⟨rfl, by simp [runTagged, runItems], Or.inl (Nat.lt_succ_of_lt h)⟩
    | cons k t =>
      have e : accStep a (j, k)
          = { s := ((itemM k).run (a.s, #[])).2.1, es := ((itemM k).run (a.s, #[])).2.2, tag := j, T := a.view } := by
        unfold accStep
        rw [if_neg (by show ¬ j = a.tag; omega)]
      have hr : runTagged ((k :: t).map fun k => (j, k)) a = runTagged (t.map fun k => (j, k)) (accStep a (j, k)) := rfl
      obtain ⟨a1, ha1⟩ : ∃ a1, a1 = accStep a (j, k) := ⟨_, rfl⟩
      have htag : a1.tag = j := by rw [ha1, e]
      rw [hr, ← ha1, runTagged_same t j a1 htag, ha1, e]
      exact ⟨rfl, rfl, Or.inl (Nat.lt_succ_self j)⟩
  · rw [runTagged_same _ _ _ h1, h2]
    refine ⟨rfl, ?_, Or.inl (by show a.tag < j + 1; omega)⟩
    simp [Acc.view, h1, h2]

theorem step_fst (s : Spec.State) (x : Trace.Input) : (Spec.step s x).1 = ((Spec.input x).run (s, #[])).2.1 := rfl

theorem step_snd (s : Spec.State) (x : Trace.Input) :
    (Spec.step s x).2 = ((Spec.input x).run (s, #[])).2.2.toList := rfl

/-- **The Spec over the items is the Spec over the inputs**: the state
is the one `Spec.step` reaches, the kept lines are those of its steps. -/
theorem runTagged_later (l : List Trace.Input) :
    ∀ (j : Nat) (a : Acc), a.s.cfg.link = .slip → Fresh a j →
      (runTagged (laterL l j) a).s = l.foldl (fun s i => (Spec.step s i).1) a.s ∧
      (runTagged (laterL l j) a).view = a.view ++ specKept l j a.s := by
  induction l with
  | nil => intro j a _ _; exact ⟨rfl, by simp [specKept, laterL, runTagged]⟩
  | cons x t ih =>
    intro j a hslip hfresh
    obtain ⟨h1, h2, h3⟩ := runTagged_input (itemsOf x) j a hfresh
    have hin := input_items x a.s #[] hslip
    rw [← hin] at h1 h2
    rw [← step_fst] at h1
    rw [← step_snd] at h2
    have hsl : (runTagged (itemsAt j x) a).s.cfg.link = .slip := by
      show (runTagged ((itemsOf x).map fun k => (j, k)) a).s.cfg.link = _
      rw [h1, Spec.step_cfg]; exact hslip
    obtain ⟨g1, g2⟩ := ih (j + 1) (runTagged (itemsAt j x) a) hsl h3
    have hr : runTagged (laterL (x :: t) j) a = runTagged (laterL t (j + 1)) (runTagged (itemsAt j x) a) := by
      show List.foldl accStep a (itemsAt j x ++ laterL t (j + 1)) = _
      rw [List.foldl_append]
      rfl
    rw [hr, g1, g2]
    have h1' : (runTagged (itemsAt j x) a).s = (Spec.step a.s x).1 := h1
    have h2' : (runTagged (itemsAt j x) a).view
        = a.view ++ ((Spec.step a.s x).2.filter keep).map (fun e => (j, e)) := h2
    rw [h1', h2']
    exact ⟨rfl, by simp [specKept, List.append_assoc]⟩

/-! ## From the initial state -/

/-- **The stack, run from its initial state**: `j + 1` calls of `main`
do not trap, and the state after them satisfies `MainInv` against the
Spec after the first `j + 1` items of the input, with the same kept
lines. -/
theorem main_run (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (inputs : Array Trace.Input) (n j : Nat) :
    ∃ (st' : St) (w' : TW), mainIter (n + 4716) p (j + 1) (Sem.initial Net.prog inputs) = some st' ∧
      MainInv st' (runTagged ((later inputs 0).take (j + 1)) ⟨Spec.State.init {}, #[], 0, []⟩).s w' 296
        Spec.ourIpDefault 296 ∧
      kept st'.world = (runTagged ((later inputs 0).take (j + 1)) ⟨Spec.State.init {}, #[], 0, []⟩).view ∧
      witems st'.world = (later inputs 0).drop (j + 1) := by
  obtain ⟨w0, hinv0⟩ := boot_inv inputs
  have hwi : witems (bootSt inputs).world = later inputs 0 := witems_start inputs 0 _ rfl rfl rfl
  obtain ⟨st', w', hit, hinv', _, hk', hwi'⟩ := main_iter p hP hR hp 296 Spec.ourIpDefault 296 n (j + 1)
    (bootSt inputs) ⟨Spec.State.init {}, #[], 0, []⟩ w0 hinv0 (by rfl) (by rfl)
  rw [hwi] at hinv' hk' hwi'
  refine ⟨st', w', ?_, hinv', hk', hwi'⟩
  have hb := boot_call p hP hp inputs (n + 4676)
  have hit' : mainIter (n + 4716) p (j + 1) (bootSt inputs) = some st' := hit
  rw [mainIter] at hit' ⊢
  rw [show n + 4716 = n + 4676 + 40 by omega, hb]
  exact hit'

/-- **All of the input.**  Once every item has been read, the stack's
state satisfies `MainInv` against the state the Spec reaches
(`Spec.reach`), and the kept lines of its trace — transmissions and
drops, each with the number of its input — are those of the Spec's
steps. -/
theorem main_run_all (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (inputs : Array Trace.Input) (n j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ (st' : St) (w' : TW), mainIter (n + 4716) p (j + 1) (Sem.initial Net.prog inputs) = some st' ∧
      MainInv st' (Spec.reach {} inputs.toList) w' 296 Spec.ourIpDefault 296 ∧
      kept st'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems st'.world = [] := by
  obtain ⟨st', w', hit, hinv', hk', hwi'⟩ := main_run p hP hR hp inputs n j
  rw [List.take_of_length_le hj] at hinv' hk'
  rw [List.drop_eq_nil_of_le hj] at hwi'
  obtain ⟨g1, g2⟩ := runTagged_later inputs.toList 0 ⟨Spec.State.init {}, #[], 0, []⟩ rfl (Or.inr ⟨rfl, rfl⟩)
  have hl : later inputs 0 = laterL inputs.toList 0 := rfl
  rw [hl, g1] at hinv'
  rw [hl, g2] at hk'
  exact ⟨st', w', hit, hinv', by rw [hk']; rfl, hwi'⟩

/-- info: 'Ember.Proof.Refine.main_run_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_run_all

end Ember.Proof.Refine
