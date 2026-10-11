import Ember.Proof.IRPlace

/-!
# Ember.Proof.IRWp — reasoning about the lowering (plan M7.1)

* `wp m E Q s`: if the lowering action `m`, in the environment `E` and
  from the state `s`, succeeds, its result and final state satisfy `Q`;
* `Ext s s'`: a later state — more instructions, more temporaries;
* `Final c fn f sF`: `f` is the function whose lowering ended in `sF`:
  what was emitted is in its body, where every label is defined once;
* `Runs`: code that computes — it changes temporaries only, and none
  below a mark.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global

/-! ## The lowering's monad -/

def wp {α : Type} (m : LM α) (E : Env) (Q : α → LS → Prop) (s : LS) : Prop :=
  match m E s with
  | .ok (a, s') => Q a s'
  | .error _ => True

section
variable {α β : Type} {E : Env} {s : LS}

theorem wp_pure (a : α) (Q : α → LS → Prop) : wp (pure a : LM α) E Q s ↔ Q a s := Iff.rfl

theorem wp_bind (m : LM α) (g : α → LM β) (Q : β → LS → Prop) :
    wp (m >>= g) E Q s ↔ wp m E (fun a s' => wp (g a) E Q s') s := by
  unfold wp
  show (match (m E s >>= fun r => g r.1 E r.2) with
    | .ok (a, s') => Q a s'
    | .error _ => True) ↔ _
  cases h : m E s with
  | error e => simp [bind, Except.bind]
  | ok r => obtain ⟨a, s'⟩ := r; simp [bind, Except.bind]

theorem wp_mono {m : LM α} {Q Q' : α → LS → Prop} (h : wp m E Q s) (hq : ∀ a s', Q a s' → Q' a s') :
    wp m E Q' s := by
  unfold wp at h ⊢
  cases hm : m E s with
  | error e => trivial
  | ok r =>
    obtain ⟨a, s'⟩ := r
    rw [hm] at h
    exact hq a s' h

theorem wp_read (Q : Env → LS → Prop) : wp (read : LM Env) E Q s ↔ Q E s := Iff.rfl

theorem wp_err (msg : String) (Q : α → LS → Prop) : wp (err msg : LM α) E Q s ↔ True := Iff.rfl

theorem wp_emit (i : Instr) (Q : Unit → LS → Prop) : wp (emit i) E Q s ↔ Q () { s with out := s.out.push i } :=
  Iff.rfl

theorem wp_newTmp (n : Nat) (Q : Nat → LS → Prop) :
    wp (newTmp n) E Q s ↔ Q s.tmps.size { s with tmps := s.tmps.push n } := Iff.rfl

theorem wp_newLabel (Q : Nat → LS → Prop) : wp newLabel E Q s ↔ Q s.labels { s with labels := s.labels + 1 } :=
  Iff.rfl

theorem wp_allocLocal (n : Nat) (Q : Slot → LS → Prop) :
    wp (allocLocal n) E Q s ↔
      Q { area := .frame E.fn, off := s.cur } { s with cur := s.cur + n, max := Nat.max s.max (s.cur + n) } :=
  Iff.rfl

theorem wp_size (t : Ty) (Q : Nat → LS → Prop) : wp (size t) E Q s ↔ Q (sizeOf E.prog t) s := Iff.rfl

theorem wp_constVar (x : String) (Q : Option Nat → LS → Prop) : wp (constVar? x) E Q s ↔ Q (E.constVar? x) s :=
  Iff.rfl

theorem wp_withReader (g : Env → Env) (m : LM α) (Q : α → LS → Prop) :
    wp (withReader g m) E Q s ↔ wp m (g E) Q s := Iff.rfl

theorem wp_pureE (m : Env → Except String α) (Q : α → LS → Prop) :
    wp (pureE m) E Q s ↔ (∀ a, m E = .ok a → Q a s) := by
  unfold wp pureE
  cases h : m E with
  | error e => simp
  | ok a => simp

theorem wp_tyOf (e : Expr) (Q : Ty → LS → Prop) : wp (tyOf e) E Q s ↔ (∀ t, E.tyOf e = .ok t → Q t s) :=
  wp_pureE _ _

theorem wp_varInfo (x : String) (Q : VarInfo → LS → Prop) :
    wp (varInfo x) E Q s ↔ (∀ i, E.varInfo x = .ok i → Q i s) := wp_pureE _ _

theorem wp_inScope (m : LM α) (Q : α → LS → Prop) :
    wp (inScope m) E Q s ↔ wp m E (fun a s' => Q a { s' with cur := s.cur }) s := by
  unfold wp inScope
  cases h : m E s with
  | error e => simp
  | ok r => obtain ⟨a, s'⟩ := r; simp

theorem wp_trapLabel (Q : Nat → LS → Prop) :
    wp trapLabel E Q s ↔
      match s.trapLabel with
      | some l => Q l s
      | none => Q s.labels { s with labels := s.labels + 1, trapLabel := some s.labels } := by
  unfold wp trapLabel
  cases s.trapLabel <;> rfl

end

/-! ## Later states -/

/-- `s'` comes after `s`. -/
structure Ext (s s' : LS) : Prop where
  out : ∀ i, i < s.out.size → s'.out[i]? = s.out[i]?
  osz : s.out.size ≤ s'.out.size
  tmps : s.tmps.size ≤ s'.tmps.size
  trap : ∀ t, s.trapLabel = some t → s'.trapLabel = some t
  max : s.max ≤ s'.max
  inv : s.cur ≤ s.max → s'.cur ≤ s'.max

theorem Ext.refl (s : LS) : Ext s s := ⟨fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, id⟩

theorem Ext.trans {a b c : LS} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨fun i hi => by rw [h2.out i (by have := h1.osz; omega), h1.out i hi], Nat.le_trans h1.osz h2.osz,
    Nat.le_trans h1.tmps h2.tmps, fun t h => h2.trap t (h1.trap t h), Nat.le_trans h1.max h2.max,
    fun h => h2.inv (h1.inv h)⟩

theorem Ext.emit (s : LS) (i : Instr) : Ext s { s with out := s.out.push i } :=
  ⟨fun j hj => by simp only [Array.getElem?_push]; rw [if_neg (by omega)], by simp, Nat.le_refl _, fun _ h => h, Nat.le_refl _, id⟩

theorem Ext.newTmp (s : LS) (n : Nat) : Ext s { s with tmps := s.tmps.push n } :=
  ⟨fun _ _ => rfl, Nat.le_refl _, by simp, fun _ h => h, Nat.le_refl _, id⟩

theorem Ext.newLabel (s : LS) : Ext s { s with labels := s.labels + 1 } :=
  ⟨fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, id⟩

theorem Ext.alloc (s : LS) (n : Nat) : Ext s { s with cur := s.cur + n, max := Nat.max s.max (s.cur + n) } :=
  ⟨fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_max_left _ _, fun _ => Nat.le_max_right _ _⟩

/-- A scope closes: the frame in use is what it was. -/
theorem Ext.scope {s s' : LS} (h : Ext s s') : Ext s { s' with cur := s.cur } :=
  ⟨h.out, h.osz, h.tmps, h.trap, h.max, fun hc => Nat.le_trans hc h.max⟩

/-- The trap label, whichever case `trapLabel` is in. -/
theorem wp_trapLabel' {E : Env} {s : LS} {Q : Nat → LS → Prop}
    (h : ∀ tl s', Ext s s' → s'.cur = s.cur → s'.out = s.out → s'.tmps = s.tmps → s'.trapLabel = some tl →
      Q tl s') : wp trapLabel E Q s := by
  rw [wp_trapLabel]
  cases ht : s.trapLabel with
  | some l => exact h l s (Ext.refl s) rfl rfl rfl ht
  | none =>
    exact h _ _ ⟨fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, fun t h' => (by rw [ht] at h'; cases h'),
      Nat.le_refl _, id⟩ rfl rfl rfl rfl

/-! ## The function at the end -/

/-- `f` is what the lowering that ended in `sF` made, for the function `fn`. -/
structure Final (c : Ctx) (fn : String) (f : IR.Fn) (sF : LS) : Prop where
  fn : c.prog.fn? fn = some f
  code : ∀ (i : Nat), i < sF.out.size → f.body[i]? = sF.out[i]?
  tmps : sF.tmps.size ≤ f.tmps.size
  uniq : ∀ (i j l : Nat), f.body[i]? = some (Instr.label l) → f.body[j]? = some (Instr.label l) → i = j
  trap : ∀ t, sF.trapLabel = some t → ∃ i : Nat, f.body[i]? = some (Instr.label t) ∧ f.body[i + 1]? = some Instr.trap
  frame : sF.max ≤ f.frame

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

theorem Final.at_ (F : Final c fn f sF) {s : LS} (hx : Ext s sF) {i : Nat} {ins : Instr} (h : s.out[i]? = some ins) :
    f.body[i]? = some ins := by
  have hi : i < s.out.size := by
    rcases Nat.lt_or_ge i s.out.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  rw [F.code i (by have := hx.osz; omega), hx.out i hi]
  exact h

/-- The instruction just emitted. -/
theorem Final.emitted (F : Final c fn f sF) {s : LS} {out : Array Instr} {ins : Instr} (hx : Ext s sF)
    (ho : s.out = out.push ins) : f.body[out.size]? = some ins :=
  F.at_ hx (by rw [ho]; simp)

theorem isLabel_iff (l : Nat) (ins : Instr) : isLabel l ins = true ↔ ins = .label l := by
  cases ins <;> simp [isLabel]

/-- Where a label is. -/
theorem Final.label (F : Final c fn f sF) {i l : Nat} (h : f.body[i]? = some (Instr.label l)) : labelAt f l = some i := by
  unfold labelAt
  rw [Array.findIdx?_eq_some_iff_getElem]
  have hi : i < f.body.size := by
    rcases Nat.lt_or_ge i f.body.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  rw [Array.getElem?_eq_getElem hi] at h
  simp only [Option.some.injEq] at h
  refine ⟨hi, by rw [h]; simp [isLabel], fun j hj hp => ?_⟩
  have hj' : j < f.body.size := by omega
  have hjl : f.body[j]? = some (Instr.label l) := by
    rw [Array.getElem?_eq_getElem hj']
    exact congrArg some ((isLabel_iff l _).mp (by simpa using hp))
  have := F.uniq j i l hjl (by rw [Array.getElem?_eq_getElem hi, h])
  omega

end

/-! ## Operands and temporaries -/

/-- The same temporaries below `k`. -/
def Agree (k : Nat) (a b : Array Nat) : Prop := ∀ t, t < k → b[t]? = a[t]?

theorem Agree.refl (k : Nat) (a : Array Nat) : Agree k a a := fun _ _ => rfl

theorem Agree.trans {k k' : Nat} {a b d : Array Nat} (h1 : Agree k a b) (h2 : Agree k' b d) (hk : k ≤ k') :
    Agree k a d := fun t ht => by rw [h2 t (by omega), h1 t ht]

theorem Agree.mono {k k' : Nat} {a b : Array Nat} (h : Agree k' a b) (hk : k ≤ k') : Agree k a b :=
  fun t ht => h t (by omega)

theorem Agree.set {k d : Nat} (a : Array Nat) (x : Nat) (hd : k ≤ d) : Agree k a (a.setIfInBounds d x) :=
  fun t ht => Array.getElem?_setIfInBounds_ne (by omega)

theorem opd_const (c : Ctx) (st : St) (tmps : Array Nat) (n v : Nat) : opd c st tmps n (.const v) = modN n v := rfl

theorem opd_tmp (c : Ctx) (st : St) (tmps : Array Nat) (n t : Nat) :
    opd c st tmps n (.tmp t) = modN n (tmps.getD t 0) := rfl

theorem opd_slot (c : Ctx) (st : St) (tmps : Array Nat) (n : Nat) (sl : Slot) :
    opd c st tmps n (.slot sl) = rd st.mem (c.layout.addr sl) n := rfl

/-- An operand whose temporary is below `k` has the same value. -/
theorem opd_agree (c : Ctx) (st : St) {tmps tmps' : Array Nat} (n : Nat) {o : Opd} {k : Nat}
    (ho : ∀ t, o = .tmp t → t < k) (h : Agree k tmps tmps') : opd c st tmps' n o = opd c st tmps n o := by
  cases o with
  | const v => rfl
  | slot sl => rfl
  | tmp t =>
    simp only [opd_tmp, Array.getD_eq_getD_getElem?, h t (ho t rfl)]

/-- A temporary just written. -/
theorem opd_set (c : Ctx) (st : St) (tmps : Array Nat) (n d x : Nat) (hd : d < tmps.size) :
    opd c st (tmps.setIfInBounds d x) n (.tmp d) = modN n x := by
  simp only [opd_tmp, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hd, Option.getD_some]

theorem modN_modN (n v : Nat) : modN n (modN n v) = modN n v := by
  simp [modN]

theorem modN_of_lt {n v : Nat} (h : v < 2 ^ (8 * n)) : modN n v = v := Nat.mod_eq_of_lt h

theorem setDst_tmp (c : Ctx) (st : St) (tmps : Array Nat) (n d v : Nat) :
    setDst c st tmps n (.tmp d) v = (st, tmps.setIfInBounds d (modN n v)) := rfl

theorem setDst_slot (c : Ctx) (st : St) (tmps : Array Nat) (n : Nat) (sl : Slot) (v : Nat) :
    setDst c st tmps n (.slot sl) v = ({ st with mem := wr st.mem (c.layout.addr sl) n v }, tmps) := rfl

theorem addr_off (c : Ctx) (sl : Slot) (k : Nat) :
    c.layout.addr { sl with off := sl.off + k } = c.layout.addr sl + k := by
  simp [Layout.addr, Nat.add_assoc]

/-! ## Code that computes -/

/-- From `a` to `b`: memory and the world as they were, the temporaries
below `k` too; `P` of the temporaries at the end. -/
def Runs (c : Ctx) (f : IR.Fn) (ist : St) (a b k : Nat) (tmps : Array Nat) (P : Array Nat → Prop) : Prop :=
  ∃ tmps', Reach c f a tmps ist b tmps' ist ∧ tmps'.size = tmps.size ∧ Agree k tmps tmps' ∧ P tmps'

section
variable {c : Ctx} {f : IR.Fn} {ist : St} {a b d k k' : Nat} {tmps : Array Nat} {P Q : Array Nat → Prop}

theorem Runs.done (h : P tmps) : Runs c f ist a a k tmps P := ⟨tmps, Reach.refl, rfl, Agree.refl _ _, h⟩

theorem Runs.seq (h1 : Runs c f ist a b k tmps P) (hk : k ≤ k')
    (h2 : ∀ tmps', tmps'.size = tmps.size → Agree k tmps tmps' → P tmps' → Runs c f ist b d k' tmps' Q) :
    Runs c f ist a d k tmps Q := by
  obtain ⟨t1, r1, s1, a1, p1⟩ := h1
  obtain ⟨t2, r2, s2, a2, p2⟩ := h2 t1 s1 a1 p1
  exact ⟨t2, r1.trans r2, by rw [s2, s1], a1.trans a2 hk, p2⟩

theorem Runs.mono (h : Runs c f ist a b k tmps P)
    (hpq : ∀ t, t.size = tmps.size → Agree k tmps t → P t → Q t) : Runs c f ist a b k tmps Q := by
  obtain ⟨t1, r1, s1, a1, p1⟩ := h
  exact ⟨t1, r1, s1, a1, hpq t1 s1 a1 p1⟩

theorem Runs.weaken (h : Runs c f ist a b k' tmps P) (hk : k ≤ k') : Runs c f ist a b k tmps P := by
  obtain ⟨t1, r1, s1, a1, p1⟩ := h
  exact ⟨t1, r1, s1, a1.mono hk, p1⟩

/-- Code that computes, then the end. -/
theorem Runs.ends {r : Res} (h1 : Runs c f ist a b k tmps P)
    (h2 : ∀ tmps', tmps'.size = tmps.size → Agree k tmps tmps' → P tmps' → Ends c f b tmps' ist r) :
    Ends c f a tmps ist r := by
  obtain ⟨t1, r1, s1, a1, p1⟩ := h1
  exact r1.ends (h2 t1 s1 a1 p1)

/-- One instruction that writes a temporary. -/
theorem Runs.tmp {ins : Instr} {t x : Nat} (hb : f.body[a]? = some ins)
    (hs : step c ist tmps ins = .next ist (tmps.setIfInBounds t x)) (ht : k ≤ t)
    (hP : P (tmps.setIfInBounds t x)) : Runs c f ist a (a + 1) k tmps P :=
  ⟨_, Reach.next hb hs, by simp, Agree.set _ _ ht, hP⟩

/-- One instruction that changes nothing (a label, a branch not taken). -/
theorem Runs.skip {ins : Instr} (hb : f.body[a]? = some ins) (hs : step c ist tmps ins = .next ist tmps)
    (hP : P tmps) : Runs c f ist a (a + 1) k tmps P :=
  ⟨_, Reach.next hb hs, rfl, Agree.refl _ _, hP⟩

end

end Ember.Proof.IRSim
