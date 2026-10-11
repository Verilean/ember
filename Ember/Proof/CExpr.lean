import Ember.Proof.CArith
import Ember.Proof.CPlace

/-!
# Ember.Proof.CExpr — the emitter is right about expressions (plan M5.8)
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C

/-! ## The emitter's monad

`wpc m g Q cs`: if the emitter action `m`, in the environment `g` and
from the state `cs`, succeeds, its result and final state satisfy `Q`. -/

def wpc {α : Type} (m : CM α) (g : C.Env) (Q : α → CS → Prop) (cs : CS) : Prop :=
  match (m.run g).run cs with
  | .ok (a, cs') => Q a cs'
  | .error _ => True

section
variable {α β : Type} {g : C.Env} {cs : CS}

theorem wpc_pure (a : α) (Q : α → CS → Prop) : wpc (pure a : CM α) g Q cs ↔ Q a cs := Iff.rfl

theorem wpc_bind (m : CM α) (f : α → CM β) (Q : β → CS → Prop) :
    wpc (m >>= f) g Q cs ↔ wpc m g (fun a cs' => wpc (f a) g Q cs') cs := by
  unfold wpc
  show (match ((m.run g).run cs >>= fun r => ((f r.1).run g).run r.2) with
    | .ok (a, cs') => Q a cs'
    | .error _ => True) ↔ _
  cases h : (m.run g).run cs with
  | error e => simp [bind, Except.bind]
  | ok r => obtain ⟨a, cs'⟩ := r; simp [bind, Except.bind]

theorem wpc_read (Q : C.Env → CS → Prop) : wpc (read : CM C.Env) g Q cs ↔ Q g cs := Iff.rfl

theorem wpc_emit (s : CStmt) (Q : Unit → CS → Prop) :
    wpc (emit s) g Q cs ↔ Q () { cs with out := cs.out.push s } := Iff.rfl

theorem wpc_fresh (Q : String → CS → Prop) :
    wpc fresh g Q cs ↔ Q (tmpName cs.tmp) { cs with tmp := cs.tmp + 1 } := Iff.rfl

theorem wpc_err (msg : String) (Q : α → CS → Prop) : wpc (err msg : CM α) g Q cs ↔ True := Iff.rfl

theorem wpc_pureE (m : C.Env → Except String α) (Q : α → CS → Prop) :
    wpc (pureE m) g Q cs ↔ (∀ a, m g = .ok a → Q a cs) := by
  unfold wpc pureE
  show (match (match m g with | .ok a => Except.ok (a, cs) | .error msg => Except.error msg) with
    | .ok (a, cs') => Q a cs'
    | .error _ => True) ↔ _
  cases h : m g with
  | error e => simp
  | ok a => simp

theorem wpc_withReader (f : C.Env → C.Env) (m : CM α) (Q : α → CS → Prop) :
    wpc (withReader f m) g Q cs ↔ wpc m (f g) Q cs := Iff.rfl

theorem wpc_mono {m : CM α} {Q Q' : α → CS → Prop} (h : wpc m g Q cs) (hq : ∀ a cs', Q a cs' → Q' a cs') :
    wpc m g Q' cs := by
  unfold wpc at h ⊢
  cases hm : (m.run g).run cs with
  | error e => trivial
  | ok r => obtain ⟨a, cs'⟩ := r; rw [hm] at h; exact hq a cs' h

end

open Ember.C.Sem (CVal CProg Runs Traps Ext)

/-! ## Temporaries -/

theorem tmpName_inj {a b : Nat} (h : tmpName a = tmpName b) : a = b := by
  unfold tmpName at h
  have h1 := (String.append_right_inj "t").mp h
  simp only [Nat.toString_eq_repr] at h1
  have h2 := congrArg String.toList h1
  simp only [Nat.toList_repr] at h2
  have h3 := congrArg (fun l => Nat.ofDigitChars 10 l 0) h2
  simpa using h3

/-- No temporary from number `t0` on is in scope, or a global. -/
def Fresh (t0 : Nat) (cst : C.Sem.St) (cenv : C.Sem.Env) : Prop :=
  ∀ k, t0 ≤ k → cenv.lookup (tmpName k) = none ∧ cst.globals.lookup (tmpName k) = none

/-- The variables `xs` are temporaries with numbers in `[t0, t1)`. -/
def Temps (xs : C.Sem.Env) (t0 t1 : Nat) : Prop :=
  ∀ y, y ∈ xs.map (·.1) → ∃ k, t0 ≤ k ∧ k < t1 ∧ y = tmpName k

section
variable {t0 t1 t2 : Nat} {cst : C.Sem.St} {cenv xs xs' : C.Sem.Env}

theorem Fresh.ext (hf : Fresh t0 cst cenv) (ht : Temps xs t0 t1) : Ext xs cenv cst := fun y hy => by
  obtain ⟨k, h0, _, rfl⟩ := ht y hy
  exact hf k h0

theorem Fresh.append (hf : Fresh t0 cst cenv) (ht : Temps xs t0 t1) (h01 : t0 ≤ t1) : Fresh t1 cst (xs ++ cenv) := by
  intro k hk
  refine ⟨?_, (hf k (by omega)).2⟩
  have hn : tmpName k ∉ xs.map (·.1) := fun hm => by
    obtain ⟨j, _, hj, e⟩ := ht _ hm
    have := tmpName_inj e
    omega
  rw [List.lookup_append, C.Sem.lookup_eq_none_of_not_mem hn, (hf k (by omega)).1]
  rfl

theorem Temps.nil : Temps [] t0 t1 := fun y hy => by simp at hy

theorem Temps.mono (ht : Temps xs t0 t1) {a b : Nat} (ha : a ≤ t0) (hb : t1 ≤ b) : Temps xs a b := fun y hy => by
  obtain ⟨k, h0, h1, e⟩ := ht y hy
  exact ⟨k, by omega, by omega, e⟩

theorem Temps.append (h1 : Temps xs t0 t1) (h2 : Temps xs' t1 t2) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) :
    Temps (xs' ++ xs) t0 t2 := fun y hy => by
  simp only [List.map_append, List.mem_append] at hy
  rcases hy with hy | hy
  · exact (h2.mono h01 (Nat.le_refl _)) y hy
  · exact (h1.mono (Nat.le_refl _) h12) y hy

theorem Temps.one (k : Nat) (v : CVal) : Temps [(tmpName k, v)] k (k + 1) := fun y hy => by
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
  exact ⟨k, Nat.le_refl _, Nat.lt_succ_self _, hy⟩

end

/-! ## Places and the relation between the states -/

/-- The C lvalue `c` designates the storage `L`, which holds `cv`:
directly, or through a pointer (a by-reference record, `ptr`, or a
by-reference array). -/
def PlaceLoc (cp : CProg) (cst : C.Sem.St) (cenv : C.Sem.Env) (c : CExpr) (ptr : Bool) (cv : CVal)
    (L : C.Sem.Loc) : Prop :=
  ∃ l0, C.Sem.lval cp cst cenv c = some l0 ∧
    ((ptr = false ∧ L = l0 ∧ C.Sem.read cst cenv l0 = some cv) ∨
     (C.Sem.read cst cenv l0 = some (.ptr L) ∧ C.Sem.read cst cenv L = some cv ∧
        ((ptr = true ∧ ∃ n fs, cv = .strct n fs) ∨ (ptr = false ∧ ∃ ys, cv = .arr ys))))

/-- The C lvalue `c` designates storage holding `cv`. -/
def PlaceAt (cp : CProg) (cst : C.Sem.St) (cenv : C.Sem.Env) (c : CExpr) (ptr : Bool) (cv : CVal) : Prop :=
  ∃ L, PlaceLoc cp cst cenv c ptr cv L

theorem PlaceLoc.ext {cp : CProg} {cst : C.Sem.St} {cenv xs : C.Sem.Env} {c : CExpr} {ptr : Bool} {cv : CVal}
    {L : C.Sem.Loc} (hx : Ext xs cenv cst) (h : PlaceLoc cp cst cenv c ptr cv L) :
    PlaceLoc cp cst (xs ++ cenv) c ptr cv L := by
  obtain ⟨l0, hl, hr⟩ := h
  refine ⟨l0, C.Sem.lval_ext hx c hl, ?_⟩
  rcases hr with ⟨hp, hL, hr⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨hp, hL, C.Sem.read_ext hx hr⟩
  · exact Or.inr ⟨C.Sem.read_ext hx h1, C.Sem.read_ext hx h2, h3⟩

theorem PlaceAt.ext {cp : CProg} {cst : C.Sem.St} {cenv xs : C.Sem.Env} {c : CExpr} {ptr : Bool} {cv : CVal}
    (hx : Ext xs cenv cst) (h : PlaceAt cp cst cenv c ptr cv) : PlaceAt cp cst (xs ++ cenv) c ptr cv := by
  obtain ⟨L, h⟩ := h
  exact ⟨L, h.ext hx⟩

/-- **The relation an expression needs** between the Ember state and
the C state: every variable in scope holds a value of its type, and its
C lvalue designates storage holding that value; the record definitions
and the width of `int` are those the unit was emitted for. -/
structure ERel (g : C.Env) (cp : CProg) (st : Lang.Sem.St) (env : Lang.Sem.Env) (cst : C.Sem.St)
    (cenv : C.Sem.Env) : Prop where
  typed : VarsTyped g st env
  place : ∀ x v info, Lang.Sem.lookup st env x = some v → g.varInfo x = .ok info →
    PlaceAt cp cst cenv info.c info.ptr (cval g.opts v)
  flds : ∀ r sd, g.prog.struct? r = some sd →
    cp.unit.structs.lookup (g.opts.structName r) = some (sd.fields.map fun ft => (cty g.opts ft.2, ft.1))
  ints : cp.intBits = g.opts.profile.intBits
  i16 : 16 ≤ cp.intBits
  l32 : 32 ≤ cp.longBits
  nobug : g.opts.bugDropCast = false
  /-- Every variable the emitter knows has a value. -/
  scope : ∀ x info, g.varInfo x = .ok info → ∃ v, Lang.Sem.lookup st env x = some v

theorem ERel.ext {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv xs : C.Sem.Env} (h : ERel g cp st env cst cenv) (hx : Ext xs cenv cst) :
    ERel g cp st env cst (xs ++ cenv) :=
  ⟨h.typed, fun x v info h1 h2 => (h.place x v info h1 h2).ext hx, h.flds, h.ints, h.i16, h.l32, h.nobug, h.scope⟩

/-! ## Fragments

What a piece of emitted code — the statements `pre`, using the
temporaries `[t0, t1)` — does from related states: if the Ember side has
a value (`ok`), `pre` runs, declares temporaries only, and `res` holds;
if not, `pre` ends in `ember_trap`. -/

def Frag (g : C.Env) (cp : CProg) (t0 t1 : Nat) (pre : List CStmt)
    (ok : Lang.Sem.St → Lang.Sem.Env → Prop)
    (res : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop) : Prop :=
  t0 ≤ t1 ∧ ∀ st env cst cenv, ERel g cp st env cst cenv → Fresh t0 cst cenv →
    (ok st env → ∃ xs, Temps xs t0 t1 ∧ Runs cp cst cenv pre (xs ++ cenv) ∧ res st env cst (xs ++ cenv)) ∧
    (¬ ok st env → Traps cp cst cenv pre)

/-- `res` survives the declaration of more variables. -/
def Stable (res : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop) : Prop :=
  ∀ st env cst cenv ys, Ext ys cenv cst → res st env cst cenv → res st env cst (ys ++ cenv)

section
variable {g : C.Env} {cp : CProg} {t0 t1 t2 : Nat} {pre pre1 pre2 : List CStmt}
  {ok ok1 ok2 ok' : Lang.Sem.St → Lang.Sem.Env → Prop}
  {res res1 res2 res' : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop}

theorem Frag.seq (h1 : Frag g cp t0 t1 pre1 ok1 res1) (h2 : Frag g cp t1 t2 pre2 ok2 res2) (hs : Stable res1) :
    Frag g cp t0 t2 (pre1 ++ pre2) (fun st env => ok1 st env ∧ ok2 st env)
      (fun st env cst cenv => res1 st env cst cenv ∧ res2 st env cst cenv) := by
  obtain ⟨h01, h1⟩ := h1
  obtain ⟨h12, h2⟩ := h2
  refine ⟨Nat.le_trans h01 h12, fun st env cst cenv hrel hfr => ?_⟩
  obtain ⟨a1, b1⟩ := h1 st env cst cenv hrel hfr
  by_cases hk1 : ok1 st env
  · obtain ⟨xs1, ht1, hr1, hres1⟩ := a1 hk1
    have hx1 := hfr.ext ht1
    obtain ⟨a2, b2⟩ := h2 st env cst (xs1 ++ cenv) (hrel.ext hx1) (hfr.append ht1 h01)
    constructor
    · rintro ⟨_, hk2⟩
      obtain ⟨xs2, ht2, hr2, hres2⟩ := a2 hk2
      have hx2 := (hfr.append ht1 h01).ext ht2
      refine ⟨xs2 ++ xs1, ht1.append ht2 h01 h12, ?_, ?_⟩
      · rw [List.append_assoc]; exact hr1.append hr2
      · rw [List.append_assoc]; exact ⟨hs _ _ _ _ _ hx2 hres1, hres2⟩
    · intro hn
      exact hr1.traps (b2 fun hk2 => hn ⟨hk1, hk2⟩)
  · exact ⟨fun h => absurd h.1 hk1, fun _ => (b1 hk1).append⟩

theorem Frag.nil (t : Nat) (h : ∀ st env cst cenv, ERel g cp st env cst cenv → ok st env → res st env cst cenv)
    (hok : ∀ st env cst cenv, ERel g cp st env cst cenv → ok st env) :
    Frag g cp t t [] ok res :=
  ⟨Nat.le_refl _, fun st env cst cenv hrel _ =>
    ⟨fun hk => ⟨[], Temps.nil, Runs.nil, h st env cst cenv hrel hk⟩, fun hn => absurd (hok st env cst cenv hrel) hn⟩⟩

theorem Frag.conseq (h : Frag g cp t0 t1 pre ok res)
    (hok : ∀ st env cst cenv, ERel g cp st env cst cenv → (ok' st env ↔ ok st env))
    (hres : ∀ st env cst cenv, ERel g cp st env cst cenv → ok st env → res st env cst cenv → res' st env cst cenv) :
    Frag g cp t0 t1 pre ok' res' := by
  obtain ⟨h01, h⟩ := h
  refine ⟨h01, fun st env cst cenv hrel hfr => ?_⟩
  obtain ⟨a, b⟩ := h st env cst cenv hrel hfr
  have hok' := hok st env cst cenv hrel
  constructor
  · intro hk
    obtain ⟨xs, ht, hr, hre⟩ := a (hok'.mp hk)
    exact ⟨xs, ht, hr, hres st env cst _ (hrel.ext (hfr.ext ht)) (hok'.mp hk) hre⟩
  · intro hn
    exact b fun hk => hn (hok'.mpr hk)

end

section
variable {g : C.Env} {cp : CProg} {t0 t1 t2 : Nat} {pre pre1 pre2 : List CStmt}
  {ok ok1 ok2 ok' : Lang.Sem.St → Lang.Sem.Env → Prop}
  {res res1 res2 res' : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop}

/-- A fragment followed by statements whose behaviour depends on what the fragment established. -/
theorem Frag.bind (h1 : Frag g cp t0 t1 pre1 ok1 res1) (h12 : t1 ≤ t2)
    (h2 : ∀ st env cst cenv, ERel g cp st env cst cenv → Fresh t1 cst cenv → ok1 st env → res1 st env cst cenv →
      (ok2 st env → ∃ xs, Temps xs t1 t2 ∧ Runs cp cst cenv pre2 (xs ++ cenv) ∧ res2 st env cst (xs ++ cenv)) ∧
      (¬ ok2 st env → Traps cp cst cenv pre2)) :
    Frag g cp t0 t2 (pre1 ++ pre2) (fun st env => ok1 st env ∧ ok2 st env) res2 := by
  obtain ⟨h01, h1⟩ := h1
  refine ⟨Nat.le_trans h01 h12, fun st env cst cenv hrel hfr => ?_⟩
  obtain ⟨a1, b1⟩ := h1 st env cst cenv hrel hfr
  by_cases hk1 : ok1 st env
  · obtain ⟨xs1, ht1, hr1, hres1⟩ := a1 hk1
    have hx1 := hfr.ext ht1
    obtain ⟨a2, b2⟩ := h2 st env cst (xs1 ++ cenv) (hrel.ext hx1) (hfr.append ht1 h01) hk1 hres1
    constructor
    · rintro ⟨_, hk2⟩
      obtain ⟨xs2, ht2, hr2, hres2⟩ := a2 hk2
      refine ⟨xs2 ++ xs1, ht1.append ht2 h01 h12, ?_, ?_⟩
      · rw [List.append_assoc]; exact hr1.append hr2
      · rw [List.append_assoc]; exact hres2
    · intro hn
      exact hr1.traps (b2 fun hk2 => hn ⟨hk1, hk2⟩)
  · exact ⟨fun h => absurd h.1 hk1, fun _ => (b1 hk1).append⟩

end

/-- The Ember expression has a value. -/
def EOk (g : C.Env) (e : Expr) : Lang.Sem.St → Lang.Sem.Env → Prop :=
  fun st env => (Lang.Sem.evalE g.prog st env e).isSome = true

/-- The C expression `ce` has the value of the Ember expression `e`. -/
def ERes (g : C.Env) (cp : CProg) (e : Expr) (ce : CExpr) :
    Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop :=
  fun st env cst cenv => ∀ v, Lang.Sem.evalE g.prog st env e = some v →
    C.Sem.evalC cp cst cenv ce = some (cval g.opts v)

/-- The storage `L` of the place `e` is that of its variable, at its path. -/
def Rooted (g : C.Env) (cp : CProg) (e : Expr) (L : C.Sem.Loc) :
    Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop :=
  fun st env cst cenv => ∀ x q, lpath g.prog st env e = some (x, q) → ∀ info vx, g.varInfo x = .ok info →
    Lang.Sem.lookup st env x = some vx →
    ∃ Lx, PlaceLoc cp cst cenv info.c info.ptr (cval g.opts vx) Lx ∧ L = { Lx with path := Lx.path ++ q }

/-- The C lvalue `c` designates the storage of the Ember place `e`. -/
def PRes (g : C.Env) (cp : CProg) (e : Expr) (c : CExpr) (ptr : Bool) :
    Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop :=
  fun st env cst cenv => ∀ v, Lang.Sem.evalE g.prog st env e = some v →
    ∃ L, PlaceLoc cp cst cenv c ptr (cval g.opts v) L ∧ Rooted g cp e L st env cst cenv

theorem ERes.stable (g : C.Env) (cp : CProg) (e : Expr) (ce : CExpr) : Stable (ERes g cp e ce) :=
  fun _ _ _ _ _ hx h v hv => C.Sem.evalC_ext hx ce (h v hv)

theorem PRes.stable (g : C.Env) (cp : CProg) (e : Expr) (c : CExpr) (ptr : Bool) : Stable (PRes g cp e c ptr) :=
  fun _ _ _ _ _ hx h v hv => by
    obtain ⟨L, hL, hroot⟩ := h v hv
    refine ⟨L, hL.ext hx, fun x q hq info vx hi hlk => ?_⟩
    obtain ⟨Lx, hLx, e⟩ := hroot x q hq info vx hi hlk
    exact ⟨Lx, hLx.ext hx, e⟩

theorem Stable.and {r1 r2 : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop} (h1 : Stable r1)
    (h2 : Stable r2) : Stable (fun st env cst cenv => r1 st env cst cenv ∧ r2 st env cst cenv) :=
  fun st env cst cenv ys hx h => ⟨h1 st env cst cenv ys hx h.1, h2 st env cst cenv ys hx h.2⟩

/-! ## Single statements -/

section
variable {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env}

theorem exec_decl (m : Nat) (t : CTy) (x : String) (c : CExpr) (cv cv' : CVal) (hcall : C.Sem.asCall c = none)
    (hev : C.Sem.evalC cp cst cenv c = some cv) (hconv : C.Sem.convTo cp t cv = some cv') :
    C.Sem.execS (m + 1) cp cst cenv (.decl t x (some c)) = .ok cst ((x, cv') :: cenv) .normal := by
  simp only [C.Sem.execS, hcall, hev, hconv]

theorem exec_void (m : Nat) (e : CExpr) :
    C.Sem.execS (m + 1) cp cst cenv (.expr (.cast .void e)) = .ok cst cenv .normal := by
  simp only [C.Sem.execS, C.Sem.asCall]

theorem evalC_var_head (x : String) (cv : CVal) :
    C.Sem.evalC cp cst ((x, cv) :: cenv) (.var x) = some cv := by
  simp [C.Sem.evalC, C.Sem.varLoc, List.lookup, C.Sem.read, C.Sem.readBase, C.Sem.getPath]

/-- `T t = c; (void)t;` -/
theorem hide_step (ct : CTy) (ce : CExpr) (cv : CVal) (k : Nat) (hcall : C.Sem.asCall ce = none)
    (hev : C.Sem.evalC cp cst cenv ce = some cv) (hconv : C.Sem.convTo cp ct cv = some cv) :
    Runs cp cst cenv [.decl ct (tmpName k) (some ce), .expr (.cast .void (.var (tmpName k)))]
      ([(tmpName k, cv)] ++ cenv) := by
  have r1 : Runs cp cst cenv [.decl ct (tmpName k) (some ce)] ((tmpName k, cv) :: cenv) :=
    Runs.single fun m => exec_decl (m + 4) ct _ ce cv cv hcall hev hconv
  have r2 : Runs cp cst ((tmpName k, cv) :: cenv) [.expr (.cast .void (.var (tmpName k)))]
      ((tmpName k, cv) :: cenv) := Runs.single fun m => exec_void (m + 4) _
  exact r1.append r2

end

theorem wpc_hide {g : C.Env} {cs : CS} (ct : CTy) (c : CExpr) (Q : CExpr → CS → Prop) :
    wpc (hide ct c) g Q cs ↔
      if c.isSimple = true then Q c cs
      else Q (.var (tmpName cs.tmp))
        { out := (cs.out.push (.decl ct (tmpName cs.tmp) (some c))).push (.expr (.cast .void (.var (tmpName cs.tmp)))),
          tmp := cs.tmp + 1 } := by
  unfold hide
  by_cases h : c.isSimple = true
  · simp only [h, if_true]; exact Iff.rfl
  · simp only [h, Bool.false_eq_true, if_false]; exact Iff.rfl

/-! ## The operators in C -/

/-- The width an operation on `w`-bit operands is computed in. -/
def ubits (cp : CProg) (w : Width) : Nat := if w.bits ≤ cp.intBits then cp.intBits else w.bits

theorem ubits_ge (cp : CProg) (w : Width) : w.bits ≤ ubits cp w := by
  unfold ubits; split <;> omega

theorem ubits_int (cp : CProg) (w : Width) : cp.intBits ≤ ubits cp w := by
  unfold ubits; split <;> omega

theorem castTo_opTy (o : Opts) (cp : CProg) (hI : cp.intBits = o.profile.intBits) (w : Width) (k x : Nat)
    (hx : x < 2 ^ w.bits) : C.Sem.castTo cp (opTy o w) (.int k x) = some (.int (ubits cp w) x) := by
  have hlt : x < 2 ^ ubits cp w := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (ubits_ge cp w))
  unfold opTy ubits at *
  simp only [Profile.promotes, decide_eq_true_eq, ← hI]
  split
  · rename_i h
    simp only [h, if_true] at hlt
    simp only [C.Sem.castTo, Nat.mod_eq_of_lt hlt]
  · rename_i h
    simp only [h, if_false] at hlt
    simp only [C.Sem.castTo, Nat.mod_eq_of_lt hlt]

theorem castTo_uint (cp : CProg) (n k x : Nat) : C.Sem.castTo cp (.uint n) (.int k x) = some (.int n (x % 2 ^ n)) := rfl

theorem sub_mod_pow (a b n m : Nat) (hb : b ≤ 2 ^ n) (hnm : n ≤ m) :
    (2 ^ m + a - b) % 2 ^ m % 2 ^ n = (2 ^ n + a - b) % 2 ^ n := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnm)]
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [Nat.pow_add]
  have hK : 0 < 2 ^ d := Nat.two_pow_pos d
  obtain ⟨K, hK'⟩ : ∃ K, 2 ^ d = K + 1 := ⟨2 ^ d - 1, by omega⟩
  rw [hK', Nat.mul_succ]
  have : 2 ^ n * K + 2 ^ n + a - b = (2 ^ n + a - b) + 2 ^ n * K := by omega
  rw [this, Nat.add_mul_mod_self_left]

/-- The six operators the emitter writes as `(T)((U)a op (U)b)`. -/
def simpleSym : BinOp → Option String
  | .add => some "+" | .sub => some "-" | .mul => some "*"
  | .band => some "&" | .bor => some "|" | .bxor => some "^"
  | _ => none

theorem c_simple (cp : CProg) (op : BinOp) (sym : String) (hs : simpleSym op = some sym) (ub n x y : Nat)
    (hn : n ≤ ub) (hI : cp.intBits ≤ ub) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    (C.Sem.binop cp sym (.int ub x) (.int ub y)).bind (C.Sem.castTo cp (.uint n))
      = some (.int n (natOp op n x y)) := by
  have hI' : ¬ ub < cp.intBits := by omega
  have hd := Nat.pow_dvd_pow 2 hn
  cases op <;> simp only [simpleSym, Option.some.injEq, reduceCtorEq] at hs <;> subst hs <;>
    simp only [C.Sem.binop, C.Sem.isCompare, C.Sem.arith, String.reduceBEq, Bool.or_self, Bool.false_eq_true,
      if_false, if_true, Nat.max_self, hI', Option.bind_some, castTo_uint, natOp, Option.some.injEq,
      C.Sem.CVal.int.injEq, true_and]
  · exact Nat.mod_mod_of_dvd _ hd
  · exact sub_mod_pow x y n ub (Nat.le_of_lt hy) hn
  · exact Nat.mod_mod_of_dvd _ hd
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)
  · exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hx hy)
  · exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy)

/-! ## Constants and variables -/

theorem evalC_litC (cp : CProg) (cst : C.Sem.St) (cenv : C.Sem.Env) (w : Width) (n : Nat) (hn : n < 2 ^ w.bits)
    (h16 : 16 ≤ cp.intBits) (h32 : 32 ≤ cp.longBits) :
    C.Sem.evalC cp cst cenv (litC w n) = some (.int w.bits n) := by
  have hb : ∃ b, C.Sem.litBits cp (suffix w) = some b ∧ w.bits ≤ b := by
    cases w
    · exact ⟨cp.intBits, rfl, by simp only [Width.bits]; omega⟩
    · exact ⟨cp.intBits, rfl, by simp only [Width.bits]; omega⟩
    · exact ⟨cp.longBits, rfl, by simp only [Width.bits]; omega⟩
    · exact ⟨64, rfl, Nat.le_refl _⟩
  obtain ⟨b, hb, hle⟩ := hb
  have hlt : n < 2 ^ b := Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hle)
  simp only [litC, C.Sem.evalC, hb, hlt, if_true, castTo_uint, Nat.mod_eq_of_lt hn]

/-- An lvalue's value is what its storage holds. -/
theorem evalC_of_lval (cp : CProg) (cst : C.Sem.St) (cenv : C.Sem.Env) (c : CExpr) (l : C.Sem.Loc)
    (h : C.Sem.lval cp cst cenv c = some l) : C.Sem.evalC cp cst cenv c = C.Sem.read cst cenv l := by
  cases c with
  | var x => simp only [C.Sem.lval] at h; simp only [C.Sem.evalC, h]
  | index a i =>
    simp only [C.Sem.lval] at h
    simp only [C.Sem.evalC]
    cases ha : C.Sem.lval cp cst cenv a with
    | none => simp [ha] at h
    | some la =>
      cases hi : C.Sem.evalC cp cst cenv i with
      | none => simp [ha, hi] at h
      | some iv => simp only [ha, hi] at h ⊢; simp only [h]
  | dot a f =>
    simp only [C.Sem.lval] at h
    simp only [C.Sem.evalC]
    cases ha : C.Sem.lval cp cst cenv a with
    | none => simp [ha] at h
    | some la => simp only [ha] at h ⊢; simp only [h]
  | arrow a f =>
    simp only [C.Sem.lval] at h
    simp only [C.Sem.evalC]
    cases ha : C.Sem.lval cp cst cenv a with
    | none => simp [ha] at h
    | some la => simp only [ha] at h ⊢; simp only [h]
  | _ => simp [C.Sem.lval] at h

/-- A scalar at a place is the value of the lvalue. -/
theorem PlaceAt.evalC {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} {c : CExpr} {ptr : Bool} {cv : CVal}
    (h : PlaceAt cp cst cenv c ptr cv) (hs : (∀ n fs, cv ≠ .strct n fs) ∧ ∀ ys, cv ≠ .arr ys) :
    C.Sem.evalC cp cst cenv c = some cv := by
  obtain ⟨L, l0, hl, hr⟩ := h
  rw [evalC_of_lval cp cst cenv c l0 hl]
  rcases hr with ⟨_, _, hr⟩ | ⟨_, _, h3⟩
  · exact hr
  · rcases h3 with ⟨_, n, fs, e⟩ | ⟨_, ys, e⟩
    · exact absurd e (hs.1 n fs)
    · exact absurd e (hs.2 ys)

theorem cval_scalar (o : Opts) (p : Prog) (t : Ty) (v : Val) (hs : t.isScalar = true) (h : HasTy p t v) :
    (∀ n fs, cval o v ≠ .strct n fs) ∧ ∀ ys, cval o v ≠ .arr ys := by
  cases t with
  | int w => obtain ⟨x, rfl, _⟩ := hasTy_int h; simp [cval]
  | bool => obtain ⟨b, rfl⟩ := hasTy_bool h; simp [cval]
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

theorem wpc_placeVar {g : C.Env} {cs : CS} (x : String) (Q : CExpr × Ty × Bool → CS → Prop) :
    wpc (placeVar x) g Q cs ↔ ∀ info, g.varInfo x = .ok info → Q (info.c, info.ty, info.ptr) cs := by
  unfold placeVar varInfo
  simp only [wpc_bind, wpc_pureE, wpc_pure]

/-! ## The statements about `expr` and `place` -/

/-- What the emitter relies on about the form of a compiled expression:
it is not a call (so it can initialise a temporary), not a bare literal,
and if it is a constant `(T)n`, then `n` is the value. -/
structure Shape (g : C.Env) (e : Expr) (ce : CExpr) : Prop where
  nocall : C.Sem.asCall ce = none
  nolit : ∀ n s, ce ≠ .lit n s
  lit : ∀ n, ce.litVal? = some n → ∀ st env x, VarsTyped g st env → Lang.Sem.evalE g.prog st env e = some x →
    x.toNat = n

theorem Shape.plain {g : C.Env} {e : Expr} {ce : CExpr} (h1 : C.Sem.asCall ce = none) (h2 : ce.litVal? = none) :
    Shape g e ce :=
  ⟨h1, fun n s h => by rw [h] at h2; simp [CExpr.litVal?] at h2, fun n h => by rw [h2] at h; exact absurd h (by simp)⟩

/-- What `expr e` yields: the statements `pre` it emitted and the
expression `ce`, such that from related states `pre` runs and `ce` has
the value of `e` — or `pre` traps when `e` has no value. -/
def EPost (g : C.Env) (cp : CProg) (e : Expr) (cs : CS) (ce : CExpr) (cs' : CS) : Prop :=
  ∃ pre, cs'.out = cs.out ++ pre.toArray ∧ Shape g e ce ∧
    Frag g cp cs.tmp cs'.tmp pre (EOk g e) (ERes g cp e ce)

/-- What `place e` yields. -/
def PPost (g : C.Env) (cp : CProg) (e : Expr) (cs : CS) (r : CExpr × Ty × Bool) (cs' : CS) : Prop :=
  ∃ pre, cs'.out = cs.out ++ pre.toArray ∧ g.tyOf e = .ok r.2.1 ∧
    Frag g cp cs.tmp cs'.tmp pre (EOk g e) (PRes g cp e r.1 r.2.2)

theorem EPost.nil {g : C.Env} {cp : CProg} {e : Expr} {cs : CS} {ce : CExpr} (hc : Shape g e ce)
    (hok : ∀ st env cst cenv, ERel g cp st env cst cenv → EOk g e st env)
    (h : ∀ st env cst cenv, ERel g cp st env cst cenv → ERes g cp e ce st env cst cenv) :
    EPost g cp e cs ce cs :=
  ⟨[], by simp, hc, Frag.nil _ (fun st env cst cenv hr _ => h st env cst cenv hr) hok⟩

theorem closed_post {g : C.Env} {cp : CProg} {e : Expr} {cs : CS} {c : CExpr} (hw : WT g e) {t : Ty}
    (ht : g.tyOf e = .ok t) (h : closedConst e = some c) : EPost g cp e cs c cs := by
  have key : ∃ v, closedVal e = some v ∧ ((∃ w x, v = .int w x ∧ c = litC w x.toNat) ∨ ∃ b, v = .bool b ∧ c = .blit b) := by
    unfold closedConst at h
    split at h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · cases hv : closedVal e with
      | none => simp [hv] at h
      | some v =>
        cases v with
        | int w x => simp only [hv, Option.some.injEq] at h; exact ⟨_, rfl, Or.inl ⟨w, x, rfl, h.symm⟩⟩
        | bool b => simp only [hv, Option.some.injEq] at h; exact ⟨_, rfl, Or.inr ⟨b, rfl, h.symm⟩⟩
        | arr _ => simp [hv] at h
        | record _ _ => simp [hv] at h
  obtain ⟨v, hv, hc⟩ := key
  have hev := fun (st : Lang.Sem.St) (env : Lang.Sem.Env) => closed_evalE e v hv g.prog st env
  refine EPost.nil ?_ (fun st env _ _ _ => by simp [EOk, hev st env]) ?_
  · rcases hc with ⟨w, x, rfl, rfl⟩ | ⟨b, _, rfl⟩
    · refine ⟨rfl, fun n s h => by simp [litC] at h, fun n hn st env y _ hy => ?_⟩
      rw [hev st env] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      simpa [litC, CExpr.litVal?, Val.toNat] using hn
    · exact Shape.plain rfl rfl
  · intro st env cst cenv hrel v' hv'
    rw [hev st env] at hv'
    simp only [Option.some.injEq] at hv'
    subst hv'
    have hty := evalE_hasTy g st env hrel.typed e v t hw (hev st env) ht
    rcases hc with ⟨w, x, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
    · have hx : x.toNat < 2 ^ w.bits := by
        cases t with
        | int w' => obtain ⟨y, e1, hy⟩ := hasTy_int hty; cases e1; exact hy
        | bool => obtain ⟨b, e1⟩ := hasTy_bool hty; cases e1
        | arr _ _ => obtain ⟨_, e1, _⟩ := hasTy_arr hty; cases e1
        | record _ => obtain ⟨_, _, e1, _⟩ := hasTy_record hty; cases e1
      rw [cval_int]
      exact evalC_litC cp cst cenv w x.toNat hx hrel.i16 hrel.l32
    · rw [cval_bool]; rfl

/-- What an operator's emission yields after the statements `pre` of its operands. -/
def KPost (g : C.Env) (cp : CProg) (e : Expr) (t0 : Nat) (pre : List CStmt) (cs : CS) (ce : CExpr) (cs' : CS) :
    Prop :=
  ∃ pre', cs'.out = cs.out ++ pre'.toArray ∧ Shape g e ce ∧
    Frag g cp t0 cs'.tmp (pre ++ pre') (EOk g e) (ERes g cp e ce)

/-- `hide`: the expression `c`, which has the value of `e'` after the
fragment so far, is kept or put in a temporary; either way the result has
that value. -/
theorem hide_frag {g : C.Env} {cp : CProg} {cs : CS} {t0 : Nat} {pre : List CStmt}
    {ok : Lang.Sem.St → Lang.Sem.Env → Prop} {res : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop}
    (e' : Expr) (ct : CTy) (c : CExpr) (F : Frag g cp t0 cs.tmp pre ok res) (hst : Stable res)
    (hval : ∀ st env cst cenv, ERel g cp st env cst cenv → ok st env → res st env cst cenv →
      ∃ v, Lang.Sem.evalE g.prog st env e' = some v ∧ C.Sem.evalC cp cst cenv c = some (cval g.opts v) ∧
        C.Sem.convTo cp ct (cval g.opts v) = some (cval g.opts v))
    (hcall : C.Sem.asCall c = none) :
    wpc (hide ct c) g (fun c' cs' => ∃ pre', cs'.out = cs.out ++ pre'.toArray ∧
      (c.isSimple = true → c' = c) ∧ (c.isSimple = false → ∃ k, c' = .var (tmpName k)) ∧
      Frag g cp t0 cs'.tmp (pre ++ pre') ok
        (fun st env cst cenv => res st env cst cenv ∧ ERes g cp e' c' st env cst cenv)) cs := by
  rw [wpc_hide]
  by_cases hs : c.isSimple = true
  · rw [if_pos hs]
    refine ⟨[], by simp, fun _ => rfl, fun h => by rw [hs] at h; exact absurd h (by simp), ?_⟩
    rw [List.append_nil]
    refine F.conseq (fun _ _ _ _ _ => Iff.rfl) fun st env cst cenv hrel hk hr => ⟨hr, fun v' hv' => ?_⟩
    obtain ⟨v, h1, h2, _⟩ := hval st env cst cenv hrel hk hr
    rw [h1] at hv'
    simp only [Option.some.injEq] at hv'
    subst hv'
    exact h2
  · rw [if_neg hs]
    refine ⟨[.decl ct (tmpName cs.tmp) (some c), .expr (.cast .void (.var (tmpName cs.tmp)))],
      by rw [← Array.toList_inj]; simp,
      fun h => absurd h hs, fun _ => ⟨_, rfl⟩, ?_⟩
    have B := F.bind (t2 := cs.tmp + 1) (ok2 := fun _ _ => True)
      (res2 := fun st env cst cenv => res st env cst cenv ∧ ERes g cp e' (.var (tmpName cs.tmp)) st env cst cenv)
      (pre2 := [.decl ct (tmpName cs.tmp) (some c), .expr (.cast .void (.var (tmpName cs.tmp)))])
      (Nat.le_succ _) (fun st env cst cenv hrel hfr hk hr => by
        obtain ⟨v, h1, h2, h3⟩ := hval st env cst cenv hrel hk hr
        refine ⟨fun _ => ⟨[(tmpName cs.tmp, cval g.opts v)], Temps.one _ _, hide_step ct c _ _ hcall h2 h3, ?_, ?_⟩,
          fun h => absurd trivial h⟩
        · exact hst _ _ _ _ _ (hfr.ext (Temps.one _ _)) hr
        · intro v' hv'
          rw [h1] at hv'
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact evalC_var_head _ _)
    exact B.conseq (fun _ _ _ _ _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩) fun _ _ _ _ _ _ h => h

/-! ## Binary operators: typing and values -/

/-- The operand types an operator is checked for. -/
def BinTy (op : BinOp) (ta tb : Ty) : Prop :=
  if op.isLogic then ta = .bool ∧ tb = .bool
  else if op.isShift then (∃ w, ta = .int w) ∧ ∃ w, tb = .int w
  else if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true
  else ∃ w, ta = .int w ∧ tb = .int w

theorem wt_bin {g : C.Env} {op : BinOp} {a b : Expr} (hw : WT g (.bin op a b)) :
    WT g a ∧ WT g b ∧ ∃ ta tb, g.tyOf a = .ok ta ∧ g.tyOf b = .ok tb ∧ BinTy op ta tb := by
  simp only [WT] at hw
  obtain ⟨wa, wb, hty⟩ := hw
  refine ⟨wa, wb, ?_⟩
  unfold BinTy
  by_cases h1 : op.isLogic = true
  · rw [if_pos h1] at hty
    exact ⟨_, _, hty.1, hty.2, by rw [if_pos h1]; exact ⟨rfl, rfl⟩⟩
  · rw [if_neg h1] at hty
    by_cases h2 : op.isShift = true
    · rw [if_pos h2] at hty
      obtain ⟨⟨w, e1⟩, ⟨w', e2⟩⟩ := hty
      exact ⟨_, _, e1, e2, by rw [if_neg h1, if_pos h2]; exact ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩⟩
    · rw [if_neg h2] at hty
      by_cases h3 : op = .eq ∨ op = .ne
      · rw [if_pos h3] at hty
        obtain ⟨t, e1, e2, hs⟩ := hty
        exact ⟨_, _, e1, e2, by rw [if_neg h1, if_neg h2, if_pos h3]; exact ⟨rfl, hs⟩⟩
      · rw [if_neg h3] at hty
        obtain ⟨w, e1, e2⟩ := hty
        exact ⟨_, _, e1, e2, by rw [if_neg h1, if_neg h2, if_neg h3]; exact ⟨w, rfl, rfl⟩⟩

theorem binop_total (p : Prog) (op : BinOp) (ta tb : Ty) (x y : Val) (hty : BinTy op ta tb)
    (hx : HasTy p ta x) (hy : HasTy p tb y) : ∃ v, Lang.Sem.binop op x y = some v := by
  unfold BinTy at hty
  cases op <;> simp only [BinOp.isLogic, BinOp.isShift, Bool.false_eq_true, if_false, if_true, reduceCtorEq,
    or_false, false_or, or_self] at hty
  all_goals first
    | (obtain ⟨w, rfl, rfl⟩ := hty
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ := hty
       obtain ⟨a, rfl, _⟩ := hasTy_int hx
       obtain ⟨b, rfl, _⟩ := hasTy_int hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := hty
       obtain ⟨a, rfl⟩ := hasTy_bool hx
       obtain ⟨b, rfl⟩ := hasTy_bool hy
       exact ⟨_, rfl⟩)
    | (obtain ⟨rfl, hs⟩ := hty
       cases ta with
       | int w =>
         obtain ⟨a, rfl, _⟩ := hasTy_int hx
         obtain ⟨b, rfl, _⟩ := hasTy_int hy
         exact ⟨_, rfl⟩
       | bool =>
         obtain ⟨a, rfl⟩ := hasTy_bool hx
         obtain ⟨b, rfl⟩ := hasTy_bool hy
         exact ⟨_, rfl⟩
       | arr _ _ => simp [Ty.isScalar] at hs
       | record _ => simp [Ty.isScalar] at hs)

theorem evalE_bin_some {p : Prog} {st : Lang.Sem.St} {env : Lang.Sem.Env} {op : BinOp} {a b : Expr} {v : Val} :
    Lang.Sem.evalE p st env (.bin op a b) = some v ↔
      ∃ x y, Lang.Sem.evalE p st env a = some x ∧ Lang.Sem.evalE p st env b = some y ∧
        Lang.Sem.binop op x y = some v := by
  simp only [Lang.Sem.evalE]
  cases ha : Lang.Sem.evalE p st env a with
  | none => simp
  | some x =>
    cases hb : Lang.Sem.evalE p st env b with
    | none => simp
    | some y => simp

/-- The values of two operands after their fragment. -/
theorem ops_vals {g : C.Env} {cp : CProg} {a b : Expr} {ca cb : CExpr} {ta tb : Ty}
    {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env}
    (hrel : ERel g cp st env cst cenv) (wa : WT g a) (wb : WT g b) (hta : g.tyOf a = .ok ta)
    (htb : g.tyOf b = .ok tb) (hk : EOk g a st env ∧ EOk g b st env)
    (hr : ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv) :
    ∃ x y, Lang.Sem.evalE g.prog st env a = some x ∧ Lang.Sem.evalE g.prog st env b = some y ∧
      C.Sem.evalC cp cst cenv ca = some (cval g.opts x) ∧ C.Sem.evalC cp cst cenv cb = some (cval g.opts y) ∧
      HasTy g.prog ta x ∧ HasTy g.prog tb y := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk.1
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hk.2
  exact ⟨x, y, hx, hy, hr.1 x hx, hr.2 y hy, evalE_hasTy g st env hrel.typed a x ta wa hx hta,
    evalE_hasTy g st env hrel.typed b y tb wb hy htb⟩

theorem EOk_bin {g : C.Env} {cp : CProg} {op : BinOp} {a b : Expr} {st : Lang.Sem.St} {env : Lang.Sem.Env}
    {cst : C.Sem.St} {cenv : C.Sem.Env} (hrel : ERel g cp st env cst cenv) (hw : WT g (.bin op a b)) :
    EOk g (.bin op a b) st env ↔ EOk g a st env ∧ EOk g b st env := by
  obtain ⟨wa, wb, ta, tb, hta, htb, hty⟩ := wt_bin hw
  unfold EOk
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨x, y, hx, hy, _⟩ := evalE_bin_some.mp hv
    simp [hx, hy]
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h2
    obtain ⟨v, hv⟩ := binop_total g.prog op ta tb x y hty
      (evalE_hasTy g st env hrel.typed a x ta wa hx hta) (evalE_hasTy g st env hrel.typed b y tb wb hy htb)
    rw [evalE_bin_some.mpr ⟨x, y, hx, hy, hv⟩]
    rfl

theorem KPost.pure {g : C.Env} {cp : CProg} {e : Expr} {t0 : Nat} {pre : List CStmt} {cs : CS} {ce : CExpr}
    {ok : Lang.Sem.St → Lang.Sem.Env → Prop} {res : Lang.Sem.St → Lang.Sem.Env → C.Sem.St → C.Sem.Env → Prop}
    (F : Frag g cp t0 cs.tmp pre ok res) (hs : Shape g e ce)
    (hok : ∀ st env cst cenv, ERel g cp st env cst cenv → (EOk g e st env ↔ ok st env))
    (hres : ∀ st env cst cenv, ERel g cp st env cst cenv → ok st env → res st env cst cenv →
      ERes g cp e ce st env cst cenv) :
    KPost g cp e t0 pre cs ce cs :=
  ⟨[], by simp, hs, by rw [List.append_nil]; exact F.conseq hok hres⟩

/-! ## C expressions, one constructor at a time -/

section
variable {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env}

theorem evalC_cast (t : CTy) (a : CExpr) :
    C.Sem.evalC cp cst cenv (.cast t a) = (C.Sem.evalC cp cst cenv a).bind (C.Sem.castTo cp t) := by
  simp only [C.Sem.evalC]
  cases C.Sem.evalC cp cst cenv a <;> rfl

theorem evalC_un (op : String) (a : CExpr) :
    C.Sem.evalC cp cst cenv (.un op a) = (C.Sem.evalC cp cst cenv a).bind (C.Sem.unop cp op) := by
  simp only [C.Sem.evalC]
  cases C.Sem.evalC cp cst cenv a <;> rfl

theorem evalC_bin (sym : String) (a b : CExpr) (x y : CVal) (h1 : (sym == "&&") = false)
    (h2 : (sym == "||") = false) (ha : C.Sem.evalC cp cst cenv a = some x) (hb : C.Sem.evalC cp cst cenv b = some y) :
    C.Sem.evalC cp cst cenv (.bin sym a b) = C.Sem.binop cp sym x y := by
  simp only [C.Sem.evalC, h1, h2, Bool.false_eq_true, if_false, ha, hb]

theorem evalC_cond (c a b : CExpr) (cv : CVal) (t : Bool) (hc : C.Sem.evalC cp cst cenv c = some cv)
    (ht : C.Sem.truthy cv = some t) :
    C.Sem.evalC cp cst cenv (.cond c a b) = if t then C.Sem.evalC cp cst cenv a else C.Sem.evalC cp cst cenv b := by
  simp only [C.Sem.evalC, hc, ht]
  cases t <;> rfl

theorem evalC_logic (land : Bool) (a b : CExpr) (p q : Bool) (ha : C.Sem.evalC cp cst cenv a = some (.bool p))
    (hb : C.Sem.evalC cp cst cenv b = some (.bool q)) :
    C.Sem.evalC cp cst cenv (.bin (if land then "&&" else "||") a b)
      = some (.bool (if land then p && q else p || q)) := by
  cases land <;> cases p <;> cases q <;>
    simp [C.Sem.evalC, ha, hb, C.Sem.truthy]

/-- `(T)((U)a op (U)b)` for the operators without a guard. -/
theorem evalC_arithE (o : Opts) (hI : cp.intBits = o.profile.intBits) (w : Width) (sym : String)
    (h1 : (sym == "&&") = false) (h2 : (sym == "||") = false) (ca cb : CExpr) (kx ky x y : Nat)
    (hx : x < 2 ^ w.bits) (hy : y < 2 ^ w.bits) (ha : C.Sem.evalC cp cst cenv ca = some (.int kx x))
    (hb : C.Sem.evalC cp cst cenv cb = some (.int ky y)) :
    C.Sem.evalC cp cst cenv (arithE o w sym ca cb)
      = (C.Sem.binop cp sym (.int (ubits cp w) x) (.int (ubits cp w) y)).bind (C.Sem.castTo cp (.uint w.bits)) := by
  have ea : C.Sem.evalC cp cst cenv (.cast (opTy o w) ca) = some (.int (ubits cp w) x) := by
    rw [evalC_cast, ha]; exact castTo_opTy o cp hI w kx x hx
  have eb : C.Sem.evalC cp cst cenv (.cast (opTy o w) cb) = some (.int (ubits cp w) y) := by
    rw [evalC_cast, hb]; exact castTo_opTy o cp hI w ky y hy
  unfold arithE
  rw [evalC_cast, evalC_bin sym _ _ _ _ h1 h2 ea eb]

end

/-! ## `binC` -/

section
variable {g : C.Env} {cp : CProg} {op : BinOp} {a b : Expr} {ca cb : CExpr} {ta tb : Ty} {t0 : Nat}
  {pre : List CStmt} {cs : CS}

/-- The fragment of two compiled operands. -/
abbrev Ops2 (g : C.Env) (cp : CProg) (a b : Expr) (ca cb : CExpr) (t0 : Nat) (pre : List CStmt) (cs : CS) : Prop :=
  Frag g cp t0 cs.tmp pre (fun st env => EOk g a st env ∧ EOk g b st env)
    (fun st env cst cenv => ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv)

theorem logic_ok (F : Ops2 g cp a b ca cb t0 pre cs) (hw : WT g (.bin op a b)) (hta : g.tyOf a = .ok ta)
    (htb : g.tyOf b = .ok tb) (hty : BinTy op ta tb) (hl : op.isLogic = true) :
    KPost g cp (.bin op a b) t0 pre cs (.bin (if op == .land then "&&" else "||") ca cb) cs := by
  obtain ⟨wa, wb, _⟩ := wt_bin hw
  refine KPost.pure F (Shape.plain rfl rfl) (fun st env cst cenv hrel => EOk_bin hrel hw) ?_
  intro st env cst cenv hrel hk hr v hv
  obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
  unfold BinTy at hty
  rw [if_pos hl] at hty
  obtain ⟨rfl, rfl⟩ := hty
  obtain ⟨p, rfl⟩ := hasTy_bool tx
  obtain ⟨q, rfl⟩ := hasTy_bool ty
  obtain ⟨_, _, hx', hy', hb⟩ := evalE_bin_some.mp hv
  rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'
  rw [cval_bool] at hca hcb
  cases op <;> simp only [BinOp.isLogic, Bool.false_eq_true] at hl
  · simp only [Lang.Sem.binop, Option.some.injEq] at hb
    subst hb
    rw [cval_bool]
    exact evalC_logic true ca cb p q hca hcb
  · simp only [Lang.Sem.binop, Option.some.injEq] at hb
    subst hb
    rw [cval_bool]
    exact evalC_logic false ca cb p q hca hcb

theorem simple_ok (F : Ops2 g cp a b ca cb t0 pre cs) (hw : WT g (.bin op a b)) {w : Width}
    (hta : g.tyOf a = .ok (.int w)) (htb : g.tyOf b = .ok (.int w)) (sym : String) (hs : simpleSym op = some sym) :
    KPost g cp (.bin op a b) t0 pre cs (arithE g.opts w sym ca cb) cs := by
  obtain ⟨wa, wb, _⟩ := wt_bin hw
  have hsym : (sym == "&&") = false ∧ (sym == "||") = false ∧ op.isCompare = false ∧ op.isLogic = false := by
    cases op <;> simp only [simpleSym, Option.some.injEq, reduceCtorEq] at hs <;> subst hs <;> decide
  refine KPost.pure F (Shape.plain rfl rfl) (fun st env cst cenv hrel => EOk_bin hrel hw) ?_
  intro st env cst cenv hrel hk hr v hv
  obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
  obtain ⟨xv, rfl, hxl⟩ := hasTy_int tx
  obtain ⟨yv, rfl, hyl⟩ := hasTy_int ty
  obtain ⟨_, _, hx', hy', hb⟩ := evalE_bin_some.mp hv
  rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'
  obtain ⟨r, hr1, hr2⟩ := binop_arith op hsym.2.2.1 hsym.2.2.2 w w xv yv hxl (fun _ => hyl)
  rw [hr1] at hb
  cases hb
  rw [cval_int] at hca hcb ⊢
  rw [evalC_arithE g.opts hrel.ints w sym hsym.1 hsym.2.1 ca cb _ _ _ _ hxl hyl hca hcb, hr2]
  exact c_simple cp op sym hs _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl hyl

end

/-! ## Comparisons -/

theorem c_cmp (cp : CProg) (op : BinOp) (hc : op.isCompare = true) (k1 k2 x y : Nat) :
    C.Sem.binop cp (cmpSym op) (.int k1 x) (.int k2 y) = some (.bool (natCmp op x y)) := by
  cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;>
    simp [cmpSym, C.Sem.binop, C.Sem.isCompare, C.Sem.compare, natCmp]

/-- A comparison of two scalars of one type, in C. -/
theorem cmp_val (o : Opts) (cp : CProg) (p : Prog) (op : BinOp) (hc : op.isCompare = true) (ta tb : Ty)
    (hty : BinTy op ta tb) (x y v : Val) (hx : HasTy p ta x) (hy : HasTy p tb y)
    (hb : Lang.Sem.binop op x y = some v) :
    C.Sem.binop cp (cmpSym op) (cval o x) (cval o y) = some (cval o v) := by
  have hl : op.isLogic = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  have hs : op.isShift = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  unfold BinTy at hty
  rw [if_neg (by simp [hl]), if_neg (by simp [hs])] at hty
  have int_case : ∀ (w w' : Width) (xv yv : UInt64), x = .int w xv → y = .int w' yv →
      C.Sem.binop cp (cmpSym op) (cval o x) (cval o y) = some (cval o v) := by
    intro w w' xv yv ex ey
    subst ex ey
    rw [binop_cmp op hc] at hb
    cases hb
    simp only [cval_int, cval_bool]
    exact c_cmp cp op hc _ _ _ _
  by_cases h3 : op = .eq ∨ op = .ne
  · rw [if_pos h3] at hty
    obtain ⟨rfl, hsc⟩ := hty
    cases ta with
    | int w =>
      obtain ⟨xv, ex, _⟩ := hasTy_int hx
      obtain ⟨yv, ey, _⟩ := hasTy_int hy
      exact int_case w w xv yv ex ey
    | bool =>
      obtain ⟨p1, rfl⟩ := hasTy_bool hx
      obtain ⟨q1, rfl⟩ := hasTy_bool hy
      rcases h3 with rfl | rfl
      · simp only [Lang.Sem.binop, Option.some.injEq] at hb
        subst hb
        simp [cmpSym, C.Sem.binop, C.Sem.isCompare]
      · simp only [Lang.Sem.binop, Option.some.injEq] at hb
        subst hb
        simp [cmpSym, C.Sem.binop, C.Sem.isCompare]
    | arr _ _ => simp [Ty.isScalar] at hsc
    | record _ => simp [Ty.isScalar] at hsc
  · rw [if_neg h3] at hty
    obtain ⟨w, rfl, rfl⟩ := hty
    obtain ⟨xv, ex, _⟩ := hasTy_int hx
    obtain ⟨yv, ey, _⟩ := hasTy_int hy
    exact int_case w w xv yv ex ey

theorem decide_sound (op : BinOp) (hc : op.isCompare = true) (hi c x : Nat) (hx : x ≤ hi) (r : Bool) :
    (C.decide op hi c false = some r → natCmp op x c = r) ∧ (C.decide op hi c true = some r → natCmp op c x = r) := by
  cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;>
    simp only [C.decide, natCmp, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] <;>
    constructor <;> intro h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
    simp only [beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      Bool.not_eq_true', bne_eq_false_iff_eq, Nat.beq_eq] at * <;> omega

theorem convTo_cty (o : Opts) (cp : CProg) (p : Prog) (t : Ty) (v : Val) (hs : t.isScalar = true)
    (h : HasTy p t v) : C.Sem.convTo cp (cty o t) (cval o v) = some (cval o v) := by
  cases t with
  | int w =>
    obtain ⟨x, rfl, hx⟩ := hasTy_int h
    simp only [cty, C.Sem.convTo, cval_int, castTo_uint, Nat.mod_eq_of_lt hx]
  | bool => obtain ⟨b, rfl⟩ := hasTy_bool h; simp [cty, C.Sem.convTo, C.Sem.castTo]
  | arr _ _ => simp [Ty.isScalar] at hs
  | record _ => simp [Ty.isScalar] at hs

theorem same_scalar (o : Opts) (p : Prog) (op : BinOp) (hc : op.isCompare = true) (t tb : Ty)
    (hty : BinTy op t tb) (x y v : Val) (hx : HasTy p t x) (hy : HasTy p tb y) (he : cval o x = cval o y)
    (hb : Lang.Sem.binop op x y = some v) : v = .bool (op == .eq || op == .le || op == .ge) := by
  have hl : op.isLogic = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  have hs : op.isShift = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  unfold BinTy at hty
  rw [if_neg (by simp [hl]), if_neg (by simp [hs])] at hty
  have int_case : ∀ (w w' : Width) (xv yv : UInt64), x = .int w xv → y = .int w' yv →
      v = .bool (op == .eq || op == .le || op == .ge) := by
    intro w w' xv yv ex ey
    subst ex ey
    simp only [cval_int, C.Sem.CVal.int.injEq] at he
    rw [binop_cmp op hc, he.2] at hb
    cases hb
    cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;>
      first | (simp [natCmp]; done) | (simp [natCmp]; decide)
  by_cases h3 : op = .eq ∨ op = .ne
  · rw [if_pos h3] at hty
    obtain ⟨rfl, hsc⟩ := hty
    cases t with
    | int w =>
      obtain ⟨xv, ex, _⟩ := hasTy_int hx
      obtain ⟨yv, ey, _⟩ := hasTy_int hy
      exact int_case w w xv yv ex ey
    | bool =>
      obtain ⟨p1, rfl⟩ := hasTy_bool hx
      obtain ⟨q1, rfl⟩ := hasTy_bool hy
      simp only [cval_bool, C.Sem.CVal.bool.injEq] at he
      subst he
      rcases h3 with rfl | rfl
      · simp only [Lang.Sem.binop, Option.some.injEq] at hb
        subst hb
        simp
        decide
      · simp only [Lang.Sem.binop, Option.some.injEq] at hb
        subst hb
        simp
        decide
    | arr _ _ => simp [Ty.isScalar] at hsc
    | record _ => simp [Ty.isScalar] at hsc
  · rw [if_neg h3] at hty
    obtain ⟨w, rfl, rfl⟩ := hty
    obtain ⟨xv, ex, _⟩ := hasTy_int hx
    obtain ⟨yv, ey, _⟩ := hasTy_int hy
    exact int_case w w xv yv ex ey

theorem binTy_cmp {op : BinOp} {ta tb : Ty} (hc : op.isCompare = true) (hty : BinTy op ta tb) :
    tb = ta ∧ ta.isScalar = true := by
  have hl : op.isLogic = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  have hs : op.isShift = false := by cases op <;> simp [BinOp.isCompare] at hc <;> rfl
  unfold BinTy at hty
  rw [if_neg (by simp [hl]), if_neg (by simp [hs])] at hty
  by_cases h3 : op = .eq ∨ op = .ne
  · rw [if_pos h3] at hty; exact ⟨hty.1.symm, hty.2⟩
  · rw [if_neg h3] at hty; obtain ⟨w, rfl, rfl⟩ := hty; exact ⟨rfl, rfl⟩

section
variable {g : C.Env} {cp : CProg} {op : BinOp} {a b : Expr} {ca cb : CExpr} {ta tb : Ty} {t0 : Nat}
  {pre : List CStmt} {cs : CS}

theorem cmp_ok (F : Ops2 g cp a b ca cb t0 pre cs) (sa : Shape g a ca) (sb : Shape g b cb)
    (hw : WT g (.bin op a b)) (hta : g.tyOf a = .ok ta) (htb : g.tyOf b = .ok tb) (hty : BinTy op ta tb)
    (hc : op.isCompare = true) :
    wpc (cmpC g.opts op ta ca cb) g (KPost g cp (.bin op a b) t0 pre cs) cs := by
  obtain ⟨wa, wb, _⟩ := wt_bin hw
  obtain ⟨rfl, hsc⟩ := binTy_cmp hc hty
  have hokb := fun st env cst cenv (hrel : ERel g cp st env cst cenv) => EOk_bin (op := op) hrel hw
  unfold cmpC
  cases hf : cmpFold op tb ca cb with
  | some r =>
    simp only [wpc_pure]
    refine KPost.pure F (Shape.plain rfl rfl) hokb ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
    obtain ⟨_, _, hx', hy', hb⟩ := evalE_bin_some.mp hv
    rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'
    have hvr : v = .bool r := by
      unfold cmpFold at hf
      by_cases hsame : ca.same cb = true
      · rw [if_pos hsame] at hf
        simp only [Option.some.injEq] at hf
        subst hf
        have e := CExpr.same_eq ca cb hsame
        subst e
        rw [hca] at hcb
        simp only [Option.some.injEq] at hcb
        exact same_scalar g.opts g.prog op hc tb tb hty x y v tx ty hcb hb
      · rw [if_neg hsame] at hf
        cases tb with
        | int w =>
          obtain ⟨xv, rfl, hxl⟩ := hasTy_int tx
          obtain ⟨yv, rfl, hyl⟩ := hasTy_int ty
          rw [binop_cmp op hc] at hb
          cases hb
          have hxl' : xv.toNat ≤ w.modulus - 1 := by unfold Width.modulus; omega
          have hyl' : yv.toNat ≤ w.modulus - 1 := by unfold Width.modulus; omega
          simp only at hf
          cases ha : ca.litVal? with
          | none =>
            cases hbl : cb.litVal? with
            | none => simp [ha, hbl] at hf
            | some c =>
              simp only [ha, hbl] at hf
              have hyc : yv.toNat = c := sb.lit c hbl st env _ hrel.typed hy
              rw [hyc, (decide_sound op hc _ c xv.toNat hxl' r).1 hf]
          | some c =>
            cases hbl : cb.litVal? with
            | some c' => simp [ha, hbl] at hf
            | none =>
              simp only [ha, hbl] at hf
              have hxc : xv.toNat = c := sa.lit c ha st env _ hrel.typed hx
              rw [hxc, (decide_sound op hc _ c yv.toNat hyl' r).2 hf]
        | bool => simp at hf
        | arr _ _ => simp at hf
        | record _ => simp at hf
    subst hvr
    rw [cval_bool]
    rfl
  | none =>
    simp only [wpc_bind, wpc_pure]
    have hv1 : ∀ st env cst cenv, ERel g cp st env cst cenv → EOk g a st env ∧ EOk g b st env →
        ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv →
        ∃ v, Lang.Sem.evalE g.prog st env a = some v ∧ C.Sem.evalC cp cst cenv ca = some (cval g.opts v) ∧
          C.Sem.convTo cp (cty g.opts tb) (cval g.opts v) = some (cval g.opts v) := by
      intro st env cst cenv hrel hk hr
      obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
      exact ⟨x, hx, hca, convTo_cty g.opts cp g.prog tb x hsc tx⟩
    refine wpc_mono (hide_frag a (cty g.opts tb) ca F ((ERes.stable g cp a ca).and (ERes.stable g cp b cb)) hv1
      sa.nocall) ?_
    rintro c1 cs1 ⟨pre1, ho1, _, _, F1⟩
    have hv2 : ∀ st env cst cenv, ERel g cp st env cst cenv → EOk g a st env ∧ EOk g b st env →
        (ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv) ∧ ERes g cp a c1 st env cst cenv →
        ∃ v, Lang.Sem.evalE g.prog st env b = some v ∧ C.Sem.evalC cp cst cenv cb = some (cval g.opts v) ∧
          C.Sem.convTo cp (cty g.opts tb) (cval g.opts v) = some (cval g.opts v) := by
      intro st env cst cenv hrel hk hr
      obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr.1
      exact ⟨y, hy, hcb, convTo_cty g.opts cp g.prog tb y hsc ty⟩
    refine wpc_mono (hide_frag b (cty g.opts tb) cb F1
      (((ERes.stable g cp a ca).and (ERes.stable g cp b cb)).and (ERes.stable g cp a c1)) hv2 sb.nocall) ?_
    rintro c2 cs2 ⟨pre2, ho2, _, _, F2⟩
    refine ⟨pre1 ++ pre2, by rw [ho2, ho1]; simp, Shape.plain rfl rfl, ?_⟩
    rw [← List.append_assoc]
    refine F2.conseq hokb ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr.1.1
    obtain ⟨_, _, hx', hy', hb⟩ := evalE_bin_some.mp hv
    rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'
    have h1 : (cmpSym op == "&&") = false ∧ (cmpSym op == "||") = false := by
      cases op <;> simp only [BinOp.isCompare, Bool.false_eq_true] at hc <;> decide
    rw [evalC_bin (cmpSym op) c1 c2 _ _ h1.1 h1.2 (hr.1.2 x hx) (hr.2 y hy)]
    exact cmp_val g.opts cp g.prog op hc tb tb hty x y v tx ty hb

end

/-! ## Division and shifts -/

/-- The value of an arithmetic operator on typed operands. -/
theorem bin_arith_val {g : C.Env} {op : BinOp} {a b : Expr} {w sw : Width} {st : Lang.Sem.St}
    {env : Lang.Sem.Env} (htyp : VarsTyped g st env) (wa : WT g a) (wb : WT g b)
    (hta : g.tyOf a = .ok (.int w)) (htb : g.tyOf b = .ok (.int sw)) (hc : op.isCompare = false)
    (hl : op.isLogic = false) (hsh : op.isShift = false → sw = w) {v : Val}
    (hv : Lang.Sem.evalE g.prog st env (.bin op a b) = some v) :
    ∃ xv yv r, Lang.Sem.evalE g.prog st env a = some (.int w xv) ∧ Lang.Sem.evalE g.prog st env b = some (.int sw yv) ∧
      xv.toNat < 2 ^ w.bits ∧ yv.toNat < 2 ^ sw.bits ∧ v = .int w r ∧
      r.toNat = natOp op w.bits xv.toNat yv.toNat := by
  obtain ⟨x, y, hx, hy, hb⟩ := evalE_bin_some.mp hv
  obtain ⟨xv, rfl, hxl⟩ := hasTy_int (evalE_hasTy g st env htyp a x _ wa hx hta)
  obtain ⟨yv, rfl, hyl⟩ := hasTy_int (evalE_hasTy g st env htyp b y _ wb hy htb)
  obtain ⟨r, hr1, hr2⟩ := binop_arith op hc hl w sw xv yv hxl (fun h => by rw [hsh h] at hyl; exact hyl)
  rw [hr1] at hb
  cases hb
  exact ⟨xv, yv, r, hx, hy, hxl, hyl, rfl, hr2⟩

theorem c_div (cp : CProg) (isDiv : Bool) (ub n x y : Nat) (hn : n ≤ ub) (hI : cp.intBits ≤ ub)
    (hx : x < 2 ^ n) (hy : y ≠ 0) :
    (C.Sem.binop cp (if isDiv then "/" else "%") (.int ub x) (.int ub y)).bind (C.Sem.castTo cp (.uint n))
      = some (.int n (natOp (if isDiv then .div else .mod) n x y)) := by
  have hI' : ¬ ub < cp.intBits := by omega
  cases isDiv <;>
    simp only [C.Sem.binop, C.Sem.isCompare, C.Sem.arith, String.reduceBEq, Bool.or_self, Bool.false_eq_true,
      if_false, if_true, Nat.max_self, hI', Option.bind_some, castTo_uint, natOp, Option.some.injEq,
      C.Sem.CVal.int.injEq, true_and, hy, beq_iff_eq, reduceCtorEq]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx)
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)

theorem c_shift (cp : CProg) (isShl : Bool) (ub n k x y : Nat) (hn : n ≤ ub) (hI : cp.intBits ≤ ub)
    (hx : x < 2 ^ n) (hy : y < n) :
    (C.Sem.binop cp (if isShl then "<<" else ">>") (.int ub x) (.int k y)).bind (C.Sem.castTo cp (.uint n))
      = some (.int n (natOp (if isShl then .shl else .shr) n x y)) := by
  have hI' : ¬ ub < cp.intBits := by omega
  have hy' : ¬ y ≥ ub := by omega
  have hy'' : ¬ y ≥ n := by omega
  cases isShl <;>
    simp only [C.Sem.binop, C.Sem.isCompare, String.reduceBEq, Bool.or_self, Bool.false_eq_true,
      if_false, if_true, hI', hy', hy'', decide_false, Option.bind_some, castTo_uint, natOp, Option.some.injEq,
      C.Sem.CVal.int.injEq, true_and, reduceCtorEq, Bool.or_false]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)
  · exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)

theorem natOp_lt (op : BinOp) (hc : op.isCompare = false) (hl : op.isLogic = false) (n x y : Nat)
    (hx : x < 2 ^ n) (hy : op.isShift = false → y < 2 ^ n) : natOp op n x y < 2 ^ n := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  cases op <;> simp only [BinOp.isCompare, BinOp.isLogic, BinOp.isShift, Bool.true_eq_false, forall_const] at hc hl hy <;>
    simp only [natOp]
  · exact Nat.mod_lt _ hp
  · exact Nat.mod_lt _ hp
  · exact Nat.mod_lt _ hp
  · split
    · exact hp
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  · split
    · exact hp
    · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx
  · exact Nat.lt_of_le_of_lt Nat.and_le_left hx
  · exact Nat.or_lt_two_pow hx hy
  · exact Nat.xor_lt_two_pow hx hy
  · split
    · exact hp
    · exact Nat.mod_lt _ hp
  · split
    · exact hp
    · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx

theorem helper_name (isDiv : Bool) (w : Width) :
    C.Sem.helper (s!"ember_{if isDiv then "div" else "mod"}{w.bits}") = some (w.bits, isDiv) := by
  cases isDiv <;> cases w <;> rfl

theorem evalC_lit_suffix (cp : CProg) (cst : C.Sem.St) (cenv : C.Sem.Env) (w : Width) (n : Nat)
    (hn : n < 2 ^ 16) (h16 : 16 ≤ cp.intBits) (h32 : 32 ≤ cp.longBits) :
    ∃ b, C.Sem.evalC cp cst cenv (.lit n (suffix w)) = some (.int b n) := by
  have hb : ∃ b, C.Sem.litBits cp (suffix w) = some b ∧ 16 ≤ b := by
    cases w
    · exact ⟨cp.intBits, rfl, h16⟩
    · exact ⟨cp.intBits, rfl, h16⟩
    · exact ⟨cp.longBits, rfl, by omega⟩
    · exact ⟨64, rfl, by decide⟩
  obtain ⟨b, hb, hle⟩ := hb
  have hlt : n < 2 ^ b := Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hle)
  exact ⟨b, by simp only [C.Sem.evalC, hb, hlt, if_true]⟩

section
variable {g : C.Env} {cp : CProg} {a b : Expr} {ca cb : CExpr} {t0 : Nat} {pre : List CStmt} {cs : CS}

theorem div_ok (isDiv : Bool) (F : Ops2 g cp a b ca cb t0 pre cs) (sa : Shape g a ca) (sb : Shape g b cb)
    {w : Width} (hw : WT g (.bin (if isDiv then .div else .mod) a b)) (hta : g.tyOf a = .ok (.int w))
    (htb : g.tyOf b = .ok (.int w)) :
    wpc (divC g.opts isDiv w ca cb) g (KPost g cp (.bin (if isDiv then .div else .mod) a b) t0 pre cs) cs := by
  have hfacts : (if isDiv then BinOp.div else BinOp.mod).isCompare = false ∧
      (if isDiv then BinOp.div else BinOp.mod).isLogic = false ∧
      ((if isDiv then "/" else "%") == "&&") = false ∧ ((if isDiv then "/" else "%") == "||") = false := by
    cases isDiv <;> decide
  generalize hop : (if isDiv then BinOp.div else BinOp.mod) = op at hw hfacts ⊢
  obtain ⟨hc, hl, hs1, hs2⟩ := hfacts
  obtain ⟨wa, wb, _⟩ := wt_bin hw
  have hokb := fun st env cst cenv (hrel : ERel g cp st env cst cenv) => EOk_bin (op := op) hrel hw
  -- the values at a state
  have val : ∀ {st env cst cenv}, ERel g cp st env cst cenv →
      ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv → ∀ {v}, Lang.Sem.evalE g.prog st env (.bin op a b) = some v →
      ∃ (xv yv r : UInt64), Lang.Sem.evalE g.prog st env b = some (.int w yv) ∧ xv.toNat < 2 ^ w.bits ∧ yv.toNat < 2 ^ w.bits ∧
        C.Sem.evalC cp cst cenv ca = some (.int w.bits xv.toNat) ∧ C.Sem.evalC cp cst cenv cb = some (.int w.bits yv.toNat) ∧
        v = .int w r ∧ r.toNat = natOp op w.bits xv.toNat yv.toNat := by
    intro st env cst cenv hrel hr v hv
    obtain ⟨xv, yv, r, hx, hy, hxl, hyl, rfl, hr2⟩ := bin_arith_val hrel.typed wa wb hta htb hc hl (fun _ => rfl) hv
    have h1 := hr.1 _ hx
    have h2 := hr.2 _ hy
    rw [cval_int] at h1 h2
    exact ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩
  unfold divC
  cases hlv : cb.litVal? with
  | some c =>
    simp only [wpc_pure]
    by_cases h0 : c = 0
    · subst h0
      simp only [beq_self_eq_true, if_true]
      refine KPost.pure F ⟨rfl, fun n s h => by simp [litC] at h, fun n hn st env x htyp hx => ?_⟩ hokb ?_
      · obtain ⟨xv, yv, r, _, hy, _, _, rfl, hr2⟩ := bin_arith_val htyp wa wb hta htb hc hl (fun _ => rfl) hx
        have hy0 : yv.toNat = 0 := sb.lit 0 hlv st env _ htyp hy
        have hn0 : n = 0 := by simpa [litC, CExpr.litVal?] using hn.symm
        subst hop
        show r.toNat = n
        rw [hr2, hy0, hn0]
        cases isDiv <;> simp [natOp]
      · intro st env cst cenv hrel hk hr v hv
        obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr hv
        have hy0 : yv.toNat = 0 := sb.lit 0 hlv st env _ hrel.typed hy
        rw [cval_int, evalC_litC cp cst cenv w 0 (Nat.two_pow_pos _) hrel.i16 hrel.l32, hr2, hy0]
        subst hop
        cases isDiv <;> simp [natOp]
    · have hb0 : (c == 0) = false := by simpa using h0
      simp only [hb0, Bool.false_eq_true, if_false]
      refine KPost.pure F (Shape.plain rfl rfl) hokb ?_
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr hv
      have hyc : yv.toNat = c := sb.lit c hlv st env _ hrel.typed hy
      rw [cval_int, evalC_arithE g.opts hrel.ints w _ hs1 hs2 ca cb _ _ _ _ hxl hyl h1 h2, hr2, ← hop]
      exact c_div cp isDiv _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl (by rw [hyc]; exact h0)
  | none =>
    simp only []
    by_cases hz : (g.opts.profile == Profile.sdccZ80) = true
    · simp only [hz, if_true, wpc_pure]
      refine KPost.pure F (Shape.plain (by simp only [C.Sem.asCall, helper_name]; rfl) rfl) hokb ?_
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr hv
      rw [cval_int, hr2, ← hop]
      simp only [C.Sem.evalC, helper_name, C.Sem.evalCs, h1, h2, C.Sem.helperVal, Nat.mod_eq_of_lt hxl,
        Nat.mod_eq_of_lt hyl]
      cases isDiv <;> simp [natOp]
    · simp only [hz, Bool.false_eq_true, if_false, wpc_bind, wpc_pure]
      have hv1 : ∀ st env cst cenv, ERel g cp st env cst cenv → EOk g a st env ∧ EOk g b st env →
          ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv →
          ∃ v, Lang.Sem.evalE g.prog st env b = some v ∧ C.Sem.evalC cp cst cenv cb = some (cval g.opts v) ∧
            C.Sem.convTo cp (.uint w.bits) (cval g.opts v) = some (cval g.opts v) := by
        intro st env cst cenv hrel hk hr
        obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
        exact ⟨y, hy, hcb, convTo_cty g.opts cp g.prog (.int w) y rfl ty⟩
      refine wpc_mono (hide_frag b (.uint w.bits) cb F ((ERes.stable g cp a ca).and (ERes.stable g cp b cb)) hv1
        sb.nocall) ?_
      rintro d cs1 ⟨pre1, ho1, _, _, F1⟩
      refine ⟨pre1, ho1, Shape.plain rfl rfl, F1.conseq hokb ?_⟩
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr.1 hv
      have hd := hr.2 _ hy
      rw [cval_int] at hd
      obtain ⟨bz, hz0⟩ := evalC_lit_suffix cp cst cenv w 0 (by decide) hrel.i16 hrel.l32
      have hcmp : C.Sem.evalC cp cst cenv (.bin "==" d (.lit 0 (suffix w))) = some (.bool (yv.toNat == 0)) := by
        rw [evalC_bin "==" _ _ _ _ rfl rfl hd hz0]
        simp [C.Sem.binop, C.Sem.isCompare, C.Sem.compare]
      rw [cval_int, evalC_cast, evalC_cond _ _ _ _ _ hcmp rfl, hr2, ← hop]
      by_cases hy0 : yv.toNat = 0
      · simp only [hy0, beq_self_eq_true, if_true, evalC_litC cp cst cenv w 0 (Nat.two_pow_pos _) hrel.i16 hrel.l32]
        cases isDiv <;> simp [natOp, castTo_uint]
      · have hb0 : (yv.toNat == 0) = false := by simpa using hy0
        simp only [hb0, Bool.false_eq_true, if_false]
        rw [evalC_arithE g.opts hrel.ints w _ hs1 hs2 ca d _ _ _ _ hxl hyl h1 hd,
          c_div cp isDiv _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl hy0]
        simp only [Option.bind_some, castTo_uint]
        rw [Nat.mod_eq_of_lt]
        exact natOp_lt _ (by cases isDiv <;> rfl) (by cases isDiv <;> rfl) _ _ _ hxl (fun _ => hyl)

end

/-- `(T)((U)a << s)` -/
theorem evalC_shiftE {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} (o : Opts)
    (hI : cp.intBits = o.profile.intBits) (w : Width) (sym : String) (h1 : (sym == "&&") = false)
    (h2 : (sym == "||") = false) (ca s : CExpr) (kx k x y : Nat) (hx : x < 2 ^ w.bits)
    (ha : C.Sem.evalC cp cst cenv ca = some (.int kx x)) (hb : C.Sem.evalC cp cst cenv s = some (.int k y)) :
    C.Sem.evalC cp cst cenv (shiftE o w sym ca s)
      = (C.Sem.binop cp sym (.int (ubits cp w) x) (.int k y)).bind (C.Sem.castTo cp (.uint w.bits)) := by
  have ea : C.Sem.evalC cp cst cenv (.cast (opTy o w) ca) = some (.int (ubits cp w) x) := by
    rw [evalC_cast, ha]; exact castTo_opTy o cp hI w kx x hx
  unfold shiftE
  rw [evalC_cast, evalC_bin sym _ _ _ _ h1 h2 ea hb]

section
variable {g : C.Env} {cp : CProg} {a b : Expr} {ca cb : CExpr} {t0 : Nat} {pre : List CStmt} {cs : CS}

theorem shift_ok (isShl : Bool) (F : Ops2 g cp a b ca cb t0 pre cs) (sb : Shape g b cb)
    {w sw : Width} (hw : WT g (.bin (if isShl then .shl else .shr) a b)) (hta : g.tyOf a = .ok (.int w))
    (htb : g.tyOf b = .ok (.int sw)) :
    wpc (shiftC g.opts isShl w sw ca cb) g (KPost g cp (.bin (if isShl then .shl else .shr) a b) t0 pre cs) cs := by
  have hfacts : (if isShl then BinOp.shl else BinOp.shr).isCompare = false ∧
      (if isShl then BinOp.shl else BinOp.shr).isLogic = false ∧
      (if isShl then BinOp.shl else BinOp.shr).isShift = true ∧
      ((if isShl then "<<" else ">>") == "&&") = false ∧ ((if isShl then "<<" else ">>") == "||") = false := by
    cases isShl <;> decide
  have hbig : ∀ y, y ≥ w.bits → natOp (if isShl then BinOp.shl else BinOp.shr) w.bits = fun x y' =>
      natOp (if isShl then BinOp.shl else BinOp.shr) w.bits x y' := fun _ _ => rfl
  have hzero : ∀ x y, y ≥ w.bits → natOp (if isShl then BinOp.shl else BinOp.shr) w.bits x y = 0 := by
    intro x y hy; cases isShl <;> simp [natOp, hy]
  generalize hop : (if isShl then BinOp.shl else BinOp.shr) = op at hw hfacts hzero ⊢
  obtain ⟨hc, hl, hsh, hs1, hs2⟩ := hfacts
  obtain ⟨wa, wb, _⟩ := wt_bin hw
  have hokb := fun st env cst cenv (hrel : ERel g cp st env cst cenv) => EOk_bin (op := op) hrel hw
  have h64 := bits_le w
  have val : ∀ {st env cst cenv}, ERel g cp st env cst cenv →
      ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv → ∀ {v}, Lang.Sem.evalE g.prog st env (.bin op a b) = some v →
      ∃ (xv yv r : UInt64), Lang.Sem.evalE g.prog st env b = some (.int sw yv) ∧ xv.toNat < 2 ^ w.bits ∧ yv.toNat < 2 ^ sw.bits ∧
        C.Sem.evalC cp cst cenv ca = some (.int w.bits xv.toNat) ∧ C.Sem.evalC cp cst cenv cb = some (.int sw.bits yv.toNat) ∧
        v = .int w r ∧ r.toNat = natOp op w.bits xv.toNat yv.toNat := by
    intro st env cst cenv hrel hr v hv
    obtain ⟨xv, yv, r, hx, hy, hxl, hyl, rfl, hr2⟩ := bin_arith_val hrel.typed wa wb hta htb hc hl
      (fun h => by rw [hsh] at h; exact absurd h (by simp)) hv
    have h1 := hr.1 _ hx
    have h2 := hr.2 _ hy
    rw [cval_int] at h1 h2
    exact ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩
  unfold shiftC
  cases hlv : cb.litVal? with
  | some c =>
    simp only [wpc_pure]
    by_cases h0 : c ≥ w.bits
    · simp only [h0, if_true]
      refine KPost.pure F ⟨rfl, fun n s h => by simp [litC] at h, fun n hn st env x htyp hx => ?_⟩ hokb ?_
      · obtain ⟨xv, yv, r, _, hy, _, _, rfl, hr2⟩ := bin_arith_val htyp wa wb hta htb hc hl
          (fun h => by rw [hsh] at h; exact absurd h (by simp)) hx
        have hyc : yv.toNat = c := sb.lit c hlv st env _ htyp hy
        have hn0 : n = 0 := by simpa [litC, CExpr.litVal?] using hn.symm
        show r.toNat = n
        rw [hr2, hn0]
        exact hzero _ _ (by rw [hyc]; exact h0)
      · intro st env cst cenv hrel hk hr v hv
        obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr hv
        have hyc : yv.toNat = c := sb.lit c hlv st env _ hrel.typed hy
        rw [cval_int, evalC_litC cp cst cenv w 0 (Nat.two_pow_pos _) hrel.i16 hrel.l32, hr2,
          hzero _ _ (by rw [hyc]; exact h0)]
    · simp only [h0, if_false]
      refine KPost.pure F (Shape.plain rfl rfl) hokb ?_
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr hv
      have hyc : yv.toNat = c := sb.lit c hlv st env _ hrel.typed hy
      rw [cval_int, evalC_shiftE g.opts hrel.ints w _ hs1 hs2 ca cb _ _ _ _ hxl h1 h2, hr2, ← hop]
      exact c_shift cp isShl _ _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl (by omega)
  | none =>
    simp only [wpc_bind, wpc_pure]
    have hv1 : ∀ st env cst cenv, ERel g cp st env cst cenv → EOk g a st env ∧ EOk g b st env →
        ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv →
        ∃ v, Lang.Sem.evalE g.prog st env b = some v ∧ C.Sem.evalC cp cst cenv cb = some (cval g.opts v) ∧
          C.Sem.convTo cp (.uint sw.bits) (cval g.opts v) = some (cval g.opts v) := by
      intro st env cst cenv hrel hk hr
      obtain ⟨x, y, hx, hy, hca, hcb, tx, ty⟩ := ops_vals hrel wa wb hta htb hk hr
      exact ⟨y, hy, hcb, convTo_cty g.opts cp g.prog (.int sw) y rfl ty⟩
    refine wpc_mono (hide_frag b (.uint sw.bits) cb F ((ERes.stable g cp a ca).and (ERes.stable g cp b cb)) hv1
      sb.nocall) ?_
    rintro d cs1 ⟨pre1, ho1, _, _, F1⟩
    by_cases hm : sw.modulus ≤ w.bits
    · simp only [hm, if_true]
      refine ⟨pre1, ho1, Shape.plain rfl rfl, F1.conseq hokb ?_⟩
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr.1 hv
      have hd := hr.2 _ hy
      rw [cval_int] at hd
      rw [cval_int, evalC_shiftE g.opts hrel.ints w _ hs1 hs2 ca d _ _ _ _ hxl h1 hd, hr2, ← hop]
      exact c_shift cp isShl _ _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl (by unfold Width.modulus at hm; omega)
    · simp only [hm, if_false]
      refine ⟨pre1, ho1, Shape.plain rfl rfl, F1.conseq hokb ?_⟩
      intro st env cst cenv hrel hk hr v hv
      obtain ⟨xv, yv, r, hy, hxl, hyl, h1, h2, rfl, hr2⟩ := val hrel hr.1 hv
      have hd := hr.2 _ hy
      rw [cval_int] at hd
      obtain ⟨bz, hz0⟩ := evalC_lit_suffix cp cst cenv sw w.bits (by omega) hrel.i16 hrel.l32
      have hcmp : C.Sem.evalC cp cst cenv (.bin ">=" d (.lit w.bits (suffix sw)))
          = some (.bool (decide (yv.toNat ≥ w.bits))) := by
        rw [evalC_bin ">=" _ _ _ _ rfl rfl hd hz0]
        simp [C.Sem.binop, C.Sem.isCompare, C.Sem.compare]
      rw [cval_int, evalC_cast, evalC_cond _ _ _ _ _ hcmp rfl, hr2]
      by_cases hy0 : yv.toNat ≥ w.bits
      · simp only [hy0, decide_true, if_true, evalC_litC cp cst cenv w 0 (Nat.two_pow_pos _) hrel.i16 hrel.l32,
          hzero _ _ hy0]
        simp [castTo_uint]
      · simp only [hy0, decide_false, Bool.false_eq_true, if_false]
        rw [evalC_shiftE g.opts hrel.ints w _ hs1 hs2 ca d _ _ _ _ hxl h1 hd, ← hop,
          c_shift cp isShl _ _ _ _ _ (ubits_ge cp w) (ubits_int cp w) hxl (by omega)]
        simp only [Option.bind_some, castTo_uint]
        rw [Nat.mod_eq_of_lt]
        exact natOp_lt _ (by cases isShl <;> rfl) (by cases isShl <;> rfl) _ _ _ hxl
          (fun h => by cases isShl <;> simp [BinOp.isShift] at h)

end

theorem wpc_tyOf {g : C.Env} {cs : CS} (e : Expr) (Q : Ty → CS → Prop) :
    wpc (tyOf e) g Q cs ↔ ∀ t, g.tyOf e = .ok t → Q t cs := by
  unfold tyOf
  rw [wpc_pureE]

section
variable {g : C.Env} {cp : CProg} {op : BinOp} {a b : Expr} {ca cb : CExpr} {ta tb : Ty} {t0 : Nat}
  {pre : List CStmt} {cs : CS}

/-- **A binary operator**: after the fragment of its operands, what
`binC` emits has the value of the Ember expression. -/
theorem binC_ok (F : Ops2 g cp a b ca cb t0 pre cs) (sa : Shape g a ca) (sb : Shape g b cb)
    (hw : WT g (.bin op a b)) (hta : g.tyOf a = .ok ta) (htb : g.tyOf b = .ok tb) (hty : BinTy op ta tb)
    (hbug : g.opts.bugDropCast = false) :
    wpc (binC g.opts op ta b ca cb) g (KPost g cp (.bin op a b) t0 pre cs) cs := by
  unfold binC
  by_cases hl : op.isLogic = true
  · rw [if_pos hl, wpc_pure]
    exact logic_ok F hw hta htb hty hl
  rw [if_neg hl]
  by_cases hc : op.isCompare = true
  · rw [if_pos hc]
    exact cmp_ok F sa sb hw hta htb hty hc
  rw [if_neg hc]
  unfold BinTy at hty
  rw [if_neg hl] at hty
  cases op <;> simp only [BinOp.isLogic, BinOp.isCompare, BinOp.isShift, not_true_eq_false, Bool.false_eq_true,
    if_false, if_true, reduceCtorEq, or_self, not_false_eq_true] at hl hc hty
  case add =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [hbug, Bool.false_eq_true, if_false, wpc_pure]
    exact simple_ok F hw hta htb "+" rfl
  case sub =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [wpc_pure]
    exact simple_ok F hw hta htb "-" rfl
  case mul =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [wpc_pure]
    exact simple_ok F hw hta htb "*" rfl
  case band =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [wpc_pure]
    exact simple_ok F hw hta htb "&" rfl
  case bor =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [wpc_pure]
    exact simple_ok F hw hta htb "|" rfl
  case bxor =>
    obtain ⟨w, rfl, rfl⟩ := hty
    simp only [wpc_pure]
    exact simple_ok F hw hta htb "^" rfl
  case div =>
    obtain ⟨w, rfl, rfl⟩ := hty
    exact div_ok true F sa sb hw hta htb
  case mod =>
    obtain ⟨w, rfl, rfl⟩ := hty
    exact div_ok false F sa sb hw hta htb
  case shl =>
    obtain ⟨⟨w, rfl⟩, ⟨sw, rfl⟩⟩ := hty
    simp only [wpc_bind, wpc_tyOf]
    intro t ht
    rw [htb] at ht
    cases ht
    exact shift_ok true F sb hw hta htb
  case shr =>
    obtain ⟨⟨w, rfl⟩, ⟨sw, rfl⟩⟩ := hty
    simp only [wpc_bind, wpc_tyOf]
    intro t ht
    rw [htb] at ht
    cases ht
    exact shift_ok false F sb hw hta htb

end

/-! ## Unary operators, casts, conditionals -/

theorem not_mod_pow (x n m : Nat) (hx : x < 2 ^ n) (hnm : n ≤ m) : (2 ^ m - 1 - x) % 2 ^ n = 2 ^ n - 1 - x := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [Nat.pow_add]
  have hK : 0 < 2 ^ d := Nat.two_pow_pos d
  obtain ⟨K, hK'⟩ : ∃ K, 2 ^ d = K + 1 := ⟨2 ^ d - 1, by omega⟩
  rw [hK', Nat.mul_succ]
  have : 2 ^ n * K + 2 ^ n - 1 - x = (2 ^ n - 1 - x) + 2 ^ n * K := by omega
  rw [this, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem evalE_un_some {p : Prog} {st : Lang.Sem.St} {env : Lang.Sem.Env} {op : UnOp} {a : Expr} {v : Val}
    (h : Lang.Sem.evalE p st env (.un op a) = some v) : ∃ x, Lang.Sem.evalE p st env a = some x := by
  simp only [Lang.Sem.evalE] at h
  cases ha : Lang.Sem.evalE p st env a with
  | none => cases op <;> simp [ha] at h
  | some x => exact ⟨x, rfl⟩

section
variable {g : C.Env} {cp : CProg} {a : Expr} {ca : CExpr} {ta : Ty} {t0 : Nat} {pre : List CStmt} {cs : CS}

theorem unC_ok (op : UnOp) (F : Frag g cp t0 cs.tmp pre (EOk g a) (ERes g cp a ca)) (hw : WT g (.un op a))
    (hta : g.tyOf a = .ok ta) :
    wpc (unC g.opts op ta ca) g (KPost g cp (.un op a) t0 pre cs) cs := by
  simp only [WT] at hw
  obtain ⟨wa, hty⟩ := hw
  have hval : ∀ {st env cst cenv}, ERel g cp st env cst cenv → EOk g a st env → ERes g cp a ca st env cst cenv →
      ∃ x, Lang.Sem.evalE g.prog st env a = some x ∧ C.Sem.evalC cp cst cenv ca = some (cval g.opts x) ∧
        HasTy g.prog ta x := by
    intro st env cst cenv hrel hk hr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact ⟨x, hx, hr x hx, evalE_hasTy g st env hrel.typed a x ta wa hx hta⟩
  cases op with
  | lnot =>
    simp only [if_true] at hty
    rw [hta] at hty
    cases hty
    simp only [unC, wpc_pure]
    refine KPost.pure F (Shape.plain rfl rfl) ?_ ?_
    · intro st env cst cenv hrel
      constructor
      · intro h
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
        obtain ⟨x, hx⟩ := evalE_un_some hv
        simp [EOk, hx]
      · intro hk
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨p, rfl⟩ := hasTy_bool (evalE_hasTy g st env hrel.typed a x _ wa hx hta)
        simp [EOk, Lang.Sem.evalE, hx]
    · intro st env cst cenv hrel hk hr v hv
      obtain ⟨x, hx, hca, tx⟩ := hval hrel hk hr
      obtain ⟨p, rfl⟩ := hasTy_bool tx
      simp only [Lang.Sem.evalE, hx, Option.some.injEq] at hv
      subst hv
      rw [cval_bool] at hca ⊢
      simp [C.Sem.evalC, hca, C.Sem.unop, C.Sem.truthy]
  | bnot =>
    simp only [reduceCtorEq, if_false] at hty
    obtain ⟨w, hw2⟩ := hty
    rw [hta] at hw2
    cases hw2
    simp only [unC, wpc_pure]
    refine KPost.pure F (Shape.plain rfl rfl) ?_ ?_
    · intro st env cst cenv hrel
      constructor
      · intro h
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
        obtain ⟨x, hx⟩ := evalE_un_some hv
        simp [EOk, hx]
      · intro hk
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨xv, rfl, _⟩ := hasTy_int (evalE_hasTy g st env hrel.typed a x _ wa hx hta)
        simp [EOk, Lang.Sem.evalE, hx]
    · intro st env cst cenv hrel hk hr v hv
      obtain ⟨x, hx, hca, tx⟩ := hval hrel hk hr
      obtain ⟨xv, rfl, hxl⟩ := hasTy_int tx
      simp only [Lang.Sem.evalE, hx, Option.some.injEq] at hv
      subst hv
      rw [cval_int] at hca ⊢
      have ea : C.Sem.evalC cp cst cenv (.cast (opTy g.opts w) ca) = some (.int (ubits cp w) xv.toNat) := by
        rw [evalC_cast, hca]; exact castTo_opTy g.opts cp hrel.ints w _ _ hxl
      have hI' : ¬ ubits cp w < cp.intBits := by have := ubits_int cp w; omega
      have eu : C.Sem.evalC cp cst cenv (.un "~" (.cast (opTy g.opts w) ca))
          = some (.int (ubits cp w) (2 ^ ubits cp w - 1 - xv.toNat)) := by
        rw [evalC_un, ea]
        simp only [Option.bind_some, C.Sem.unop, String.reduceBEq, Bool.false_eq_true, if_false, if_true, hI']
      rw [evalC_cast, eu]
      simp only [Option.bind_some, castTo_uint, mask_toNat, UInt64.toNat_not]
      rw [show UInt64.size = 2 ^ 64 from rfl, not_mod_pow _ _ _ hxl (ubits_ge cp w), not_mod_pow _ _ 64 hxl (bits_le w)]
  | neg =>
    simp only [reduceCtorEq, if_false] at hty
    obtain ⟨w, hw2⟩ := hty
    rw [hta] at hw2
    cases hw2
    simp only [unC, wpc_pure]
    refine KPost.pure F (Shape.plain rfl rfl) ?_ ?_
    · intro st env cst cenv hrel
      constructor
      · intro h
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
        obtain ⟨x, hx⟩ := evalE_un_some hv
        simp [EOk, hx]
      · intro hk
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨xv, rfl, _⟩ := hasTy_int (evalE_hasTy g st env hrel.typed a x _ wa hx hta)
        simp [EOk, Lang.Sem.evalE, hx]
    · intro st env cst cenv hrel hk hr v hv
      obtain ⟨x, hx, hca, tx⟩ := hval hrel hk hr
      obtain ⟨xv, rfl, hxl⟩ := hasTy_int tx
      simp only [Lang.Sem.evalE, hx, Option.some.injEq] at hv
      subst hv
      rw [cval_int] at hca ⊢
      have ea : C.Sem.evalC cp cst cenv (.cast (opTy g.opts w) ca) = some (.int (ubits cp w) xv.toNat) := by
        rw [evalC_cast, hca]; exact castTo_opTy g.opts cp hrel.ints w _ _ hxl
      have e0 : C.Sem.evalC cp cst cenv (.lit 0 "u") = some (.int cp.intBits 0) := by
        simp [C.Sem.evalC, C.Sem.litBits, Nat.two_pow_pos]
      have hI := ubits_int cp w
      have hI' : ¬ ubits cp w < cp.intBits := by omega
      rw [evalC_cast, evalC_bin "-" _ _ _ _ rfl rfl e0 ea]
      simp only [C.Sem.binop, C.Sem.isCompare, C.Sem.arith, String.reduceBEq, Bool.or_self, Bool.false_eq_true,
        if_false, if_true, Nat.max_eq_right hI, hI', Option.bind_some, castTo_uint, mask_toNat, UInt64.toNat_sub,
        Option.some.injEq, C.Sem.CVal.int.injEq, true_and]
      rw [sub_mod_pow 0 xv.toNat w.bits (ubits cp w) (Nat.le_of_lt hxl) (ubits_ge cp w)]
      have hx64 := xv.toNat_lt
      have e : 2 ^ 64 - xv.toNat + (0 : UInt64).toNat = 2 ^ 64 + 0 - xv.toNat := by
        simp only [UInt64.toNat_zero]; omega
      rw [e, sub_mod_pow 0 xv.toNat w.bits 64 (Nat.le_of_lt hxl) (bits_le w)]

end

section
variable {g : C.Env} {cp : CProg} {a : Expr} {ca : CExpr} {ta : Ty} {t0 : Nat} {pre : List CStmt} {cs : CS}

theorem castC_ok (w : Width) (F : Frag g cp t0 cs.tmp pre (EOk g a) (ERes g cp a ca)) (sa : Shape g a ca)
    (hw : WT g (.cast w a)) (hta : g.tyOf a = .ok ta) :
    KPost g cp (.cast w a) t0 pre cs (castC w ta ca) cs := by
  simp only [WT] at hw
  obtain ⟨wa, t, ht, hsc⟩ := hw
  rw [hta] at ht
  cases ht
  have hok : ∀ st env cst cenv, ERel g cp st env cst cenv → (EOk g (.cast w a) st env ↔ EOk g a st env) := by
    intro st env cst cenv hrel
    constructor
    · intro h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      simp only [Lang.Sem.evalE] at hv
      cases ha : Lang.Sem.evalE g.prog st env a with
      | none => simp [ha] at hv
      | some x => simp [EOk, ha]
    · intro hk
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
      have tx := evalE_hasTy g st env hrel.typed a x _ wa hx hta
      cases ta with
      | int w0 => obtain ⟨xv, rfl, _⟩ := hasTy_int tx; simp [EOk, Lang.Sem.evalE, hx]
      | bool => obtain ⟨p, rfl⟩ := hasTy_bool tx; simp [EOk, Lang.Sem.evalE, hx]
      | arr _ _ => simp [Ty.isScalar] at hsc
      | record _ => simp [Ty.isScalar] at hsc
  cases ta with
  | bool =>
    refine KPost.pure F (Shape.plain rfl rfl) hok ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    obtain ⟨p, rfl⟩ := hasTy_bool (evalE_hasTy g st env hrel.typed a x _ wa hx hta)
    have hca := hr _ hx
    rw [cval_bool] at hca
    simp only [Lang.Sem.evalE, hx, Option.some.injEq] at hv
    subst hv
    obtain ⟨b1, h1⟩ := evalC_lit_suffix cp cst cenv w 1 (by decide) hrel.i16 hrel.l32
    obtain ⟨b0, h0⟩ := evalC_lit_suffix cp cst cenv w 0 (by decide) hrel.i16 hrel.l32
    have hw8 := bits_pos w
    have h256 : 1 < 2 ^ w.bits := Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hw8)
    show C.Sem.evalC cp cst cenv (.cast (.uint w.bits) (.cond ca (.lit 1 (suffix w)) (.lit 0 (suffix w)))) = _
    rw [cval_int, evalC_cast, evalC_cond _ _ _ _ p hca rfl]
    cases p
    · simp [h0, castTo_uint]
    · simp [h1, castTo_uint, Nat.mod_eq_of_lt h256]
  | int w0 =>
    have hshape : Shape g (.cast w a) (.cast (.uint w.bits) ca) := by
      refine Shape.plain rfl ?_
      cases ca <;> first | rfl | (rename_i n s; exact absurd rfl (sa.nolit n s))
    refine KPost.pure F hshape hok ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    obtain ⟨xv, rfl, _⟩ := hasTy_int (evalE_hasTy g st env hrel.typed a x _ wa hx hta)
    have hca := hr _ hx
    rw [cval_int] at hca
    simp only [Lang.Sem.evalE, hx, Option.some.injEq] at hv
    subst hv
    show C.Sem.evalC cp cst cenv (.cast (.uint w.bits) ca) = _
    rw [cval_int, evalC_cast, hca, mask_toNat]
    rfl
  | arr _ _ => simp [Ty.isScalar] at hsc
  | record _ => simp [Ty.isScalar] at hsc

end

section
variable {g : C.Env} {cp : CProg} {c a b : Expr} {cc ca cb : CExpr} {ta : Ty} {t0 : Nat} {pre : List CStmt}
  {cs : CS}

theorem condC_ok
    (F : Frag g cp t0 cs.tmp pre (fun st env => EOk g c st env ∧ EOk g a st env ∧ EOk g b st env)
      (fun st env cst cenv => ERes g cp c cc st env cst cenv ∧ ERes g cp a ca st env cst cenv ∧
        ERes g cp b cb st env cst cenv))
    (hw : WT g (.cond c a b)) (hta : g.tyOf a = .ok ta) :
    KPost g cp (.cond c a b) t0 pre cs (condC ta cc ca cb) cs := by
  simp only [WT] at hw
  obtain ⟨wc, wa, wb, htc, t, ht, htb, hsc⟩ := hw
  rw [hta] at ht
  cases ht
  have hok : ∀ st env cst cenv, ERel g cp st env cst cenv →
      (EOk g (.cond c a b) st env ↔ EOk g c st env ∧ EOk g a st env ∧ EOk g b st env) := by
    intro st env cst cenv hrel
    unfold EOk
    simp only [Lang.Sem.evalE]
    cases Lang.Sem.evalE g.prog st env c <;> cases Lang.Sem.evalE g.prog st env a <;>
      cases Lang.Sem.evalE g.prog st env b <;> simp
  have hval : ∀ {st env cst cenv}, ERel g cp st env cst cenv →
      EOk g c st env ∧ EOk g a st env ∧ EOk g b st env →
      ERes g cp c cc st env cst cenv ∧ ERes g cp a ca st env cst cenv ∧ ERes g cp b cb st env cst cenv →
      ∀ {v}, Lang.Sem.evalE g.prog st env (.cond c a b) = some v →
      ∃ (p : Bool) (x y : Val), C.Sem.evalC cp cst cenv cc = some (.bool p) ∧
        C.Sem.evalC cp cst cenv ca = some (cval g.opts x) ∧ C.Sem.evalC cp cst cenv cb = some (cval g.opts y) ∧
        HasTy g.prog ta x ∧ HasTy g.prog ta y ∧ v = if p then x else y := by
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hk.1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk.2.1
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hk.2.2
    obtain ⟨p, rfl⟩ := hasTy_bool (evalE_hasTy g st env hrel.typed c cv _ wc hcv htc)
    have h1 := hr.1 _ hcv
    rw [cval_bool] at h1
    simp only [Lang.Sem.evalE, hcv, hx, hy, Option.some.injEq, Val.toBool] at hv
    exact ⟨p, x, y, h1, hr.2.1 _ hx, hr.2.2 _ hy, evalE_hasTy g st env hrel.typed a x _ wa hx hta,
      evalE_hasTy g st env hrel.typed b y _ wb hy htb, hv.symm⟩
  cases ta with
  | int w =>
    refine KPost.pure F (Shape.plain rfl rfl) hok ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨p, x, y, h1, h2, h3, tx, ty, rfl⟩ := hval hrel hk hr hv
    obtain ⟨xv, rfl, hxl⟩ := hasTy_int tx
    obtain ⟨yv, rfl, hyl⟩ := hasTy_int ty
    rw [cval_int] at h2 h3
    show C.Sem.evalC cp cst cenv (.cast (.uint w.bits) (.cond cc ca cb)) = _
    rw [evalC_cast, evalC_cond _ _ _ _ p h1 rfl]
    cases p
    · simp [h3, castTo_uint, Nat.mod_eq_of_lt hyl]
    · simp [h2, castTo_uint, Nat.mod_eq_of_lt hxl]
  | bool =>
    refine KPost.pure F (Shape.plain rfl rfl) hok ?_
    intro st env cst cenv hrel hk hr v hv
    obtain ⟨p, x, y, h1, h2, h3, tx, ty, rfl⟩ := hval hrel hk hr hv
    show C.Sem.evalC cp cst cenv (.cond cc ca cb) = _
    rw [evalC_cond _ _ _ _ p h1 rfl]
    cases p
    · simpa using h3
    · simpa using h2
  | arr _ _ => simp [Ty.isScalar] at hsc
  | record _ => simp [Ty.isScalar] at hsc

end

/-! ## Places: fields and elements -/

theorem getPath_append (v : CVal) (p q : List Nat) :
    C.Sem.getPath v (p ++ q) = (C.Sem.getPath v p).bind (C.Sem.getPath · q) := by
  induction p generalizing v with
  | nil => rfl
  | cons i r ih =>
    cases v with
    | arr xs =>
      simp only [List.cons_append, C.Sem.getPath]
      cases xs[i]? with
      | none => rfl
      | some x => exact ih x
    | strct n fs =>
      simp only [List.cons_append, C.Sem.getPath]
      cases fs[i]? with
      | none => rfl
      | some x => exact ih x
    | int _ _ => rfl
    | bool _ => rfl
    | ptr _ => rfl

/-- Reading one step further into a location. -/
theorem read_step (cst : C.Sem.St) (cenv : C.Sem.Env) (l : C.Sem.Loc) (v x : CVal) (i : Nat)
    (h : C.Sem.read cst cenv l = some v) (hx : C.Sem.getPath v [i] = some x) :
    C.Sem.read cst cenv { l with path := l.path ++ [i] } = some x := by
  unfold C.Sem.read at h ⊢
  cases hb : C.Sem.readBase cst cenv l.base with
  | none => simp [hb] at h
  | some bv =>
    simp only [hb] at h ⊢
    rw [getPath_append, h]
    exact hx

theorem fieldIdx_eq {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv : C.Sem.Env} (hrel : ERel g cp st env cst cenv) (r f : String) (sd : StructDef)
    (hsd : g.prog.struct? r = some sd) :
    C.Sem.fieldIdx cp (g.opts.structName r) f = sd.fields.findIdx? (·.1 == f) := by
  unfold C.Sem.fieldIdx
  rw [hrel.flds r sd hsd]
  simp only [List.findIdx?_map]
  rfl

theorem findIdx_of_lookup {α : Type} (l : List (String × α)) (f : String) (t : α) (h : l.lookup f = some t) :
    ∃ i, l.findIdx? (·.1 == f) = some i := by
  induction l with
  | nil => simp at h
  | cons a r ih =>
    obtain ⟨k, x⟩ := a
    rw [List.findIdx?_cons]
    by_cases hk : (k == f) = true
    · exact ⟨0, by simp [hk]⟩
    · have hk' : (f == k) = false := by
        cases hfk : f == k
        · rfl
        · rw [beq_iff_eq] at hfk; exact absurd (by rw [beq_iff_eq]; exact hfk.symm) hk
      simp only [List.lookup, hk'] at h
      obtain ⟨i, hi⟩ := ih h
      exact ⟨i + 1, by simp [hk, hi]⟩

/-- The field of a record place. -/
theorem field_place {g : C.Env} {cp : CProg} {st : Lang.Sem.St} {env : Lang.Sem.Env} {cst : C.Sem.St}
    {cenv : C.Sem.Env} (hrel : ERel g cp st env cst cenv) (c : CExpr) (ptr : Bool) (rn f : String)
    (fs : Array Val) (sd : StructDef) (hsd : g.prog.struct? rn = some sd) (i : Nat)
    (hi : sd.fields.findIdx? (·.1 == f) = some i) (fv : Val) (hfv : fs[i]? = some fv) (L : C.Sem.Loc)
    (h : PlaceLoc cp cst cenv c ptr (cval g.opts (.record rn fs)) L) :
    PlaceLoc cp cst cenv (if ptr then .arrow c f else .dot c f) false (cval g.opts fv)
      { L with path := L.path ++ [i] } := by
  have hidx := (fieldIdx_eq hrel rn f sd hsd).trans hi
  have hget : C.Sem.getPath (cval g.opts (.record rn fs)) [i] = some (cval g.opts fv) := by
    simp [cval_record, C.Sem.getPath, hfv]
  obtain ⟨l0, hl, hr⟩ := h
  rcases hr with ⟨rfl, rfl, hr⟩ | ⟨h1, h2, h3⟩
  · refine ⟨{ L with path := L.path ++ [i] }, ?_, Or.inl ⟨rfl, rfl, read_step cst cenv L _ _ i hr hget⟩⟩
    rw [cval_record] at hr
    simp [C.Sem.lval, hl, C.Sem.dotLoc, hr, hidx]
  · rcases h3 with ⟨rfl, _⟩ | ⟨_, ys, e⟩
    · refine ⟨{ L with path := L.path ++ [i] }, ?_, Or.inl ⟨rfl, rfl, read_step cst cenv L _ _ i h2 hget⟩⟩
      rw [cval_record] at h2
      simp [C.Sem.lval, hl, C.Sem.arrowLoc, h1, C.Sem.dotLoc, h2, hidx]
    · rw [cval_record] at e; cases e

/-- The element of an array place. -/
theorem index_place {g : C.Env} {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env} (c ic : CExpr) (ptr : Bool)
    (xs : Array Val) (k iv : Nat) (x : Val) (hx : xs[iv]? = some x)
    (hic : C.Sem.evalC cp cst cenv ic = some (.int k iv)) (L : C.Sem.Loc)
    (h : PlaceLoc cp cst cenv c ptr (cval g.opts (.arr xs)) L) :
    PlaceLoc cp cst cenv (.index c ic) false (cval g.opts x) { L with path := L.path ++ [iv] } := by
  have hget : C.Sem.getPath (cval g.opts (.arr xs)) [iv] = some (cval g.opts x) := by
    simp [cval_arr, C.Sem.getPath, hx]
  obtain ⟨l0, hl, hr⟩ := h
  rcases hr with ⟨_, rfl, hr⟩ | ⟨h1, h2, _⟩
  · refine ⟨{ L with path := L.path ++ [iv] }, ?_, Or.inl ⟨rfl, rfl, read_step cst cenv L _ _ iv hr hget⟩⟩
    rw [cval_arr] at hr
    simp [C.Sem.lval, hl, hic, C.Sem.idxLoc, hr]
  · refine ⟨{ L with path := L.path ++ [iv] }, ?_, Or.inl ⟨rfl, rfl, read_step cst cenv L _ _ iv h2 hget⟩⟩
    simp [C.Sem.lval, hl, hic, C.Sem.idxLoc, h1]

/-- The path of an element. -/
theorem rooted_index {g : C.Env} {cp : CProg} {b i : Expr} {L : C.Sem.Loc} {st : Lang.Sem.St}
    {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env} {iw : Width} {iv : UInt64}
    (hi : Lang.Sem.evalE g.prog st env i = some (.int iw iv)) (h : Rooted g cp b L st env cst cenv) :
    Rooted g cp (.index b i) { L with path := L.path ++ [iv.toNat] } st env cst cenv := by
  intro x q hq info vx hinfo hlk
  simp only [lpath, hi] at hq
  cases hb : lpath g.prog st env b with
  | none => simp [hb] at hq
  | some xq =>
    obtain ⟨x0, q0⟩ := xq
    simp only [hb, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨Lx, hLx, e⟩ := h x0 q0 hb info vx hinfo hlk
    refine ⟨Lx, hLx, ?_⟩
    rw [e]
    simp [Val.toNat, List.append_assoc]

/-- The path of a field. -/
theorem rooted_field {g : C.Env} {cp : CProg} {b : Expr} {f : String} {L : C.Sem.Loc} {st : Lang.Sem.St}
    {env : Lang.Sem.Env} {cst : C.Sem.St} {cenv : C.Sem.Env} {rn : String} {fs : Array Val} {i : Nat}
    (hb : Lang.Sem.evalE g.prog st env b = some (.record rn fs)) (hi : Lang.Sem.fieldIndex g.prog rn f = some i)
    (h : Rooted g cp b L st env cst cenv) :
    Rooted g cp (.field b f) { L with path := L.path ++ [i] } st env cst cenv := by
  intro x q hq info vx hinfo hlk
  simp only [lpath, hb] at hq
  cases hbl : lpath g.prog st env b with
  | none => simp [hbl] at hq
  | some xq =>
    obtain ⟨x0, q0⟩ := xq
    simp only [hbl, hi, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨Lx, hLx, e⟩ := h x0 q0 hbl info vx hinfo hlk
    refine ⟨Lx, hLx, ?_⟩
    rw [e]
    simp [List.append_assoc]

/-! ## The index check -/

section
variable {cp : CProg} {cst : C.Sem.St} {cenv : C.Sem.Env}

theorem check_runs (m : Nat) (cnd : CExpr) (msg : String) (h : C.Sem.evalC cp cst cenv cnd = some (.bool false)) :
    C.Sem.execS (m + 5) cp cst cenv (.ite cnd [.expr (.call "ember_trap" [.str msg])] []) = .ok cst cenv .normal := by
  simp [C.Sem.execS, h, C.Sem.truthy, C.Sem.execB, C.Sem.execL]

theorem check_traps (m : Nat) (cnd : CExpr) (msg : String) (h : C.Sem.evalC cp cst cenv cnd = some (.bool true)) :
    C.Sem.execS (m + 5) cp cst cenv (.ite cnd [.expr (.call "ember_trap" [.str msg])] []) = .trap cst := by
  simp [C.Sem.execS, h, C.Sem.truthy, C.Sem.execB, C.Sem.execL, C.Sem.asCall, C.Sem.helper, C.Sem.callC]

end

theorem indexSafe_lt {g : C.Env} {i : Expr} {iw : Width} {n : Nat} (hs : indexSafe i iw n = true) (wi : WT g i)
    (hti : g.tyOf i = .ok (.int iw)) {p : Prog} {st : Lang.Sem.St} {env : Lang.Sem.Env} {iv : UInt64}
    (hl : iv.toNat < 2 ^ iw.bits) (hv : Lang.Sem.evalE p st env i = some (.int iw iv)) : iv.toNat < n := by
  have other : (iw == .w8 && decide (n ≥ 256)) = true → iv.toNat < n := by
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have : iw = .w8 := by
      cases iw
      · rfl
      all_goals exact absurd h.1 (by decide)
    subst this
    simp only [Width.bits] at hl
    omega
  cases i with
  | lit v ow =>
    cases ow with
    | none => simp [WT] at wi
    | some w =>
      simp only [WT] at wi
      simp only [indexSafe, decide_eq_true_eq] at hs
      simp only [Lang.Sem.evalE, Option.some.injEq, Val.int.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rw [mask_toNat, UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ (pow_bits_dvd w), Nat.mod_eq_of_lt wi]
      exact hs
  | blit _ => exact other hs
  | var _ => exact other hs
  | field _ _ => exact other hs
  | index _ _ => exact other hs
  | bin _ _ _ => exact other hs
  | un _ _ => exact other hs
  | cast _ _ => exact other hs
  | cond _ _ _ => exact other hs

theorem wpc_placeField {g : C.Env} {cs : CS} (c : CExpr) (t : Ty) (ptr : Bool) (f : String)
    (Q : CExpr × Ty × Bool → CS → Prop) :
    wpc (placeField (c, t, ptr) f) g Q cs ↔
      ∀ rn ft, t = .record rn → g.fieldTy rn f = .ok ft → Q (if ptr then .arrow c f else .dot c f, ft, false) cs := by
  unfold placeField
  cases t with
  | record rn =>
    simp only [wpc_bind, fieldTy, wpc_pureE, wpc_pure]
    exact ⟨fun h rn' ft e hft => by cases e; exact h ft hft, fun h ft hft => h rn ft rfl hft⟩
  | int _ => simp [wpc_err]
  | bool => simp [wpc_err]
  | arr _ _ => simp [wpc_err]

theorem wpc_trapMsg_of {g : C.Env} {cs : CS} (s : String) (Q : String → CS → Prop) (h : ∀ m, Q m cs) :
    wpc (trapMsg s) g Q cs := by
  unfold trapMsg
  simp only [wpc_bind, wpc_read, wpc_pure]
  exact h _

theorem evalE_index {p : Prog} {st : Lang.Sem.St} {env : Lang.Sem.Env} {b i : Expr} {xs : Array Val} {w : Width}
    {iv : UInt64} (hb : Lang.Sem.evalE p st env b = some (.arr xs)) (hi : Lang.Sem.evalE p st env i = some (.int w iv)) :
    Lang.Sem.evalE p st env (.index b i) = xs[iv.toNat]? := by
  simp [Lang.Sem.evalE, hb, hi, Val.toNat]

section
variable {g : C.Env} {cp : CProg} {b i : Expr} {c ic : CExpr} {ptr : Bool} {el : Ty} {n : Nat} {iw : Width}
  {t0 : Nat} {pre : List CStmt} {cs : CS}

theorem placeIndex_ok
    (F : Frag g cp t0 cs.tmp pre (fun st env => EOk g b st env ∧ EOk g i st env)
      (fun st env cst cenv => PRes g cp b c ptr st env cst cenv ∧ ERes g cp i ic st env cst cenv))
    (si : Shape g i ic) (wb : WT g b) (wi : WT g i) (htb : g.tyOf b = .ok (.arr el n))
    (hti : g.tyOf i = .ok (.int iw)) (hn : n < 65536) :
    wpc (placeIndex (c, .arr el n, ptr) i iw ic) g (fun r cs' => ∃ pre', cs'.out = cs.out ++ pre'.toArray ∧
      r.2.1 = el ∧ (∃ c', r.1 = .index c c') ∧
      Frag g cp t0 cs'.tmp (pre ++ pre') (EOk g (.index b i)) (PRes g cp (.index b i) r.1 r.2.2)) cs := by
  have lv : ∀ {st env cst cenv}, ERel g cp st env cst cenv → EOk g b st env ∧ EOk g i st env →
      ∃ (xs : Array Val) (iv : UInt64), Lang.Sem.evalE g.prog st env b = some (.arr xs) ∧ xs.size = n ∧
        Lang.Sem.evalE g.prog st env i = some (.int iw iv) ∧ iv.toNat < 2 ^ iw.bits := by
    intro st env cst cenv hrel hk
    obtain ⟨bv, hb⟩ := Option.isSome_iff_exists.mp hk.1
    obtain ⟨ivv, hi⟩ := Option.isSome_iff_exists.mp hk.2
    obtain ⟨xs, rfl, hsz, _⟩ := hasTy_arr (evalE_hasTy g st env hrel.typed b bv _ wb hb htb)
    obtain ⟨iv, rfl, hil⟩ := hasTy_int (evalE_hasTy g st env hrel.typed i ivv _ wi hi hti)
    exact ⟨xs, iv, hb, hsz, hi, hil⟩
  have hsome : ∀ {st : Lang.Sem.St} {env : Lang.Sem.Env},
      EOk g (.index b i) st env → EOk g b st env ∧ EOk g i st env := by
    intro st env h
    unfold EOk at h ⊢
    simp only [Lang.Sem.evalE] at h
    cases hb : Lang.Sem.evalE g.prog st env b <;> cases hi : Lang.Sem.evalE g.prog st env i <;> simp [hb, hi] at h ⊢
  unfold placeIndex
  dsimp only
  by_cases hs : indexSafe i iw n = true
  · rw [if_pos hs, wpc_pure]
    refine ⟨[], by simp, rfl, ⟨_, rfl⟩, ?_⟩
    rw [List.append_nil]
    refine F.conseq ?_ ?_
    · intro st env cst cenv hrel
      refine ⟨hsome, fun hk => ?_⟩
      obtain ⟨xs, iv, hb, hsz, hi, hil⟩ := lv hrel hk
      have hlt := indexSafe_lt hs wi hti hil hi
      unfold EOk
      rw [evalE_index hb hi, Array.getElem?_eq_getElem (by omega)]
      rfl
    · intro st env cst cenv hrel hk hr v hv
      obtain ⟨xs, iv, hb, hsz, hi, hil⟩ := lv hrel hk
      rw [evalE_index hb hi] at hv
      have h2 := hr.2 _ hi
      rw [cval_int] at h2
      obtain ⟨L, hL, hroot⟩ := hr.1 _ hb
      exact ⟨_, index_place c ic ptr xs _ _ v hv h2 L hL, rooted_index hi hroot⟩
  · rw [if_neg hs]
    simp only [wpc_bind, wpc_fresh, wpc_emit]
    refine wpc_trapMsg_of _ _ (fun msg => ?_)
    rw [wpc_pure]
    refine ⟨[.decl (.uint iw.bits) (tmpName cs.tmp) (some ic), .ite (.bin ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw)))
          [.expr (.call "ember_trap" [.str msg])] []], by rw [← Array.toList_inj]; simp, rfl, ⟨_, rfl⟩, ?_⟩
    have B := F.bind (t2 := cs.tmp + 1) (ok2 := fun st env => EOk g (.index b i) st env)
      (res2 := PRes g cp (.index b i) (.index c (.var (tmpName cs.tmp))) false) (Nat.le_succ _)
      (pre2 := [.decl (.uint iw.bits) (tmpName cs.tmp) (some ic),
        .ite (.bin ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw)))
          [.expr (.call "ember_trap" [.str msg])] []])
      (fun st env cst cenv hrel hfr hk hr => by
        obtain ⟨xs, iv, hb, hsz, hi, hil⟩ := lv hrel hk
        have h2 := hr.2 _ hi
        rw [cval_int] at h2
        have hx1 := hfr.ext (Temps.one cs.tmp (.int iw.bits iv.toNat))
        have r1 : Runs cp cst cenv [.decl (.uint iw.bits) (tmpName cs.tmp) (some ic)]
            ([(tmpName cs.tmp, .int iw.bits iv.toNat)] ++ cenv) :=
          Runs.single fun m => exec_decl (m + 4) _ _ ic _ _ si.nocall h2
            (by simp only [C.Sem.convTo, castTo_uint, Nat.mod_eq_of_lt hil])
        obtain ⟨bz, hz⟩ := evalC_lit_suffix cp cst ([(tmpName cs.tmp, CVal.int iw.bits iv.toNat)] ++ cenv) iw n
          (by omega) hrel.i16 hrel.l32
        have hcnd : C.Sem.evalC cp cst ([(tmpName cs.tmp, CVal.int iw.bits iv.toNat)] ++ cenv)
            (.bin ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw))) = some (.bool (decide (iv.toNat ≥ n))) := by
          have e := evalC_bin (cp := cp) (cst := cst) (cenv := [(tmpName cs.tmp, CVal.int iw.bits iv.toNat)] ++ cenv)
            ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw)) _ _ rfl rfl (evalC_var_head _ _) hz
          rw [e]
          simp [C.Sem.binop, C.Sem.isCompare, C.Sem.compare]
        have hev : Lang.Sem.evalE g.prog st env (.index b i) = xs[iv.toNat]? := evalE_index hb hi
        constructor
        · intro hok
          have hlt : iv.toNat < n := by
            unfold EOk at hok
            rw [hev] at hok
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hok
            have := (Array.getElem?_eq_some_iff.mp hv).1
            omega
          have hcnd' : C.Sem.evalC cp cst ([(tmpName cs.tmp, CVal.int iw.bits iv.toNat)] ++ cenv)
              (.bin ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw))) = some (.bool false) := by
            rw [hcnd]; simp; omega
          refine ⟨[(tmpName cs.tmp, .int iw.bits iv.toNat)], Temps.one _ _,
            r1.append (Runs.single fun m => check_runs m _ _ hcnd'), ?_⟩
          intro v hv
          rw [hev] at hv
          obtain ⟨L, hL, hroot⟩ := PRes.stable g cp b c ptr _ _ _ _ _ hx1 hr.1 _ hb
          exact ⟨_, index_place c _ ptr xs _ _ v hv (evalC_var_head _ _) L hL, rooted_index hi hroot⟩
        · intro hno
          have hge : iv.toNat ≥ n := by
            unfold EOk at hno
            rw [hev] at hno
            by_cases hlt : iv.toNat < n
            · rw [Array.getElem?_eq_getElem (by omega)] at hno; exact absurd rfl hno
            · omega
          have hcnd' : C.Sem.evalC cp cst ([(tmpName cs.tmp, CVal.int iw.bits iv.toNat)] ++ cenv)
              (.bin ">=" (.var (tmpName cs.tmp)) (.lit n (suffix iw))) = some (.bool true) := by
            rw [hcnd]; simp; omega
          exact r1.traps (Traps.single fun m => check_traps m _ _ hcnd'))
    exact B.conseq (fun st env cst cenv hrel => ⟨fun h => ⟨hsome h, h⟩, fun h => h.2⟩) fun _ _ _ _ _ _ h => h

end

/-! ## Fields; places as values -/

theorem field_frag {g : C.Env} {cp : CProg} {b : Expr} {c : CExpr} {ptr : Bool} {rn f : String} {ft : Ty}
    {t0 t1 : Nat} {pre : List CStmt} (Fb : Frag g cp t0 t1 pre (EOk g b) (PRes g cp b c ptr)) (wb : WT g b)
    (htb : g.tyOf b = .ok (.record rn)) (hft : g.fieldTy rn f = .ok ft) :
    Frag g cp t0 t1 pre (EOk g (.field b f)) (PRes g cp (.field b f) (if ptr then .arrow c f else .dot c f) false) := by
  -- the record's definition and the field's number
  have hdef : ∃ sd i, g.prog.struct? rn = some sd ∧ sd.fields.findIdx? (·.1 == f) = some i ∧ i < sd.fields.length := by
    unfold Env.fieldTy at hft
    cases hsd : g.prog.struct? rn with
    | none => simp [hsd, Env.err] at hft
    | some sd =>
      simp only [hsd] at hft
      cases hl : sd.fields.lookup f with
      | none => simp [hl, Env.err] at hft
      | some t =>
        obtain ⟨i, hi⟩ := findIdx_of_lookup sd.fields f t hl
        obtain ⟨hlt, _⟩ := lookup_of_findIdx sd.fields f i hi
        exact ⟨sd, i, rfl, hi, hlt⟩
  obtain ⟨sd, i, hsd, hi, hlt⟩ := hdef
  have key : ∀ {st env cst cenv}, ERel g cp st env cst cenv → ∀ bv, Lang.Sem.evalE g.prog st env b = some bv →
      ∃ fs fv, bv = .record rn fs ∧ fs[i]? = some fv ∧ Lang.Sem.evalE g.prog st env (.field b f) = some fv := by
    intro st env cst cenv hrel bv hb
    obtain ⟨fs, sd', rfl, hsd', hsz, _⟩ := hasTy_record (evalE_hasTy g st env hrel.typed b bv _ wb hb htb)
    rw [hsd] at hsd'
    cases hsd'
    have hlt' : i < fs.size := by omega
    refine ⟨fs, fs[i], rfl, Array.getElem?_eq_getElem hlt', ?_⟩
    simp [Lang.Sem.evalE, hb, Lang.Sem.fieldIndex, hsd, hi, Array.getElem?_eq_getElem hlt']
  refine Fb.conseq ?_ ?_
  · intro st env cst cenv hrel
    constructor
    · intro h
      unfold EOk at h ⊢
      simp only [Lang.Sem.evalE] at h
      cases hb : Lang.Sem.evalE g.prog st env b with
      | none => simp [hb] at h
      | some x => rfl
    · intro hk
      obtain ⟨bv, hb⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨fs, fv, _, _, hev⟩ := key hrel bv hb
      simp [EOk, hev]
  · intro st env cst cenv hrel hk hr v hv
    obtain ⟨bv, hb⟩ := Option.isSome_iff_exists.mp hk
    obtain ⟨fs, fv, rfl, hfv, hev⟩ := key hrel bv hb
    rw [hev] at hv
    cases hv
    obtain ⟨L, hL, hroot⟩ := hr _ hb
    exact ⟨_, field_place hrel c ptr rn f fs sd hsd i hi v hfv L hL,
      rooted_field hb (by simp [Lang.Sem.fieldIndex, hsd, hi]) hroot⟩

theorem tyOf_field {g : C.Env} {b : Expr} {rn f : String} {ft : Ty} (htb : g.tyOf b = .ok (.record rn))
    (hft : g.fieldTy rn f = .ok ft) : g.tyOf (.field b f) = .ok ft := by
  simp only [Env.tyOf, htb]
  exact hft

theorem tyOf_index {g : C.Env} {b i : Expr} {el : Ty} {n : Nat} (htb : g.tyOf b = .ok (.arr el n)) :
    g.tyOf (.index b i) = .ok el := by
  simp only [Env.tyOf, htb]

/-- A place of scalar type, read as a value. -/
theorem epost_of_frag {g : C.Env} {cp : CProg} {e : Expr} {c : CExpr} {ptr : Bool} {t : Ty} {t0 t1 : Nat}
    {pre : List CStmt} (F : Frag g cp t0 t1 pre (EOk g e) (PRes g cp e c ptr)) (hw : WT g e)
    (ht : g.tyOf e = .ok t) (hsc : t.isScalar = true) :
    Frag g cp t0 t1 pre (EOk g e) (ERes g cp e c) := by
  refine F.conseq (fun _ _ _ _ _ => Iff.rfl) ?_
  intro st env cst cenv hrel hk hr v hv
  obtain ⟨L, hL, _⟩ := hr v hv
  exact PlaceAt.evalC ⟨L, hL⟩ (cval_scalar g.opts g.prog t v hsc (evalE_hasTy g st env hrel.typed e v t hw hv ht))

theorem wpc_indexWidth {g : C.Env} {cs : CS} (i : Expr) (Q : Width → CS → Prop) :
    wpc (indexWidth i) g Q cs ↔ ∀ w, g.tyOf i = .ok (.int w) → Q w cs := by
  unfold indexWidth
  rw [wpc_pureE]
  unfold Env.indexWidth
  constructor
  · intro h w hw
    exact h w (by simp [hw])
  · intro h w hw
    cases ht : g.tyOf i with
    | error m => simp [ht] at hw
    | ok t =>
      cases t with
      | int w' => simp only [ht, Except.ok.injEq] at hw; subst hw; exact h w' ht
      | bool => simp [ht, Env.err] at hw
      | arr _ _ => simp [ht, Env.err] at hw
      | record _ => simp [ht, Env.err] at hw

/-- What the proofs need of the emitter's environment: variables are C
variables, and the planted bug is off. -/
def EnvOK (g : C.Env) : Prop :=
  (∀ x info, g.varInfo x = .ok info → ∃ nm, info.c = .var nm) ∧ g.opts.bugDropCast = false

theorem binTy_scalar {op : BinOp} {ta tb : Ty} (h : BinTy op ta tb) : ta.isScalar = true ∧ tb.isScalar = true := by
  unfold BinTy at h
  split at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  · split at h
    · obtain ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ := h; exact ⟨rfl, rfl⟩
    · split at h
      · obtain ⟨rfl, hs⟩ := h; exact ⟨hs, hs⟩
      · obtain ⟨w, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-! ## The theorem -/

mutual

/-- **`place e`** emits statements and an lvalue such that, from related
states, the statements run and the lvalue designates the storage of `e`
— or they trap when `e` has no value (an index out of range). -/
theorem place_ok (cp : CProg) : ∀ (e : Expr) (g : C.Env) (cs : CS), EnvOK g → WT g e →
    wpc (place e) g (PPost g cp e cs) cs
  | .var x, g, cs, _, _ => by
    rw [place, wpc_placeVar]
    intro info hi
    refine ⟨[], by simp, by simp [Env.tyOf, hi], Frag.nil _ ?_ ?_⟩
    · intro st env cst cenv hrel _ v hv
      simp only [Lang.Sem.evalE] at hv
      obtain ⟨L, hL⟩ := hrel.place x v info hv hi
      refine ⟨L, hL, fun x' q hq info' vx hi' hlk => ?_⟩
      simp only [lpath, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [hi] at hi'
      cases hi'
      rw [hv] at hlk
      cases hlk
      exact ⟨L, hL, by simp⟩
    · intro st env cst cenv hrel
      obtain ⟨v, hv⟩ := hrel.scope x info hi
      simp [EOk, Lang.Sem.evalE, hv]
  | .field b f, g, cs, hg, hw => by
    rw [place, wpc_bind]
    refine wpc_mono (place_ok cp b g cs hg hw) ?_
    rintro ⟨c, t, ptr⟩ cs1 ⟨pre, ho, hty, F⟩
    rw [wpc_placeField]
    intro rn ft e hft
    subst e
    exact ⟨pre, ho, tyOf_field hty hft, field_frag F hw hty hft⟩
  | .index b i, g, cs, hg, hw => by
    have hw' := hw
    simp only [WT] at hw'
    obtain ⟨wb, wi, _, hlen⟩ := hw'
    rw [place, wpc_bind]
    refine wpc_mono (place_ok cp b g cs hg wb) ?_
    rintro ⟨c, t, ptr⟩ cs1 ⟨pre1, ho1, hty, Fb⟩
    cases t with
    | arr el n =>
      dsimp only at hty ⊢
      simp only [wpc_bind, wpc_indexWidth]
      intro iw hti
      refine wpc_mono (expr_ok cp i g cs1 hg wi (.int iw) hti rfl) ?_
      rintro ic cs2 ⟨pre2, ho2, si, Fi⟩
      refine wpc_mono (placeIndex_ok (Fb.seq Fi (PRes.stable g cp b c ptr)) si wb wi hty hti (hlen el n hty)) ?_
      rintro r cs3 ⟨pre3, ho3, hel, _, F3⟩
      refine ⟨pre1 ++ pre2 ++ pre3, by rw [ho3, ho2, ho1]; simp, by rw [hel]; exact tyOf_index hty, F3⟩
    | int _ => simp [wpc_err]
    | bool => simp [wpc_err]
    | record _ => simp [wpc_err]
  | .lit _ _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)
  | .blit _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)
  | .bin _ _ _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)
  | .un _ _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)
  | .cast _ _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)
  | .cond _ _ _, g, cs, _, _ => by rw [place] <;> first | exact trivial | (intros; contradiction)

/-- **`expr e`**, for an expression of scalar type: the statements it
emits run and the C expression has the value of `e` — or they trap when
`e` has no value. -/
theorem expr_ok (cp : CProg) : ∀ (e : Expr) (g : C.Env) (cs : CS), EnvOK g → WT g e →
    ∀ t, g.tyOf e = .ok t → t.isScalar = true → wpc (expr e) g (EPost g cp e cs) cs
  | .lit v (some w), g, cs, _, hw, t, ht, _ => by
    simp only [WT] at hw
    rw [expr]
    simp only [wpc_bind, wpc_read, closedConst, wpc_pure]
    refine EPost.nil ⟨rfl, fun n s h => by simp [litC] at h, fun n hn st env x _ hx => ?_⟩ ?_ ?_
    · simp only [Lang.Sem.evalE, Option.some.injEq] at hx
      subst hx
      have : v = n := by simpa [litC, CExpr.litVal?] using hn
      subst this
      show (mask w (UInt64.ofNat v)).toNat = v
      rw [mask_toNat, UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ (pow_bits_dvd w), Nat.mod_eq_of_lt hw]
    · intro st env cst cenv _
      simp [EOk, Lang.Sem.evalE]
    · intro st env cst cenv hrel x hx
      simp only [Lang.Sem.evalE, Option.some.injEq] at hx
      subst hx
      rw [cval_int, mask_toNat, UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ (pow_bits_dvd w), Nat.mod_eq_of_lt hw]
      exact evalC_litC cp cst cenv w v hw hrel.i16 hrel.l32
  | .lit _ none, g, cs, _, hw, _, _, _ => absurd hw (by simp [WT])
  | .blit b, g, cs, _, _, t, ht, _ => by
    rw [expr]
    simp only [wpc_bind, wpc_read, closedConst, wpc_pure]
    refine EPost.nil (Shape.plain rfl rfl) ?_ ?_
    · intro st env cst cenv _
      simp [EOk, Lang.Sem.evalE]
    · intro st env cst cenv hrel x hx
      simp only [Lang.Sem.evalE, Option.some.injEq] at hx
      subst hx
      rw [cval_bool]
      rfl
  | .var x, g, cs, hg, hw, t, ht, hsc => by
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.var x) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      simp only [wpc_bind, wpc_placeVar, wpc_pure]
      intro info hi
      obtain ⟨nm, hnm⟩ := hg.1 x info hi
      have hti : info.ty = t := by simpa [Env.tyOf, hi] using ht
      refine EPost.nil (by rw [hnm]; exact Shape.plain rfl rfl) ?_ ?_
      · intro st env cst cenv hrel
        obtain ⟨v, hv⟩ := hrel.scope x info hi
        simp [EOk, Lang.Sem.evalE, hv]
      · intro st env cst cenv hrel v hv
        simp only [Lang.Sem.evalE] at hv
        exact (hrel.place x v info hv hi).evalC
          (cval_scalar g.opts g.prog info.ty v (by rw [hti]; exact hsc) (hrel.typed x v info hv hi))
  | .field b f, g, cs, hg, hw, t, ht, hsc => by
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.field b f) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      rw [wpc_bind]
      refine wpc_mono (place_ok cp b g cs hg hw) ?_
      rintro ⟨c, tb, ptr⟩ cs1 ⟨pre, ho, hty, F⟩
      rw [wpc_bind, wpc_placeField]
      intro rn ft e hft
      subst e
      rw [wpc_pure]
      have htf := tyOf_field hty hft
      rw [ht] at htf
      cases htf
      refine ⟨pre, ho, ?_, epost_of_frag (field_frag F hw hty hft) hw ht hsc⟩
      cases ptr <;> exact Shape.plain rfl rfl
  | .index b i, g, cs, hg, hw, t, ht, hsc => by
    have hw' := hw
    simp only [WT] at hw'
    obtain ⟨wb, wi, _, hlen⟩ := hw'
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.index b i) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      rw [wpc_bind]
      refine wpc_mono (place_ok cp b g cs hg wb) ?_
      rintro ⟨c, tb, ptr⟩ cs1 ⟨pre1, ho1, hty, Fb⟩
      cases tb with
      | arr el n =>
        dsimp only at hty ⊢
        simp only [wpc_bind, wpc_indexWidth]
        intro iw hti
        refine wpc_mono (expr_ok cp i g cs1 hg wi (.int iw) hti rfl) ?_
        rintro ic cs2 ⟨pre2, ho2, si, Fi⟩
        refine wpc_mono (placeIndex_ok (Fb.seq Fi (PRes.stable g cp b c ptr)) si wb wi hty hti (hlen el n hty)) ?_
        rintro r cs3 ⟨pre3, ho3, hel, ⟨c', hc'⟩, F3⟩
        rw [wpc_pure]
        have hti' := tyOf_index (i := i) hty
        rw [ht] at hti'
        cases hti'
        refine ⟨pre1 ++ pre2 ++ pre3, by rw [ho3, ho2, ho1]; simp, by rw [hc']; exact Shape.plain rfl rfl,
          epost_of_frag F3 hw ht hsc⟩
      | int _ => simp [wpc_err]
      | bool => simp [wpc_err]
      | record _ => simp [wpc_err]
  | .bin op a b, g, cs, hg, hw, t, ht, _ => by
    obtain ⟨wa, wb, ta, tb, hta, htb, hty⟩ := wt_bin hw
    obtain ⟨hsa, hsb⟩ := binTy_scalar hty
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.bin op a b) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      simp only [wpc_bind, wpc_tyOf]
      intro ta' hta'
      rw [hta] at hta'
      cases hta'
      refine wpc_mono (expr_ok cp a g cs hg wa ta hta hsa) ?_
      rintro ca cs1 ⟨pre1, ho1, sa, Fa⟩
      refine wpc_mono (expr_ok cp b g cs1 hg wb tb htb hsb) ?_
      rintro cb cs2 ⟨pre2, ho2, sb, Fb⟩
      refine wpc_mono (binC_ok (Fa.seq Fb (ERes.stable g cp a ca)) sa sb hw hta htb hty hg.2) ?_
      rintro ce cs3 ⟨pre3, ho3, sh, F3⟩
      exact ⟨pre1 ++ pre2 ++ pre3, by rw [ho3, ho2, ho1]; simp, sh, F3⟩
  | .un op a, g, cs, hg, hw, t, ht, _ => by
    have hw' := hw
    simp only [WT] at hw'
    obtain ⟨wa, hty⟩ := hw'
    have hta : ∃ ta, g.tyOf a = .ok ta ∧ ta.isScalar = true := by
      split at hty
      · exact ⟨_, hty, rfl⟩
      · obtain ⟨w, h⟩ := hty; exact ⟨_, h, rfl⟩
    obtain ⟨ta, hta, hsa⟩ := hta
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.un op a) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      rw [wpc_bind]
      refine wpc_mono (expr_ok cp a g cs hg wa ta hta hsa) ?_
      rintro ca cs1 ⟨pre1, ho1, sa, Fa⟩
      simp only [wpc_bind, wpc_tyOf]
      intro ta' hta'
      rw [hta] at hta'
      cases hta'
      refine wpc_mono (unC_ok op Fa hw hta) ?_
      rintro ce cs3 ⟨pre3, ho3, sh, F3⟩
      exact ⟨pre1 ++ pre3, by rw [ho3, ho1]; simp, sh, F3⟩
  | .cast w a, g, cs, hg, hw, t, ht, _ => by
    have hw' := hw
    simp only [WT] at hw'
    obtain ⟨wa, ta, hta, hsa⟩ := hw'
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.cast w a) with
    | some c => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      rw [wpc_bind]
      refine wpc_mono (expr_ok cp a g cs hg wa ta hta hsa) ?_
      rintro ca cs1 ⟨pre1, ho1, sa, Fa⟩
      simp only [wpc_bind, wpc_tyOf]
      intro ta' hta'
      rw [hta] at hta'
      cases hta'
      rw [wpc_pure]
      obtain ⟨pre3, ho3, sh, F3⟩ := castC_ok w Fa sa hw hta
      exact ⟨pre1 ++ pre3, by rw [ho3, ho1]; simp, sh, F3⟩
  | .cond c a b, g, cs, hg, hw, t, ht, _ => by
    have hw' := hw
    simp only [WT] at hw'
    obtain ⟨wc, wa, wb, htc, ta, hta, htb, hsa⟩ := hw'
    rw [expr]
    simp only [wpc_bind, wpc_read]
    cases hcc : closedConst (.cond c a b) with
    | some c' => dsimp only; rw [wpc_pure]; exact closed_post hw ht hcc
    | none =>
      dsimp only
      rw [wpc_bind]
      refine wpc_mono (expr_ok cp c g cs hg wc .bool htc rfl) ?_
      rintro cc cs1 ⟨pre1, ho1, sc, Fc⟩
      rw [wpc_bind]
      refine wpc_mono (expr_ok cp a g cs1 hg wa ta hta hsa) ?_
      rintro ca cs2 ⟨pre2, ho2, sa, Fa⟩
      rw [wpc_bind]
      refine wpc_mono (expr_ok cp b g cs2 hg wb ta htb hsa) ?_
      rintro cb cs3 ⟨pre3, ho3, sb, Fb⟩
      simp only [wpc_bind, wpc_tyOf]
      intro ta' hta'
      rw [hta] at hta'
      cases hta'
      rw [wpc_pure]
      have F := Fc.seq (Fa.seq Fb (ERes.stable g cp a ca)) (ERes.stable g cp c cc)
      obtain ⟨pre4, ho4, sh, F4⟩ := condC_ok F hw hta
      exact ⟨pre1 ++ (pre2 ++ pre3) ++ pre4, by rw [ho4, ho3, ho2, ho1]; simp, sh, F4⟩

end

/-- info: 'Ember.Proof.CSim.expr_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expr_ok

end Ember.Proof.CSim
