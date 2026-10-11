import Ember.Proof.IRStmt

/-!
# Ember.Proof.IRCall — calls and effects (plan M7.1)

A call stores its arguments in the callee's frame (one of them travels
in a register and is stored by the call itself), runs the callee, and
stores the result.  `callInstr_ok`: given that the callee's code
simulates the callee (`FnSim`, for less fuel), the code up to and with
the call instruction simulates the call; `effInstr_ok`: the same for an
effect.  `withResult_ok`, `declCall_ok`: where the result goes.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK IsPlace NoWriteL
  ReturnsL NoRef hasTy_zero copyBack_noref)

/-! ## The Ember side -/

/-- A call, as its arguments, the callee, and where the result goes. -/
theorem execS_call (p : Prog) (k : Nat) (st : Lang.Sem.St) (env : Lang.Sem.Env) (dst : Option Expr) (g : String)
    (args : List Expr) (fd : Lang.Fn) (hfd : p.fn? g = some fd) (hnr : ∀ prm, prm ∈ fd.params → prm.byRef = false) :
    Lang.Sem.execS (k + 1) p st env (.call dst g args) =
      match Lang.Sem.evalArgs p st env args with
      | none => .trap st
      | some vs =>
        match Lang.Sem.call k p st g vs with
        | .ok v st' => Lang.Sem.storeResult p st' env dst v
        | .trap st' => .trap st'
        | .fuel => .fuel := by
  simp only [Lang.Sem.execS, hfd, Lang.Sem.call]
  cases Lang.Sem.evalArgs p st env args with
  | none => rfl
  | some vs =>
    simp only []
    cases hB : Lang.Sem.execB k p st ((fd.params.map (·.name)).zip vs) fd.body with
    | fuel => rfl
    | trap st' => rfl
    | ok st' cenv o =>
      simp only [copyBack_noref p cenv fd.params args st' env hnr]
      cases o <;> rfl

theorem execS_eff (p : Prog) (k : Nat) (st : Lang.Sem.St) (env : Lang.Sem.Env) (dst : Option Expr) (e : Effect)
    (args : List Expr) :
    Lang.Sem.execS (k + 1) p st env (.eff dst e args) =
      match Lang.Sem.evalArgs p st env args with
      | none => .trap st
      | some vs => Lang.Sem.storeResult p (Lang.Sem.effect p st e vs).2 env dst (Lang.Sem.effect p st e vs).1 := by
  simp only [Lang.Sem.execS]
  cases Lang.Sem.evalArgs p st env args <;> rfl

theorem fn?_name {p : Prog} {g : String} {fd : Lang.Fn} (h : p.fn? g = some fd) : fd.name = g := by
  unfold Lang.Prog.fn? at h
  simpa using List.find?_some h

/-! ## Parameters and their arguments, position by position -/

/-- The parameter `q` with the argument `b` is at offset `off`. -/
def Occurs (lp : Prog) : List Lang.Param → List Expr → Nat → Lang.Param → Expr → Nat → Prop
  | prm :: ps, a :: as, lo, q, b, off =>
    (q = prm ∧ b = a ∧ off = lo) ∨ Occurs lp ps as (lo + sizeOf lp prm.ty) q b off
  | _, _, _, _, _, _ => False

theorem slots_end_ge (lp : Prog) : ∀ (ps : List Lang.Param) (lo : Nat), lo ≤ (paramSlotsFrom lp ps lo).2
  | [], _ => Nat.le_refl _
  | prm :: ps, lo => by
    simp only [paramSlotsFrom]
    exact Nat.le_trans (Nat.le_add_right _ _) (slots_end_ge lp ps _)

theorem slots_cons (lp : Prog) (prm : Lang.Param) (ps : List Lang.Param) (lo : Nat) (h : prm.byRef = false) :
    paramSlotsFrom lp (prm :: ps) lo =
      ((prm, lo) :: (paramSlotsFrom lp ps (lo + sizeOf lp prm.ty)).1,
        (paramSlotsFrom lp ps (lo + sizeOf lp prm.ty)).2) := by
  simp only [paramSlotsFrom, h, Bool.false_eq_true, if_false]

theorem occurs_bounds (lp : Prog) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q : Lang.Param)
    (b : Expr) (off : Nat), (∀ prm, prm ∈ ps → prm.byRef = false) → Occurs lp ps args lo q b off →
    lo ≤ off ∧ off + sizeOf lp q.ty ≤ (paramSlotsFrom lp ps lo).2
  | [], _, _, _, _, _, _, h => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, b, off, hnr, h => by
    rw [slots_cons lp prm ps lo (hnr prm (by simp))]
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨Nat.le_refl _, slots_end_ge lp ps _⟩
    · have := occurs_bounds lp ps as _ q b off (fun r hr => hnr r (by simp [hr])) h
      exact ⟨by omega, this.2⟩

/-- Two parameters at one offset are one (every parameter takes a byte at least). -/
theorem occurs_unique (lp : Prog) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q q' : Lang.Param)
    (b b' : Expr) (off : Nat), (∀ prm, prm ∈ ps → prm.byRef = false ∧ 0 < sizeOf lp prm.ty) →
    Occurs lp ps args lo q b off → Occurs lp ps args lo q' b' off → q = q' ∧ b = b'
  | [], _, _, _, _, _, _, _, _, h, _ => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, _, _, h, _ => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, q', b, b', off, hps, h, h' => by
    have hnr : ∀ r, r ∈ ps → r.byRef = false := fun r hr => (hps r (by simp [hr])).1
    have hpos := (hps prm (by simp)).2
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · rcases h' with ⟨rfl, rfl, _⟩ | h'
      · exact ⟨rfl, rfl⟩
      · have := (occurs_bounds lp ps as _ q' b' _ hnr h').1
        omega
    · rcases h' with ⟨rfl, rfl, rfl⟩ | h'
      · have := (occurs_bounds lp ps as _ q b _ hnr h).1
        omega
      · exact occurs_unique lp ps as _ q q' b b' off (fun r hr => hps r (by simp [hr])) h h'

/-- Two parameters at different offsets share no byte. -/
theorem occurs_apart (lp : Prog) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q q' : Lang.Param)
    (b b' : Expr) (off off' : Nat), (∀ prm, prm ∈ ps → prm.byRef = false) →
    Occurs lp ps args lo q b off → Occurs lp ps args lo q' b' off' → off ≠ off' →
    off + sizeOf lp q.ty ≤ off' ∨ off' + sizeOf lp q'.ty ≤ off
  | [], _, _, _, _, _, _, _, _, _, h, _, _ => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, _, _, _, h, _, _ => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, q', b, b', off, off', hnr, h, h', hne => by
    have hnr' : ∀ r, r ∈ ps → r.byRef = false := fun r hr => hnr r (by simp [hr])
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · rcases h' with ⟨rfl, rfl, rfl⟩ | h'
      · exact absurd rfl hne
      · exact .inl (occurs_bounds lp ps as _ q' b' _ hnr' h').1
    · rcases h' with ⟨rfl, rfl, rfl⟩ | h'
      · exact .inr (occurs_bounds lp ps as _ q b _ hnr' h).1
      · exact occurs_apart lp ps as _ q q' b b' off off' hnr' h h' hne

/-- A slot of the parameters has its argument. -/
theorem occurs_of_mem (lp : Prog) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q : Lang.Param)
    (off : Nat), (∀ prm, prm ∈ ps → prm.byRef = false) → args.length = ps.length →
    (q, off) ∈ (paramSlotsFrom lp ps lo).1 → ∃ b, Occurs lp ps args lo q b off
  | [], _, _, _, _, _, _, h => by simp [paramSlotsFrom] at h
  | prm :: ps, [], _, _, _, _, hl, _ => by simp at hl
  | prm :: ps, a :: as, lo, q, off, hnr, hl, h => by
    rw [slots_cons lp prm ps lo (hnr prm (by simp))] at h
    rcases List.mem_cons.mp h with he | hr
    · cases he
      exact ⟨a, .inl ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, hb⟩ := occurs_of_mem lp ps as _ q off (fun r hr' => hnr r (by simp [hr'])) (by simpa using hl) hr
      exact ⟨b, .inr hb⟩

/-- The argument that travels in a register: the one at the offset `inReg`. -/
def regPick (lp : Prog) (inReg : Option Nat) : List Lang.Param → List Expr → Nat → Option Expr → Option Expr
  | prm :: ps, a :: as, lo, r =>
    if inReg == some lo then regPick lp inReg ps as (lo + sizeOf lp prm.ty) (some a)
    else regPick lp inReg ps as (lo + sizeOf lp prm.ty) r
  | _, _, _, r => r

theorem regPick_none (lp : Prog) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (r : Option Expr),
    regPick lp none ps args lo r = r
  | [], _, _, _ => by simp [regPick]
  | _ :: _, [], _, _ => by simp [regPick]
  | prm :: ps, a :: as, lo, r => by
    simp only [regPick]
    exact regPick_none lp ps as _ r

/-- What `regPick` finds is an argument at that offset (or what it started with). -/
theorem regPick_spec (lp : Prog) (ro : Nat) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat)
    (r : Option Expr) (a : Expr), regPick lp (some ro) ps args lo r = some a →
    r = some a ∨ ∃ q, Occurs lp ps args lo q a ro
  | [], _, _, _, _, h => by simp [regPick] at h; exact .inl h
  | _ :: _, [], _, _, _, h => by simp [regPick] at h; exact .inl h
  | prm :: ps, b :: as, lo, r, a, h => by
    simp only [regPick] at h
    by_cases hlo : (some ro == some lo) = true
    · rw [if_pos hlo] at h
      have hro : ro = lo := by simpa using hlo
      rcases regPick_spec lp ro ps as _ (some b) a h with h1 | ⟨q, hq⟩
      · cases h1
        exact .inr ⟨prm, .inl ⟨rfl, rfl, hro⟩⟩
      · exact .inr ⟨q, .inr hq⟩
    · rw [if_neg hlo] at h
      rcases regPick_spec lp ro ps as _ r a h with h1 | ⟨q, hq⟩
      · exact .inl h1
      · exact .inr ⟨q, .inr hq⟩

/-- An argument at that offset: `regPick` finds one. -/
theorem regPick_some (lp : Prog) (ro : Nat) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat)
    (r : Option Expr) (q : Lang.Param) (b : Expr), Occurs lp ps args lo q b ro →
    ∃ a, regPick lp (some ro) ps args lo r = some a
  | [], _, _, _, _, _, h => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, h => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, r, q, b, h => by
    simp only [regPick]
    have hrest : ∀ r' : Option Expr, r'.isSome = true →
        ∃ a', regPick lp (some ro) ps as (lo + sizeOf lp prm.ty) r' = some a' := by
      intro r' hr'
      cases hp : regPick lp (some ro) ps as (lo + sizeOf lp prm.ty) r' with
      | some a' => exact ⟨a', rfl⟩
      | none =>
        -- nothing found, so what it started with: which is something
        exfalso
        have : ∀ (ps : List Lang.Param) (as : List Expr) (lo : Nat) (r' : Option Expr), r'.isSome = true →
            (regPick lp (some ro) ps as lo r').isSome = true := by
          intro ps
          induction ps with
          | nil => intro as lo r' h'; simpa [regPick] using h'
          | cons p ps ih =>
            intro as lo r' h'
            cases as with
            | nil => simpa [regPick] using h'
            | cons x xs =>
              simp only [regPick]
              split
              · exact ih xs _ _ rfl
              · exact ih xs _ _ h'
        have h2 := this ps as (lo + sizeOf lp prm.ty) r' hr'
        rw [hp] at h2
        cases h2
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · rw [if_pos (by simp)]
      exact hrest _ rfl
    · by_cases hlo : (some ro == some lo) = true
      · rw [if_pos hlo]
        exact hrest _ rfl
      · rw [if_neg hlo]
        exact regPick_some lp ro ps as _ r q b h

/-- The arguments' values, one for each parameter, each of its type. -/
theorem evalArgs_occurs (lp : Prog) (E : Env) (hp : E.prog = lp) (lst : Lang.Sem.St) (env : Lang.Sem.Env)
    (hvt : VarsTyped E lst env) : ∀ (ps : List Lang.Param) (args : List Expr) (vs : List Val) (lo : Nat)
    (q : Lang.Param) (b : Expr) (off : Nat), ArgsOK E (ps.map (·.ty)) args →
    Lang.Sem.evalArgs lp lst env args = some vs → Occurs lp ps args lo q b off →
    ∃ v, Lang.Sem.evalE lp lst env b = some v ∧ HasTy lp q.ty v ∧ WT E b ∧ E.tyOf b = .ok q.ty ∧
      q.ty.isScalar = true
  | [], _, _, _, _, _, _, _, _, h => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, _, _, h => by simp [Occurs] at h
  | prm :: ps, a :: as, vs, lo, q, b, off, hw, hev, h => by
    obtain ⟨hwa, hta, hsa, hrest⟩ := hw
    simp only [Lang.Sem.evalArgs] at hev
    cases hva : Lang.Sem.evalE lp lst env a with
    | none => simp [hva] at hev
    | some v =>
      cases hvs : Lang.Sem.evalArgs lp lst env as with
      | none => simp [hva, hvs] at hev
      | some vs' =>
        rcases h with ⟨rfl, rfl, rfl⟩ | h
        · subst hp
          exact ⟨v, hva, evalE_hasTy E lst env hvt b v _ hwa hva hta, hwa, hta, hsa⟩
        · exact evalArgs_occurs lp E hp lst env hvt ps as vs' _ q b off hrest hvs h

/-! ## The arguments, into the callee's frame -/

/-- Every argument that does not travel in the register has a value. -/
def NonRegOK (lp : Prog) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (inReg : Option Nat) :
    List Lang.Param → List Expr → Nat → Prop
  | prm :: ps, a :: as, lo =>
    (inReg = some lo ∨ (Lang.Sem.evalE lp lst env a).isSome = true) ∧
      NonRegOK lp lst env inReg ps as (lo + sizeOf lp prm.ty)
  | _, _, _ => True

/-- The value of every such argument is in its parameter's slot. -/
def PHold (c : Ctx) (lp : Prog) (g : String) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (inReg : Option Nat)
    (m : ByteArray) : List Lang.Param → List Expr → Nat → Prop
  | prm :: ps, a :: as, lo =>
    (inReg = some lo ∨ ∃ v, Lang.Sem.evalE lp lst env a = some v ∧
        rd m (fbase c g + lo) (sizeOf lp prm.ty) = v.toNat) ∧
      PHold c lp g lst env inReg m ps as (lo + sizeOf lp prm.ty)
  | _, _, _ => True

theorem phold_occurs {c : Ctx} {lp : Prog} {g : String} {lst : Lang.Sem.St} {env : Lang.Sem.Env}
    {inReg : Option Nat} {m : ByteArray} : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q : Lang.Param)
    (b : Expr) (off : Nat), PHold c lp g lst env inReg m ps args lo → Occurs lp ps args lo q b off →
    inReg ≠ some off → ∃ v, Lang.Sem.evalE lp lst env b = some v ∧ rd m (fbase c g + off) (sizeOf lp q.ty) = v.toNat
  | [], _, _, _, _, _, _, h, _ => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, h, _ => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, b, off, hp, h, hne => by
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · rcases hp.1 with h1 | h1
      · exact absurd h1 hne
      · exact h1
    · exact phold_occurs ps as _ q b off hp.2 h hne

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

/-- The code for the arguments: all those that do not travel in the
register have values, which are then in the callee's frame; or one has
none, and the code traps. -/
def GSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (g : String) (inReg : Option Nat) (ps : List Lang.Param)
    (args : List Expr) (lo : Nat) (s s' : LS) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    (∀ A, fbase c g + lo ≤ A → A < fbase c g + (paramSlotsFrom E.prog ps lo).2 →
      ¬ InGlobals E.prog c A ∧ ¬ (fbase c E.fn ≤ A ∧ A < fbase c E.fn + cur)) →
    fbase c g + (paramSlotsFrom E.prog ps lo).2 ≤ 65536 →
    (NonRegOK E.prog lst env inReg ps args lo →
      ∃ m1 tmps', Reach c f s.out.size tmps ist s'.out.size tmps' { ist with mem := m1 } ∧
        tmps'.size = tmps.size ∧ m1.size = 65536 ∧
        (∀ A, A < fbase c g + lo ∨ fbase c g + (paramSlotsFrom E.prog ps lo).2 ≤ A →
          m1.get! A = ist.mem.get! A) ∧
        PHold c E.prog g lst env inReg m1 ps args lo) ∧
    (¬ NonRegOK E.prog lst env inReg ps args lo →
      ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = ist.world)

/-- What `callArgs` promises. -/
def GPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (g : String) (inReg : Option Nat) (ps : List Lang.Param)
    (args : List Expr) (lo : Nat) (reg0 : Option Expr) (s : LS) (reg : Option Expr) (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ reg = regPick E.prog inReg ps args lo reg0 ∧ GSem c f sF E g inReg ps args lo s s'

theorem callArgs_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (g : String)
    (inReg : Option Nat) : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (reg0 : Option Expr) (s : LS),
    (∀ prm, prm ∈ ps → prm.byRef = false) → ArgsOK E (ps.map (·.ty)) args →
    wp (callArgs g inReg ((paramSlotsFrom E.prog ps lo).1.zip args) reg0) E
      (GPost c f sF E g inReg ps args lo reg0 s) s
  | [], args, lo, reg0, s, _, _ => by
    simp only [paramSlotsFrom, List.zip_nil_left, callArgs, wp_pure]
    refine ⟨Ext.refl s, rfl, by simp [regPick], ?_⟩
    intro cur lst env ist tmps hxF hrel hsz hfr hb
    exact ⟨fun _ => ⟨ist.mem, tmps, Reach.refl, rfl, hrel.size, fun _ _ => rfl, trivial⟩,
      fun hn => absurd trivial hn⟩
  | prm :: ps, [], _, _, _, _, hw => hw.elim
  | prm :: ps, a :: as, lo, reg0, s, hps, hw => by
    obtain ⟨hwa, hta, hsa, hrest⟩ := hw
    have hbr : prm.byRef = false := hps prm (by simp)
    have hps' : ∀ r, r ∈ ps → r.byRef = false := fun r hr => hps r (by simp [hr])
    have hsnd : (paramSlotsFrom E.prog (prm :: ps) lo).2 =
        (paramSlotsFrom E.prog ps (lo + sizeOf E.prog prm.ty)).2 := by rw [slots_cons E.prog prm ps lo hbr]
    rw [slots_cons E.prog prm ps lo hbr]
    simp only [List.zip_cons_cons, callArgs, hbr, Bool.false_eq_true, if_false]
    by_cases hreg : (inReg == some lo) = true
    · rw [if_pos hreg]
      have hreg' : inReg = some lo := by simpa using hreg
      refine wp_mono (callArgs_ok F L hE g inReg ps as (lo + sizeOf E.prog prm.ty) (some a) s hps' hrest) ?_
      intro reg s' ⟨hx, hc, hr, hsem⟩
      refine ⟨hx, hc, by rw [hr]; simp only [regPick, hreg, if_true], ?_⟩
      intro cur lst env ist tmps hxF hrel hsz hfr hb
      simp only [hsnd] at hfr hb ⊢
      obtain ⟨h1, h2⟩ := hsem cur lst env ist tmps hxF hrel hsz (fun A a1 a2 => hfr A (by omega) a2) hb
      refine ⟨fun hn => ?_, fun hn => ?_⟩
      · obtain ⟨m1, t', r, sz, hm1, hag, hph⟩ := h1 hn.2
        exact ⟨m1, t', r, sz, hm1, fun A hA => hag A (by omega), ⟨.inl hreg', hph⟩⟩
      · exact h2 (fun hn' => hn ⟨.inl hreg', hn'⟩)
    · rw [if_neg hreg]
      have hreg' : inReg ≠ some lo := by simpa using hreg
      simp only [wp_bind]
      refine wp_mono (exprToSlot_ok F L hE a prm.ty _ s hwa hta hsa) ?_
      intro _ s1 ⟨hx1, hc1, hs1⟩
      refine wp_mono (callArgs_ok F L hE g inReg ps as (lo + sizeOf E.prog prm.ty) reg0 s1 hps' hrest) ?_
      intro reg s' ⟨hx, hc, hr, hsem⟩
      refine ⟨hx1.trans hx, by rw [hc, hc1], by rw [hr]; simp only [regPick, hreg, Bool.false_eq_true, if_false], ?_⟩
      intro cur lst env ist tmps hxF hrel hsz hfr hb
      simp only [hsnd] at hfr hb ⊢
      have hend := slots_end_ge E.prog ps (lo + sizeOf E.prog prm.ty)
      have h1 := hs1 cur lst env ist tmps (hx.trans hxF) hrel hsz
      cases hev : Lang.Sem.evalE E.prog lst env a with
      | none =>
        simp only [hev] at h1
        refine ⟨fun hn => ?_, fun _ => ⟨ist, h1, rfl⟩⟩
        rcases hn.1 with h | h
        · exact absurd h hreg'
        · rw [hev] at h; cases h
      | some v =>
        simp only [hev] at h1
        obtain ⟨t1, sz1, _, r1⟩ := h1
        rw [setDst_slot, addr_frame] at r1
        have hv := evalE_hasTy E lst env (hrel.typed L) a v _ hwa hev hta
        have hms := hrel.size
        have hout : ∀ A, A < fbase c g + lo ∨ fbase c g + lo + sizeOf E.prog prm.ty ≤ A →
            (wr ist.mem (fbase c g + lo) (sizeOf E.prog prm.ty) v.toNat).get! A = ist.mem.get! A :=
          fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
        have hrel1 : SRel c E cur lst env
            { ist with mem := wr ist.mem (fbase c g + lo) (sizeOf E.prog prm.ty) v.toNat } := by
          refine hrel.frame L (by rw [wr_size]; exact hms) (fun A hA => hout A ?_)
          by_cases hin : fbase c g + lo ≤ A ∧ A < fbase c g + lo + sizeOf E.prog prm.ty
          · have := hfr A hin.1 (by omega)
            rcases hA with h | h
            · exact absurd h this.1
            · exact absurd h this.2
          · omega
        obtain ⟨h2a, h2b⟩ := hsem cur lst env _ t1 hxF hrel1 (by rw [sz1]; exact hsz)
          (fun A a1 a2 => hfr A (by omega) a2) hb
        refine ⟨fun hn => ?_, fun hn => ?_⟩
        · obtain ⟨m1, t', r, sz, hm1, hag, hph⟩ := h2a hn.2
          refine ⟨m1, t', r1.trans r, by rw [sz, sz1], hm1, fun A hA => ?_, ⟨.inr ⟨v, hev, ?_⟩, hph⟩⟩
          · rw [hag A (by omega)]
            exact hout A (by omega)
          · rw [rd_congr _ m1 _ _ (by omega) (fun x x1 x2 => hag x (by omega)),
              rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (toNat_lt hv hsa)]
        · obtain ⟨ist', he, hw'⟩ := h2b (fun hn' => hn ⟨.inr (by rw [hev]; rfl), hn'⟩)
          exact ⟨ist', r1.ends he, hw'⟩

end

/-! ## The callee -/

/-- The context's program is the lowering of `lp`, as emitted. -/
structure Lowered (lp : Prog) (c : Ctx) : Prop where
  fns : ∀ g fd, lp.fn? g = some fd → ∃ gf, c.prog.fn? g = some gf ∧ lowerFnRaw lp fd = .ok gf
  drops : c.dropReasons = lp.dropReasons
  notes : c.notes = lp.notes

theorem lowerFnRaw_shape {lp : Prog} {fd : Lang.Fn} {gf : IR.Fn} (h : lowerFnRaw lp fd = .ok gf) :
    gf.regParam = regParamSlot lp fd ∧ (paramSlots lp fd).2 ≤ gf.frame := by
  unfold lowerFnRaw at h
  split at h
  · cases h
    exact ⟨rfl, Nat.le_max_right _ _⟩
  · cases h

/-- The values of the arguments are in the parameters' slots. -/
def ParamsAt (c : Ctx) (lp : Prog) (g : String) (m : ByteArray) : List (Lang.Param × Nat) → List Val → Prop
  | [], [] => True
  | (prm, off) :: ps, v :: vs =>
    HasTy lp prm.ty v ∧ rd m (fbase c g + off) (sizeOf lp prm.ty) = v.toNat ∧ ParamsAt c lp g m ps vs
  | _, _ => False

/-- The value a block returns, if it returns one. -/
def outVal : Lang.Sem.Out → Option Val
  | .ret v => v
  | _ => none

theorem call_eq (lp : Prog) (k : Nat) (lst : Lang.Sem.St) (g : String) (vs : List Val) (fd : Lang.Fn)
    (hfd : lp.fn? g = some fd) :
    Lang.Sem.call k lp lst g vs =
      match Lang.Sem.execB k lp lst ((fd.params.map (·.name)).zip vs) fd.body with
      | .ok st' _ o => .ok (outVal o) st'
      | .trap st' => .trap st'
      | .fuel => .fuel := by
  simp only [Lang.Sem.call, hfd]
  cases Lang.Sem.execB k lp lst ((fd.params.map (·.name)).zip vs) fd.body with
  | fuel => rfl
  | trap _ => rfl
  | ok st' env' o => cases o <;> rfl

/-- **The code of every function simulates the function**, for `k` units of fuel. -/
def FnSim (c : Ctx) (lp : Prog) (k : Nat) : Prop :=
  ∀ g fd lst vs ist, lp.fn? g = some fd → GS c lp lst ist → ParamsAt c lp g ist.mem (paramSlots lp fd).1 vs →
    match Lang.Sem.execB k lp lst ((fd.params.map (·.name)).zip vs) fd.body with
    | .fuel => True
    | .trap lst' => ∃ m ist', callF m c g ist = .trap ist' ∧ ist'.world = lst'.world
    | .ok lst' _ o => ∃ m ist', callF m c g ist = .ok ((outVal o).map Val.toNat) ist' ∧ GS c lp lst' ist' ∧
        KeepOut c lp g ist.mem ist'.mem ∧ RetOK lp fd.ret (outVal o)

theorem reach_trans {p : IR.Prog} {a b d : String} (h1 : IR.Reach p a b) (h2 : IR.Reach p b d) : IR.Reach p a d := by
  induction h2 with
  | call hc => exact .step h1 hc
  | step _ hc ih => exact .step ih hc

/-- A call in the body: the callee can be reached. -/
theorem reach_of_call {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS} (F : Final c fn f sF) {pc : Nat} {g : String}
    {ret : Option (Nat × Dst)} {reg : Option (Nat × Opd)} (hb : f.body[pc]? = some (.call g ret reg)) :
    IR.Reach c.prog fn g := by
  refine .call ?_
  simp only [calleesOf, F.fn, Option.map_some, Option.getD_some, IR.Fn.callees]
  rw [List.mem_eraseDups]
  refine List.mem_append.mpr (.inl ?_)
  simp only [IR.Fn.calls, List.mem_filterMap]
  exact ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb), rfl⟩

/-- An address the caller cares about is none of the callee's. -/
theorem callee_keeps {lp : Prog} {c : Ctx} (L : LayOK lp c) {fn g : String} (hr : IR.Reach c.prog fn g) {A : Nat}
    (hA : Outside lp c fn A ∨ InFrame c fn A) : ¬ InFrame c g A ∧ Outside lp c g A := by
  rcases hA with ⟨h1, h2, h3⟩ | hin
  · exact ⟨h3 g hr, h1, h3 g hr, fun h hh => h3 h (reach_trans hr hh)⟩
  · exact ⟨L.fapart fn g A hr hin, L.fglob fn A hin, L.fapart fn g A hr hin,
      fun h hh => L.fapart fn h A (reach_trans hr hh) hin⟩

/-! ## Arguments, again -/

theorem argsOK_length {E : Env} : ∀ (ts : List Ty) (args : List Expr), ArgsOK E ts args → args.length = ts.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ts, _ :: as, h => by simp [argsOK_length ts as h.2.2.2]

theorem argsOK_occurs {E : Env} : ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q : Lang.Param)
    (b : Expr) (off : Nat), ArgsOK E (ps.map (·.ty)) args → Occurs E.prog ps args lo q b off →
    WT E b ∧ E.tyOf b = .ok q.ty ∧ q.ty.isScalar = true
  | [], _, _, _, _, _, _, h => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, b, off, hw, h => by
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨hw.1, hw.2.1, hw.2.2.1⟩
    · exact argsOK_occurs ps as _ q b off hw.2.2.2 h

/-- Arguments that all have values. -/
theorem evalArgs_of_occurs (lp : Prog) (lst : Lang.Sem.St) (env : Lang.Sem.Env) : ∀ (ps : List Lang.Param)
    (args : List Expr) (lo : Nat), args.length = ps.length →
    (∀ q b off, Occurs lp ps args lo q b off → (Lang.Sem.evalE lp lst env b).isSome = true) →
    ∃ vs, Lang.Sem.evalArgs lp lst env args = some vs
  | [], [], _, _, _ => ⟨[], rfl⟩
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | prm :: ps, a :: as, lo, hl, h => by
    obtain ⟨vs, hvs⟩ := evalArgs_of_occurs lp lst env ps as (lo + sizeOf lp prm.ty) (by simpa using hl)
      (fun q b off ho => h q b off (.inr ho))
    have ha := h prm a lo (.inl ⟨rfl, rfl, rfl⟩)
    cases hva : Lang.Sem.evalE lp lst env a with
    | none => rw [hva] at ha; cases ha
    | some v => exact ⟨v :: vs, by simp only [Lang.Sem.evalArgs, hva, hvs]⟩

theorem nonReg_occurs {lp : Prog} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {inReg : Option Nat} :
    ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat) (q : Lang.Param) (b : Expr) (off : Nat),
    NonRegOK lp lst env inReg ps args lo → Occurs lp ps args lo q b off → inReg ≠ some off →
    (Lang.Sem.evalE lp lst env b).isSome = true
  | [], _, _, _, _, _, _, h, _ => by simp [Occurs] at h
  | _ :: _, [], _, _, _, _, _, h, _ => by simp [Occurs] at h
  | prm :: ps, a :: as, lo, q, b, off, hn, h, hne => by
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · rcases hn.1 with h1 | h1
      · exact absurd h1 hne
      · exact h1
    · exact nonReg_occurs ps as _ q b off hn.2 h hne

theorem nonReg_of_occurs {lp : Prog} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {inReg : Option Nat} :
    ∀ (ps : List Lang.Param) (args : List Expr) (lo : Nat),
    (∀ q b off, Occurs lp ps args lo q b off → (Lang.Sem.evalE lp lst env b).isSome = true) →
    NonRegOK lp lst env inReg ps args lo
  | [], _, _, _ => by simp [NonRegOK]
  | _ :: _, [], _, _ => by simp [NonRegOK]
  | prm :: ps, a :: as, lo, h =>
    ⟨.inr (h prm a lo (.inl ⟨rfl, rfl, rfl⟩)), nonReg_of_occurs ps as _ (fun q b off ho => h q b off (.inr ho))⟩

/-- The parameters hold the arguments' values, when every slot does. -/
theorem paramsAt_of {c : Ctx} {lp : Prog} {g : String} {m : ByteArray} {lst : Lang.Sem.St} {env : Lang.Sem.Env} :
    ∀ (ps : List Lang.Param) (args : List Expr) (vs : List Val) (lo : Nat),
    (∀ prm, prm ∈ ps → prm.byRef = false) → Lang.Sem.evalArgs lp lst env args = some vs →
    args.length = ps.length →
    (∀ q b off, Occurs lp ps args lo q b off → ∃ v, Lang.Sem.evalE lp lst env b = some v ∧ HasTy lp q.ty v ∧
      rd m (fbase c g + off) (sizeOf lp q.ty) = v.toNat) →
    ParamsAt c lp g m (paramSlotsFrom lp ps lo).1 vs
  | [], [], vs, _, _, hev, _, _ => by
    simp only [Lang.Sem.evalArgs, Option.some.injEq] at hev
    subst hev
    trivial
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | prm :: ps, a :: as, vs, lo, hnr, hev, hl, h => by
    rw [slots_cons lp prm ps lo (hnr prm (by simp))]
    simp only [Lang.Sem.evalArgs] at hev
    cases hva : Lang.Sem.evalE lp lst env a with
    | none => simp [hva] at hev
    | some v =>
      cases hvs : Lang.Sem.evalArgs lp lst env as with
      | none => simp [hva, hvs] at hev
      | some vs' =>
        simp only [hva, hvs, Option.some.injEq] at hev
        subst hev
        obtain ⟨v', hv', hty, hrd⟩ := h prm a lo (.inl ⟨rfl, rfl, rfl⟩)
        rw [hva] at hv'
        cases hv'
        exact ⟨hty, hrd, paramsAt_of ps as vs' _ (fun r hr => hnr r (by simp [hr])) hvs (by simpa using hl)
          (fun q b off ho => h q b off (.inr ho))⟩

/-! ## The call -/

theorem size_pos (p : Prog) {t : Ty} (h : t.isScalar = true) : 0 < sizeOf p t := by
  cases t with
  | int w => cases w <;> simp [IR.sizeOf, Width.bits]
  | bool => simp [IR.sizeOf]
  | arr _ _ => simp [Ty.isScalar] at h
  | record _ => simp [Ty.isScalar] at h

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

/-- **The code up to an invocation** (a call or an effect), which ends
at `s1` and is followed by the instruction `mk ret`: the arguments are
evaluated, the invocation `act` happens, and its result is stored where
`ret` says. -/
def ISem (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (args : List Expr)
    (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (retTy : Option Ty) (s s1 : LS)
    (mk : Option (Nat × Dst) → Instr) : Prop :=
  ∀ k ret cur lst env ist tmps, k < N → Ext s1 sF → f.body[s1.out.size]? = some (mk ret) →
    SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalArgs E.prog lst env args with
    | none => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = ist.world
    | some vs =>
      match act k lst vs with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok v lst' => ∃ ist2 tmps1,
          Reach c f s.out.size tmps ist (s1.out.size + 1) (setRet c ist2 tmps1 ret (v.map Val.toNat)).2
            (setRet c ist2 tmps1 ret (v.map Val.toNat)).1 ∧
          tmps1.size = tmps.size ∧ SRel c E cur lst' env ist2 ∧ Keep c E cur ist.mem ist2.mem ∧
          RetOK E.prog retTy v

/-- What `callInstr` and `effInstr` promise. -/
def IPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (args : List Expr)
    (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (retTy : Option Ty) (s : LS)
    (r : Option Nat × (Option (Nat × Dst) → Instr)) (s1 : LS) : Prop :=
  Ext s s1 ∧ s1.cur = s.cur ∧ r.1 = retTy.map (sizeOf E.prog) ∧ ISem c f sF N E args act retTy s s1 r.2

/-- The argument that travels in the register, as an operand. -/
def RegSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (fd : Lang.Fn) (args : List Expr) (reg : Option (Nat × Opd))
    (s1 s2 : LS) : Prop :=
  match regParamOf E.prog fd with
  | none => reg = none ∧ s2 = s1
  | some pr => ∃ a o, reg = some (sizeOf E.prog pr.1.ty, o) ∧ Occurs E.prog fd.params args 0 pr.1 a pr.2 ∧
      ESem c f sF E a (sizeOf E.prog pr.1.ty) s1 s2 o

theorem call_sem (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hfn : E.fn = fn) (hlow : Lowered E.prog c)
    (N : Nat) (H : ∀ k, k < N → FnSim c E.prog k) (g : String) (args : List Expr) (fd : Lang.Fn)
    (hfd : E.prog.fn? g = some fd) (hFn : FnOK E.prog fd) (hargs : ArgsOK E (fd.params.map (·.ty)) args)
    (s s1 s2 : LS) (reg : Option (Nat × Opd)) (hx12 : Ext s1 s2)
    (hs1 : GSem c f sF E g ((regParamOf E.prog fd).map (·.2)) fd.params args 0 s s1)
    (hreg : RegSem c f sF E fd args reg s1 s2) :
    ISem c f sF N E args (fun k lst vs => Lang.Sem.call k E.prog lst g vs) fd.ret s s2
      (fun r => Instr.call g r reg) := by
  intro k ret cur lst env ist tmps hk hxF hb hrel hsz
  obtain ⟨gf, hgf, hlow'⟩ := hlow.fns g fd hfd
  obtain ⟨hrp, hframe⟩ := lowerFnRaw_shape hlow'
  have hname := fn?_name hfd
  have hps : ∀ prm, prm ∈ fd.params → prm.byRef = false := fun p h => (hFn.params p h).1
  have hpos : ∀ prm, prm ∈ fd.params → prm.byRef = false ∧ 0 < sizeOf E.prog prm.ty :=
    fun p h => ⟨(hFn.params p h).1, size_pos _ (hFn.params p h).2⟩
  have hlen : args.length = fd.params.length := by
    have := argsOK_length _ _ hargs
    simpa using this
  have hreach : IR.Reach c.prog E.fn g := by rw [hfn]; exact reach_of_call F hb
  obtain ⟨f', hf', hfit⟩ := hrel.fit
  have hgb := L.fbound g gf hgf
  have hpsz : (paramSlotsFrom E.prog fd.params 0).2 ≤ gf.frame := hframe
  -- the callee's parameters are in its frame
  have hin : ∀ A, fbase c g ≤ A → A < fbase c g + (paramSlotsFrom E.prog fd.params 0).2 → InFrame c g A :=
    fun A a1 a2 => ⟨gf, hgf, a1, by omega⟩
  have hfr : ∀ A, fbase c g + 0 ≤ A → A < fbase c g + (paramSlotsFrom E.prog fd.params 0).2 →
      ¬ InGlobals E.prog c A ∧ ¬ (fbase c E.fn ≤ A ∧ A < fbase c E.fn + cur) :=
    fun A a1 a2 => ⟨L.fglob g A (hin A (by omega) a2),
      fun hc => L.fapart E.fn g A hreach ⟨f', hf', hc.1, by omega⟩ (hin A (by omega) a2)⟩
  have hG := hs1 cur lst env ist tmps (hx12.trans hxF) hrel hsz hfr (by omega)
  -- after the arguments, the relation still holds
  have hframe1 : ∀ (m1 : ByteArray), m1.size = 65536 →
      (∀ A, A < fbase c g + 0 ∨ fbase c g + (paramSlotsFrom E.prog fd.params 0).2 ≤ A →
        m1.get! A = ist.mem.get! A) → SRel c E cur lst env { ist with mem := m1 } := by
    intro m1 hm1 hag1
    refine hrel.frame L hm1 (fun A hA => hag1 A ?_)
    by_cases hc : fbase c g + 0 ≤ A ∧ A < fbase c g + (paramSlotsFrom E.prog fd.params 0).2
    · have := hfr A hc.1 hc.2
      rcases hA with h | h
      · exact absurd h this.1
      · exact absurd h this.2
    · omega
  cases hev : Lang.Sem.evalArgs E.prog lst env args with
  | none =>
    simp only []
    by_cases hnr : NonRegOK E.prog lst env ((regParamOf E.prog fd).map (·.2)) fd.params args 0
    · obtain ⟨m1, t1, r1, sz1, hm1, hag1, hph⟩ := hG.1 hnr
      have hrel1 := hframe1 m1 hm1 hag1
      unfold RegSem at hreg
      -- every other argument has a value: the one in the register has none
      cases hrpo : regParamOf E.prog fd with
      | none =>
        exfalso
        simp only [hrpo, Option.map_none] at hnr
        obtain ⟨vs, hvs⟩ := evalArgs_of_occurs E.prog lst env fd.params args 0 hlen
          (fun q b off ho => nonReg_occurs _ _ _ q b off hnr ho (by simp))
        rw [hvs] at hev
        cases hev
      | some pr =>
        obtain ⟨prm, ro⟩ := pr
        simp only [hrpo, Option.map_some] at hreg hnr
        obtain ⟨a, o, _, hoa, hsa⟩ := hreg
        cases hva : Lang.Sem.evalE E.prog lst env a with
        | none =>
          have h2 := hsa cur lst env { ist with mem := m1 } t1 hxF hrel1 (by rw [sz1]; exact hsz)
          simp only [hva] at h2
          exact ⟨_, r1.ends h2, rfl⟩
        | some v =>
          exfalso
          obtain ⟨vs, hvs⟩ := evalArgs_of_occurs E.prog lst env fd.params args 0 hlen (fun q b off ho => by
            by_cases hoff : off = ro
            · subst hoff
              obtain ⟨_, rfl⟩ := occurs_unique E.prog fd.params args 0 q prm b a off hpos ho hoa
              rw [hva]; rfl
            · exact nonReg_occurs _ _ _ q b off hnr ho (by simpa using fun h => hoff h.symm))
          rw [hvs] at hev
          cases hev
    · exact hG.2 hnr
  | some vs =>
    simp only []
    have hocc : ∀ q b off, Occurs E.prog fd.params args 0 q b off →
        ∃ v, Lang.Sem.evalE E.prog lst env b = some v ∧ HasTy E.prog q.ty v ∧ WT E b ∧ E.tyOf b = .ok q.ty ∧
          q.ty.isScalar = true :=
      fun q b off ho => evalArgs_occurs E.prog E rfl lst env (hrel.typed L) fd.params args vs 0 q b off hargs hev ho
    have hnr : NonRegOK E.prog lst env ((regParamOf E.prog fd).map (·.2)) fd.params args 0 :=
      nonReg_of_occurs _ _ _ (fun q b off ho => by obtain ⟨v, hv, _⟩ := hocc q b off ho; rw [hv]; rfl)
    obtain ⟨m1, t1, r1, sz1, hm1, hag1, hph⟩ := hG.1 hnr
    have hrel1 := hframe1 m1 hm1 hag1
    -- the register argument, and the state the callee starts in
    have hstart : ∃ t2 m2, Reach c f s1.out.size t1 { ist with mem := m1 } s2.out.size t2 { ist with mem := m1 } ∧
        t2.size = t1.size ∧
        step c { ist with mem := m1 } t2 (.call g ret reg) = .call g { ist with mem := m2 } ret ∧
        m2.size = 65536 ∧ (∀ A, ¬ InFrame c g A → m2.get! A = m1.get! A) ∧
        ParamsAt c E.prog g m2 (paramSlots E.prog fd).1 vs := by
      unfold RegSem at hreg
      cases hrpo : regParamOf E.prog fd with
      | none =>
        simp only [hrpo, Option.map_none] at hreg hph
        obtain ⟨rfl, rfl⟩ := hreg
        refine ⟨t1, m1, Reach.refl, rfl, rfl, hm1, fun _ _ => rfl, ?_⟩
        refine paramsAt_of fd.params args vs 0 hps hev hlen (fun q b off ho => ?_)
        obtain ⟨v, hv, hty, _⟩ := hocc q b off ho
        obtain ⟨v', hv', hrd⟩ := phold_occurs _ _ _ q b off hph ho (by simp)
        rw [hv] at hv'
        cases hv'
        exact ⟨v, hv, hty, hrd⟩
      | some pr =>
        obtain ⟨prm, ro⟩ := pr
        simp only [hrpo, Option.map_some] at hreg hph
        obtain ⟨a, o, rfl, hoa, hsa⟩ := hreg
        obtain ⟨vr, hvr, htyr, hwa, hta, hsc⟩ := hocc prm a ro hoa
        have h2 := hsa cur lst env { ist with mem := m1 } t1 hxF hrel1 (by rw [sz1]; exact hsz)
        simp only [hvr] at h2
        obtain ⟨t2, r2, sz2, ag2, ho⟩ := h2
        have hbnd := occurs_bounds E.prog fd.params args 0 prm a ro hps hoa
        refine ⟨t2, wr m1 (fbase c g + ro) (sizeOf E.prog prm.ty) vr.toNat, r2, sz2, ?_,
          by rw [wr_size]; exact hm1, fun A hA => ?_, ?_⟩
        · simp only [step, hgf, hrp, regParamSlot, hrpo, Option.map_some, hname, addr_frame, ho]
        · refine wr_get_out _ _ _ _ _ (by omega) (by omega) ?_
          by_cases hc : fbase c g + ro ≤ A ∧ A < fbase c g + ro + sizeOf E.prog prm.ty
          · exact absurd (hin A (by omega) (by omega)) hA
          · omega
        · refine paramsAt_of fd.params args vs 0 hps hev hlen (fun q b off ho' => ?_)
          obtain ⟨v, hv, hty, _⟩ := hocc q b off ho'
          refine ⟨v, hv, hty, ?_⟩
          by_cases hoff : off = ro
          · subst hoff
            obtain ⟨rfl, rfl⟩ := occurs_unique E.prog fd.params args 0 q prm b a off hpos ho' hoa
            rw [hvr] at hv
            cases hv
            rw [rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (toNat_lt htyr hsc)]
          · obtain ⟨v', hv', hrd⟩ := phold_occurs _ _ _ q b off hph ho' (by simpa using fun h => hoff h.symm)
            rw [hv] at hv'
            cases hv'
            have hb2 := occurs_bounds E.prog fd.params args 0 q b off hps ho'
            have hap := occurs_apart E.prog fd.params args 0 q prm b a off ro hps ho' hoa hoff
            rw [rd_wr_out _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
            exact hrd
    obtain ⟨t2, m2, r2, sz2, hstep, hm2, hag2, hpar⟩ := hstart
    -- the callee
    have hgs : GS c E.prog lst { ist with mem := m2 } :=
      ⟨hm2, hrel.world, hrel1.glob.frame L (fun A hA => hag2 A (fun hin' => L.fglob g A hin' hA))⟩
    have hF := H k hk g fd lst vs { ist with mem := m2 } hfd hgs hpar
    rw [call_eq E.prog k lst g vs fd hfd]
    -- what the caller cares about, after the callee
    have hkeepA : ∀ (ist' : St), KeepOut c E.prog g m2 ist'.mem → ∀ A,
        (Outside E.prog c E.fn A ∨ InFrame c E.fn A) → ist'.mem.get! A = ist.mem.get! A := by
      intro ist' hko A hA
      obtain ⟨hng, hog⟩ := callee_keeps L hreach hA
      rw [hko A hog, hag2 A hng]
      refine hag1 A ?_
      by_cases hc : fbase c g ≤ A ∧ A < fbase c g + (paramSlotsFrom E.prog fd.params 0).2
      · exact absurd (hin A hc.1 hc.2) hng
      · omega
    cases hB : Lang.Sem.execB k E.prog lst ((fd.params.map (·.name)).zip vs) fd.body with
    | fuel => trivial
    | trap lst' =>
      simp only [hB] at hF ⊢
      obtain ⟨m, ist', hcf, hw⟩ := hF
      exact ⟨ist', r1.ends (r2.ends (Ends.call_trap hb hstep hcf)), hw⟩
    | ok lst' env' o =>
      simp only [hB] at hF ⊢
      obtain ⟨m, ist', hcf, hgs', hko, hret⟩ := hF
      have hfb := L.fbound _ _ hf'
      have htop := hrel.loc.2
      refine ⟨ist', t2, r1.trans (r2.trans (Reach.call hb hstep hcf)), by rw [sz2, sz1], ?_, ?_, hret⟩
      · refine ⟨hgs'.1, hgs'.2.1, hgs'.2.2, ⟨hrel.loc.1.frame (by omega) (fun o ho => ?_), htop⟩, ⟨f', hf', hfit⟩⟩
        have := inVars_lt_top ho
        exact hkeepA ist' hko _ (.inr ⟨f', hf', Nat.le_add_right _ _, by omega⟩)
      · intro A hA
        refine hkeepA ist' hko A ?_
        rcases hA with h | ⟨a1, a2, _⟩
        · exact .inl h
        · exact .inr ⟨f', hf', a1, by omega⟩

/-- **A call, up to its instruction.** -/
theorem callInstr_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn)
    (hlow : Lowered E.prog c) (hok : ProgOK E.prog) (N : Nat) (H : ∀ k, k < N → FnSim c E.prog k) (g : String)
    (args : List Expr) (fd : Lang.Fn) (hfd : E.prog.fn? g = some fd)
    (hargs : ArgsOK E (fd.params.map (·.ty)) args) (s : LS) :
    wp (callInstr g args) E
      (IPost c f sF N E args (fun k lst vs => Lang.Sem.call k E.prog lst g vs) fd.ret s) s := by
  have hFn := hok g fd hfd
  have hps : ∀ prm, prm ∈ fd.params → prm.byRef = false := fun p h => (hFn.params p h).1
  have hpos : ∀ prm, prm ∈ fd.params → prm.byRef = false ∧ 0 < sizeOf E.prog prm.ty :=
    fun p h => ⟨(hFn.params p h).1, size_pos _ (hFn.params p h).2⟩
  have hlen : args.length = fd.params.length := by
    have := argsOK_length _ _ hargs
    simpa using this
  unfold callInstr
  simp only [wp_bind, wp_read, hfd, paramSlots]
  refine wp_mono (callArgs_ok F L hE g _ fd.params args 0 none s hps hargs) ?_
  intro regArg s1 ⟨hx1, hc1, hreg, hs1⟩
  -- the end, whatever the register argument
  have fin : ∀ (reg : Option (Nat × Opd)) (s2 : LS), Ext s1 s2 → s2.cur = s1.cur →
      RegSem c f sF E fd args reg s1 s2 →
      wp (match fd.ret with
          | some t => do pure (some (← size t))
          | none => pure none) E
        (fun rn s' => IPost c f sF N E args (fun k lst vs => Lang.Sem.call k E.prog lst g vs) fd.ret s
          (rn, fun r => Instr.call g r reg) s') s2 := by
    intro reg s2 hx12 hc2 hrs
    have hsem := call_sem F L hfn hlow N H g args fd hfd hFn hargs s s1 s2 reg hx12 hs1 hrs
    cases hret : fd.ret with
    | none =>
      rw [hret] at hsem
      simp only [wp_bind, wp_pure]
      exact ⟨hx1.trans hx12, by rw [hc2, hc1], rfl, hsem⟩
    | some t =>
      rw [hret] at hsem
      simp only [wp_bind, wp_size, wp_pure]
      exact ⟨hx1.trans hx12, by rw [hc2, hc1], rfl, hsem⟩
  cases hrpo : regParamOf E.prog fd with
  | none =>
    have hra : regArg = none := by
      rw [hreg, hrpo]
      exact regPick_none _ _ _ _ _
    subst hra
    simp only [wp_pure]
    exact fin none s1 (Ext.refl _) rfl (by unfold RegSem; rw [hrpo]; exact ⟨rfl, rfl⟩)
  | some pr =>
    obtain ⟨prm, ro⟩ := pr
    have hrpo' := hrpo
    simp only [regParamOf, paramSlots] at hrpo'
    have hmem : (prm, ro) ∈ (paramSlotsFrom E.prog fd.params 0).1 :=
      List.mem_reverse.mp (List.mem_of_find?_eq_some hrpo')
    obtain ⟨b, hob⟩ := occurs_of_mem E.prog fd.params args 0 prm ro hps hlen hmem
    obtain ⟨a, ha⟩ := regPick_some E.prog ro fd.params args 0 none prm b hob
    have hoa : Occurs E.prog fd.params args 0 prm a ro := by
      rcases regPick_spec E.prog ro fd.params args 0 none a ha with h | ⟨q, hq⟩
      · cases h
      · obtain ⟨rfl, rfl⟩ := occurs_unique E.prog fd.params args 0 q prm a b ro hpos hq hob
        exact hob
    have hra : regArg = some a := by
      rw [hreg, hrpo]
      exact ha
    subst hra
    obtain ⟨hwa, hta, hsa⟩ := argsOK_occurs fd.params args 0 prm a ro hargs hoa
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hta] at ht
    cases ht
    refine wp_mono (expr_ok F a E s1 prm.ty L hE hwa hta hsa) ?_
    intro o s2 ⟨hx2, hc2, ho2, hs2⟩
    simp only [wp_pure]
    exact fin (some (sizeOf E.prog prm.ty, o)) s2 hx2 hc2 (by unfold RegSem; rw [hrpo]; exact ⟨a, o, rfl, hoa, hs2⟩)

/-! ## Effects -/

theorem getD_map_toNat (vs : List Val) (i : Nat) : (vs.map Val.toNat).getD i 0 = (vs.getD i (.bool false)).toNat := by
  induction vs generalizing i with
  | nil => simp [Val.toNat]
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem headD_eq_getD (vs : List Val) : vs.headD (.bool false) = vs.getD 0 (.bool false) := by
  cases vs <;> rfl

theorem ofNat_mod256 (x : Nat) : UInt8.ofNat (x % 256) = x.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [Nat.toUInt8]

/-- **An effect on the world is the same on both sides.** -/
theorem effect_sim (c : Ctx) (lp : Prog) (hd : c.dropReasons = lp.dropReasons) (hn : c.notes = lp.notes)
    (lst : Lang.Sem.St) (e : Effect) (vs : List Val) :
    ∃ w', (Lang.Sem.effect lp lst e vs).2 = { lst with world := w' } ∧
      IR.Sem.effect c lst.world e (vs.map Val.toNat) = ((Lang.Sem.effect lp lst e vs).1.map Val.toNat, w') ∧
      RetOK lp e.sig.2 (Lang.Sem.effect lp lst e vs).1 := by
  cases e with
  | inputNext =>
    refine ⟨lst.world.next.2, rfl, ?_, ?_⟩
    · simp [IR.Sem.effect, Lang.Sem.effect, Val.toNat]
    · exact ⟨_, rfl, rfl, by rw [UInt16.toNat_toUInt64]; exact lst.world.next.1.toNat_lt⟩
  | ringPop =>
    refine ⟨lst.world.next.2, rfl, ?_, ?_⟩
    · simp [IR.Sem.effect, Lang.Sem.effect, Val.toNat]
    · exact ⟨_, rfl, rfl, by rw [UInt16.toNat_toUInt64]; exact lst.world.next.1.toNat_lt⟩
  | inputFrame =>
    refine ⟨lst.world.nextFramed.2, rfl, ?_, ?_⟩
    · simp [IR.Sem.effect, Lang.Sem.effect, Val.toNat]
    · exact ⟨_, rfl, rfl, by rw [UInt16.toNat_toUInt64]; exact lst.world.nextFramed.1.toNat_lt⟩
  | outByte =>
    refine ⟨_, rfl, ?_, rfl⟩
    simp only [IR.Sem.effect, Lang.Sem.effect, getD_map_toNat, headD_eq_getD, ofNat_mod256, Option.map_none]
  | outEnd => exact ⟨_, rfl, rfl, rfl⟩
  | drop =>
    refine ⟨_, rfl, ?_, rfl⟩
    simp only [IR.Sem.effect, Lang.Sem.effect, getD_map_toNat, headD_eq_getD, hd, Option.map_none]
  | note =>
    refine ⟨_, rfl, ?_, rfl⟩
    simp only [IR.Sem.effect, Lang.Sem.effect, getD_map_toNat, headD_eq_getD, hn, Option.map_none]
  | mmioRead32 =>
    refine ⟨lst.world, rfl, ?_, ?_⟩
    · simp only [IR.Sem.effect, Lang.Sem.effect, getD_map_toNat, headD_eq_getD, Val.toNat, Nat.toUInt32,
        Option.map_some, UInt32.toNat_toUInt64]
    · exact ⟨_, rfl, rfl, by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _⟩
  | mmioWrite32 =>
    refine ⟨_, rfl, ?_, rfl⟩
    simp only [IR.Sem.effect, Lang.Sem.effect, getD_map_toNat, headD_eq_getD, Nat.toUInt32, Option.map_none]

/-- The arguments of an effect, as operands. -/
def OSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (args : List Expr) (s s' : LS) (os : List (Nat × Opd)) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalArgs E.prog lst env args with
    | none => Ends c f s.out.size tmps ist (.trap ist)
    | some vs => Runs c f ist s.out.size s'.out.size s.tmps.size tmps
        (fun t' => os.map (fun a => opd c ist t' a.1 a.2) = vs.map Val.toNat)

def OPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (args : List Expr) (s : LS) (os : List (Nat × Opd)) (s' : LS) :
    Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ (∀ x, x ∈ os → ∀ t, x.2 = .tmp t → t < s'.tmps.size) ∧ OSem c f sF E args s s' os

theorem effArgs_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) :
    ∀ (ts : List Ty) (args : List Expr) (s : LS), ArgsOK E ts args →
    wp (effArgs (ts.zip args)) E (OPost c f sF E args s) s
  | [], [], s, _ => by
    simp only [List.zip_nil_left, effArgs, wp_pure]
    refine ⟨Ext.refl s, rfl, by simp, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    simp only [Lang.Sem.evalArgs]
    exact Runs.done rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | t :: ts, a :: as, s, hw => by
    obtain ⟨hwa, hta, hsa, hrest⟩ := hw
    simp only [List.zip_cons_cons, effArgs, wp_bind, wp_size]
    refine wp_mono (expr_ok F a E s t L hE hwa hta hsa) ?_
    intro o s1 ⟨hx1, hc1, ho1, hs1⟩
    refine wp_mono (effArgs_ok F L hE ts as s1 hrest) ?_
    intro os s2 ⟨hx2, hc2, hos, hs2⟩
    rw [wp_pure]
    refine ⟨hx1.trans hx2, by rw [hc2, hc1], fun x hx t ht => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · have := (ho1.1 t ht).2
        have := hx2.tmps
        omega
      · exact hos x hx' t ht
    · intro cur lst env ist tmps hxF hrel hsz
      have h1 := hs1 cur lst env ist tmps (hx2.trans hxF) hrel hsz
      simp only [Lang.Sem.evalArgs]
      cases hva : Lang.Sem.evalE E.prog lst env a with
      | none => simp only [hva] at h1 ⊢; exact h1
      | some v =>
        simp only [hva] at h1
        cases hvs : Lang.Sem.evalArgs E.prog lst env as with
        | none =>
          refine h1.ends (fun t1 hts _ _ => ?_)
          have h2 := hs2 cur lst env ist t1 hxF hrel (by rw [hts]; exact hsz)
          simp only [hvs] at h2
          exact h2
        | some vs =>
          refine h1.seq hx1.tmps (fun t1 hts _ ho => ?_)
          have h2 := hs2 cur lst env ist t1 hxF hrel (by rw [hts]; exact hsz)
          simp only [hvs] at h2
          refine h2.mono (fun t2 _ ag2 hos' => ?_)
          simp only [List.map_cons, hos']
          rw [opd_agree c ist _ (fun t ht => (ho1.1 t ht).2) ag2, ho]

theorem step_eff (c : Ctx) (ist : St) (tmps : Array Nat) (e : Effect) (args : List (Nat × Opd))
    (ret : Option (Nat × Dst)) :
    step c ist tmps (.eff e args ret) =
      .set (setRet c { ist with world := (IR.Sem.effect c ist.world e (args.map fun a => opd c ist tmps a.1 a.2)).2 } tmps ret
        (IR.Sem.effect c ist.world e (args.map fun a => opd c ist tmps a.1 a.2)).1) := rfl

/-- **An effect, up to its instruction.** -/
theorem effInstr_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hlow : Lowered E.prog c)
    (N : Nat) (e : Effect) (args : List Expr) (hargs : ArgsOK E e.sig.1 args) (s : LS) :
    wp (effInstr e args) E
      (IPost c f sF N E args
        (fun _ lst vs => .ok (Lang.Sem.effect E.prog lst e vs).1 (Lang.Sem.effect E.prog lst e vs).2) e.sig.2 s) s := by
  unfold effInstr
  simp only [wp_bind]
  refine wp_mono (effArgs_ok F L hE e.sig.1 args s hargs) ?_
  intro os s1 ⟨hx1, hc1, hos, hs1⟩
  have hsem : ISem c f sF N E args
      (fun _ lst vs => .ok (Lang.Sem.effect E.prog lst e vs).1 (Lang.Sem.effect E.prog lst e vs).2) e.sig.2 s s1
      (Instr.eff e os) := by
    intro k ret cur lst env ist tmps hk hxF hb hrel hsz
    have h1 := hs1 cur lst env ist tmps hxF hrel hsz
    cases hev : Lang.Sem.evalArgs E.prog lst env args with
    | none => simp only [hev] at h1 ⊢; exact ⟨ist, h1, rfl⟩
    | some vs =>
      simp only [hev] at h1 ⊢
      obtain ⟨t1, r1, sz1, _, hov⟩ := h1
      obtain ⟨w', hw1, hw2, hret⟩ := effect_sim c E.prog hlow.drops hlow.notes lst e vs
      have hstep := step_eff c ist t1 e os ret
      rw [hov, hrel.world, hw2] at hstep
      refine ⟨{ ist with world := w' }, t1, r1.trans (Reach.next hb hstep), sz1, ?_, Keep.refl _, hret⟩
      rw [hw1]
      exact hrel.setWorld w'
  cases hret : e.sig.2 with
  | none =>
    rw [hret] at hsem
    simp only [wp_bind, wp_pure]
    exact ⟨hx1, hc1, rfl, hsem⟩
  | some t =>
    rw [hret] at hsem
    simp only [wp_bind, wp_size, wp_pure]
    exact ⟨hx1, hc1, rfl, hsem⟩

/-! ## Where the result goes -/

/-- A value that is in an operand, stored at a place. -/
def StSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (d : Expr) (ty : Ty) (o : Opd) (s s' : LS) : Prop :=
  ∀ cur lst env ist tmps (v : Val), Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    HasTy E.prog ty v → opd c ist tmps (sizeOf E.prog ty) o = v.toNat →
    match Lang.Sem.assign E.prog lst env d v with
    | none => Ends c f s.out.size tmps ist (.trap ist)
    | some (lst', env') => ∃ ist' tmps', Reach c f s.out.size tmps ist s'.out.size tmps' ist' ∧
        tmps'.size = tmps.size ∧ SRel c E cur lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem

def StPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (d : Expr) (ty : Ty) (o : Opd) (s : LS) (_ : Unit) (s' : LS) :
    Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ StSem c f sF E d ty o s s'

theorem storeAt_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (d : Expr) (ty : Ty)
    (o : Opd) (s : LS) (hw : WT E d) (htd : E.tyOf d = .ok ty) (hs : ty.isScalar = true) (hwr : Writable E d)
    (ho : ∀ t, o = .tmp t → t < s.tmps.size) :
    wp (do let r ← place d; storeTo (sizeOf E.prog ty) r.1 o) E (StPost c f sF E d ty o s) s := by
  simp only [wp_bind]
  refine wp_mono (place_ok F d E s ty L hE hw htd) ?_
  intro a s2 ⟨hx2, hc2, hat, ⟨⟨sl, hroot⟩, hidx⟩, hs2⟩
  have hboth : ∀ (ins : Instr) (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St)
      (tmps : Array Nat) (v : Val), Ext { s2 with out := s2.out.push ins } sF → SRel c E cur lst env ist →
      tmps.size = f.tmps.size → HasTy E.prog ty v → opd c ist tmps (sizeOf E.prog ty) o = v.toNat →
      (∀ t2 A, addr c ist t2 a.1 = some A → ∀ x, opd c ist t2 (sizeOf E.prog ty) o = x →
        step c ist t2 ins = .next { ist with mem := wr ist.mem A (sizeOf E.prog ty) x } t2) →
      (∀ t2, addr c ist t2 a.1 = none → step c ist t2 ins = .stop (.trap ist)) →
      match Lang.Sem.assign E.prog lst env d v with
      | none => Ends c f s.out.size tmps ist (.trap ist)
      | some (lst', env') => ∃ ist' tmps', Reach c f s.out.size tmps ist (s2.out.size + 1) tmps' ist' ∧
          tmps'.size = tmps.size ∧ SRel c E cur lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem := by
    intro ins cur lst env ist tmps v hxF hrel hsz hv hov hsome hnone
    have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
    have hb := F.emitted hxF rfl
    have h2 := hs2 cur lst env ist tmps hxF2 hrel hsz
    cases hel : Lang.Sem.evalE E.prog lst env d with
    | none =>
      rw [assign_none _ _ _ _ _ hel]
      simp only [hel] at h2
      rcases h2 with h2 | h2
      · exact h2
      · exact h2.ends (fun t2 _ _ hA => Ends.stop hb (hnone t2 hA) (by simp))
    | some lv =>
      simp only [hel] at h2
      obtain ⟨t2, r2, sz2, ag2, A, hA, hpl⟩ := h2
      have ho2 : opd c ist t2 (sizeOf E.prog ty) o = v.toNat := by
        rw [opd_agree c ist _ ho ag2]
        exact hov
      exact assign_end hpl hrel.size hs hwr hv (r2.trans (Reach.next hb (hsome t2 A hA _ ho2))) sz2
  unfold storeTo
  cases hi : a.1.idx with
  | none =>
    simp only [hroot, wp_emit]
    refine ⟨hx2.trans (Ext.emit _ _), hc2, ?_⟩
    intro cur lst env ist tmps v hxF hrel hsz hv hov
    simp only [Array.size_push]
    refine hboth _ cur lst env ist tmps v hxF hrel hsz hv hov (fun t2 A hA x hx => ?_) (fun t2 hA => ?_)
    · rw [addr_static c ist t2 hroot hi] at hA
      cases hA
      rw [step_mov, hx]
      rfl
    · rw [addr_static c ist t2 hroot hi] at hA
      cases hA
  | some ix =>
    simp only [hroot, wp_emit]
    refine ⟨hx2.trans (Ext.emit _ _), hc2, ?_⟩
    intro cur lst env ist tmps v hxF hrel hsz hv hov
    simp only [Array.size_push]
    refine hboth _ cur lst env ist tmps v hxF hrel hsz hv hov (fun t2 A hA x hx => ?_) (fun t2 hA => ?_)
    · rw [step_store_some c ist t2 _ _ _ hA, hx]
    · exact step_store_none c ist t2 _ _ _ hA

/-- An invocation with its result stored. -/
def RSem (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (args : List Expr)
    (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (dst : Option Expr) (s s' : LS) : Prop :=
  ∀ k cur lst env ist tmps, k < N → Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalArgs E.prog lst env args with
    | none => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst.world
    | some vs =>
      match act k lst vs with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok v lst' =>
        match Lang.Sem.storeResult E.prog lst' env dst v with
        | .ok lst'' env'' _ => ∃ ist' tmps', Reach c f s.out.size tmps ist s'.out.size tmps' ist' ∧
            tmps'.size = tmps.size ∧ SRel c E cur lst'' env'' ist' ∧ Keep c E cur ist.mem ist'.mem
        | .trap lst'' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst''.world
        | .fuel => True

def RPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (args : List Expr)
    (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (dst : Option Expr) (s : LS) (_ : Unit) (s' : LS) :
    Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ RSem c f sF N E args act dst s s'

theorem setRet_none (c : Ctx) (st : St) (tmps : Array Nat) (r : Option Nat) : setRet c st tmps none r = (st, tmps) :=
  rfl

theorem setRet_some (c : Ctx) (st : St) (tmps : Array Nat) (n : Nat) (d : Dst) (r : Option Nat) :
    setRet c st tmps (some (n, d)) r = setDst c st tmps n d (r.getD 0) := rfl

/-- **Where the result of a call or an effect goes.** -/
theorem withResult_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (N : Nat)
    (args : List Expr) (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (retTy : Option Ty)
    (dst : Option Expr) (hdst : DstOK E dst retTy) (s s1 : LS) (r : Option Nat × (Option (Nat × Dst) → Instr))
    (h : IPost c f sF N E args act retTy s r s1) :
    wp (withResult dst r.1 r.2) E (RPost c f sF N E args act dst s) s1 := by
  obtain ⟨hx1, hc1, hr1, hs1⟩ := h
  -- no destination: the instruction alone
  have hnone : (∀ (st : Lang.Sem.St) (env : Lang.Sem.Env) (v : Option Val),
        Lang.Sem.storeResult E.prog st env dst v = .ok st env .normal) →
      wp (emit (r.2 none)) E (RPost c f sF N E args act dst s) s1 := by
    intro hst
    rw [wp_emit]
    refine ⟨hx1.trans (Ext.emit _ _), hc1, ?_⟩
    intro k cur lst env ist tmps hk hxF hrel hsz
    have hI := hs1 k none cur lst env ist tmps hk ((Ext.emit _ _).trans hxF) (F.emitted hxF rfl) hrel hsz
    simp only [Array.size_push]
    cases hev : Lang.Sem.evalArgs E.prog lst env args with
    | none =>
      simp only [hev] at hI ⊢
      obtain ⟨ist', he, hw⟩ := hI
      exact ⟨ist', he, by rw [hw, hrel.world]⟩
    | some vs =>
      simp only [hev] at hI ⊢
      cases hact : act k lst vs with
      | fuel => trivial
      | trap lst' => simp only [hact] at hI ⊢; exact hI
      | ok v lst' =>
        simp only [hact] at hI ⊢
        obtain ⟨ist2, t1, r1, sz1, hrel', hkeep, _⟩ := hI
        rw [hst]
        exact ⟨ist2, t1, r1, sz1, hrel', hkeep⟩
  cases dst with
  | none =>
    have : withResult none r.1 r.2 = emit (r.2 none) := by
      unfold withResult
      cases r.1 <;> rfl
    rw [this]
    exact hnone (fun st env v => by cases v <;> rfl)
  | some d =>
    obtain ⟨_, hwr, hwd, t, hrt, htd, hs⟩ := hdst
    subst hrt
    simp only [Option.map_some] at hr1
    unfold withResult
    simp only [hr1, wp_bind]
    -- the result, once the invocation is over
    have hres : ∀ (k : Nat) (ret : Option (Nat × Dst)) (s2 : LS) (cur : Nat) (lst : Lang.Sem.St)
        (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat), k < N → Ext s2 sF →
        s2.out[s1.out.size]? = some (r.2 ret) → Ext s1 s2 → SRel c E cur lst env ist → tmps.size = f.tmps.size →
        match Lang.Sem.evalArgs E.prog lst env args with
        | none => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst.world
        | some vs =>
          match act k lst vs with
          | .fuel => True
          | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
          | .ok v lst' => ∃ x ist2 tmps1, v = some x ∧ HasTy E.prog t x ∧
              Reach c f s.out.size tmps ist (s1.out.size + 1) (setRet c ist2 tmps1 ret (some x.toNat)).2
                (setRet c ist2 tmps1 ret (some x.toNat)).1 ∧
              tmps1.size = tmps.size ∧ SRel c E cur lst' env ist2 ∧ Keep c E cur ist.mem ist2.mem := by
      intro k ret s2 cur lst env ist tmps hk hxF hb hx12 hrel hsz
      have hI := hs1 k ret cur lst env ist tmps hk (hx12.trans hxF) (F.at_ hxF hb) hrel hsz
      cases hev : Lang.Sem.evalArgs E.prog lst env args with
      | none =>
        simp only [hev] at hI ⊢
        obtain ⟨ist', he, hw⟩ := hI
        exact ⟨ist', he, by rw [hw, hrel.world]⟩
      | some vs =>
        simp only [hev] at hI ⊢
        cases hact : act k lst vs with
        | fuel => trivial
        | trap lst' => simp only [hact] at hI ⊢; exact hI
        | ok v lst' =>
          simp only [hact] at hI ⊢
          obtain ⟨ist2, t1, r1, sz1, hrel', hkeep, x, rfl, hx⟩ := hI
          exact ⟨x, ist2, t1, rfl, hx, r1, sz1, hrel', hkeep⟩
    have hvar : ∀ (x : String), d = .var x → wp (plainSlot d) E (fun simple s' =>
        wp (match simple with
          | some sl => emit (r.2 (some (sizeOf E.prog t, .slot sl)))
          | none => do
            let tt ← newTmp (sizeOf E.prog t)
            emit (r.2 (some (sizeOf E.prog t, .tmp tt)))
            let rr ← place d
            storeTo (sizeOf E.prog t) rr.1 (.tmp tt)) E (RPost c f sF N E args act (some d) s) s') s1 := by
      intro x hdx
      subst hdx
      simp only [plainSlot, wp_bind, wp_varInfo]
      intro info hinfo
      obtain ⟨sl, hat⟩ := hE.varInfo hinfo
      have hti : info.ty = t := by
        simp only [Env.tyOf, hinfo, Except.ok.injEq] at htd
        exact htd
      subst hti
      simp only [hat, wp_pure, wp_emit]
      refine ⟨hx1.trans (Ext.emit _ _), hc1, ?_⟩
      intro k cur lst env ist tmps hk hxF hrel hsz
      have hR := hres k (some (sizeOf E.prog info.ty, .slot sl)) _ cur lst env ist tmps hk hxF (by simp)
        (Ext.emit _ _) hrel hsz
      simp only [Array.size_push]
      cases hev : Lang.Sem.evalArgs E.prog lst env args with
      | none => simp only [hev] at hR ⊢; exact hR
      | some vs =>
        simp only [hev] at hR ⊢
        cases hact : act k lst vs with
        | fuel => trivial
        | trap lst' => simp only [hact] at hR ⊢; exact hR
        | ok v lst' =>
          simp only [hact] at hR ⊢
          obtain ⟨xv, ist2, t1, rfl, hxv, r1, sz1, hrel', hkeep⟩ := hR
          rw [setRet_some, setDst_slot] at r1
          obtain ⟨_, lv, _, hlv, _⟩ := hrel'.var L hinfo
          have hpl := PlaceAt.var L hrel' hinfo hat hlv
          obtain ⟨lst'', env'', ha, hrel'', hkeep', _⟩ := wr_place hpl hrel'.size hs hwr hxv
          simp only [Lang.Sem.storeResult, ha]
          exact ⟨_, t1, r1, sz1, hrel'', hkeep.trans hkeep'⟩
    have hother : (∀ x, d ≠ .var x) → wp (plainSlot d) E (fun simple s' =>
        wp (match simple with
          | some sl => emit (r.2 (some (sizeOf E.prog t, .slot sl)))
          | none => do
            let tt ← newTmp (sizeOf E.prog t)
            emit (r.2 (some (sizeOf E.prog t, .tmp tt)))
            let rr ← place d
            storeTo (sizeOf E.prog t) rr.1 (.tmp tt)) E (RPost c f sF N E args act (some d) s) s') s1 := by
      intro hnv
      have hps : plainSlot d = pure none := by
        cases d with
        | var x => exact absurd rfl (hnv x)
        | _ => rfl
      rw [hps, wp_pure]
      rw [wp_bind, wp_newTmp, wp_bind, wp_emit]
      refine wp_mono (storeAt_ok F L hE d t (.tmp s1.tmps.size) _ hwd htd hs hwr (fun tt htt => by
        cases htt
        simp)) ?_
      intro _ s3 ⟨hx3, hc3, hs3⟩
      have hx13 := (Ext.newTmp s1 (sizeOf E.prog t)).trans ((Ext.emit _ (r.2 (some (sizeOf E.prog t, .tmp s1.tmps.size)))).trans hx3)
      refine ⟨hx1.trans hx13, by rw [hc3]; exact hc1, ?_⟩
      intro k cur lst env ist tmps hk hxF hrel hsz
      have hR := hres k (some (sizeOf E.prog t, .tmp s1.tmps.size)) _ cur lst env ist tmps hk (hx3.trans hxF)
        (by simp) ((Ext.newTmp s1 _).trans (Ext.emit _ _)) hrel hsz
      cases hev : Lang.Sem.evalArgs E.prog lst env args with
      | none => simp only [hev] at hR ⊢; exact hR
      | some vs =>
        simp only [hev] at hR ⊢
        cases hact : act k lst vs with
        | fuel => trivial
        | trap lst' => simp only [hact] at hR ⊢; exact hR
        | ok v lst' =>
          simp only [hact] at hR ⊢
          obtain ⟨xv, ist2, t1, rfl, hxv, r1, sz1, hrel', hkeep⟩ := hR
          rw [setRet_some, setDst_tmp] at r1
          have hlt : s1.tmps.size < t1.size := by
            rw [sz1]
            refine F.tmps_lt hxF hsz ?_
            have := hx3.tmps
            simp only [Array.size_push] at this
            omega
          have hsz4 : (t1.setIfInBounds s1.tmps.size (modN (sizeOf E.prog t) xv.toNat)).size = f.tmps.size := by
            rw [Array.size_setIfInBounds, sz1]
            exact hsz
          have h3 := hs3 cur lst' env ist2 (t1.setIfInBounds s1.tmps.size (modN (sizeOf E.prog t) xv.toNat)) xv hxF
            hrel' hsz4 hxv (by
              rw [opd_set c ist2 t1 _ _ _ hlt, modN_modN]
              exact modN_of_lt (toNat_lt hxv hs))
          simp only [Array.size_push] at h3
          simp only [Lang.Sem.storeResult]
          cases ha : Lang.Sem.assign E.prog lst' env d xv with
          | none =>
            simp only [ha] at h3 ⊢
            exact ⟨ist2, r1.ends h3, hrel'.world⟩
          | some p =>
            obtain ⟨lst'', env''⟩ := p
            simp only [ha] at h3 ⊢
            obtain ⟨ist', t', r3, sz3, hrel'', hkeep'⟩ := h3
            exact ⟨ist', t', r1.trans r3, by rw [sz3]; simp [sz1], hrel'', hkeep.trans hkeep'⟩
    cases d with
    | var x => exact hvar x rfl
    | field b fld => exact hother (fun x h => by cases h)
    | index b i => exact hother (fun x h => by cases h)
    | lit _ _ => exact hother (fun x h => by cases h)
    | blit _ => exact hother (fun x h => by cases h)
    | bin _ _ _ => exact hother (fun x h => by cases h)
    | un _ _ => exact hother (fun x h => by cases h)
    | cast _ _ => exact hother (fun x h => by cases h)
    | cond _ _ _ => exact hother (fun x h => by cases h)

/-! ## The statements -/

theorem storeResult_out {p : Prog} {st : Lang.Sem.St} {env : Lang.Sem.Env} {dst : Option Expr} {v : Option Val}
    {st' : Lang.Sem.St} {env' : Lang.Sem.Env} {o : Lang.Sem.Out}
    (h : Lang.Sem.storeResult p st env dst v = .ok st' env' o) : o = .normal := by
  unfold Lang.Sem.storeResult at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h; rfl

/-- A statement that is an invocation with its result stored. -/
theorem invoke_ok {E : Env} (N : Nat) (rt : Option Ty) (stm : Stmt) (args : List Expr)
    (act : Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes) (dst : Option Expr)
    (hexec : ∀ k lst env, Lang.Sem.execS (k + 1) E.prog lst env stm =
      match Lang.Sem.evalArgs E.prog lst env args with
      | none => .trap lst
      | some vs =>
        match act k lst vs with
        | .ok v lst' => Lang.Sem.storeResult E.prog lst' env dst v
        | .trap lst' => .trap lst'
        | .fuel => .fuel)
    (henv : ∀ off, envAfter E off stm = E) (s s' : LS) (h : RPost c f sF N E args act dst s () s') :
    SPost c f sF N rt E stm s E s' := by
  obtain ⟨hx, hc, hsem⟩ := h
  refine ⟨hx, (henv s.cur).symm, by rw [hc]; exact Nat.le_refl _, ?_⟩
  intro n lst env ist tmps hn hxF hrel hsz hend
  cases n with
  | zero => rw [Lang.Sem.execS]; trivial
  | succ k =>
    rw [hexec]
    have hR := hsem k s.cur lst env ist tmps (by omega) hxF hrel hsz
    cases hev : Lang.Sem.evalArgs E.prog lst env args with
    | none => simp only [hev] at hR ⊢; exact hR
    | some vs =>
      simp only [hev] at hR ⊢
      cases hact : act k lst vs with
      | fuel => trivial
      | trap lst' => simp only [hact] at hR ⊢; exact hR
      | ok v lst' =>
        simp only [hact] at hR ⊢
        cases hst : Lang.Sem.storeResult E.prog lst' env dst v with
        | fuel => trivial
        | trap lst'' => simp only [hst] at hR ⊢; exact hR
        | ok lst'' env'' o =>
          simp only [hst] at hR ⊢
          cases storeResult_out hst
          obtain ⟨ist', t', r1, sz1, hrel', hkeep⟩ := hR
          exact ⟨ist', t', r1, sz1, by rw [hc]; exact hrel', hkeep⟩

/-- A call. -/
theorem call_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn)
    (hlow : Lowered E.prog c) (hok : ProgOK E.prog) (N : Nat) (H : ∀ k, k < N → FnSim c E.prog k) (rt : Option Ty)
    (dst : Option Expr) (g : String) (args : List Expr) (s : LS)
    (hw : ∃ fd, E.prog.fn? g = some fd ∧ ArgsOK E (fd.params.map (·.ty)) args ∧ DstOK E dst fd.ret) :
    wp (do let r ← callInstr g args; withResult dst r.1 r.2; read) E
      (SPost c f sF N rt E (.call dst g args) s) s := by
  obtain ⟨fd, hfd, hargs, hdst⟩ := hw
  simp only [wp_bind, wp_read]
  refine wp_mono (callInstr_ok F L hE hfn hlow hok N H g args fd hfd hargs s) ?_
  intro r s1 hI
  refine wp_mono (withResult_ok F L hE N args _ fd.ret dst hdst s s1 r hI) ?_
  intro _ s2 hR
  exact invoke_ok N rt _ args _ dst
    (fun k lst env => execS_call E.prog k lst env dst g args fd hfd (fun p h => ((hok g fd hfd).params p h).1))
    (fun _ => rfl) s s2 hR

/-- An effect. -/
theorem eff_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hlow : Lowered E.prog c)
    (N : Nat) (rt : Option Ty) (dst : Option Expr) (e : Effect) (args : List Expr) (s : LS)
    (hw : ArgsOK E e.sig.1 args ∧ DstOK E dst e.sig.2) :
    wp (do let r ← effInstr e args; withResult dst r.1 r.2; read) E
      (SPost c f sF N rt E (.eff dst e args) s) s := by
  obtain ⟨hargs, hdst⟩ := hw
  simp only [wp_bind, wp_read]
  refine wp_mono (effInstr_ok F L hE hlow N e args hargs s) ?_
  intro r s1 hI
  refine wp_mono (withResult_ok F L hE N args _ e.sig.2 dst hdst s s1 r hI) ?_
  intro _ s2 hR
  exact invoke_ok N rt _ args _ dst (fun k lst env => execS_eff E.prog k lst env dst e args) (fun _ => rfl) s s2 hR

/-! ## A declaration whose value is a call's or an effect's result -/

def initArgs : Init → List Expr
  | .call _ a => a
  | .eff _ a => a

def initAct (lp : Prog) : Init → Nat → Lang.Sem.St → List Val → Lang.Sem.CallRes
  | .call g _ => fun k lst vs => Lang.Sem.call k lp lst g vs
  | .eff e _ => fun _ lst vs => .ok (Lang.Sem.effect lp lst e vs).1 (Lang.Sem.effect lp lst e vs).2

/-- The arguments, the invocation, and its result as the new variable. -/
def DSem (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (x : String) (ty : Ty) (i : Init) (s s' : LS) : Prop :=
  ∀ k lst env ist tmps, k < N → Ext s' sF → SRel c E s.cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalArgs E.prog lst env (initArgs i) with
    | none => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst.world
    | some vs =>
      match initAct E.prog i k lst vs with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok v lst' => ∃ xv ist' tmps', v = some xv ∧ Reach c f s.out.size tmps ist s'.out.size tmps' ist' ∧
          tmps'.size = tmps.size ∧
          SRel c { E with vars := (x, { ty, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars }
            (s.cur + sizeOf E.prog ty) lst' ((x, xv) :: env) ist' ∧
          Keep c E s.cur ist.mem ist'.mem

def DPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (E : Env) (x : String) (ty : Ty) (i : Init) (s : LS) (E' : Env)
    (s' : LS) : Prop :=
  Ext s s' ∧ E' = { E with vars := (x, { ty, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars } ∧
    s'.cur = s.cur + sizeOf E.prog ty ∧ DSem c f sF N E x ty i s s'

theorem declCall_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn)
    (hlow : Lowered E.prog c) (hok : ProgOK E.prog) (N : Nat) (H : ∀ k, k < N → FnSim c E.prog k) (x : String)
    (ty : Ty) (i : Init) (s : LS) (hty : TyOK E.prog ty) (hi : InitOK E ty i) :
    wp (declCall x ty i) E (DPost c f sF N E x ty i s) s := by
  unfold declCall
  simp only [wp_bind, wp_read, wp_size, wp_allocLocal]
  have hI : ty.isScalar = true ∧ ∀ s1, wp (match i with
        | .call g args => callInstr g args
        | .eff e args => effInstr e args) E
      (IPost c f sF N E (initArgs i) (initAct E.prog i) (some ty) s1) s1 := by
    cases i with
    | call g args =>
      obtain ⟨fd, hfd, hargs, hret⟩ := hi
      refine ⟨(hok g fd hfd).ret ty hret, fun s1 => ?_⟩
      have := callInstr_ok F L hE hfn hlow hok N H g args fd hfd hargs s1
      rw [hret] at this
      exact this
    | eff e args =>
      obtain ⟨hargs, hret⟩ := hi
      refine ⟨?_, fun s1 => ?_⟩
      · cases e <;> simp [Effect.sig] at hret <;> subst hret <;> rfl
      · have := effInstr_ok F L hE hlow N e args hargs s1
        rw [hret] at this
        exact this
  obtain ⟨hs, hI⟩ := hI
  refine wp_mono (hI _) ?_
  intro r s2 ⟨hx2, hc2, hr, hsem⟩
  simp only [Option.map_some] at hr
  simp only [hr, wp_emit, wp_pure]
  have hx02 := (Ext.alloc s (sizeOf E.prog ty)).trans hx2
  refine ⟨hx02.trans (Ext.emit _ _), rfl, hc2, ?_⟩
  intro k lst env ist tmps hk hxF hrel hsz
  have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
  have hR := hsem k (some (sizeOf E.prog ty, .slot { area := .frame E.fn, off := s.cur })) s.cur lst env ist tmps hk
    hxF2 (F.emitted hxF rfl) hrel hsz
  simp only [Array.size_push]
  cases hev : Lang.Sem.evalArgs E.prog lst env (initArgs i) with
  | none =>
    simp only [hev] at hR ⊢
    obtain ⟨ist', he, hw⟩ := hR
    exact ⟨ist', he, by rw [hw, hrel.world]⟩
  | some vs =>
    simp only [hev] at hR ⊢
    cases hact : initAct E.prog i k lst vs with
    | fuel => trivial
    | trap lst' => simp only [hact] at hR ⊢; exact hR
    | ok v lst' =>
      simp only [hact] at hR ⊢
      obtain ⟨ist2, t1, r1, sz1, hrel', hkeep, xv, rfl, hxv⟩ := hR
      rw [setRet_some, setDst_slot, addr_frame] at r1
      simp only [Option.map_some, Option.getD_some] at r1
      obtain ⟨f', hf', hfit⟩ := F.fit hfn (hx2.trans hxF2) (k := s.cur + sizeOf E.prog ty) (Nat.le_max_right _ _)
      have hfb := L.fbound _ _ hf'
      have hms := hrel'.size
      have hm : ∀ A, A < fbase c E.fn + s.cur ∨ fbase c E.fn + s.cur + sizeOf E.prog ty ≤ A →
          (wr ist2.mem (fbase c E.fn + s.cur) (sizeOf E.prog ty) xv.toNat).get! A = ist2.mem.get! A :=
        fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
      refine ⟨xv, _, t1, rfl, r1, sz1, ?_, hkeep.trans (Keep.above hf' hfit (fun A hA => hm A (by omega)))⟩
      refine hrel'.push L x ty xv (by rw [wr_size]; exact hms) hty hxv ⟨f', hf', hfit⟩ hm ?_
      rw [holds_scalar hs, rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (toNat_lt hxv hs)]

end

end Ember.Proof.IRSim
