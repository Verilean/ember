import Ember.Proof.IRArith

/-!
# Ember.Proof.IRExpr — the lowering is right about expressions (plan M7.1)

`expr_ok`, `exprTo_ok`, `place_ok`: the instructions the lowering emits
for a well-typed expression compute, from related states, the value
`Lang.Sem.evalE` gives — into an operand, into a destination, or as an
address — or end in a trap when it has none.  They change temporaries
only (and the destination).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK closed_evalE)

/-- Every variable in scope has an address of its own (no by-reference parameters). -/
def EnvOK (E : Env) : Prop := ∀ x info, E.vars.lookup x = some info → ∃ sl, info.at_ = .static sl

theorem EnvOK.varInfo {E : Env} (h : EnvOK E) {x : String} {info : VarInfo} (hx : E.varInfo x = .ok info) :
    ∃ sl, info.at_ = .static sl := by
  unfold Env.varInfo at hx
  cases hv : E.vars.lookup x with
  | some i =>
    simp only [hv, Except.ok.injEq] at hx
    subst hx
    exact h x _ hv
  | none =>
    simp only [hv] at hx
    cases hg : E.prog.global? x with
    | none => simp [hg, Env.err] at hx
    | some g =>
      simp only [hg, Except.ok.injEq] at hx
      subst hx
      exact ⟨_, rfl⟩

/-- An operand made between `s` and `s'`, of `n` bytes. -/
def OpdOK (s s' : LS) (n : Nat) (o : Opd) : Prop :=
  (∀ t, o = .tmp t → s.tmps.size ≤ t ∧ t < s'.tmps.size) ∧ ∀ v, o = .const v → v < 2 ^ (8 * n)

/-- An address made between `s` and `s'`. -/
def AddrOK (s s' : LS) (a : Addr) : Prop :=
  (∃ sl, a.root = .static sl) ∧ ∀ x, a.idx = some x → ∀ t, x.opd = .tmp t → s.tmps.size ≤ t ∧ t < s'.tmps.size

theorem addr_agree (c : Ctx) (ist : St) {tmps tmps' : Array Nat} {a : Addr} {k : Nat}
    (ha : ∀ x, a.idx = some x → ∀ t, x.opd = .tmp t → t < k) (h : Agree k tmps tmps') :
    addr c ist tmps' a = addr c ist tmps a := by
  unfold addr
  cases hi : a.idx with
  | none => rfl
  | some x => simp only [opd_agree c ist x.size (ha x hi) h]

theorem step_load_some (c : Ctx) (ist : St) (tmps : Array Nat) (n : Nat) (d : Dst) (p : Addr) {A : Nat}
    (h : addr c ist tmps p = some A) (hb : inBound c ist tmps p = true) :
    step c ist tmps (.load n d p) = .set (setDst c ist tmps n d (rd ist.mem A n)) := by
  simp only [step, h, hb, if_true]

theorem inBound_agree (c : Ctx) (ist : St) {tmps tmps' : Array Nat} {a : Addr} {k : Nat}
    (ha : ∀ x, a.idx = some x → ∀ t, x.opd = .tmp t → t < k) (h : Agree k tmps tmps') :
    inBound c ist tmps' a = inBound c ist tmps a := by
  unfold inBound
  cases hi : a.idx with
  | none => rfl
  | some x => simp only [opd_agree c ist x.size (ha x hi) h]

theorem inBound_static (c : Ctx) (ist : St) (tmps : Array Nat) {a : Addr} (hi : a.idx = none) :
    inBound c ist tmps a = true := by
  simp [inBound, hi]

theorem step_load_none (c : Ctx) (ist : St) (tmps : Array Nat) (n : Nat) (d : Dst) (p : Addr)
    (h : addr c ist tmps p = none) : step c ist tmps (.load n d p) = .stop (.trap ist) := by
  simp only [step, h]

section
variable (c : Ctx) (fn : String) (f : IR.Fn) (sF : LS)

/-- The code between `s` and `s'` leaves the value of `e`, of `n`
bytes, in the operand `o` — or traps when `e` has none. -/
def ESem (E : Env) (e : Expr) (n : Nat) (s s' : LS) (o : Opd) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env e with
    | some v => Runs c f ist s.out.size s'.out.size s.tmps.size tmps (fun tmps' => opd c ist tmps' n o = v.toNat)
    | none => Ends c f s.out.size tmps ist (.trap ist)

/-- The code between `s` and `s'` stores the value of `e` to `dst`. -/
def TSem (E : Env) (e : Expr) (n : Nat) (s s' : LS) (dst : Dst) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env e with
    | some v => ∃ tmps1, tmps1.size = tmps.size ∧ Agree s.tmps.size tmps tmps1 ∧
        Reach c f s.out.size tmps ist s'.out.size (setDst c ist tmps1 n dst v.toNat).2
          (setDst c ist tmps1 n dst v.toNat).1
    | none => Ends c f s.out.size tmps ist (.trap ist)

/-- The code between `s` and `s'` forms the address of the place `e`: it
traps, or the address is that of the place, or (an index out of range,
found where the address is used) there is none. -/
def PSem (E : Env) (e : Expr) (ty : Ty) (s s' : LS) (a : Addr) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env e with
    | some v => Runs c f ist s.out.size s'.out.size s.tmps.size tmps
        (fun tmps' => ∃ A, addr c ist tmps' a = some A ∧ inBound c ist tmps' a = true ∧
          PlaceAt c E cur lst env ist e ty v A)
    | none => Ends c f s.out.size tmps ist (.trap ist) ∨
        Runs c f ist s.out.size s'.out.size s.tmps.size tmps (fun tmps' => addr c ist tmps' a = none)

variable {c fn f sF}

/-- What `place` promises. -/
def PPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (e : Expr) (ty : Ty) (s : LS) (r : Addr × Ty) (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ r.2 = ty ∧ AddrOK s s' r.1 ∧ PSem c f sF E e ty s s' r.1

/-- What `expr` promises. -/
def EPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (e : Expr) (ty : Ty) (s : LS) (o : Opd) (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ OpdOK s s' (sizeOf E.prog ty) o ∧ ESem c f sF E e (sizeOf E.prog ty) s s' o

/-- What `exprTo` promises. -/
def TPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (e : Expr) (ty : Ty) (dst : Dst) (s : LS) (_ : Unit)
    (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ TSem c f sF E e (sizeOf E.prog ty) s s' dst

theorem Final.tmps_lt (F : Final c fn f sF) {s : LS} (hx : Ext s sF) {tmps : Array Nat}
    (hsz : tmps.size = f.tmps.size) {t : Nat} (ht : t < s.tmps.size) : t < tmps.size := by
  have := hx.tmps
  have := F.tmps
  omega

/-- A variable as a place. -/
theorem placeVar_ok {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (x : String) (s : LS) (ty : Ty)
    (hty : E.tyOf (.var x) = .ok ty) : wp (placeVar x) E (PPost c f sF E (.var x) ty s) s := by
  unfold placeVar
  simp only [wp_bind, wp_varInfo]
  intro info hinfo
  obtain ⟨sl, hat⟩ := hE.varInfo hinfo
  have hti : info.ty = ty := by
    simp only [Env.tyOf, hinfo, Except.ok.injEq] at hty
    exact hty
  simp only [hat, wp_pure]
  refine ⟨Ext.refl s, rfl, hti, ⟨⟨sl, rfl⟩, by simp⟩, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  simp only [Lang.Sem.evalE]
  obtain ⟨sl', v, h1, h2, _⟩ := hrel.var L hinfo
  rw [h2]
  subst hti
  exact Runs.done ⟨c.layout.addr sl, rfl, rfl, PlaceAt.var L hrel hinfo hat h2⟩

/-- A place that is a slot of its own: its address. -/
theorem addr_static (c : Ctx) (ist : St) (tmps : Array Nat) {a : Addr} {sl : Slot} (hr : a.root = .static sl)
    (hi : a.idx = none) : addr c ist tmps a = some (c.layout.addr { sl with off := sl.off + a.off }) := by
  simp only [addr, hr, hi, addr_off]

/-- A place as an operand. -/
theorem loadPlace_ok (F : Final c fn f sF) {E : Env} (e : Expr) (ty : Ty) (hs : ty.isScalar = true) (s s1 : LS)
    (r : Addr × Ty) (h : PPost c f sF E e ty s r s1) : wp (loadPlace r) E (EPost c f sF E e ty s) s1 := by
  obtain ⟨hx, hcur, hty, ⟨⟨sl, hroot⟩, hidx⟩, hsem⟩ := h
  subst hty
  unfold loadPlace
  cases hi : r.1.idx with
  | none =>
    simp only [hroot, wp_pure]
    refine ⟨hx, hcur, ⟨by simp, by simp⟩, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hp := hsem cur lst env ist tmps hxF hrel hsz
    cases hev : Lang.Sem.evalE E.prog lst env e with
    | some v =>
      simp only [hev] at hp ⊢
      refine hp.mono (fun t _ _ ⟨A, hA, hin, hpl⟩ => ?_)
      rw [addr_static c ist t hroot hi] at hA
      cases hA
      rw [opd_slot, ← (holds_scalar hs).mp hpl.holds]
    | none =>
      simp only [hev] at hp ⊢
      rcases hp with hp | ⟨t, _, _, _, hA⟩
      · exact hp
      · rw [addr_static c ist t hroot hi] at hA
        cases hA
  | some ix =>
    simp only [hroot, loadTmp, wp_bind, wp_size, wp_newTmp, wp_emit, wp_pure]
    have hx1 := (Ext.newTmp s1 (sizeOf E.prog r.2)).trans
      (Ext.emit _ (Instr.load (sizeOf E.prog r.2) (.tmp s1.tmps.size) r.1))
    refine ⟨hx.trans hx1, hcur, ⟨fun t ht => ?_, by simp⟩, ?_⟩
    · simp only [Opd.tmp.injEq] at ht
      subst ht
      have := hx.tmps
      simp only [Array.size_push]
      omega
    · intro cur lst env ist tmps hxF hrel hsz
      have hp := hsem cur lst env ist tmps (hx1.trans hxF) hrel hsz
      have hb : f.body[s1.out.size]? = some (.load (sizeOf E.prog r.2) (.tmp s1.tmps.size) r.1) :=
        F.at_ hxF (by simp)
      have hd : s1.tmps.size < tmps.size := F.tmps_lt hxF hsz (by simp)
      simp only [Array.size_push]
      cases hev : Lang.Sem.evalE E.prog lst env e with
      | some v =>
        simp only [hev] at hp ⊢
        refine hp.seq (Nat.le_refl _) (fun t hts _ ⟨A, hA, hin, hpl⟩ => ?_)
        refine Runs.tmp hb (step_load_some c ist t _ _ _ hA hin) hx.tmps ?_
        rw [opd_set c ist t _ _ _ (by omega), modN_modN, modN_of_lt (rd_lt _ _ _)]
        exact (holds_scalar hs).mp hpl.holds
      | none =>
        simp only [hev] at hp ⊢
        rcases hp with hp | hp
        · exact hp
        · exact hp.ends (fun t _ _ hA => Ends.stop hb (step_load_none c ist t _ _ _ hA) (by simp))

/-- One instruction that stores to a destination. -/
theorem reach_set (F : Final c fn f sF) {s : LS} {out : Array Instr} {ins : Instr} (hxF : Ext s sF)
    (ho : s.out = out.push ins) {ist : St} {t : Array Nat} {n : Nat} {dst : Dst} {v : Nat}
    (hs : step c ist t ins = .set (setDst c ist t n dst v)) :
    Reach c f out.size t ist (out.size + 1) (setDst c ist t n dst v).2 (setDst c ist t n dst v).1 :=
  Reach.next (F.emitted hxF ho) hs

/-- A place's value to a destination. -/
theorem movPlace_ok (F : Final c fn f sF) {E : Env} (e : Expr) (ty : Ty) (hs : ty.isScalar = true) (s s1 : LS)
    (r : Addr × Ty) (dst : Dst) (h : PPost c f sF E e ty s r s1) :
    wp (movPlace (sizeOf E.prog ty) dst r) E (TPost c f sF E e ty dst s) s1 := by
  obtain ⟨hx, hcur, hty, ⟨⟨sl, hroot⟩, hidx⟩, hsem⟩ := h
  subst hty
  unfold movPlace
  cases hi : r.1.idx with
  | none =>
    simp only [hroot, wp_emit]
    refine ⟨hx.trans (Ext.emit _ _), hcur, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hp := hsem cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
    simp only [Array.size_push]
    cases hev : Lang.Sem.evalE E.prog lst env e with
    | some v =>
      simp only [hev] at hp ⊢
      obtain ⟨t, hr, hts, hag, A, hA, hin, hpl⟩ := hp
      rw [addr_static c ist t hroot hi] at hA
      cases hA
      refine ⟨t, hts, hag, hr.trans (reach_set F hxF rfl ?_)⟩
      rw [step_mov, opd_slot, (holds_scalar hs).mp hpl.holds]
    | none =>
      simp only [hev] at hp ⊢
      rcases hp with hp | ⟨t, _, _, _, hA⟩
      · exact hp
      · rw [addr_static c ist t hroot hi] at hA
        cases hA
  | some ix =>
    simp only [hroot, wp_emit]
    refine ⟨hx.trans (Ext.emit _ _), hcur, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hp := hsem cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
    simp only [Array.size_push]
    cases hev : Lang.Sem.evalE E.prog lst env e with
    | some v =>
      simp only [hev] at hp ⊢
      obtain ⟨t, hr, hts, hag, A, hA, hin, hpl⟩ := hp
      refine ⟨t, hts, hag, hr.trans (reach_set F hxF rfl ?_)⟩
      rw [step_load_some c ist t _ _ _ hA hin, (holds_scalar hs).mp hpl.holds]
    | none =>
      simp only [hev] at hp ⊢
      rcases hp with hp | hp
      · exact hp
      · exact hp.ends (fun t _ _ hA => Ends.stop (F.emitted hxF rfl) (step_load_none c ist t _ _ _ hA) (by simp))

/-- The value of a closed expression: it has one, of the expression's type. -/
theorem closed_val {E : Env} {e : Expr} {ty : Ty} {k : Nat} (hw : WT E e) (hty : E.tyOf e = .ok ty)
    (hs : ty.isScalar = true) (hc : closed? e = some k) :
    k < 2 ^ (8 * sizeOf E.prog ty) ∧ ∃ val, val.toNat = k ∧
      ∀ (lst : Lang.Sem.St) (env : Lang.Sem.Env), Lang.Sem.evalE E.prog lst env e = some val := by
  obtain ⟨val, hcv, hk⟩ := closed_sem hc
  have hall := closed_evalE e val hcv E.prog
  have hv : HasTy E.prog ty val := by
    let st0 : Lang.Sem.St := { globals := [], world := { inputs := #[] } }
    have hvt : VarsTyped E st0 [] := by
      intro x v info hl _
      simp [Lang.Sem.lookup, st0] at hl
    exact evalE_hasTy E st0 [] hvt e val ty hw (hall st0 []) hty
  exact ⟨hk ▸ toNat_lt hv hs, val, hk, hall⟩

/-- A closed expression as an operand. -/
theorem closedE_ok {E : Env} {e : Expr} {ty : Ty} {k : Nat} (s : LS) (hw : WT E e) (hty : E.tyOf e = .ok ty)
    (hs : ty.isScalar = true) (hc : closed? e = some k) : EPost c f sF E e ty s (.const k) s := by
  obtain ⟨hk, val, hv, hall⟩ := closed_val hw hty hs hc
  refine ⟨Ext.refl s, rfl, ⟨by simp, fun v hv' => by cases hv'; exact hk⟩, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  rw [hall lst env]
  exact Runs.done (by rw [opd_const, modN_of_lt hk, hv])

/-- A closed expression to a destination. -/
theorem closedTo_ok (F : Final c fn f sF) {E : Env} {e : Expr} {ty : Ty} {k : Nat} (s : LS) (dst : Dst)
    (hw : WT E e) (hty : E.tyOf e = .ok ty) (hs : ty.isScalar = true) (hc : closed? e = some k) :
    wp (emit (.mov (sizeOf E.prog ty) dst (.const k))) E (TPost c f sF E e ty dst s) s := by
  obtain ⟨hk, val, hv, hall⟩ := closed_val hw hty hs hc
  rw [wp_emit]
  refine ⟨Ext.emit _ _, rfl, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  rw [hall lst env]
  simp only [Array.size_push]
  refine ⟨tmps, rfl, Agree.refl _ _, reach_set F hxF rfl ?_⟩
  rw [step_mov, opd_const, modN_of_lt hk, hv]

/-- An expression evaluated into a temporary of its own, as an operand. -/
theorem tmp_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (e : Expr) (ty : Ty) (hw : WT E e)
    (hty : E.tyOf e = .ok ty) (hs : ty.isScalar = true) (s s' : LS)
    (h : TPost c f sF E e ty (.tmp s.tmps.size) { s with tmps := s.tmps.push (sizeOf E.prog ty) } () s') :
    EPost c f sF E e ty s (.tmp s.tmps.size) s' := by
  obtain ⟨hx, hcur, hsem⟩ := h
  have hlt : s.tmps.size < s'.tmps.size := by
    have := hx.tmps
    simp only [Array.size_push] at this
    omega
  refine ⟨(Ext.newTmp s _).trans hx, hcur, ⟨fun t ht => by cases ht; exact ⟨Nat.le_refl _, hlt⟩, by simp⟩, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hp := hsem cur lst env ist tmps hxF hrel hsz
  cases hev : Lang.Sem.evalE E.prog lst env e with
  | none => simp only [hev] at hp ⊢; exact hp
  | some v =>
    simp only [hev] at hp ⊢
    obtain ⟨t1, hts, hag, hr⟩ := hp
    simp only [Array.size_push] at hag
    rw [setDst_tmp] at hr
    have hv := evalE_hasTy E lst env (hrel.typed L) e v ty hw hev hty
    refine ⟨_, hr, by simp [hts], (hag.mono (Nat.le_succ _)).trans (Agree.set _ _ (Nat.le_refl _)) (Nat.le_refl _), ?_⟩
    show opd c ist (t1.setIfInBounds _ _) _ _ = _
    rw [opd_set c ist t1 _ _ _ (by rw [hts]; exact F.tmps_lt hxF hsz hlt), modN_modN, modN_of_lt (toNat_lt hv hs)]

/-- What `extTmp` promises: the new temporary holds the operand, cut to `n` bytes. -/
def XPost (c : Ctx) (f : IR.Fn) (sF : LS) (n m : Nat) (o : Opd) (s1 : LS) (o' : Opd) (s' : LS) : Prop :=
  Ext s1 s' ∧ s'.cur = s1.cur ∧ o' = .tmp s1.tmps.size ∧ s'.tmps.size = s1.tmps.size + 1 ∧
    ∀ ist tmps, Ext s' sF → tmps.size = f.tmps.size →
      Runs c f ist s1.out.size s'.out.size s1.tmps.size tmps
        (fun tmps' => opd c ist tmps' n o' = modN n (opd c ist tmps m o))

/-- An operand extended or truncated into a new temporary. -/
theorem extTmp_ok (F : Final c fn f sF) {E : Env} (n m : Nat) (o : Opd) (s1 : LS) :
    wp (extTmp n m o) E (XPost c f sF n m o s1) s1 := by
  unfold extTmp
  simp only [wp_bind, wp_newTmp, wp_emit, wp_pure]
  have hx1 := (Ext.newTmp s1 n).trans (Ext.emit _ (Instr.ext n (.tmp s1.tmps.size) m o))
  refine ⟨hx1, rfl, rfl, by simp, ?_⟩
  intro ist tmps hxF hsz
  simp only [Array.size_push]
  have hd : s1.tmps.size < tmps.size := F.tmps_lt hxF hsz (by simp)
  refine Runs.tmp (F.emitted hxF rfl) (step_ext c ist tmps n (.tmp s1.tmps.size) m o) (Nat.le_refl _) ?_
  rw [opd_set c ist tmps _ _ _ hd]
  simp only [modN_modN]

theorem addr_add_off (c : Ctx) (ist : St) (tmps : Array Nat) (a : Addr) (k : Nat) :
    addr c ist tmps { a with off := a.off + k } = (addr c ist tmps a).map (· + k) := by
  cases hi : a.idx with
  | none => simp [addr, hi, Nat.add_assoc]
  | some x =>
    cases hl : x.len with
    | none =>
      simp only [addr, hi, hl, Option.map_some, Option.some.injEq]
      omega
    | some len =>
      simp only [addr, hi, hl]
      split
      · simp only [Option.map_some, Option.some.injEq]
        omega
      · rfl

/-- A field of a record, as a place. -/
theorem field_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (b : Expr) (fld : String) (ty : Ty) (s : LS)
    (hw : WT E b) (hty : E.tyOf (.field b fld) = .ok ty)
    (ihb : ∀ tb, E.tyOf b = .ok tb → wp (place b) E (PPost c f sF E b tb s) s) :
    wp (place (.field b fld)) E (PPost c f sF E (.field b fld) ty s) s := by
  rw [place]
  simp only [Env.tyOf] at hty
  cases htb : E.tyOf b with
  | error m => simp [htb] at hty
  | ok tb =>
    cases tb with
    | int _ => simp [htb, Env.err] at hty
    | bool => simp [htb, Env.err] at hty
    | arr _ _ => simp [htb, Env.err] at hty
    | record rn =>
      simp only [htb] at hty
      cases hfo : fieldOff E.prog rn fld with
      | none => simp [hfo, Env.err] at hty
      | some p =>
        obtain ⟨off, ft⟩ := p
        simp only [hfo, Except.ok.injEq] at hty
        subst hty
        simp only [wp_bind]
        refine wp_mono (ihb _ htb) ?_
        intro r s1 ⟨hx, hcur, hrt, haok, hsem⟩
        simp only [hrt, wp_bind, wp_read, hfo, wp_pure]
        refine ⟨hx, hcur, rfl, ⟨haok.1, haok.2⟩, ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        have hp := hsem cur lst env ist tmps hxF hrel hsz
        simp only [Lang.Sem.evalE]
        cases hev : Lang.Sem.evalE E.prog lst env b with
        | none =>
          simp only [hev] at hp ⊢
          rcases hp with hp | hp
          · exact .inl hp
          · exact .inr (hp.mono (fun t _ _ hA => by rw [addr_add_off, hA]; rfl))
        | some bv =>
          simp only [hev] at hp ⊢
          have hv := evalE_hasTy E lst env (hrel.typed L) b bv _ hw hev htb
          obtain ⟨fs, sd, rfl, hsd, hsz', hfs⟩ := hasTy_record hv
          simp only [fieldOff, hsd, Option.map_some, Option.getD_some] at hfo
          cases hi : sd.fields.findIdx? (·.1 == fld) with
          | none => rw [fieldOffIn_none _ _ _ _ hi] at hfo; cases hfo
          | some i =>
            obtain ⟨hlt, hl⟩ := fieldOffIn_of_findIdx E.prog sd.fields fld 0 i hi
            rw [hl] at hfo
            simp only [Option.some.injEq, Prod.mk.injEq, Nat.zero_add] at hfo
            obtain ⟨rfl, rfl⟩ := hfo
            have hlt' : i < fs.size := by omega
            simp only [Lang.Sem.fieldIndex, hsd, hi, Array.getElem?_eq_getElem hlt']
            exact hp.mono (fun t _ _ ⟨A, hA, hin, hpl⟩ =>
              ⟨_, by rw [addr_add_off, hA]; rfl, hin, PlaceAt.field hpl hev hsd hi hlt hlt'⟩)

/-- What `lowIdx` promises: the low two bytes of the operand. -/
def LPost (c : Ctx) (f : IR.Fn) (sF : LS) (m : Nat) (o : Opd) (s0 s3 : LS) (low : Opd) (s' : LS) : Prop :=
  Ext s3 s' ∧ s'.cur = s3.cur ∧ (∀ t, low = .tmp t → s0.tmps.size ≤ t ∧ t < s'.tmps.size) ∧
    ∀ ist tmps, Ext s' sF → tmps.size = f.tmps.size →
      Runs c f ist s3.out.size s'.out.size s3.tmps.size tmps
        (fun tmps' => opd c ist tmps' 2 low = opd c ist tmps m o % 65536)

theorem lowIdx_ok (F : Final c fn f sF) {E : Env} (m : Nat) (hm : 2 ≤ m) (o : Opd) (s0 s3 : LS)
    (h03 : s0.tmps.size ≤ s3.tmps.size) (ho : ∀ t, o = .tmp t → s0.tmps.size ≤ t ∧ t < s3.tmps.size) :
    wp (lowIdx m o) E (LPost c f sF m o s0 s3) s3 := by
  have hext : ∀ o, wp (extTmp 2 m o) E (LPost c f sF m o s0 s3) s3 := by
    intro o
    refine wp_mono (extTmp_ok F 2 m o s3) ?_
    intro o' s' ⟨hx, hcur, ho', hts, hsem⟩
    refine ⟨hx, hcur, fun t ht => ?_, fun ist tmps hxF hsz => ?_⟩
    · rw [ho'] at ht
      cases ht
      omega
    · exact (hsem ist tmps hxF hsz).mono (fun t _ _ h => by rw [h]; rfl)
  cases o with
  | slot sl =>
    simp only [lowIdx, wp_pure]
    refine ⟨Ext.refl _, rfl, by simp, fun ist tmps hxF hsz => Runs.done ?_⟩
    simp only [opd_slot]
    rw [show m = 2 + (m - 2) by omega, ← rd_low]
  | const v => exact hext _
  | tmp t => exact hext _

theorem step_trap (c : Ctx) (ist : St) (tmps : Array Nat) : step c ist tmps .trap = .stop (.trap ist) := rfl

theorem step_br (c : Ctx) (ist : St) (tmps : Array Nat) (k : Cmp) (n : Nat) (a b : Opd) (l : Nat) :
    step c ist tmps (.br k n a b l) =
      if cmpOp k (opd c ist tmps n a) (opd c ist tmps n b) then .goto l else .next ist tmps := rfl

theorem step_label (c : Ctx) (ist : St) (tmps : Array Nat) (l : Nat) : step c ist tmps (.label l) = .next ist tmps :=
  rfl

theorem step_jmp (c : Ctx) (ist : St) (tmps : Array Nat) (l : Nat) : step c ist tmps (.jmp l) = .goto l := rfl

/-- A jump to the trap label ends in the trap. -/
theorem Final.trap_ends (F : Final c fn f sF) {s : LS} (hx : Ext s sF) {tl : Nat} (ht : s.trapLabel = some tl)
    {pc : Nat} {ins : Instr} {ist : St} {tmps : Array Nat} (hb : f.body[pc]? = some ins)
    (hs : step c ist tmps ins = .goto tl) : Ends c f pc tmps ist (.trap ist) := by
  obtain ⟨i, h1, h2⟩ := F.trap tl (hx.trap tl ht)
  exact (Reach.goto hb hs (F.label h1)).ends
    ((Reach.next h1 (step_label c ist tmps tl)).ends (Ends.stop h2 (step_trap c ist tmps) (by simp)))

/-- An element of an array, as a place. -/
theorem index_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (b i : Expr) (ty : Ty) (s : LS)
    (hw : WT E (.index b i)) (hty : E.tyOf (.index b i) = .ok ty)
    (ihb : ∀ tb, E.tyOf b = .ok tb → wp (place b) E (PPost c f sF E b tb s) s)
    (ihi : ∀ ti s1, E.tyOf i = .ok ti → ti.isScalar = true → wp (expr i) E (EPost c f sF E i ti s1) s1) :
    wp (place (.index b i)) E (PPost c f sF E (.index b i) ty s) s := by
  rw [place]
  obtain ⟨hwb, hwi, ⟨iw, hti⟩, hn, _⟩ := hw
  simp only [Env.tyOf] at hty
  cases htb : E.tyOf b with
  | error m => simp [htb] at hty
  | ok tb =>
    cases tb with
    | int _ => simp [htb, Env.err] at hty
    | bool => simp [htb, Env.err] at hty
    | record _ => simp [htb, Env.err] at hty
    | arr el n =>
      simp only [htb, Except.ok.injEq] at hty
      subst hty
      have hn' := hn el n htb
      simp only [wp_bind]
      refine wp_mono (ihb _ htb) ?_
      intro r s1 ⟨hx, hcur, hrt, ⟨⟨sl, hroot⟩, hidx⟩, hsem⟩
      simp only [hrt, wp_bind, wp_size]
      cases hri : r.1.idx with
      | some ix => simp only [Option.isSome_some, if_true, wp_err]
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        -- the array, wherever the code after `place b` goes on
        have hbS : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat) (bv : Val),
            Ext s1 sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
            Lang.Sem.evalE E.prog lst env b = some bv → ∃ xs, bv = .arr xs ∧ xs.size = n ∧
              Runs c f ist s.out.size s1.out.size s.tmps.size tmps (fun _ =>
                PlaceAt c E cur lst env ist b (.arr el n) (.arr xs)
                  (c.layout.addr { sl with off := sl.off + r.1.off })) := by
          intro cur lst env ist tmps bv hxF hrel hsz hev
          have hp := hsem cur lst env ist tmps hxF hrel hsz
          simp only [hev] at hp
          have hv := evalE_hasTy E lst env (hrel.typed L) b bv _ hwb hev htb
          obtain ⟨xs, rfl, hxs, _⟩ := hasTy_arr hv
          refine ⟨xs, rfl, hxs, hp.mono (fun t _ _ ⟨A, hA, hin, hpl⟩ => ?_)⟩
          rw [addr_static c ist t hroot hri] at hA
          cases hA
          exact hpl
        have hbN : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat),
            Ext s1 sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
            Lang.Sem.evalE E.prog lst env b = none → Ends c f s.out.size tmps ist (.trap ist) := by
          intro cur lst env ist tmps hxF hrel hsz hev
          have hp := hsem cur lst env ist tmps hxF hrel hsz
          simp only [hev] at hp
          rcases hp with hp | ⟨t, _, _, _, hA⟩
          · exact hp
          · rw [addr_static c ist t hroot hri] at hA
            cases hA
        cases hci : closed? i with
        | some v =>
          obtain ⟨_, ival, hiv, hiall⟩ := closed_val hwi hti rfl hci
          by_cases hvn : v < n
          · simp only [hvn, if_true, wp_pure]
            refine ⟨hx, hcur, rfl, ⟨⟨sl, hroot⟩, fun x hx' => by simp only [hri] at hx'; cases hx'⟩, ?_⟩
            intro cur lst env ist tmps hxF hrel hsz
            simp only [Lang.Sem.evalE, hiall lst env]
            cases hev : Lang.Sem.evalE E.prog lst env b with
            | none => exact .inl (hbN cur lst env ist tmps hxF hrel hsz hev)
            | some bv =>
              obtain ⟨xs, rfl, hxs, hruns⟩ := hbS cur lst env ist tmps bv hxF hrel hsz hev
              have hlt : ival.toNat < xs.size := by omega
              simp only [Array.getElem?_eq_getElem hlt]
              refine hruns.mono (fun t _ _ hpl => ⟨_, ?_, rfl, PlaceAt.index hpl hev (hiall lst env) rfl hlt⟩)
              rw [hiv]
              simp only [addr, hroot, addr_off, Option.some.injEq]
              omega
          · simp only [hvn, if_false, wp_bind, wp_emit, wp_pure]
            refine ⟨hx.trans (Ext.emit _ _), hcur, rfl, ⟨⟨sl, hroot⟩, fun x hx' => by rw [hri] at hx'; cases hx'⟩, ?_⟩
            intro cur lst env ist tmps hxF hrel hsz
            have htrap : ∀ t, Ends c f s1.out.size t ist (.trap ist) :=
              fun t => Ends.stop (F.emitted hxF rfl) (step_trap c ist t) (by simp)
            simp only [Lang.Sem.evalE, hiall lst env]
            cases hev : Lang.Sem.evalE E.prog lst env b with
            | none => exact .inl (hbN cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz hev)
            | some bv =>
              obtain ⟨xs, rfl, hxs, hruns⟩ := hbS cur lst env ist tmps bv ((Ext.emit _ _).trans hxF) hrel hsz hev
              simp only [Array.getElem?_eq_none (show xs.size ≤ ival.toNat by omega)]
              exact .inl (hruns.ends (fun t _ _ _ => htrap t))
        | none =>
          simp only [wp_bind, wp_tyOf]
          intro it hit
          rw [hti] at hit
          cases hit
          simp only [wp_bind]
          refine wp_mono (ihi (.int iw) s1 hti rfl) ?_
          intro o s2 ⟨hx2, hcur2, ho2, hsem2⟩
          -- the array and the index, wherever the code after them goes on
          have hboth : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat)
              (xs : Array Val) (k : UInt64), Ext s2 sF → SRel c E cur lst env ist →
              tmps.size = f.tmps.size → Lang.Sem.evalE E.prog lst env b = some (.arr xs) →
              Lang.Sem.evalE E.prog lst env i = some (.int iw k) →
              Runs c f ist s.out.size s2.out.size s.tmps.size tmps (fun t =>
                opd c ist t (iw.bits / 8) o = k.toNat ∧
                PlaceAt c E cur lst env ist b (.arr el n) (.arr xs)
                  (c.layout.addr { sl with off := sl.off + r.1.off })) := by
            intro cur lst env ist tmps xs k hxF hrel hsz hevb hevi
            obtain ⟨xs', hxs', _, hruns⟩ := hbS cur lst env ist tmps _ (hx2.trans hxF) hrel hsz hevb
            cases hxs'
            refine hruns.seq hx.tmps (fun t1 hts _ hpl => ?_)
            have h2 := hsem2 cur lst env ist t1 hxF hrel (by rw [hts]; exact hsz)
            simp only [hevi] at h2
            exact h2.mono (fun t2 _ _ ho => ⟨ho, hpl⟩)
          have hsome : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat)
              (v : Val), Ext s2 sF → SRel c E cur lst env ist →
              tmps.size = f.tmps.size → Lang.Sem.evalE E.prog lst env (.index b i) = some v →
              ∃ xs k, Lang.Sem.evalE E.prog lst env b = some (.arr xs) ∧ xs.size = n ∧
                Lang.Sem.evalE E.prog lst env i = some (.int iw k) ∧ k.toNat < 2 ^ iw.bits ∧
                ∃ hlt : k.toNat < xs.size, v = xs[k.toNat] := by
            intro cur lst env ist tmps v hxF hrel hsz hev
            simp only [Lang.Sem.evalE] at hev
            cases hevb : Lang.Sem.evalE E.prog lst env b with
            | none => simp [hevb] at hev
            | some bv =>
              cases hevi : Lang.Sem.evalE E.prog lst env i with
              | none => simp [hevb, hevi] at hev
              | some iv =>
                obtain ⟨xs, rfl, hxs, _⟩ := hasTy_arr (evalE_hasTy E lst env (hrel.typed L) b bv _ hwb hevb htb)
                obtain ⟨k, rfl, hk⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) i iv _ hwi hevi hti)
                simp only [hevb, hevi, Val.toNat] at hev
                have hlt : k.toNat < xs.size := by
                  rcases Nat.lt_or_ge k.toNat xs.size with h | h
                  · exact h
                  · rw [Array.getElem?_eq_none h] at hev; cases hev
                rw [Array.getElem?_eq_getElem hlt] at hev
                exact ⟨xs, k, rfl, hxs, rfl, hk, hlt, (Option.some.inj hev).symm⟩
          -- no value: the array has none, the index has none, or it is out of range
          have hnone : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat),
              Ext s2 sF → SRel c E cur lst env ist →
              tmps.size = f.tmps.size → Lang.Sem.evalE E.prog lst env (.index b i) = none →
              Ends c f s.out.size tmps ist (.trap ist) ∨
              ∃ xs k, Lang.Sem.evalE E.prog lst env b = some (.arr xs) ∧ xs.size = n ∧
                Lang.Sem.evalE E.prog lst env i = some (.int iw k) ∧ k.toNat < 2 ^ iw.bits ∧ n ≤ k.toNat := by
            intro cur lst env ist tmps hxF hrel hsz hev
            simp only [Lang.Sem.evalE] at hev
            cases hevb : Lang.Sem.evalE E.prog lst env b with
            | none => exact .inl (hbN cur lst env ist tmps (hx2.trans hxF) hrel hsz hevb)
            | some bv =>
              obtain ⟨xs, rfl, hxs, hruns⟩ := hbS cur lst env ist tmps bv (hx2.trans hxF) hrel hsz hevb
              cases hevi : Lang.Sem.evalE E.prog lst env i with
              | none =>
                refine .inl (hruns.ends (fun t hts _ _ => ?_))
                have h2 := hsem2 cur lst env ist t hxF hrel (by rw [hts]; exact hsz)
                simp only [hevi] at h2
                exact h2
              | some iv =>
                obtain ⟨k, rfl, hk⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) i iv _ hwi hevi hti)
                simp only [hevb, hevi, Val.toNat] at hev
                refine .inr ⟨xs, k, rfl, hxs, rfl, hk, ?_⟩
                rcases Nat.lt_or_ge k.toNat xs.size with h | h
                · rw [Array.getElem?_eq_getElem h] at hev; cases hev
                · omega
          by_cases hm : iw.bits / 8 ≤ 2
          · simp only [hm, if_true, wp_pure]
            refine ⟨hx.trans hx2, by rw [hcur2, hcur], rfl, ⟨⟨sl, hroot⟩, fun x hx' t ht => ?_⟩, ?_⟩
            · simp only [Option.some.injEq] at hx'
              subst hx'
              have := ho2.1 t ht
              have := hx.tmps
              omega
            · intro cur lst env ist tmps hxF hrel hsz
              cases hev : Lang.Sem.evalE E.prog lst env (.index b i) with
              | some v =>
                obtain ⟨xs, k, hevb, hxs, hevi, hk, hlt, rfl⟩ := hsome cur lst env ist tmps v hxF hrel hsz hev
                refine (hboth cur lst env ist tmps xs k hxF hrel hsz hevb hevi).mono (fun t _ _ ⟨ho, hpl⟩ =>
                  ⟨_, ?_, by simp [inBound, ho, Val.toNat]; omega, PlaceAt.index hpl hevb hevi rfl hlt⟩)
                by_cases hbig : n ≥ 2 ^ iw.bits
                · simp only [addr, hroot, ho, addr_off, hbig, if_true, Val.toNat]
                · simp only [addr, hroot, ho, addr_off, hbig, if_false, Val.toNat]
                  rw [if_pos (by omega)]
              | none =>
                rcases hnone cur lst env ist tmps hxF hrel hsz hev with h | ⟨xs, k, hevb, hxs, hevi, hk, hge⟩
                · exact .inl h
                · refine .inr ((hboth cur lst env ist tmps xs k hxF hrel hsz hevb hevi).mono (fun t _ _ ⟨ho, _⟩ => ?_))
                  have hbig : ¬ n ≥ 2 ^ iw.bits := by omega
                  simp only [addr, hroot, ho, hbig, if_false]
                  rw [if_neg (by omega)]
          · simp only [hm, if_false, wp_bind]
            refine wp_trapLabel' (fun tl s3 hx3 hcur3 hout3 htmps3 htl => ?_)
            simp only [wp_emit]
            have hm2 : 2 ≤ iw.bits / 8 := by omega
            refine wp_mono (lowIdx_ok F (iw.bits / 8) hm2 o s
              { s3 with out := s3.out.push (.br .ge (iw.bits / 8) o (.const n) tl) }
              (by simp only [htmps3]; exact Nat.le_trans hx.tmps hx2.tmps)
              (fun t ht => by
                have := ho2.1 t ht
                have := hx.tmps
                simp only [htmps3]
                omega)) ?_
            intro low s4 ⟨hx4, hcur4, hlow, hsem4⟩
            simp only [wp_pure]
            have hx34 : Ext s3 s4 := (Ext.emit _ _).trans hx4
            refine ⟨hx.trans (hx2.trans (hx3.trans hx34)), by rw [hcur4]; simp only [hcur3, hcur2, hcur], rfl,
              ⟨⟨sl, hroot⟩, fun x hx' t ht => ?_⟩, ?_⟩
            · simp only [Option.some.injEq] at hx'
              subst hx'
              exact hlow t ht
            · intro cur lst env ist tmps hxF hrel hsz
              have hxF2 : Ext s2 sF := hx3.trans (hx34.trans hxF)
              have hbr : f.body[s2.out.size]? = some (.br .ge (iw.bits / 8) o (.const n) tl) := by
                rw [← hout3]
                exact F.emitted (hx4.trans hxF) rfl
              have hcn : ∀ t, opd c ist t (iw.bits / 8) (.const n) = n := fun t => by
                rw [opd_const]
                refine modN_of_lt (Nat.lt_of_lt_of_le hn' ?_)
                rw [show (65536 : Nat) = 2 ^ 16 from rfl]
                exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
              cases hev : Lang.Sem.evalE E.prog lst env (.index b i) with
              | some v =>
                obtain ⟨xs, k, hevb, hxs, hevi, hk, hlt, rfl⟩ := hsome cur lst env ist tmps v hxF2 hrel hsz hev
                refine (hboth cur lst env ist tmps xs k hxF2 hrel hsz hevb hevi).seq (Nat.le_refl _)
                  (fun t hts _ ⟨ho, hpl⟩ => ?_)
                have hskip : Runs c f ist s2.out.size (s2.out.size + 1) s.tmps.size t (fun t' => t' = t) :=
                  Runs.skip hbr (by rw [step_br, ho, hcn, if_neg (by simp [cmpOp]; omega)]) rfl
                refine hskip.seq (Nat.le_refl _) (fun t' _ _ ht' => ?_)
                subst ht'
                have h4 := hsem4 ist t' hxF (by rw [hts]; exact hsz)
                simp only [Array.size_push, hout3, htmps3] at h4
                refine (h4.weaken (Nat.le_trans hx.tmps hx2.tmps)).mono (fun t4 _ _ hl =>
                  ⟨_, ?_, ?_, PlaceAt.index hpl hevb hevi rfl hlt⟩)
                rotate_left
                · simp only [inBound, hl, ho, Val.toNat]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  simp
                  omega
                simp only [addr, hroot, hl, ho, addr_off, Val.toNat]
                rw [Nat.mod_eq_of_lt (by omega)]
              | none =>
                rcases hnone cur lst env ist tmps hxF2 hrel hsz hev with h | ⟨xs, k, hevb, hxs, hevi, hk, hge⟩
                · exact .inl h
                · refine .inl ((hboth cur lst env ist tmps xs k hxF2 hrel hsz hevb hevi).ends
                    (fun t hts _ ⟨ho, _⟩ => ?_))
                  exact F.trap_ends (hx34.trans hxF) htl hbr
                    (by rw [step_br, ho, hcn, if_pos (by simp [cmpOp]; omega)])

/-- The types of the operands of a well-typed binary operator. -/
theorem bin_types {E : Env} {op : BinOp} {a b : Expr} (hw : WT E (.bin op a b)) :
    ∃ ta tb, E.tyOf a = .ok ta ∧ E.tyOf b = .ok tb ∧ ta.isScalar = true ∧ tb.isScalar = true ∧
      (if op.isLogic then ta = .bool ∧ tb = .bool
       else if op.isShift then (∃ w, ta = .int w) ∧ ∃ w, tb = .int w
       else if op = .eq ∨ op = .ne then ta = tb ∧ ta.isScalar = true
       else ∃ w, ta = .int w ∧ tb = .int w) ∧
      E.tyOf (.bin op a b) = .ok (if op.isCompare || op.isLogic then .bool else ta) := by
  obtain ⟨_, _, hc⟩ := hw
  have hty : ∀ ta, E.tyOf a = .ok ta →
      E.tyOf (.bin op a b) = .ok (if op.isCompare || op.isLogic then .bool else ta) := by
    intro ta hta
    simp only [Env.tyOf]
    split
    · rfl
    · exact hta
  by_cases h1 : op.isLogic = true
  · rw [if_pos h1] at hc
    exact ⟨.bool, .bool, hc.1, hc.2, rfl, rfl, by rw [if_pos h1]; exact ⟨rfl, rfl⟩, hty _ hc.1⟩
  · rw [if_neg h1] at hc
    by_cases h2 : op.isShift = true
    · rw [if_pos h2] at hc
      obtain ⟨⟨w, ha⟩, ⟨w', hb⟩⟩ := hc
      exact ⟨.int w, .int w', ha, hb, rfl, rfl, by rw [if_neg h1, if_pos h2]; exact ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩, hty _ ha⟩
    · rw [if_neg h2] at hc
      by_cases h3 : op = .eq ∨ op = .ne
      · rw [if_pos h3] at hc
        obtain ⟨t, ha, hb, hs⟩ := hc
        exact ⟨t, t, ha, hb, hs, hs, by rw [if_neg h1, if_neg h2, if_pos h3]; exact ⟨rfl, hs⟩, hty _ ha⟩
      · rw [if_neg h3] at hc
        obtain ⟨w, ha, hb⟩ := hc
        exact ⟨.int w, .int w, ha, hb, rfl, rfl, by rw [if_neg h1, if_neg h2, if_neg h3]; exact ⟨w, rfl, rfl⟩,
          hty _ ha⟩

/-- A binary operator into a destination. -/
theorem bin_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (op : BinOp) (a b : Expr) (ty : Ty) (dst : Dst)
    (s : LS) (hw : WT E (.bin op a b)) (hty : E.tyOf (.bin op a b) = .ok ty) (hs : ty.isScalar = true)
    (iha : ∀ ta s1, E.tyOf a = .ok ta → ta.isScalar = true → wp (expr a) E (EPost c f sF E a ta s1) s1)
    (ihb : ∀ tb s1, E.tyOf b = .ok tb → tb.isScalar = true → wp (expr b) E (EPost c f sF E b tb s1) s1) :
    wp (exprTo dst (.bin op a b)) E (TPost c f sF E (.bin op a b) ty dst s) s := by
  obtain ⟨ta, tb, hta, htb, hsa, hsb, hcond, hty'⟩ := bin_types hw
  rw [hty] at hty'
  simp only [Except.ok.injEq] at hty'
  subst hty'
  rw [exprTo]
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t ht
  rw [hty] at ht
  cases ht
  cases hc : closed? (.bin op a b) with
  | some k => exact closedTo_ok F s dst hw hty hs hc
  | none =>
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t2 ht2
    rw [hta] at ht2
    cases ht2
    refine wp_mono (ihb tb s htb hsb) ?_
    intro ob s1 ⟨hx1, hc1, ho1, hs1⟩
    refine wp_mono (iha ta s1 hta hsa) ?_
    intro oa s2 ⟨hx2, hc2, ho2, hs2⟩
    have key : wp (emit (binI op (sizeOf E.prog (if op.isCompare || op.isLogic then .bool else ta)) (sizeOf E.prog ta)
        (if op.isShift then sizeOf E.prog tb else 0) dst oa ob)) E
        (TPost c f sF E (.bin op a b) (if op.isCompare || op.isLogic then .bool else ta) dst s) s2 := by
      rw [wp_emit]
      refine ⟨(hx1.trans hx2).trans (Ext.emit _ _), by rw [← hc1, ← hc2], ?_⟩
      intro cur lst env ist tmps hxF hrel hsz
      have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
      have hpb := hs1 cur lst env ist tmps (hx2.trans hxF2) hrel hsz
      simp only [Lang.Sem.evalE, Array.size_push]
      cases hevb : Lang.Sem.evalE E.prog lst env b with
      | none =>
        simp only [hevb] at hpb
        cases Lang.Sem.evalE E.prog lst env a <;> exact hpb
      | some y =>
        simp only [hevb] at hpb
        cases heva : Lang.Sem.evalE E.prog lst env a with
        | none =>
          refine hpb.ends (fun t1 hts _ _ => ?_)
          have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [hts]; exact hsz)
          simp only [heva] at h2
          exact h2
        | some x =>
          have hvx := evalE_hasTy E lst env (hrel.typed L) a x ta hw.1 heva hta
          have hvy := evalE_hasTy E lst env (hrel.typed L) b y tb hw.2.1 hevb htb
          obtain ⟨v, hv⟩ := binop_some E.prog op x y ta tb hvx hvy hcond
          simp only [hv]
          obtain ⟨t1, r1, sz1, ag1, hob⟩ := hpb
          have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [sz1]; exact hsz)
          simp only [heva] at h2
          obtain ⟨t2, r2, sz2, ag2, hoa⟩ := h2
          have hob2 : opd c ist t2 (sizeOf E.prog tb) ob = y.toNat := by
            rw [opd_agree c ist _ (fun t ht => (ho1.1 t ht).2) ag2]
            exact hob
          refine ⟨t2, by rw [sz2, sz1], ag1.trans ag2 hx1.tmps, (r1.trans r2).trans (reach_set F hxF rfl ?_)⟩
          exact binI_step c ist t2 E.prog op x y v ta tb dst oa ob hvx hvy hcond hv hoa hob2 ho2.2 ho1.2
    by_cases hsh : op.isShift = true
    · simp only [hsh, if_true, wp_bind, wp_tyOf, wp_size] at key ⊢
      intro t3 ht3
      rw [htb] at ht3
      cases ht3
      exact key
    · simp only [hsh, Bool.false_eq_true, if_false, wp_pure] at key ⊢
      exact key

/-- A unary operator into a destination. -/
theorem un_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (op : UnOp) (a : Expr) (ty : Ty) (dst : Dst)
    (s : LS) (hw : WT E (.un op a)) (hty : E.tyOf (.un op a) = .ok ty) (hs : ty.isScalar = true)
    (iha : ∀ s1, wp (expr a) E (EPost c f sF E a ty s1) s1) :
    wp (exprTo dst (.un op a)) E (TPost c f sF E (.un op a) ty dst s) s := by
  have hta : E.tyOf a = .ok ty := by simpa only [Env.tyOf] using hty
  rw [exprTo]
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t ht
  rw [hty] at ht
  cases ht
  cases hc : closed? (.un op a) with
  | some k => exact closedTo_ok F s dst hw hty hs hc
  | none =>
    simp only [wp_bind]
    refine wp_mono (iha s) ?_
    intro o s1 ⟨hx1, hc1, ho1, hs1⟩
    rw [wp_emit]
    refine ⟨hx1.trans (Ext.emit _ _), hc1, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hp := hs1 cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
    rw [evalE_un]
    simp only [Array.size_push]
    cases heva : Lang.Sem.evalE E.prog lst env a with
    | none => simp only [heva] at hp ⊢; exact hp
    | some x =>
      simp only [heva] at hp ⊢
      have hvx := evalE_hasTy E lst env (hrel.typed L) a x ty hw.1 heva hta
      obtain ⟨t1, r1, sz1, ag1, ho⟩ := hp
      obtain ⟨v, hv, _, hstep⟩ := unI_step c ist t1 E.prog op x ty dst o hvx (by simpa only [hta, Except.ok.injEq] using hw.2) ho
      simp only [hv]
      exact ⟨t1, sz1, ag1, r1.trans (reach_set F hxF rfl hstep)⟩

/-- A cast into a destination. -/
theorem castTo_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (w : Width) (a : Expr) (dst : Dst) (s : LS)
    (hw : WT E (.cast w a))
    (iha : ∀ ta s1, E.tyOf a = .ok ta → ta.isScalar = true → wp (expr a) E (EPost c f sF E a ta s1) s1) :
    wp (exprTo dst (.cast w a)) E (TPost c f sF E (.cast w a) (.int w) dst s) s := by
  obtain ⟨hwa, ta, hta, hsa⟩ := hw
  rw [exprTo]
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t ht
  simp only [Env.tyOf, Except.ok.injEq] at ht
  subst ht
  cases hc : closed? (.cast w a) with
  | some k => exact closedTo_ok F s dst ⟨hwa, ta, hta, hsa⟩ rfl rfl hc
  | none =>
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t2 ht2
    rw [hta] at ht2
    cases ht2
    refine wp_mono (iha ta s hta hsa) ?_
    intro o s1 ⟨hx1, hc1, ho1, hs1⟩
    rw [wp_emit]
    refine ⟨hx1.trans (Ext.emit _ _), hc1, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hp := hs1 cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
    rw [evalE_cast]
    simp only [Array.size_push]
    cases heva : Lang.Sem.evalE E.prog lst env a with
    | none => simp only [heva] at hp ⊢; exact hp
    | some x =>
      simp only [heva] at hp ⊢
      have hvx := evalE_hasTy E lst env (hrel.typed L) a x ta hwa heva hta
      obtain ⟨cv, hcv, _, hcn⟩ := cast_val E.prog w hvx hsa
      simp only [hcv]
      obtain ⟨t1, r1, sz1, ag1, ho⟩ := hp
      refine ⟨t1, sz1, ag1, r1.trans (reach_set F hxF rfl ?_)⟩
      rw [castI_step c ist t1 _ _ dst o x.toNat ho (toNat_lt hvx hsa), hcn]
      simp only [size_int, bits8]

/-- An operand that is not the temporary just written. -/
theorem opd_set_ne (c : Ctx) (ist : St) (tmps : Array Nat) (n d x : Nat) {o : Opd} (h : ∀ t, o = .tmp t → t ≠ d) :
    opd c ist (tmps.setIfInBounds d x) n o = opd c ist tmps n o := by
  cases o with
  | const v => rfl
  | slot sl => rfl
  | tmp t =>
    simp only [opd_tmp, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne (fun e => h t rfl e.symm)]

theorem push4 {α : Type} (xs : Array α) (a b c d : α) :
    ((((xs.push a).push b).push c).push d)[xs.size]? = some a ∧
    ((((xs.push a).push b).push c).push d)[xs.size + 1]? = some b ∧
    ((((xs.push a).push b).push c).push d)[xs.size + 2]? = some c ∧
    ((((xs.push a).push b).push c).push d)[xs.size + 3]? = some d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push, if_pos rfl]
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_pos (by simp only [Array.size_push])]
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_pos (by simp only [Array.size_push])]
  · rw [Array.getElem?_push, if_pos (by simp only [Array.size_push])]

/-- A conditional expression into a temporary. -/
theorem cond_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (cnd a b : Expr) (ty : Ty) (d : Nat) (s : LS)
    (hw : WT E (.cond cnd a b)) (hty : E.tyOf (.cond cnd a b) = .ok ty) (hs : ty.isScalar = true)
    (hd : d < s.tmps.size)
    (ihc : ∀ s1, wp (expr cnd) E (EPost c f sF E cnd .bool s1) s1)
    (iha : ∀ s1, wp (expr a) E (EPost c f sF E a ty s1) s1)
    (ihb : ∀ s1, wp (expr b) E (EPost c f sF E b ty s1) s1) :
    wp (exprTo (.tmp d) (.cond cnd a b)) E (TPost c f sF E (.cond cnd a b) ty (.tmp d) s) s := by
  obtain ⟨hwc, hwa, hwb, htc, t0, hta, htb, _⟩ := hw
  have hta' : E.tyOf a = .ok ty := by simpa only [Env.tyOf] using hty
  rw [hta] at hta'
  cases hta'
  rw [exprTo]
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t ht
  rw [hty] at ht
  cases ht
  cases hc : closed? (.cond cnd a b) with
  | some k => exact closedTo_ok F s _ ⟨hwc, hwa, hwb, htc, ty, hta, htb, hs⟩ hty hs hc
  | none =>
    simp only [wp_bind]
    refine wp_mono (ihc s) ?_
    intro oc s1 ⟨hx1, hc1, ho1, hs1⟩
    refine wp_mono (iha s1) ?_
    intro oa s2 ⟨hx2, hc2, ho2, hs2⟩
    refine wp_mono (ihb s2) ?_
    intro ob s3 ⟨hx3, hc3, ho3, hs3⟩
    simp only [wp_newLabel, wp_emit]
    have hx34 := (Ext.newLabel s3).trans ((Ext.emit _ (Instr.mov (sizeOf E.prog ty) (.tmp d) ob)).trans
      ((Ext.emit _ (Instr.br .eq 1 oc (.const 0) s3.labels)).trans
      ((Ext.emit _ (Instr.mov (sizeOf E.prog ty) (.tmp d) oa)).trans (Ext.emit _ (Instr.label s3.labels)))))
    refine ⟨((hx1.trans hx2).trans hx3).trans hx34, by rw [← hc1, ← hc2, ← hc3], ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have hxF3 : Ext s3 sF := hx34.trans hxF
    obtain ⟨g1, g2, g3, g4⟩ := push4 s3.out (Instr.mov (sizeOf E.prog ty) (.tmp d) ob)
      (Instr.br .eq 1 oc (.const 0) s3.labels) (Instr.mov (sizeOf E.prog ty) (.tmp d) oa) (Instr.label s3.labels)
    have hb1 := F.at_ hxF g1
    have hb2 := F.at_ hxF g2
    have hb3 := F.at_ hxF g3
    have hb4 := F.at_ hxF g4
    have hpc := hs1 cur lst env ist tmps (hx2.trans (hx3.trans hxF3)) hrel hsz
    simp only [Lang.Sem.evalE, Array.size_push]
    cases hevc : Lang.Sem.evalE E.prog lst env cnd with
    | none => simp only [hevc] at hpc ⊢; exact hpc
    | some cv =>
      simp only [hevc] at hpc
      cases heva : Lang.Sem.evalE E.prog lst env a with
      | none =>
        refine hpc.ends (fun t1 hts _ _ => ?_)
        have h2 := hs2 cur lst env ist t1 (hx3.trans hxF3) hrel (by rw [hts]; exact hsz)
        simp only [heva] at h2
        exact h2
      | some x =>
        obtain ⟨t1, r1, sz1, ag1, hoc⟩ := hpc
        have h2 := hs2 cur lst env ist t1 (hx3.trans hxF3) hrel (by rw [sz1]; exact hsz)
        simp only [heva] at h2
        obtain ⟨t2, r2, sz2, ag2, hoa⟩ := h2
        have h3 := hs3 cur lst env ist t2 hxF3 hrel (by rw [sz2, sz1]; exact hsz)
        cases hevb : Lang.Sem.evalE E.prog lst env b with
        | none =>
          simp only [hevb] at h3 ⊢
          exact (r1.trans r2).ends h3
        | some y =>
          simp only [hevb] at h3 ⊢
          obtain ⟨t3, r3, sz3, ag3, hob⟩ := h3
          obtain ⟨bb, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) cnd cv .bool hwc hevc htc)
          have hd1 := hx1.tmps
          have hd2 := hx2.tmps
          have hoc3 : opd c ist t3 1 oc = (Val.bool bb).toNat := by
            rw [opd_agree c ist _ (fun t ht => (ho1.1 t ht).2) (ag2.trans ag3 hd2)]
            exact hoc
          have hoa3 : opd c ist t3 (sizeOf E.prog ty) oa = x.toNat := by
            rw [opd_agree c ist _ (fun t ht => (ho2.1 t ht).2) ag3]
            exact hoa
          have hne1 : ∀ t, oc = .tmp t → t ≠ d := fun t ht => by have := (ho1.1 t ht).1; omega
          have hne2 : ∀ t, oa = .tmp t → t ≠ d := fun t ht => by have := (ho2.1 t ht).1; omega
          have r4 : Reach c f s3.out.size t3 ist (s3.out.size + 1)
              (t3.setIfInBounds d (modN (sizeOf E.prog ty) y.toNat)) ist :=
            Reach.next hb1 (by rw [step_mov, hob]; rfl)
          refine ⟨t3, by rw [sz3, sz2, sz1], (ag1.trans ag2 hd1).trans ag3 (Nat.le_trans hd1 hd2), ?_⟩
          refine ((r1.trans r2).trans r3).trans (r4.trans ?_)
          have hbr : step c ist (t3.setIfInBounds d (modN (sizeOf E.prog ty) y.toNat))
              (Instr.br .eq 1 oc (.const 0) s3.labels) =
              (if bb then .next ist (t3.setIfInBounds d (modN (sizeOf E.prog ty) y.toNat)) else .goto s3.labels) := by
            rw [step_br, opd_set_ne c ist t3 _ _ _ hne1, hoc3]
            cases bb <;> rfl
          have r6 : ∀ t, Reach c f (s3.out.size + 3) t ist (s3.out.size + 4) t ist :=
            fun t => Reach.next hb4 (step_label c ist t _)
          cases bb with
          | false =>
            simp only [Bool.false_eq_true, if_false] at hbr
            simp only [Val.toBool, Bool.false_eq_true, if_false, setDst_tmp]
            exact (Reach.goto hb2 hbr (F.label hb4)).trans (r6 _)
          | true =>
            simp only [if_true] at hbr
            simp only [Val.toBool, if_true, setDst_tmp]
            refine (Reach.next hb2 hbr).trans ((Reach.next hb3 ?_).trans (r6 _))
            rw [step_mov, opd_set_ne c ist t3 _ _ _ hne2, hoa3, setDst_tmp, Array.setIfInBounds_setIfInBounds]
            rfl

/-- What `castOpd` promises: an operand holding the low `n` bytes. -/
def CPost (c : Ctx) (f : IR.Fn) (sF : LS) (n m : Nat) (o : Opd) (s0 s2 : LS) (o' : Opd) (s' : LS) : Prop :=
  Ext s2 s' ∧ s'.cur = s2.cur ∧ (∀ t, o' = .tmp t → s0.tmps.size ≤ t ∧ t < s'.tmps.size) ∧
    (∀ v, o' ≠ .const v) ∧
    ∀ ist tmps, Ext s' sF → tmps.size = f.tmps.size → opd c ist tmps m o < 2 ^ (8 * m) →
      Runs c f ist s2.out.size s'.out.size s2.tmps.size tmps
        (fun tmps' => opd c ist tmps' n o' = opd c ist tmps m o % 2 ^ (8 * n))

theorem castOpd_ok (F : Final c fn f sF) {E : Env} (n m : Nat) (o : Opd) (s0 s2 : LS)
    (h02 : s0.tmps.size ≤ s2.tmps.size) (ho : ∀ t, o = .tmp t → s0.tmps.size ≤ t ∧ t < s2.tmps.size) :
    wp (castOpd n m o) E (CPost c f sF n m o s0 s2) s2 := by
  have hext : ∀ o, wp (extTmp n m o) E (CPost c f sF n m o s0 s2) s2 := by
    intro o
    refine wp_mono (extTmp_ok F n m o s2) ?_
    intro o' s' ⟨hx, hcur, ho', hts, hsem⟩
    refine ⟨hx, hcur, fun t ht => ?_, fun v hv => ?_, fun ist tmps hxF hsz _ => ?_⟩
    · rw [ho'] at ht
      cases ht
      omega
    · rw [ho'] at hv
      cases hv
    · exact (hsem ist tmps hxF hsz).mono (fun t _ _ h => by rw [h]; rfl)
  cases o with
  | slot sl =>
    simp only [castOpd]
    by_cases hnm : n ≤ m
    · rw [if_pos hnm, wp_pure]
      refine ⟨Ext.refl _, rfl, by simp, by simp, fun ist tmps hxF hsz _ => Runs.done ?_⟩
      simp only [opd_slot]
      rw [show m = n + (m - n) by omega, ← rd_low]
    · rw [if_neg hnm]
      exact hext _
  | const v => exact hext _
  | tmp t =>
    simp only [castOpd]
    by_cases hnm : (n == m) = true
    · rw [if_pos hnm, wp_pure]
      rw [beq_iff_eq] at hnm
      subst hnm
      refine ⟨Ext.refl _, rfl, fun t' ht' => ho t' ht', by simp, fun ist tmps hxF hsz hlt => Runs.done ?_⟩
      rw [Nat.mod_eq_of_lt hlt]
    · rw [if_neg hnm]
      exact hext _

/-- Bytes `j` to `j + n` of what is at `A`. -/
theorem rd_bytes (m : ByteArray) (A j n tot : Nat) (h : j + n ≤ tot) :
    rd m (A + j) n = rd m A tot / 2 ^ (8 * j) % 2 ^ (8 * n) := by
  obtain ⟨r, rfl⟩ : ∃ r, tot = j + (n + r) := ⟨tot - j - n, by omega⟩
  rw [← rd_high, ← rd_low]

/-- `(x >>> k : narrower)`, when `k` is whole bytes and the result lies inside `x`. -/
theorem shr_cast (w wx wk : Width) (X K : UInt64) (hX : X.toNat < 2 ^ wx.bits) (hK : K.toNat < wx.bits) :
    ∃ r cv, Lang.Sem.binop .shr (.int wx X) (.int wk K) = some r ∧ castV w r = some cv ∧
      cv.toNat = X.toNat / 2 ^ K.toNat % 2 ^ w.bits := by
  obtain ⟨r, hr1, hr2⟩ := Ember.Proof.CSim.binop_arith .shr rfl rfl wx wk X K hX (fun h => by cases h)
  refine ⟨_, _, hr1, rfl, ?_⟩
  simp only [Val.toNat, Ember.Proof.CSim.mask_toNat, hr2, Ember.Proof.CSim.natOp]
  rw [if_neg (by omega), Nat.shiftRight_eq_div_pow]

/-- A cast as an operand. -/
theorem castE_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (w : Width) (a : Expr) (s : LS)
    (hw : WT E (.cast w a)) (hc : closed? (.cast w a) = none)
    (iha : ∀ ta s1, E.tyOf a = .ok ta → ta.isScalar = true → wp (expr a) E (EPost c f sF E a ta s1) s1)
    (ihx : ∀ x k tx s1, a = .bin .shr x k → E.tyOf x = .ok tx → tx.isScalar = true →
      wp (expr x) E (EPost c f sF E x tx s1) s1) :
    wp (expr (.cast w a)) E (EPost c f sF E (.cast w a) (.int w) s) s := by
  obtain ⟨hwa, ta, hta, hsa⟩ := hw
  -- the cast itself, after code that has run (the first try at `x`, when it was not a variable)
  have main : ∀ s1, Ext s s1 → s1.cur = s.cur →
      (∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat), Ext s1 sF →
        SRel c E cur lst env ist → tmps.size = f.tmps.size →
        (Ends c f s.out.size tmps ist (.trap ist) ∧ Lang.Sem.evalE E.prog lst env a = none) ∨
        Runs c f ist s.out.size s1.out.size s.tmps.size tmps (fun _ => True)) →
      wp (do let o ← expr a; castOpd (w.bits / 8) (sizeOf E.prog ta) o) E
        (EPost c f sF E (.cast w a) (.int w) s) s1 := by
    intro s1 hx1 hc1 hpre
    simp only [wp_bind]
    refine wp_mono (iha ta s1 hta hsa) ?_
    intro o s2 ⟨hx2, hc2, ho2, hs2⟩
    refine wp_mono (castOpd_ok F (w.bits / 8) (sizeOf E.prog ta) o s s2 (Nat.le_trans hx1.tmps hx2.tmps)
      (fun t ht => by have := ho2.1 t ht; have := hx1.tmps; omega)) ?_
    intro o' s3 ⟨hx3, hc3, ho3, hnc, hs3⟩
    refine ⟨(hx1.trans hx2).trans hx3, by rw [hc3, hc2, hc1], ⟨ho3, fun v hv => absurd hv (hnc v)⟩, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    rw [evalE_cast]
    rcases hpre cur lst env ist tmps (hx2.trans (hx3.trans hxF)) hrel hsz with ⟨hends, hnone⟩ | hruns
    · simp only [hnone]
      exact hends
    · cases heva : Lang.Sem.evalE E.prog lst env a with
      | none =>
        refine hruns.ends (fun t1 hts _ _ => ?_)
        have h2 := hs2 cur lst env ist t1 (hx3.trans hxF) hrel (by rw [hts]; exact hsz)
        simp only [heva] at h2
        exact h2
      | some x =>
        have hvx := evalE_hasTy E lst env (hrel.typed L) a x ta hwa heva hta
        obtain ⟨cv, hcv, _, hcn⟩ := cast_val E.prog w hvx hsa
        simp only [hcv]
        refine hruns.seq hx1.tmps (fun t1 hts _ _ => ?_)
        have h2 := hs2 cur lst env ist t1 (hx3.trans hxF) hrel (by rw [hts]; exact hsz)
        simp only [heva] at h2
        refine h2.seq hx2.tmps (fun t2 hts2 _ hoa => ?_)
        have h3 := hs3 ist t2 hxF (by rw [hts2, hts]; exact hsz) (by rw [hoa]; exact toNat_lt hvx hsa)
        refine h3.mono (fun t3 _ _ h => ?_)
        show opd c ist t3 (w.bits / 8) o' = _
        rw [h, hoa, hcn, bits8]
  have main0 := main s (Ext.refl s) rfl (fun _ _ _ _ _ _ _ _ => .inr (Runs.done trivial))
  rw [expr]
  simp only [hc, wp_bind, wp_tyOf, wp_size]
  intro t ht
  rw [hta] at ht
  cases ht
  -- the first try: is the cast bytes of a variable?
  cases a with
  | bin op x k =>
    cases op with
    | shr =>
      obtain ⟨hwx, hwk, hsh⟩ := hwa
      simp only [BinOp.isLogic, BinOp.isShift, Bool.false_eq_true, if_false, if_true] at hsh
      obtain ⟨⟨wx, htx⟩, ⟨wk, htk⟩⟩ := hsh
      have htax : ta = .int wx := by
        simp only [Env.tyOf, BinOp.isCompare, BinOp.isLogic, Bool.or_self, Bool.false_eq_true, if_false] at hta
        rw [htx] at hta
        exact (Except.ok.inj hta).symm
      subst htax
      cases hck : closed? k with
      | none => simp only [hck, wp_pure]; exact main0
      | some kv =>
        simp only [hck]
        by_cases hcond : (kv % 8 == 0 && decide (kv / 8 + w.bits / 8 ≤ sizeOf E.prog (.int wx))) = true
        · rw [if_pos hcond]
          simp only [wp_bind]
          refine wp_mono (ihx x k (.int wx) s rfl htx rfl) ?_
          intro o s1 ⟨hx1, hc1, ho1, hs1⟩
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, size_int] at hcond
          obtain ⟨_, kval, hkv, hkall⟩ := closed_val hwk htk rfl hck
          have hw1 : 1 ≤ w.bits / 8 := by cases w <;> decide
          have hkv_lt : kv < wx.bits := by have := bits8 wx; omega
          -- the value, wherever `x` has one
          have hval : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (xv : Val),
              SRel c E cur lst env ist → Lang.Sem.evalE E.prog lst env x = some xv →
              ∃ cv, Lang.Sem.evalE E.prog lst env (.cast w (.bin .shr x k)) = some cv ∧
                cv.toNat = xv.toNat / 2 ^ kv % 2 ^ w.bits ∧ xv.toNat < 2 ^ wx.bits := by
            intro cur lst env ist xv hrel hevx
            obtain ⟨X, rfl, hX⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) x xv _ hwx hevx htx)
            obtain ⟨K, rfl, _⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) k kval _ hwk (hkall lst env) htk)
            simp only [Val.toNat] at hkv
            obtain ⟨r, cv, hr, hcv, hn⟩ := shr_cast w wx wk X K hX (by rw [hkv]; exact hkv_lt)
            refine ⟨cv, ?_, by rw [hn, hkv]; rfl, hX⟩
            rw [evalE_cast]
            simp only [Lang.Sem.evalE, hevx, hkall lst env, hr, hcv]
          have hnoneX : ∀ (lst : Lang.Sem.St) (env : Lang.Sem.Env), Lang.Sem.evalE E.prog lst env x = none →
              Lang.Sem.evalE E.prog lst env (.bin .shr x k) = none := by
            intro lst env h
            simp only [Lang.Sem.evalE, h]
          cases o with
          | slot sl =>
            simp only [wp_pure]
            refine ⟨hx1, hc1, ⟨by simp, by simp⟩, ?_⟩
            intro cur lst env ist tmps hxF hrel hsz
            have h1 := hs1 cur lst env ist tmps hxF hrel hsz
            cases hevx : Lang.Sem.evalE E.prog lst env x with
            | none =>
              simp only [hevx] at h1
              rw [evalE_cast, hnoneX lst env hevx]
              exact h1
            | some xv =>
              simp only [hevx] at h1
              obtain ⟨cv, hcv, hn, _⟩ := hval cur lst env ist xv hrel hevx
              rw [hcv]
              refine h1.mono (fun t _ _ ho => ?_)
              simp only [opd_slot, size_int, addr_off] at ho ⊢
              rw [rd_bytes _ _ _ _ _ hcond.2, ho, hn, bits8, show 8 * (kv / 8) = kv by omega]
          | const v =>
            simp only [wp_pure]
            refine main s1 hx1 hc1 (fun cur lst env ist tmps hxF hrel hsz => ?_)
            have h1 := hs1 cur lst env ist tmps hxF hrel hsz
            cases hevx : Lang.Sem.evalE E.prog lst env x with
            | none => simp only [hevx] at h1; exact .inl ⟨h1, hnoneX lst env hevx⟩
            | some xv => simp only [hevx] at h1; exact .inr (h1.mono (fun _ _ _ _ => trivial))
          | tmp t0 =>
            simp only [wp_pure]
            refine main s1 hx1 hc1 (fun cur lst env ist tmps hxF hrel hsz => ?_)
            have h1 := hs1 cur lst env ist tmps hxF hrel hsz
            cases hevx : Lang.Sem.evalE E.prog lst env x with
            | none => simp only [hevx] at h1; exact .inl ⟨h1, hnoneX lst env hevx⟩
            | some xv => simp only [hevx] at h1; exact .inr (h1.mono (fun _ _ _ _ => trivial))
        · rw [if_neg hcond]
          simp only [wp_pure]
          exact main0
    | _ => simp only [wp_pure]; exact main0
  | _ => simp only [wp_pure]; exact main0

/-- An operand to a destination. -/
theorem movOpd_ok (F : Final c fn f sF) {E : Env} (e : Expr) (ty : Ty) (s s1 : LS) (o : Opd) (dst : Dst)
    (h : EPost c f sF E e ty s o s1) :
    wp (emit (.mov (sizeOf E.prog ty) dst o)) E (TPost c f sF E e ty dst s) s1 := by
  obtain ⟨hx, hcur, _, hsem⟩ := h
  rw [wp_emit]
  refine ⟨hx.trans (Ext.emit _ _), hcur, ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hp := hsem cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
  simp only [Array.size_push]
  cases hev : Lang.Sem.evalE E.prog lst env e with
  | none => simp only [hev] at hp ⊢; exact hp
  | some v =>
    simp only [hev] at hp ⊢
    obtain ⟨t1, r1, sz1, ag1, ho⟩ := hp
    exact ⟨t1, sz1, ag1, r1.trans (reach_set F hxF rfl (by rw [step_mov, ho]))⟩

/-- Code that evaluated `e` into an operand, then code that stores `e`. -/
theorem TPost.after_expr {E : Env} {e : Expr} {ty : Ty} {s s1 s' : LS} {o : Opd} {dst : Dst}
    (h1 : EPost c f sF E e ty s o s1) (h2 : TPost c f sF E e ty dst s1 () s') : TPost c f sF E e ty dst s () s' := by
  obtain ⟨hx1, hc1, _, hs1⟩ := h1
  obtain ⟨hx2, hc2, hs2⟩ := h2
  refine ⟨hx1.trans hx2, by rw [hc2, hc1], ?_⟩
  intro cur lst env ist tmps hxF hrel hsz
  have hp := hs1 cur lst env ist tmps (hx2.trans hxF) hrel hsz
  cases hev : Lang.Sem.evalE E.prog lst env e with
  | none => simp only [hev] at hp ⊢; exact hp
  | some v =>
    simp only [hev] at hp ⊢
    obtain ⟨t1, r1, sz1, ag1, _⟩ := hp
    have h2 := hs2 cur lst env ist t1 hxF hrel (by rw [sz1]; exact hsz)
    simp only [hev] at h2
    obtain ⟨t2, sz2, ag2, r2⟩ := h2
    exact ⟨t2, by rw [sz2, sz1], ag1.trans ag2 hx1.tmps, r1.trans r2⟩

theorem constVar_spec {E : Env} {x : String} {k : Nat} (h : E.constVar? x = some k) :
    E.vars.lookup x = none ∧ ∃ g, E.prog.global? x = some g ∧ g.const = true ∧ g.ty.isScalar = true ∧
      k = (match g.init with | [v] => v % 2 ^ (8 * sizeOf E.prog g.ty) | _ => 0) := by
  unfold Env.constVar? at h
  cases hv : E.vars.lookup x with
  | some i => simp [hv] at h
  | none =>
    simp only [hv] at h
    cases hg : E.prog.global? x with
    | none => simp [hg] at h
    | some g =>
      simp only [hg] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨rfl, g, rfl, hc.1, hc.2, (Option.some.inj h).symm⟩
      · cases h

/-- A variable as an operand. -/
theorem varOpd_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (x : String) (s : LS)
    (ty : Ty) (hty : E.tyOf (.var x) = .ok ty) (hs : ty.isScalar = true) :
    wp (varOpd x) E (EPost c f sF E (.var x) ty s) s := by
  unfold varOpd
  simp only [wp_bind, wp_constVar]
  cases hcv : E.constVar? x with
  | none =>
    simp only [wp_bind]
    exact wp_mono (placeVar_ok L hE x s ty hty) (fun r s1 h => loadPlace_ok F (.var x) ty hs s s1 r h)
  | some k =>
    obtain ⟨hv, g, hg, hgc, hgs, hk⟩ := constVar_spec hcv
    have hty' : g.ty = ty := by
      simp only [Env.tyOf, Env.varInfo, hv, hg, Except.ok.injEq] at hty
      exact hty
    subst hty'
    obtain ⟨hmem, _⟩ := global?_mem hg
    have hkv : k = (initOf E.prog g).toNat := by
      rw [hk]
      exact (const_toNat E.prog g hgs (L.ginit g hmem)).symm
    have hklt : k < 2 ^ (8 * sizeOf E.prog g.ty) := by
      rw [hk]
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact Nat.two_pow_pos _
    simp only [wp_pure]
    refine ⟨Ext.refl s, rfl, ⟨by simp, fun v hv' => by cases hv'; exact hklt⟩, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    obtain ⟨hl, _⟩ := hrel.loc
    obtain ⟨v, h1, _, _, _, h5⟩ := hrel.glob.lookup hg
    simp only [Lang.Sem.evalE, Lang.Sem.lookup, hl.lookup_none hv, h1]
    refine Runs.done ?_
    rw [opd_const, modN_of_lt hklt, hkv, h5 hgc]

mutual

/-- **The address of a place.** -/
theorem place_ok (F : Final c fn f sF) : ∀ (e : Expr) (E : Env) (s : LS) (ty : Ty), LayOK E.prog c → EnvOK E →
    WT E e → E.tyOf e = .ok ty → wp (place e) E (PPost c f sF E e ty s) s
  | .var x, E, s, ty, L, hE, _, hty => by
    rw [place]
    exact placeVar_ok L hE x s ty hty
  | .field b fld, E, s, ty, L, hE, hw, hty =>
    field_ok F L b fld ty s hw hty (fun tb htb => place_ok F b E s tb L hE hw htb)
  | .index b i, E, s, ty, L, hE, hw, hty =>
    index_ok F L b i ty s hw hty (fun tb htb => place_ok F b E s tb L hE hw.1 htb)
      (fun ti s1 hti hsi => expr_ok F i E s1 ti L hE hw.2.1 hti hsi)
  | .lit _ _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
  | .blit _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
  | .bin _ _ _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
  | .un _ _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
  | .cast _ _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
  | .cond _ _ _, _, _, _, _, _, _, _ => by rw [place]; exact trivial
termination_by e => 3 * SizeOf.sizeOf e

/-- **An expression as an operand.** -/
theorem expr_ok (F : Final c fn f sF) : ∀ (e : Expr) (E : Env) (s : LS) (ty : Ty), LayOK E.prog c → EnvOK E →
    WT E e → E.tyOf e = .ok ty → ty.isScalar = true → wp (expr e) E (EPost c f sF E e ty s) s
  | .var x, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.var x) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none => exact varOpd_ok F L hE x s ty hty hs
  | .field b fld, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.field b fld) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind]
      exact wp_mono (place_ok F (.field b fld) E s ty L hE hw hty) (fun r s1 h => loadPlace_ok F _ ty hs s s1 r h)
  | .index b i, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.index b i) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind]
      exact wp_mono (place_ok F (.index b i) E s ty L hE hw hty) (fun r s1 h => loadPlace_ok F _ ty hs s s1 r h)
  | .cast w a, E, s, ty, L, hE, hw, hty, hs => by
    have hty' : ty = .int w := by
      simp only [Env.tyOf, Except.ok.injEq] at hty
      exact hty.symm
    subst hty'
    cases hc : closed? (.cast w a) with
    | some k => rw [expr]; simp only [hc, wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      refine castE_ok F L w a s hw hc (fun ta s1 hta hsa => expr_ok F a E s1 ta L hE hw.1 hta hsa) ?_
      intro x k tx s1 ha htx hsx
      subst ha
      exact expr_ok F x E s1 tx L hE hw.1.1 htx hsx
  | .lit v w, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.lit v w) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind, wp_tyOf, wp_size, wp_newTmp, wp_pure]
      intro t ht
      rw [hty] at ht
      cases ht
      exact wp_mono (exprTo_ok F (.lit v w) E _ ty (.tmp s.tmps.size) L hE hw hty hs (fun _ _ _ h => by cases h))
        (fun _ s' h => tmp_ok F L _ ty hw hty hs s s' h)
  | .blit b, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.blit b) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind, wp_tyOf, wp_size, wp_newTmp, wp_pure]
      intro t ht
      rw [hty] at ht
      cases ht
      exact wp_mono (exprTo_ok F (.blit b) E _ ty (.tmp s.tmps.size) L hE hw hty hs (fun _ _ _ h => by cases h))
        (fun _ s' h => tmp_ok F L _ ty hw hty hs s s' h)
  | .bin op a b, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.bin op a b) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind, wp_tyOf, wp_size, wp_newTmp, wp_pure]
      intro t ht
      rw [hty] at ht
      cases ht
      exact wp_mono (exprTo_ok F (.bin op a b) E _ ty (.tmp s.tmps.size) L hE hw hty hs (fun _ _ _ h => by cases h))
        (fun _ s' h => tmp_ok F L _ ty hw hty hs s s' h)
  | .un op a, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.un op a) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind, wp_tyOf, wp_size, wp_newTmp, wp_pure]
      intro t ht
      rw [hty] at ht
      cases ht
      exact wp_mono (exprTo_ok F (.un op a) E _ ty (.tmp s.tmps.size) L hE hw hty hs (fun _ _ _ h => by cases h))
        (fun _ s' h => tmp_ok F L _ ty hw hty hs s s' h)
  | .cond cnd a b, E, s, ty, L, hE, hw, hty, hs => by
    rw [expr]
    cases hc : closed? (.cond cnd a b) with
    | some k => simp only [wp_pure]; exact closedE_ok s hw hty hs hc
    | none =>
      simp only [wp_bind, wp_tyOf, wp_size, wp_newTmp, wp_pure]
      intro t ht
      rw [hty] at ht
      cases ht
      exact wp_mono (exprTo_ok F (.cond cnd a b) E _ ty (.tmp s.tmps.size) L hE hw hty hs
          (fun _ _ _ _ => ⟨_, rfl, by simp⟩))
        (fun _ s' h => tmp_ok F L _ ty hw hty hs s s' h)
termination_by e => 3 * SizeOf.sizeOf e + 2

/-- **An expression into a destination** (a conditional only into a
temporary of its own). -/
theorem exprTo_ok (F : Final c fn f sF) : ∀ (e : Expr) (E : Env) (s : LS) (ty : Ty) (dst : Dst), LayOK E.prog c →
    EnvOK E → WT E e → E.tyOf e = .ok ty → ty.isScalar = true →
    (∀ cnd a b, e = .cond cnd a b → ∃ d, dst = .tmp d ∧ d < s.tmps.size) →
    wp (exprTo dst e) E (TPost c f sF E e ty dst s) s
  | .lit v w, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    rw [exprTo]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    cases hc : closed? (.lit v w) with
    | some k => exact closedTo_ok F s dst hw hty hs hc
    | none => exact trivial
  | .blit b, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    rw [exprTo]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    cases hc : closed? (.blit b) with
    | some k => exact closedTo_ok F s dst hw hty hs hc
    | none => exact trivial
  | .var x, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    rw [exprTo]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    cases hc : closed? (.var x) with
    | some k => exact closedTo_ok F s dst hw hty hs hc
    | none =>
      simp only [wp_bind]
      refine wp_mono (varOpd_ok F L hE x s ty hty hs) ?_
      intro o s1 h1
      have hmp : wp (do movPlace (sizeOf E.prog ty) dst (← placeVar x)) E (TPost c f sF E (.var x) ty dst s) s1 := by
        simp only [wp_bind]
        refine wp_mono (placeVar_ok (f := f) (sF := sF) L hE x s1 ty hty) ?_
        intro r s2 hp
        exact wp_mono (movPlace_ok F (.var x) ty hs s1 s2 r dst hp) (fun _ s3 h3 => TPost.after_expr h1 h3)
      cases o with
      | const k => exact movOpd_ok F (.var x) ty s s1 (.const k) dst h1
      | slot sl => exact hmp
      | tmp t => exact hmp
  | .field b fld, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    rw [exprTo]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    cases hc : closed? (.field b fld) with
    | some k => exact closedTo_ok F s dst hw hty hs hc
    | none =>
      simp only [wp_bind]
      exact wp_mono (place_ok F (.field b fld) E s ty L hE hw hty) (fun r s1 h => movPlace_ok F _ ty hs s s1 r dst h)
  | .index b i, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    rw [exprTo]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    cases hc : closed? (.index b i) with
    | some k => exact closedTo_ok F s dst hw hty hs hc
    | none =>
      simp only [wp_bind]
      exact wp_mono (place_ok F (.index b i) E s ty L hE hw hty) (fun r s1 h => movPlace_ok F _ ty hs s s1 r dst h)
  | .bin op a b, E, s, ty, dst, L, hE, hw, hty, hs, _ =>
    bin_ok F L op a b ty dst s hw hty hs (fun ta s1 hta hsa => expr_ok F a E s1 ta L hE hw.1 hta hsa)
      (fun tb s1 htb hsb => expr_ok F b E s1 tb L hE hw.2.1 htb hsb)
  | .un op a, E, s, ty, dst, L, hE, hw, hty, hs, _ =>
    un_ok F L op a ty dst s hw hty hs
      (fun s1 => expr_ok F a E s1 ty L hE hw.1 (by simpa only [Env.tyOf] using hty) hs)
  | .cast w a, E, s, ty, dst, L, hE, hw, hty, hs, _ => by
    have hty' : ty = .int w := by
      simp only [Env.tyOf, Except.ok.injEq] at hty
      exact hty.symm
    subst hty'
    exact castTo_ok F L w a dst s hw (fun ta s1 hta hsa => expr_ok F a E s1 ta L hE hw.1 hta hsa)
  | .cond cnd a b, E, s, ty, dst, L, hE, hw, hty, hs, hpre => by
    obtain ⟨d, rfl, hd⟩ := hpre cnd a b rfl
    have hta : E.tyOf a = .ok ty := by simpa only [Env.tyOf] using hty
    have htb : E.tyOf b = .ok ty := by
      obtain ⟨_, _, _, _, t0, h1, h2, _⟩ := hw
      rw [h1] at hta
      cases hta
      exact h2
    exact cond_ok F L cnd a b ty d s hw hty hs hd
      (fun s1 => expr_ok F cnd E s1 .bool L hE hw.1 hw.2.2.2.1 rfl)
      (fun s1 => expr_ok F a E s1 ty L hE hw.2.1 hta hs)
      (fun s1 => expr_ok F b E s1 ty L hE hw.2.2.1 htb hs)
termination_by e => 3 * SizeOf.sizeOf e + 1

end

end

end Ember.Proof.IRSim

namespace Ember.Proof.IRSim

/-- info: 'Ember.Proof.IRSim.expr_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expr_ok

end Ember.Proof.IRSim
