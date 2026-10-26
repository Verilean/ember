import Ember.Proof.IRCall

/-!
# Ember.Proof.IRBlock — blocks, conditionals and loops (plan M7.1)

`LSim`: the code for a list of statements simulates `Lang.Sem.execL`;
`BSim`: so does the code for a block (`execB`: its variables end with
it).  Then `ite_ok`, `loop_ok`, `for_ok`, each from the simulation of
the blocks inside.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK IsPlace NoWriteL
  ReturnsL NoRef hasTy_zero keeps KeepsB)

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

/-! ## Lists of statements and blocks -/

/-- How the code for a list of statements ends: as `SOut`, but the
variables declared on the way (`pre`) are still in scope. -/
def LOut (c : Ctx) (f : IR.Fn) (rt : Option Ty) (E : Env) (cur : Nat) (env : Lang.Sem.Env) (ist : St)
    (tmps : Array Nat) (pc : Nat) (lst' : Lang.Sem.St) (env' : Lang.Sem.Env) (o : Lang.Sem.Out) (pc' : Nat) : Prop :=
  match o with
  | .normal => ∃ ist' tmps' pre cur', Reach c f pc tmps ist pc' tmps' ist' ∧ tmps'.size = tmps.size ∧
      SRel c { E with vars := pre ++ E.vars } cur' lst' env' ist' ∧ env'.length = pre.length + env.length ∧
      cur ≤ cur' ∧ Keep c E cur ist.mem ist'.mem
  | .brk => ∃ l i ist' tmps' pre cur', E.loopEnd = some l ∧ f.body[i]? = some (Instr.label l) ∧
      Reach c f pc tmps ist i tmps' ist' ∧ tmps'.size = tmps.size ∧
      SRel c { E with vars := pre ++ E.vars } cur' lst' env' ist' ∧ env'.length = pre.length + env.length ∧
      cur ≤ cur' ∧ Keep c E cur ist.mem ist'.mem
  | .ret v => ∃ ist', Ends c f pc tmps ist (.ok (v.map Val.toNat) ist') ∧ GS c E.prog lst' ist' ∧
      KeepOut c E.prog E.fn ist.mem ist'.mem ∧ RetOK E.prog rt v

def LSim (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (ss : List Stmt) (s s' : LS) : Prop :=
  ∀ n lst env ist tmps, n ≤ N → Ext s' sF → SRel c E s.cur lst env ist → tmps.size = f.tmps.size →
    (∀ l, E.loopEnd = some l → ∃ i : Nat, f.body[i]? = some (Instr.label l)) →
    match Lang.Sem.execL n E.prog lst env ss with
    | .fuel => True
    | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
    | .ok lst' env' o => LOut c f rt E s.cur env ist tmps s.out.size lst' env' o s'.out.size

/-- What `blockFrom` promises. -/
def BPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (ss : List Stmt) (s : LS) (_ : Unit)
    (s' : LS) : Prop :=
  Ext s s' ∧ s.cur ≤ s'.cur ∧ LSim c f sF N rt E ss s s'

/-- The code for a block simulates the block. -/
def BSim (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (ss : List Stmt) (s s' : LS) : Prop :=
  ∀ n lst env ist tmps, n ≤ N → Ext s' sF → SRel c E s.cur lst env ist → tmps.size = f.tmps.size →
    (∀ l, E.loopEnd = some l → ∃ i : Nat, f.body[i]? = some (Instr.label l)) →
    match Lang.Sem.execB n E.prog lst env ss with
    | .fuel => True
    | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
    | .ok lst' env' o => SOut c f rt E s.cur ist tmps s.out.size lst' env' o E s.cur s'.out.size

/-- What `inScope (blockFrom …)` promises. -/
def ScPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (ss : List Stmt) (s : LS) (_ : Unit)
    (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ BSim c f sF N rt E ss s s'

/-- **The end of a block**: the code is that of its statements; the variables go. -/
theorem scope_ok {E E0 : Env} {N : Nat} {rt : Option Ty} {ss : List Stmt} {s : LS}
    (h : wp (blockFrom E ss) E0 (BPost c f sF N rt E ss s) s) :
    wp (inScope (blockFrom E ss)) E0 (ScPost c f sF N rt E ss s) s := by
  rw [wp_inScope]
  refine wp_mono h ?_
  intro _ s' ⟨hx, hc, hsem⟩
  refine ⟨hx.scope, rfl, ?_⟩
  intro n lst env ist tmps hn hxF hrel hsz hend
  cases n with
  | zero => rw [Lang.Sem.execB]; trivial
  | succ k =>
    rw [Lang.Sem.execB]
    have hL := hsem k lst env ist tmps (by omega) hxF.unscope hrel hsz hend
    cases hE : Lang.Sem.execL k E.prog lst env ss with
    | fuel => trivial
    | trap lst' => simp only [hE] at hL ⊢; exact hL
    | ok lst' env' o =>
      simp only [hE] at hL ⊢
      cases o with
      | normal =>
        obtain ⟨ist', t', pre, cur', r, sz, hrel', hlen, hcur, hkeep⟩ := hL
        exact ⟨ist', t', r, sz, hrel'.pop (by omega) hrel.top_le hcur, hkeep⟩
      | brk =>
        obtain ⟨l, i, ist', t', pre, cur', hl, hi, r, sz, hrel', hlen, hcur, hkeep⟩ := hL
        exact ⟨l, i, ist', t', hl, hi, r, sz, hrel'.pop (by omega) hrel.top_le hcur, hkeep⟩
      | ret v => exact hL

/-! ## Putting code before and after -/

/-- Code before, which keeps what the statement's relation looks at. -/
theorem SOut.pre {rt : Option Ty} {E : Env} {cur : Nat} {ist0 ist : St} {t0 tmps : Array Nat} {pc0 pc : Nat}
    {lst' : Lang.Sem.St} {env' : Lang.Sem.Env} {o : Lang.Sem.Out} {E' : Env} {cur' pc' : Nat}
    (r : Reach c f pc0 t0 ist0 pc tmps ist) (hsz : tmps.size = t0.size) (hk : Keep c E cur ist0.mem ist.mem)
    (h : SOut c f rt E cur ist tmps pc lst' env' o E' cur' pc') :
    SOut c f rt E cur ist0 t0 pc0 lst' env' o E' cur' pc' := by
  cases o with
  | normal =>
    obtain ⟨ist', t', r', sz, hrel', hkeep⟩ := h
    exact ⟨ist', t', r.trans r', by rw [sz, hsz], hrel', hk.trans hkeep⟩
  | brk =>
    obtain ⟨l, i, ist', t', hl, hi, r', sz, hrel', hkeep⟩ := h
    exact ⟨l, i, ist', t', hl, hi, r.trans r', by rw [sz, hsz], hrel', hk.trans hkeep⟩
  | ret v =>
    obtain ⟨ist', he, hgs, hko, hret⟩ := h
    exact ⟨ist', r.ends he, hgs, hk.out.trans hko, hret⟩

/-- Code after, which changes nothing. -/
theorem SOut.post {rt : Option Ty} {E : Env} {cur : Nat} {ist : St} {tmps : Array Nat} {pc : Nat}
    {lst' : Lang.Sem.St} {env' : Lang.Sem.Env} {o : Lang.Sem.Out} {E' : Env} {cur' pc' pc'' : Nat}
    (h : SOut c f rt E cur ist tmps pc lst' env' o E' cur' pc')
    (hr : ∀ (ist' : St) (t' : Array Nat), Reach c f pc' t' ist' pc'' t' ist') :
    SOut c f rt E cur ist tmps pc lst' env' o E' cur' pc'' := by
  cases o with
  | normal =>
    obtain ⟨ist', t', r', sz, hrel', hkeep⟩ := h
    exact ⟨ist', t', r'.trans (hr ist' t'), sz, hrel', hkeep⟩
  | brk => exact h
  | ret v => exact h

/-- Memory changed where neither the globals nor the variables are. -/
theorem SRel.frame' {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}
    (L : LayOK E.prog c) (h : SRel c E cur lst env ist) {m' : ByteArray} (hsz : m'.size = 65536)
    (hm : ∀ A, InGlobals E.prog c A ∨ (fbase c E.fn ≤ A ∧ A < fbase c E.fn + topOf E.prog E.vars) →
      m'.get! A = ist.mem.get! A) : SRel c E cur lst env { ist with mem := m' } := by
  obtain ⟨hl, htop⟩ := h.loc
  obtain ⟨f', hf, hfit⟩ := h.fit
  have hb := L.fbound _ _ hf
  exact ⟨hsz, h.world, h.glob.frame L (fun A hA => hm A (.inl hA)),
    ⟨hl.frame (by omega) (fun o ho => hm _ (.inr ⟨Nat.le_add_right _ _, by have := inVars_lt_top ho; omega⟩)), htop⟩,
    ⟨f', hf, hfit⟩⟩

/-- Less of the frame in use (what is given back holds no variable). -/
theorem SRel.shrink {E : Env} {cur cur' : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}
    (h : SRel c E cur lst env ist) (htop : topOf E.prog E.vars ≤ cur') (hc : cur' ≤ cur) :
    SRel c E cur' lst env ist := by
  obtain ⟨f', hf, hfit⟩ := h.fit
  exact ⟨h.size, h.world, h.glob, ⟨h.loc.1, htop⟩, ⟨f', hf, by omega⟩⟩

/-! ## `if` -/

theorem push2 {α : Type} (xs : Array α) (a b : α) :
    ((xs.push a).push b)[xs.size]? = some a ∧ ((xs.push a).push b)[xs.size + 1]? = some b := by
  refine ⟨?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push, if_pos rfl]
  · rw [Array.getElem?_push, if_pos (by simp only [Array.size_push])]

/-- An empty block does nothing. -/
theorem execB_nil (p : Prog) (k : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) :
    Lang.Sem.execB k p lst env [] = .fuel ∨ Lang.Sem.execB k p lst env [] = .ok lst env .normal := by
  cases k with
  | zero => exact .inl (by rw [Lang.Sem.execB])
  | succ j =>
    cases j with
    | zero => exact .inl (by rw [Lang.Sem.execB, Lang.Sem.execL])
    | succ i => exact .inr (by simp [Lang.Sem.execB, Lang.Sem.execL])

theorem ite_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (N : Nat) (rt : Option Ty)
    (cnd : Expr) (t e : List Stmt) (s : LS) (hwc : WT E cnd) (htc : E.tyOf cnd = .ok .bool)
    (iht : ∀ s1, wp (blockFrom E t) E (BPost c f sF N rt E t s1) s1)
    (ihe : ∀ s1, wp (blockFrom E e) E (BPost c f sF N rt E e s1) s1) :
    wp (stmt (.ite cnd t e)) E (SPost c f sF N rt E (.ite cnd t e) s) s := by
  rw [IR.stmt]
  simp only [wp_bind, wp_read, wp_newLabel]
  refine wp_mono (condJump_ok F cnd E _ false s.labels L hE hwc htc) ?_
  intro _ s1 ⟨hx1, hc1, hs1⟩
  have hc1' : s1.cur = s.cur := hc1
  refine wp_mono (scope_ok (iht s1)) ?_
  intro _ s2 ⟨hx2, hc2, hs2⟩
  have hx02 : Ext s s2 := ((Ext.newLabel s).trans hx1).trans hx2
  -- the condition, then the block chosen
  have hcond : ∀ (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat), Ext s1 sF →
      SRel c E s.cur lst env ist → tmps.size = f.tmps.size →
      match Lang.Sem.evalE E.prog lst env cnd with
      | none => Ends c f s.out.size tmps ist (.trap ist)
      | some cv => ∃ b, cv = .bool b ∧
          if b = true then ∃ t1, Reach c f s.out.size tmps ist s1.out.size t1 ist ∧ t1.size = tmps.size
          else ∀ i : Nat, f.body[i]? = some (Instr.label s.labels) →
            ∃ t1, Reach c f s.out.size tmps ist i t1 ist ∧ t1.size = tmps.size := by
    intro lst env ist tmps hxF hrel hsz
    have hJ := hs1 s.cur lst env ist tmps hxF hrel hsz
    cases hev : Lang.Sem.evalE E.prog lst env cnd with
    | none => simp only [hev] at hJ ⊢; exact hJ
    | some cv =>
      simp only [hev] at hJ ⊢
      obtain ⟨b, rfl⟩ := hasTy_bool (evalE_hasTy E lst env (hrel.typed L) cnd cv .bool hwc hev htc)
      refine ⟨b, rfl, ?_⟩
      cases b with
      | true => simpa [Jumps, Val.toBool] using hJ
      | false => simpa [Jumps, Val.toBool] using hJ
  by_cases hem : e.isEmpty = true
  · rw [if_pos hem]
    simp only [wp_bind, wp_emit, wp_pure]
    have he : e = [] := List.isEmpty_iff.mp hem
    subst he
    refine ⟨hx02.trans (Ext.emit _ _), rfl, by simp only [hc2, hc1']; exact Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
      have hlab : f.body[s2.out.size]? = some (Instr.label s.labels) := F.emitted hxF rfl
      have hC := hcond lst env ist tmps (hx2.trans hxF2) hrel hsz
      have hlabR : ∀ (ist' : St) (t' : Array Nat), Reach c f s2.out.size t' ist' (s2.out.size + 1) t' ist' :=
        fun ist' t' => Reach.next hlab (step_label c ist' t' _)
      simp only [Array.size_push, hc2, hc1']
      cases hev : Lang.Sem.evalE E.prog lst env cnd with
      | none => simp only [hev] at hC ⊢; exact ⟨ist, hC, hrel.world⟩
      | some cv =>
        simp only [hev] at hC ⊢
        obtain ⟨b, rfl, hb⟩ := hC
        cases b with
        | true =>
          simp only [if_true] at hb
          simp only [Val.toBool, if_true]
          obtain ⟨t1, r1, sz1⟩ := hb
          have hB := hs2 k lst env ist t1 (by omega) hxF2 (by rw [hc1']; exact hrel) (by rw [sz1]; exact hsz) hend
          cases hR : Lang.Sem.execB k E.prog lst env t with
          | fuel => trivial
          | trap lst' =>
            simp only [hR] at hB ⊢
            obtain ⟨ist', he', hw⟩ := hB
            exact ⟨ist', r1.ends he', hw⟩
          | ok lst' env' o =>
            simp only [hR, hc1'] at hB ⊢
            exact (hB.post hlabR).pre r1 sz1 (Keep.refl _)
        | false =>
          simp only [Bool.false_eq_true, if_false] at hb
          simp only [Val.toBool, Bool.false_eq_true, if_false]
          obtain ⟨t1, r1, sz1⟩ := hb _ hlab
          rcases execB_nil E.prog k lst env with h0 | h0
          · rw [h0]; trivial
          · rw [h0]
            exact ⟨ist, t1, r1.trans (hlabR ist t1), sz1, hrel, Keep.refl _⟩
  · rw [if_neg hem]
    simp only [wp_bind, wp_newLabel, wp_emit]
    refine wp_mono (scope_ok (ihe _)) ?_
    intro _ s5 ⟨hx5, hc5, hs5⟩
    simp only [wp_emit, wp_pure]
    have hc5' : s5.cur = s.cur := by rw [hc5]; simp only [hc2, hc1']
    have hx23 := (Ext.newLabel s2).trans ((Ext.emit _ (Instr.jmp s2.labels)).trans (Ext.emit _ (Instr.label s.labels)))
    refine ⟨hx02.trans (hx23.trans (hx5.trans (Ext.emit _ _))), rfl, by simp only [hc5']; exact Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      have hxF5 : Ext s5 sF := (Ext.emit _ _).trans hxF
      have hxF3 := hx5.trans hxF5
      have hxF2 : Ext s2 sF := hx23.trans hxF3
      obtain ⟨g1, g2⟩ := push2 s2.out (Instr.jmp s2.labels) (Instr.label s.labels)
      have hjmp := F.at_ hxF3 g1
      have hlelse := F.at_ hxF3 g2
      have hlend : f.body[s5.out.size]? = some (Instr.label s2.labels) := F.emitted hxF rfl
      have hC := hcond lst env ist tmps (hx2.trans hxF2) hrel hsz
      have hendR : ∀ (ist' : St) (t' : Array Nat), Reach c f s5.out.size t' ist' (s5.out.size + 1) t' ist' :=
        fun ist' t' => Reach.next hlend (step_label c ist' t' _)
      simp only [Array.size_push, hc5']
      cases hev : Lang.Sem.evalE E.prog lst env cnd with
      | none => simp only [hev] at hC ⊢; exact ⟨ist, hC, hrel.world⟩
      | some cv =>
        simp only [hev] at hC ⊢
        obtain ⟨b, rfl, hb⟩ := hC
        cases b with
        | true =>
          simp only [if_true] at hb
          simp only [Val.toBool, if_true]
          obtain ⟨t1, r1, sz1⟩ := hb
          have hB := hs2 k lst env ist t1 (by omega) hxF2 (by rw [hc1']; exact hrel) (by rw [sz1]; exact hsz) hend
          cases hR : Lang.Sem.execB k E.prog lst env t with
          | fuel => trivial
          | trap lst' =>
            simp only [hR] at hB ⊢
            obtain ⟨ist', he', hw⟩ := hB
            exact ⟨ist', r1.ends he', hw⟩
          | ok lst' env' o =>
            simp only [hR, hc1'] at hB ⊢
            exact (hB.post (fun ist' t' => (Reach.goto hjmp (step_jmp c ist' t' _) (F.label hlend)).trans
              (hendR ist' t'))).pre r1 sz1 (Keep.refl _)
        | false =>
          simp only [Bool.false_eq_true, if_false] at hb
          simp only [Val.toBool, Bool.false_eq_true, if_false]
          obtain ⟨t1, r1, sz1⟩ := hb _ hlelse
          have r2 : Reach c f s.out.size tmps ist (s2.out.size + 1 + 1) t1 ist :=
            r1.trans (Reach.next hlelse (step_label c ist t1 _))
          have hB := hs5 k lst env ist t1 (by omega) hxF5 (by simp only [hc2, hc1']; exact hrel)
            (by rw [sz1]; exact hsz) hend
          simp only [Array.size_push, hc2, hc1'] at hB
          cases hR : Lang.Sem.execB k E.prog lst env e with
          | fuel => trivial
          | trap lst' =>
            simp only [hR] at hB ⊢
            obtain ⟨ist', he', hw⟩ := hB
            exact ⟨ist', r2.ends he', hw⟩
          | ok lst' env' o =>
            simp only [hR] at hB ⊢
            exact (hB.post hendR).pre r2 sz1 (Keep.refl _)

/-! ## `loop` -/

theorem push3 {α : Type} (xs : Array α) (a b d : α) :
    (((xs.push a).push b).push d)[xs.size]? = some a ∧ (((xs.push a).push b).push d)[xs.size + 1]? = some b ∧
    (((xs.push a).push b).push d)[xs.size + 2]? = some d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push, if_pos rfl]
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_pos (by simp only [Array.size_push])]
  · rw [Array.getElem?_push, if_pos (by simp only [Array.size_push])]

theorem counter_fits {max : Nat} (h : max < 2 ^ 32) : max < 2 ^ (8 * counterSize max) := by
  unfold counterSize
  split
  · omega
  · split
    · omega
    · exact h

theorem counter_pos (max : Nat) : 0 < counterSize max := by
  unfold counterSize
  split
  · decide
  · split <;> decide

/-- A scratch slot of the frame (below what is in use, above the variables) is kept. -/
theorem Keep.scratch {E : Env} {cur : Nat} {m m' : ByteArray} (h : Keep c E cur m m') (off n : Nat)
    (htop : topOf E.prog E.vars ≤ off) (hcur : off + n ≤ cur) (hb : fbase c E.fn + off + n ≤ 65536) :
    rd m' (fbase c E.fn + off) n = rd m (fbase c E.fn + off) n := by
  refine rd_congr m m' _ _ hb (fun A a1 a2 => h A (.inr ⟨by omega, by omega, fun hin => ?_⟩))
  have := inVars_lt_top hin
  omega

/-- **The loop**, from its head: the counter holds what is left. -/
theorem loop_sim (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (N : Nat) (rt : Option Ty)
    (body : List Stmt) (n kOff ptop pe top done : Nat) (hn : 0 < n) (hle : E.loopEnd = some done)
    (htop : f.body[ptop]? = some (Instr.label top))
    (hsub : f.body[pe]? = some (Instr.bin .sub n (.slot { area := .frame E.fn, off := kOff })
      (.slot { area := .frame E.fn, off := kOff }) (.const 1)))
    (hbr : f.body[pe + 1]? = some (Instr.br .ne n (.slot { area := .frame E.fn, off := kOff }) (.const 0) top))
    (hdone : f.body[pe + 2]? = some (Instr.label done))
    (hvars : topOf E.prog E.vars ≤ kOff)
    (hfit : ∃ f', c.prog.fn? E.fn = some f' ∧ kOff + n ≤ f'.frame)
    (hbody : ∀ j lst env ist tmps, j ≤ N → SRel c E (kOff + n) lst env ist →
      tmps.size = f.tmps.size →
      match Lang.Sem.execB j E.prog lst env body with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f (ptop + 1) tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok lst' env' o => SOut c f rt E (kOff + n) ist tmps (ptop + 1) lst' env' o
          E (kOff + n) pe) :
    ∀ j, j ≤ N + 1 → ∀ (K : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat),
      0 < K → K < 2 ^ (8 * n) → SRel c E (kOff + n) lst env ist →
      rd ist.mem (fbase c E.fn + kOff) n = K → tmps.size = f.tmps.size →
      match Lang.Sem.loopN j E.prog lst env K body with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f ptop tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok lst' env' o => o ≠ .brk ∧
          SOut c f rt E kOff ist tmps ptop lst' env' o
            E (kOff + n) (pe + 3) := by
  obtain ⟨f', hf', hfr⟩ := hfit
  have hfb := L.fbound _ _ hf'
  intro j
  induction j with
  | zero => intro _ K lst env ist tmps _ _ _ _ _; rw [Lang.Sem.loopN]; trivial
  | succ j ih =>
    intro hj K lst env ist tmps hK0 hKlt hrel hK hsz
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [Lang.Sem.loopN]
    have rtop : Reach c f ptop tmps ist (ptop + 1) tmps ist := Reach.next htop (step_label c ist tmps top)
    have hB := hbody j lst env ist tmps (by omega) hrel hsz
    have hdoneR : ∀ (ist' : St) (t' : Array Nat), Reach c f (pe + 2) t' ist' (pe + 3) t' ist' :=
      fun ist' t' => Reach.next hdone (step_label c ist' t' done)
    cases hR : Lang.Sem.execB j E.prog lst env body with
    | fuel => trivial
    | trap lst' =>
      simp only [hR] at hB ⊢
      obtain ⟨ist', he, hw⟩ := hB
      exact ⟨ist', rtop.ends he, hw⟩
    | ok lst' env' o =>
      simp only [hR] at hB ⊢
      cases o with
      | ret v =>
        obtain ⟨ist', he, hgs, hko, hret⟩ := hB
        exact ⟨by simp, ist', rtop.ends he, hgs, hko, hret⟩
      | brk =>
        obtain ⟨l, i, ist1, t1, hl, hi, r1, sz1, hrel1, hkeep1⟩ := hB
        rw [hle] at hl
        cases hl
        have hi' := F.uniq i (pe + 2) _ hi hdone
        subst hi'
        refine ⟨by simp, ist1, t1, rtop.trans (r1.trans (hdoneR ist1 t1)), sz1, hrel1, ?_⟩
        exact hkeep1.weaken rfl rfl (Nat.le_add_right _ _) (fun _ _ h => h)
      | normal =>
        dsimp only
        obtain ⟨ist1, t1, r1, sz1, hrel1, hkeep1⟩ := hB
        have hms := hrel1.size
        -- the counter is still there
        have hK1 : rd ist1.mem (fbase c E.fn + kOff) n = K' + 1 := by
          rw [← hK]
          exact hkeep1.scratch kOff n hvars (Nat.le_refl _) (by omega)
        -- count down
        have hwr : ∀ A, A < fbase c E.fn + kOff ∨ fbase c E.fn + kOff + n ≤ A →
            (wr ist1.mem (fbase c E.fn + kOff) n K').get! A = ist1.mem.get! A :=
          fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
        have hstep : step c ist1 t1 (Instr.bin .sub n (.slot { area := .frame E.fn, off := kOff })
            (.slot { area := .frame E.fn, off := kOff }) (.const 1)) =
            .next { ist1 with mem := wr ist1.mem (fbase c E.fn + kOff) n K' } t1 := by
          rw [step_bin, setDst_slot, opd_slot, addr_frame, hK1, opd_const,
            modN_of_lt (Nat.one_lt_two_pow (by omega))]
          simp only [binOp, modN, Step.set]
          rw [show K' + 1 + 2 ^ (8 * n) - 1 = K' + 2 ^ (8 * n) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        have hrel2 : SRel c E (kOff + n) lst' env'
            { ist1 with mem := wr ist1.mem (fbase c E.fn + kOff) n K' } := by
          refine hrel1.frame' L (by rw [wr_size]; exact hms) (fun A hA => hwr A ?_)
          rcases hA with hg | ⟨a1, a2⟩
          · by_cases hin : fbase c E.fn + kOff ≤ A ∧ A < fbase c E.fn + kOff + n
            · exact absurd hg (L.fglob _ A ⟨f', hf', by omega, by omega⟩)
            · omega
          · exact .inl (by have : topOf E.prog E.vars ≤ kOff := hvars; omega)
        have hK2 : rd (wr ist1.mem (fbase c E.fn + kOff) n K') (fbase c E.fn + kOff) n = K' := by
          rw [rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]
        have hkeep2 : Keep c E kOff ist.mem
            (wr ist1.mem (fbase c E.fn + kOff) n K') :=
          (hkeep1.weaken rfl rfl (Nat.le_add_right _ _) (fun _ _ h => h)).trans
            (Keep.above hf' hfr (fun A hA => hwr A (by omega)))
        have r2 : Reach c f ptop tmps ist (pe + 1) t1 { ist1 with mem := wr ist1.mem (fbase c E.fn + kOff) n K' } :=
          rtop.trans (r1.trans (Reach.next hsub hstep))
        have hbrs : step c { ist1 with mem := wr ist1.mem (fbase c E.fn + kOff) n K' } t1
            (Instr.br .ne n (.slot { area := .frame E.fn, off := kOff }) (.const 0) top) =
            if K' ≠ 0 then .goto top else .next { ist1 with mem := wr ist1.mem (fbase c E.fn + kOff) n K' } t1 := by
          rw [step_br, opd_slot, addr_frame, hK2, opd_const]
          simp only [cmpOp, modN, Nat.zero_mod]
          by_cases h0 : K' = 0 <;> simp [h0]
        by_cases h0 : K' = 0
        · subst h0
          rw [if_neg (by simp)] at hbrs
          have r3 := r2.trans ((Reach.next hbr hbrs).trans (hdoneR _ t1))
          cases j with
          | zero => simp only [Lang.Sem.loopN]
          | succ j' =>
            simp only [Lang.Sem.loopN]
            exact ⟨by simp, _, t1, r3, sz1, hrel2, hkeep2⟩
        · rw [if_pos h0] at hbrs
          have r3 := r2.trans (Reach.goto hbr hbrs (F.label htop))
          have hI := ih (by omega) K' lst' env' _ t1 (by omega) (by omega) hrel2 hK2 (by rw [sz1]; exact hsz)
          cases hL : Lang.Sem.loopN j E.prog lst' env' K' body with
          | fuel => trivial
          | trap lst'' =>
            simp only [hL] at hI ⊢
            obtain ⟨ist', he, hw⟩ := hI
            exact ⟨ist', r3.ends he, hw⟩
          | ok lst'' env'' o' =>
            simp only [hL] at hI ⊢
            exact ⟨hI.1, hI.2.pre r3 sz1 hkeep2⟩

theorem loop_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hfn : E.fn = fn) (N : Nat) (rt : Option Ty)
    (max : Nat) (body : List Stmt) (s : LS) (hmax : max < 2 ^ 32)
    (ihb : ∀ l s1, wp (blockFrom { E with loopEnd := l } body) E
      (BPost c f sF N rt { E with loopEnd := l } body s1) s1) :
    wp (IR.stmt (.loop max body)) E (SPost c f sF N rt E (.loop max body) s) s := by
  rw [IR.stmt]
  simp only [wp_bind, wp_read]
  by_cases h0 : (max == 0) = true
  · rw [if_pos h0, wp_pure]
    have hm0 : max = 0 := by simpa using h0
    subst hm0
    refine ⟨Ext.refl s, rfl, Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      cases k with
      | zero => simp only [Lang.Sem.loopN]
      | succ j =>
        simp only [Lang.Sem.loopN]
        exact ⟨ist, tmps, Reach.refl, rfl, hrel, Keep.refl _⟩
  · rw [if_neg h0]
    have hmpos : 0 < max := by
      rcases Nat.eq_zero_or_pos max with h | h
      · subst h; simp at h0
      · exact h
    rw [wp_bind, wp_inScope]
    simp only [wp_bind, wp_allocLocal, wp_emit, wp_newLabel]
    refine wp_mono (scope_ok (ihb (some (s.labels + 1)) _)) ?_
    intro _ sd ⟨hxd, hcd, hsd⟩
    simp only [wp_emit, wp_pure]
    have hxc := (Ext.alloc s (counterSize max)).trans
      ((Ext.emit _ (Instr.mov (counterSize max) (.slot { area := .frame E.fn, off := s.cur }) (.const max))).trans
      ((Ext.newLabel _).trans ((Ext.newLabel _).trans (Ext.emit _ (Instr.label s.labels)))))
    have hxe := (Ext.emit sd (Instr.bin .sub (counterSize max) (.slot { area := .frame E.fn, off := s.cur })
        (.slot { area := .frame E.fn, off := s.cur }) (.const 1))).trans
      ((Ext.emit _ (Instr.br .ne (counterSize max) (.slot { area := .frame E.fn, off := s.cur }) (.const 0) s.labels)).trans
        (Ext.emit _ (Instr.label (s.labels + 1))))
    refine ⟨(hxc.trans (hxd.trans hxe)).scope, rfl, Nat.le_refl _, ?_⟩
    intro n' lst env ist tmps hn hxF hrel hsz hend
    cases n' with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ j =>
      simp only [Lang.Sem.execS]
      have hxFd := hxe.trans (Ext.of_out hxF rfl rfl rfl rfl)
      have hxFc := hxd.trans hxFd
      obtain ⟨g1, g2⟩ := push2 s.out
        (Instr.mov (counterSize max) (.slot { area := .frame E.fn, off := s.cur }) (.const max)) (Instr.label s.labels)
      have hmov := F.at_ hxFc g1
      have htop := F.at_ hxFc g2
      obtain ⟨g3, g4, g5⟩ := push3 sd.out (Instr.bin .sub (counterSize max) (.slot { area := .frame E.fn, off := s.cur })
        (.slot { area := .frame E.fn, off := s.cur }) (.const 1))
        (Instr.br .ne (counterSize max) (.slot { area := .frame E.fn, off := s.cur }) (.const 0) s.labels)
        (Instr.label (s.labels + 1))
      have hsub := F.at_ hxF g3
      have hbr := F.at_ hxF g4
      have hdone := F.at_ hxF g5
      obtain ⟨f', hf', hfr⟩ := F.fit hfn hxFc (k := s.cur + counterSize max) (Nat.le_max_right _ _)
      have hfb := L.fbound _ _ hf'
      have hms := hrel.size
      have htopv := hrel.top_le
      have hwr : ∀ A, A < fbase c E.fn + s.cur ∨ fbase c E.fn + s.cur + counterSize max ≤ A →
          (wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max).get! A = ist.mem.get! A :=
        fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
      have hstep1 : step c ist tmps
          (Instr.mov (counterSize max) (.slot { area := .frame E.fn, off := s.cur }) (.const max)) =
          .next { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max } tmps := by
        rw [step_mov, setDst_slot, addr_frame, opd_const, modN_of_lt (counter_fits hmax)]
        rfl
      have hrel1 : SRel c { E with loopEnd := some (s.labels + 1) } (s.cur + counterSize max) lst env
          { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max } := by
        refine SRel.congr ((hrel.frame' L (by rw [wr_size]; exact hms) (fun A hA => hwr A ?_)).grow
          (Nat.le_add_right _ _) ⟨f', hf', hfr⟩) rfl rfl rfl
        rcases hA with hg | ⟨a1, a2⟩
        · by_cases hin : fbase c E.fn + s.cur ≤ A ∧ A < fbase c E.fn + s.cur + counterSize max
          · exact absurd hg (L.fglob _ A ⟨f', hf', by omega, by omega⟩)
          · omega
        · exact .inl (by omega)
      have hK : rd (wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max) (fbase c E.fn + s.cur)
          (counterSize max) = max := by
        rw [rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (counter_fits hmax)]
      have hbody : ∀ j lst env ist tmps, j ≤ N →
          SRel c { E with loopEnd := some (s.labels + 1) } (s.cur + counterSize max) lst env ist →
          tmps.size = f.tmps.size →
          match Lang.Sem.execB j E.prog lst env body with
          | .fuel => True
          | .trap lst' => ∃ ist', Ends c f (s.out.size + 1 + 1) tmps ist (.trap ist') ∧ ist'.world = lst'.world
          | .ok lst' env' o => SOut c f rt { E with loopEnd := some (s.labels + 1) } (s.cur + counterSize max) ist tmps
              (s.out.size + 1 + 1) lst' env' o { E with loopEnd := some (s.labels + 1) } (s.cur + counterSize max)
              sd.out.size := by
        intro j lst env ist tmps hj hrel' hsz'
        have := hsd j lst env ist tmps hj hxFd hrel' hsz' (fun l hl => by
          simp only [Option.some.injEq] at hl
          subst hl
          exact ⟨_, hdone⟩)
        simpa only [Array.size_push] using this
      have hL := loop_sim F (E := { E with loopEnd := some (s.labels + 1) }) L N rt body (counterSize max) s.cur
        (s.out.size + 1) sd.out.size s.labels (s.labels + 1) (counter_pos max) rfl htop hsub hbr hdone htopv
        ⟨f', hf', hfr⟩ hbody j (by omega) max lst env _ tmps hmpos (counter_fits hmax) hrel1 hK hsz
      have r0 : Reach c f s.out.size tmps ist (s.out.size + 1) tmps
          { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max } := Reach.next hmov hstep1
      have hk0 : Keep c E s.cur ist.mem (wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max) :=
        Keep.above hf' hfr (fun A hA => hwr A (by omega))
      simp only [Array.size_push]
      cases hR : Lang.Sem.loopN j E.prog lst env max body with
      | fuel => trivial
      | trap lst' =>
        simp only [hR] at hL ⊢
        obtain ⟨ist', he, hw⟩ := hL
        exact ⟨ist', r0.ends he, hw⟩
      | ok lst' env' o =>
        simp only [hR] at hL ⊢
        obtain ⟨hnb, hS⟩ := hL
        have hk0' : Keep c { E with loopEnd := some (s.labels + 1) } s.cur ist.mem
            (wr ist.mem (fbase c E.fn + s.cur) (counterSize max) max) := hk0
        have hS' := hS.pre r0 rfl hk0'
        cases o with
        | normal =>
          obtain ⟨ist', t', r, sz, hrel', hkeep⟩ := hS'
          exact ⟨ist', t', r, sz, (SRel.congr (E' := E) hrel' rfl rfl rfl).shrink htopv (Nat.le_add_right _ _), hkeep⟩
        | brk => exact absurd rfl hnb
        | ret v => exact hS'

/-! ## `for` -/

/-- An environment with the same names as one that starts with `x`, and the same `x`. -/
theorem keepsB_head {x : String} {v : Val} {envT env' : Lang.Sem.Env} (h : KeepsB x ((x, v) :: envT) env') :
    ∃ envT', env' = (x, v) :: envT' := by
  obtain ⟨hn, hl⟩ := h
  cases env' with
  | nil => simp at hn
  | cons a r =>
    obtain ⟨y, u⟩ := a
    simp only [List.map_cons, List.cons.injEq] at hn
    obtain ⟨rfl, _⟩ := hn
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
    subst hl
    exact ⟨r, rfl⟩

theorem ofNat_toNat_lt {k : Nat} {w : Width} (h : k < 2 ^ w.bits) : (UInt64.ofNat k).toNat = k := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Ember.Proof.CSim.bits_le w)))

/-- **The `for` loop**, from its head: the counter's slot holds the counter. -/
theorem for_sim (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hnr : NoRef E.prog) (N : Nat)
    (rt : Option Ty) (x : String) (w : Width) (body : List Stmt) (iOff curb : Nat) (limit : Opd) (hi : Nat)
    (ptop pe top done : Nat) (vars0 : List (String × VarInfo)) (hle : E.loopEnd = some done)
    (hvars : E.vars = (x, { ty := .int w, at_ := .static { area := .frame E.fn, off := iOff } }) :: vars0)
    (htop : f.body[ptop]? = some (Instr.label top))
    (hbrI : f.body[ptop + 1]? = some (Instr.br .ge (w.bits / 8) (.slot { area := .frame E.fn, off := iOff }) limit done))
    (hadd : f.body[pe]? = some (Instr.bin .add (w.bits / 8) (.slot { area := .frame E.fn, off := iOff })
      (.slot { area := .frame E.fn, off := iOff }) (.const 1)))
    (hjmp : f.body[pe + 1]? = some (Instr.jmp top))
    (hdone : f.body[pe + 2]? = some (Instr.label done))
    (hnw : NoWriteL x body) (hhi : hi < 2 ^ w.bits) (hcb : iOff + w.bits / 8 ≤ curb)
    (hfit : ∃ f', c.prog.fn? E.fn = some f' ∧ curb ≤ f'.frame)
    (Lim : ByteArray → Prop)
    (hlim1 : ∀ (ist : St) (tmps : Array Nat), Lim ist.mem → opd c ist tmps (w.bits / 8) limit = hi)
    (hlim2 : ∀ m m', Keep c E curb m m' → Lim m → Lim m')
    (hlim3 : ∀ (m : ByteArray) (v : Nat), m.size = 65536 → Lim m →
      Lim (wr m (fbase c E.fn + iOff) (w.bits / 8) v))
    (hbody : ∀ j lst env ist tmps, j ≤ N → SRel c E curb lst env ist → tmps.size = f.tmps.size →
      match Lang.Sem.execB j E.prog lst env body with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f (ptop + 2) tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok lst' env' o => SOut c f rt E curb ist tmps (ptop + 2) lst' env' o E curb pe) :
    ∀ j, j ≤ N + 1 → ∀ (cur : Nat) (lst : Lang.Sem.St) (v0 : Val) (envT : Lang.Sem.Env) (ist : St)
      (tmps : Array Nat), cur < 2 ^ w.bits →
      SRel c E curb lst ((x, .int w (UInt64.ofNat cur)) :: envT) ist → Lim ist.mem → tmps.size = f.tmps.size →
      match Lang.Sem.forLoop j E.prog lst ((x, v0) :: envT) x w cur hi body with
      | .fuel => True
      | .trap lst' => ∃ ist', Ends c f ptop tmps ist (.trap ist') ∧ ist'.world = lst'.world
      | .ok lst' env' o => o ≠ .brk ∧ ∃ v1 v2 envT', env' = (x, v1) :: envT' ∧
          SOut c f rt E iOff ist tmps ptop lst' ((x, v2) :: envT') o E curb (pe + 3) := by
  obtain ⟨f', hf', hfr⟩ := hfit
  have hfb := L.fbound _ _ hf'
  have h8 := bits8 w
  -- the counter, as a variable
  have hinfo : E.varInfo x = .ok { ty := .int w, at_ := .static { area := .frame E.fn, off := iOff } } := by
    simp [Env.varInfo, hvars, List.lookup]
  have hcount : ∀ (lst : Lang.Sem.St) (envT : Lang.Sem.Env) (ist : St) (k : Nat), k < 2 ^ w.bits →
      SRel c E curb lst ((x, .int w (UInt64.ofNat k)) :: envT) ist →
      rd ist.mem (fbase c E.fn + iOff) (w.bits / 8) = k := by
    intro lst envT ist k hk hrel
    obtain ⟨sl, v, hat, hlk, _, _, hh, _⟩ := hrel.var L hinfo
    simp only [Storage.static.injEq] at hat
    subst hat
    simp only [Lang.Sem.lookup, List.lookup, beq_self_eq_true, Option.some.injEq] at hlk
    subst hlk
    rw [addr_frame] at hh
    have := (holds_scalar (t := .int w) rfl).mp hh
    rw [size_int] at this
    rw [this]
    exact ofNat_toNat_lt hk
  have hdoneR : ∀ (ist' : St) (t' : Array Nat), Reach c f (pe + 2) t' ist' (pe + 3) t' ist' :=
    fun ist' t' => Reach.next hdone (step_label c ist' t' done)
  intro j
  induction j with
  | zero => intro _ cur lst v0 envT ist tmps _ _ _ _; rw [Lang.Sem.forLoop]; trivial
  | succ j ih =>
    intro hj cur lst v0 envT ist tmps hcur hrel hlim hsz
    rw [Lang.Sem.forLoop]
    have rtop : Reach c f ptop tmps ist (ptop + 1) tmps ist := Reach.next htop (step_label c ist tmps top)
    have hi0 := hcount lst envT ist cur hcur hrel
    have hbrs : step c ist tmps (Instr.br .ge (w.bits / 8) (.slot { area := .frame E.fn, off := iOff }) limit done) =
        if cur ≥ hi then .goto done else .next ist tmps := by
      rw [step_br, opd_slot, addr_frame, hi0, hlim1 ist tmps hlim]
      simp only [cmpOp]
      by_cases h : cur ≥ hi <;> simp [h]
    by_cases hlt : cur < hi
    · rw [if_pos hlt]
      rw [if_neg (by omega)] at hbrs
      have r0 : Reach c f ptop tmps ist (ptop + 2) tmps ist := rtop.trans (Reach.next hbrI hbrs)
      simp only [Lang.Sem.setFirst, beq_self_eq_true, if_true]
      have hB := hbody j lst _ ist tmps (by omega) hrel hsz
      cases hR : Lang.Sem.execB j E.prog lst ((x, .int w (UInt64.ofNat cur)) :: envT) body with
      | fuel => trivial
      | trap lst' =>
        simp only [hR] at hB ⊢
        obtain ⟨ist', he, hw⟩ := hB
        exact ⟨ist', r0.ends he, hw⟩
      | ok lst' env' o =>
        simp only [hR] at hB ⊢
        obtain ⟨envT', rfl⟩ := keepsB_head ((keeps E.prog hnr x j).1 _ _ _ _ _ _ hR hnw)
        cases o with
        | ret v =>
          obtain ⟨ist', he, hgs, hko, hret⟩ := hB
          exact ⟨by simp, _, .int w (UInt64.ofNat cur), envT', rfl, ist', r0.ends he, hgs, hko, hret⟩
        | brk =>
          obtain ⟨l, i, ist1, t1, hl, hi', r1, sz1, hrel1, hkeep1⟩ := hB
          rw [hle] at hl
          cases hl
          have hii := F.uniq i (pe + 2) _ hi' hdone
          subst hii
          exact ⟨by simp, _, .int w (UInt64.ofNat cur), envT', rfl, ist1, t1,
            r0.trans (r1.trans (hdoneR ist1 t1)), sz1, hrel1, hkeep1.weaken rfl rfl (by omega) (fun _ _ h => h)⟩
        | normal =>
          dsimp only
          obtain ⟨ist1, t1, r1, sz1, hrel1, hkeep1⟩ := hB
          have hms := hrel1.size
          have hi1 := hcount lst' envT' ist1 cur hcur hrel1
          have hc1 : cur + 1 < 2 ^ w.bits := by omega
          have hwr : ∀ A, A < fbase c E.fn + iOff ∨ fbase c E.fn + iOff + w.bits / 8 ≤ A →
              (wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1)).get! A = ist1.mem.get! A :=
            fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
          have hstep : step c ist1 t1 (Instr.bin .add (w.bits / 8) (.slot { area := .frame E.fn, off := iOff })
              (.slot { area := .frame E.fn, off := iOff }) (.const 1)) =
              .next { ist1 with mem := wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1) } t1 := by
            rw [step_bin, setDst_slot, opd_slot, addr_frame, hi1, opd_const,
              modN_of_lt (Nat.one_lt_two_pow (by have := Ember.Proof.CSim.bits_pos w; omega))]
            simp only [binOp, Step.set]
            rw [modN_of_lt (by rw [h8]; exact hc1)]
          -- the counter, counted up, as the variable's new value
          obtain ⟨lst2, env2, hup, hrel2, _, _⟩ := hrel1.setVar L hinfo rfl
            (by intro hv; simp [hvars, List.lookup] at hv)
            (v' := .int w (UInt64.ofNat (cur + 1)))
            (m' := wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1))
            ⟨rfl, by rw [ofNat_toNat_lt hc1]; exact hc1⟩ (by rw [wr_size]; exact hms)
            (by rw [addr_frame]; exact hwr)
            (by
              rw [addr_frame, holds_scalar (t := .int w) rfl, size_int, rd_wr _ _ _ _ (by omega) (by omega)]
              rw [Nat.mod_eq_of_lt (by rw [h8]; exact hc1)]
              exact (ofNat_toNat_lt hc1).symm)
          simp only [Lang.Sem.update, List.lookup, beq_self_eq_true, Lang.Sem.setFirst, if_true, Option.some.injEq,
            Prod.mk.injEq] at hup
          obtain ⟨rfl, rfl⟩ := hup
          have hkeep2 : Keep c E iOff ist.mem (wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1)) :=
            (hkeep1.weaken rfl rfl (by omega) (fun _ _ h => h)).trans
              (Keep.above hf' (by omega : iOff + w.bits / 8 ≤ f'.frame) (fun A hA => hwr A (by omega)))
          have hlim' : Lim (wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1)) :=
            hlim3 _ _ hms (hlim2 _ _ hkeep1 hlim)
          have r3 : Reach c f ptop tmps ist ptop t1
              { ist1 with mem := wr ist1.mem (fbase c E.fn + iOff) (w.bits / 8) (cur + 1) } :=
            r0.trans (r1.trans ((Reach.next hadd hstep).trans
              (Reach.goto hjmp (step_jmp _ _ t1 top) (F.label htop))))
          have hI := ih (by omega) (cur + 1) lst' (.int w (UInt64.ofNat cur)) envT' _ t1 hc1 hrel2 hlim'
            (by rw [sz1]; exact hsz)
          cases hL : Lang.Sem.forLoop j E.prog lst' ((x, .int w (UInt64.ofNat cur)) :: envT') x w (cur + 1) hi body with
          | fuel => trivial
          | trap lst'' =>
            simp only [hL] at hI ⊢
            obtain ⟨ist', he, hw⟩ := hI
            exact ⟨ist', r3.ends he, hw⟩
          | ok lst'' env'' o' =>
            simp only [hL] at hI ⊢
            obtain ⟨hnb, v1, v2, envT'', he, hS⟩ := hI
            exact ⟨hnb, v1, v2, envT'', he, hS.pre r3 sz1 hkeep2⟩
    · rw [if_neg hlt]
      rw [if_pos (by omega)] at hbrs
      exact ⟨by simp, v0, .int w (UInt64.ofNat cur), envT, rfl, ist, tmps,
        rtop.trans ((Reach.goto hbrI hbrs (F.label hdone)).trans (hdoneR ist tmps)), rfl, hrel, Keep.refl _⟩

/-- The upper bound of a `for`: its code leaves the bound where the
operand `limit` reads it — a constant, or a slot of its own above what
was in use. -/
def LimSem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (n : Nat) (hiE : Expr) (s1 s2 : LS) (limit : Opd) : Prop :=
  ∀ lst env ist tmps, Ext s2 sF → SRel c E s1.cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env hiE with
    | none => Ends c f s1.out.size tmps ist (.trap ist)
    | some b => ∃ m' tmps', Reach c f s1.out.size tmps ist s2.out.size tmps' { ist with mem := m' } ∧
        tmps'.size = tmps.size ∧ m'.size = 65536 ∧
        (∀ A, A < fbase c E.fn + s1.cur ∨ fbase c E.fn + s2.cur ≤ A → m'.get! A = ist.mem.get! A) ∧
        ∀ (m'' : ByteArray) (wd : World) (t : Array Nat),
          (∀ A, fbase c E.fn + s1.cur ≤ A → A < fbase c E.fn + s2.cur → m''.get! A = m'.get! A) →
          opd c { mem := m'', world := wd } t n limit = b.toNat

def LimPost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (n : Nat) (hiE : Expr) (s1 : LS) (limit : Opd) (s2 : LS) :
    Prop :=
  Ext s1 s2 ∧ s1.cur ≤ s2.cur ∧ (s2.cur = s1.cur ∨ s2.cur ≤ s2.max) ∧ LimSem c f sF E n hiE s1 s2 limit

theorem forLimit_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn)
    (hiE : Expr) (w : Width) (s1 : LS) (hw : WT E hiE) (hty : E.tyOf hiE = .ok (.int w)) :
    wp (forLimit (w.bits / 8) hiE) E (LimPost c f sF E (w.bits / 8) hiE s1) s1 := by
  unfold forLimit
  cases hch : closed? hiE with
  | some v =>
    obtain ⟨hk, val, hv, hall⟩ := closed_val hw hty rfl hch
    rw [wp_pure]
    refine ⟨Ext.refl s1, Nat.le_refl _, .inl rfl, ?_⟩
    intro lst env ist tmps hxF hrel hsz
    rw [hall lst env]
    exact ⟨ist.mem, tmps, Reach.refl, rfl, hrel.size, fun _ _ => rfl,
      fun m'' wd t _ => by rw [opd_const]; exact (modN_of_lt hk).trans hv.symm⟩
  | none =>
    simp only [wp_bind, wp_allocLocal]
    refine wp_mono (exprToSlot_ok F L hE hiE (.int w) _ _ hw hty rfl) ?_
    intro _ s2 ⟨hx2, hc2, hs2⟩
    rw [wp_pure]
    have hc2' : s2.cur = s1.cur + w.bits / 8 := hc2
    refine ⟨(Ext.alloc s1 _).trans hx2, by omega, .inr (by have := hx2.max; simp only at this; rw [hc2']; exact Nat.le_trans (Nat.le_max_right _ _) this), ?_⟩
    intro lst env ist tmps hxF hrel hsz
    have h2 := hs2 s1.cur lst env ist tmps hxF hrel hsz
    cases hev : Lang.Sem.evalE E.prog lst env hiE with
    | none => simp only [hev] at h2 ⊢; exact h2
    | some b =>
      simp only [hev] at h2 ⊢
      obtain ⟨t1, sz1, _, r1⟩ := h2
      rw [setDst_slot, addr_frame] at r1
      simp only [size_int] at r1
      have hvb := evalE_hasTy E lst env (hrel.typed L) hiE b _ hw hev hty
      obtain ⟨f', hf', hfr⟩ := F.fit hfn (hx2.trans hxF) (k := s1.cur + w.bits / 8) (Nat.le_max_right _ _)
      have hfb := L.fbound _ _ hf'
      have hms := hrel.size
      refine ⟨_, t1, r1, sz1, by rw [wr_size]; exact hms,
        fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) (by rw [hc2'] at hA; omega), fun m'' wd t hag => ?_⟩
      rw [opd_slot, addr_frame]
      show rd m'' (fbase c E.fn + s1.cur) (w.bits / 8) = b.toNat
      rw [rd_congr _ m'' _ _ (by omega) (fun A a1 a2 => hag A a1 (by rw [hc2']; omega)),
        rd_wr _ _ _ _ (by omega) (by omega)]
      exact Nat.mod_eq_of_lt (toNat_lt hvb rfl)

theorem for_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn)
    (hnr : NoRef E.prog) (N : Nat) (rt : Option Ty) (x : String) (w : Option Width) (lo hi : Expr)
    (body : List Stmt) (s : LS)
    (hw : WT E lo ∧ WT E hi ∧ E.tyOf lo = .ok (.int (w.getD .w32)) ∧ E.tyOf hi = .ok (.int (w.getD .w32)) ∧
      NoWriteL x body)
    (ihb : ∀ off l s1, wp (blockFrom
        { E with vars := (x, { ty := .int (w.getD .w32), at_ := .static { area := .frame E.fn, off } }) :: E.vars,
                 loopEnd := l } body) E
      (BPost c f sF N rt
        { E with vars := (x, { ty := .int (w.getD .w32), at_ := .static { area := .frame E.fn, off } }) :: E.vars,
                 loopEnd := l } body s1) s1) :
    wp (IR.stmt (.forRange x w lo hi body)) E (SPost c f sF N rt E (.forRange x w lo hi body) s) s := by
  obtain ⟨hwlo, hwhi, htlo, hthi, hnw⟩ := hw
  generalize hW : w.getD .w32 = W at htlo hthi ihb
  rw [IR.stmt]
  rw [wp_bind, wp_read, wp_bind, wp_inScope]
  simp only [wp_bind, wp_allocLocal, hW]
  refine wp_mono (exprToSlot_ok F L hE lo (.int W) _ _ hwlo htlo rfl) ?_
  intro _ s1 ⟨hx1, hc1, hs1⟩
  have hc1' : s1.cur = s.cur + W.bits / 8 := hc1
  refine wp_mono (forLimit_ok F L hE hfn hi W s1 hwhi hthi) ?_
  intro limit s2 ⟨hx2, hc2a, hc2b, hs2⟩
  simp only [wp_bind, wp_newLabel, wp_emit]
  refine wp_mono (scope_ok (ihb s.cur (some (s2.labels + 1)) _)) ?_
  intro _ sd ⟨hxd, hcd, hsd⟩
  have hcd' : sd.cur = s2.cur := hcd
  simp only [wp_emit, wp_pure]
  have hx01 := (Ext.alloc s (W.bits / 8)).trans hx1
  have hxb := (Ext.newLabel s2).trans ((Ext.newLabel _).trans ((Ext.emit _ (Instr.label s2.labels)).trans
    (Ext.emit _ (Instr.br .ge (W.bits / 8) (.slot { area := .frame E.fn, off := s.cur }) limit (s2.labels + 1)))))
  have hxe := (Ext.emit sd (Instr.bin .add (W.bits / 8) (.slot { area := .frame E.fn, off := s.cur })
      (.slot { area := .frame E.fn, off := s.cur }) (.const 1))).trans
    ((Ext.emit _ (Instr.jmp s2.labels)).trans (Ext.emit _ (Instr.label (s2.labels + 1))))
  refine ⟨((hx01.trans hx2).trans (hxb.trans (hxd.trans hxe))).scope, rfl, Nat.le_refl _, ?_⟩
  intro n' lst env ist tmps hn hxF hrel hsz hend
  cases n' with
  | zero => rw [Lang.Sem.execS]; trivial
  | succ j =>
    simp only [Lang.Sem.execS, hW]
    have hxFd := hxe.trans (Ext.of_out hxF rfl rfl rfl rfl)
    have hxFb := hxd.trans hxFd
    have hxF2 := hxb.trans hxFb
    have hxF1 := hx2.trans hxF2
    obtain ⟨g1, g2⟩ := push2 s2.out (Instr.label s2.labels)
      (Instr.br .ge (W.bits / 8) (.slot { area := .frame E.fn, off := s.cur }) limit (s2.labels + 1))
    have htop := F.at_ hxFb g1
    have hbrI := F.at_ hxFb g2
    obtain ⟨g3, g4, g5⟩ := push3 sd.out (Instr.bin .add (W.bits / 8) (.slot { area := .frame E.fn, off := s.cur })
      (.slot { area := .frame E.fn, off := s.cur }) (.const 1)) (Instr.jmp s2.labels) (Instr.label (s2.labels + 1))
    have hadd := F.at_ hxF g3
    have hjmp := F.at_ hxF g4
    have hdone := F.at_ hxF g5
    -- the frame holds the counter and the bound
    have hcurb : s2.cur ≤ sF.max := by
      rcases hc2b with h | h
      · rw [h, hc1']
        have h1 := hx1.max
        have h2 := hxF1.max
        simp only at h1
        exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h1) h2
      · exact Nat.le_trans h hxF2.max
    have hf' : c.prog.fn? E.fn = some f := by rw [hfn]; exact F.fn
    have hfr : s2.cur ≤ f.frame := Nat.le_trans hcurb F.frame
    have hfb := L.fbound _ _ hf'
    have hms := hrel.size
    have htopv := hrel.top_le
    have h8 : sizeOf E.prog (.int W) = W.bits / 8 := rfl
    have h1 := hs1 s.cur lst env ist tmps hxF1 hrel hsz
    simp only [Array.size_push]
    cases hlo : Lang.Sem.evalE E.prog lst env lo with
    | none =>
      simp only [hlo] at h1
      cases Lang.Sem.evalE E.prog lst env hi <;> exact ⟨ist, h1, hrel.world⟩
    | some a =>
      simp only [hlo] at h1
      obtain ⟨av, rfl, hav⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) lo a _ hwlo hlo htlo)
      obtain ⟨t1, sz1, _, r1⟩ := h1
      rw [setDst_slot, addr_frame] at r1
      simp only [Val.toNat, size_int] at r1
      have hwr : ∀ A, A < fbase c E.fn + s.cur ∨ fbase c E.fn + s.cur + W.bits / 8 ≤ A →
          (wr ist.mem (fbase c E.fn + s.cur) (W.bits / 8) av.toNat).get! A = ist.mem.get! A :=
        fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA
      -- the counter as a variable; and the state the bound is evaluated in
      have hrelp : SRel c
          { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars }
          (s.cur + W.bits / 8) lst ((x, .int W av) :: env)
          { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (W.bits / 8) av.toNat } :=
        hrel.push L x (.int W) (.int W av) (m' := wr ist.mem (fbase c E.fn + s.cur) (W.bits / 8) av.toNat)
          (by rw [wr_size]; exact hms) trivial ⟨rfl, hav⟩ ⟨f, hf', by rw [h8]; omega⟩ (by rw [h8]; exact hwr)
          (by
            rw [holds_scalar (t := .int W) rfl, h8, rd_wr _ _ _ _ (by omega) (by omega)]
            exact Nat.mod_eq_of_lt (by rw [bits8]; exact hav))
      have hrel1 : SRel c E s1.cur lst env
          { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (W.bits / 8) av.toNat } := by
        refine (hrel.frame' L (by rw [wr_size]; exact hms) (fun A hA => hwr A ?_)).grow (by omega) ⟨f, hf', by omega⟩
        rcases hA with hg | ⟨a1, a2⟩
        · by_cases hin : fbase c E.fn + s.cur ≤ A ∧ A < fbase c E.fn + s.cur + W.bits / 8
          · exact absurd hg (L.fglob _ A ⟨f, hf', by omega, by omega⟩)
          · omega
        · exact .inl (by omega)
      have h2 := hs2 lst env _ t1 hxF2 hrel1 (by rw [sz1]; exact hsz)
      cases hhi : Lang.Sem.evalE E.prog lst env hi with
      | none =>
        simp only [hhi] at h2 ⊢
        exact ⟨_, r1.ends h2, hrel.world⟩
      | some b =>
        simp only [hhi] at h2 ⊢
        obtain ⟨bv, rfl, hbv⟩ := hasTy_int (evalE_hasTy E lst env (hrel.typed L) hi b _ hwhi hhi hthi)
        obtain ⟨m2, t2, r2, sz2, hm2, hag2, hlimv⟩ := h2
        simp only [Val.toNat] at hlimv ⊢
        rw [UInt64.ofNat_toNat]
        -- the relation the body starts in
        have hrelb : SRel c
            { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                     loopEnd := some (s2.labels + 1) } s2.cur lst ((x, .int W av) :: env) { ist with mem := m2 } := by
          refine SRel.congr ((SRel.frame'
            (E := { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars })
            L hrelp hm2 (fun A hA => hag2 A ?_)).grow (by omega) ⟨f, hf', hfr⟩) rfl rfl rfl
          rcases hA with hg | ⟨a1, a2⟩
          · by_cases hin : fbase c E.fn + s1.cur ≤ A ∧ A < fbase c E.fn + s2.cur
            · exact absurd hg (L.fglob _ A ⟨f, hf', by omega, by omega⟩)
            · omega
          · have a2' : A < fbase c E.fn + topOf E.prog
                ((x, ({ ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } } : VarInfo)) :: E.vars) := a2
            have : topOf E.prog ((x, ({ ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } } : VarInfo)) :: E.vars) ≤
                s.cur + W.bits / 8 := Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩
            exact .inl (by omega)
        have hbody : ∀ j lst env ist tmps, j ≤ N →
            SRel c { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                            loopEnd := some (s2.labels + 1) } s2.cur lst env ist →
            tmps.size = f.tmps.size →
            match Lang.Sem.execB j E.prog lst env body with
            | .fuel => True
            | .trap lst' => ∃ ist', Ends c f (s2.out.size + 2) tmps ist (.trap ist') ∧ ist'.world = lst'.world
            | .ok lst' env' o => SOut c f rt
                { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                         loopEnd := some (s2.labels + 1) } s2.cur ist tmps (s2.out.size + 2) lst' env' o
                { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                         loopEnd := some (s2.labels + 1) } s2.cur sd.out.size := by
          intro j lst env ist tmps hj hrel' hsz'
          have := hsd j lst env ist tmps hj hxFd hrel' hsz' (fun l hl => by
            simp only [Option.some.injEq] at hl
            subst hl
            exact ⟨_, hdone⟩)
          simpa only [Array.size_push] using this
        have hF := for_sim F
          (E := { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                         loopEnd := some (s2.labels + 1) }) L hnr N rt x W body s.cur s2.cur limit bv.toNat
          s2.out.size sd.out.size s2.labels (s2.labels + 1) E.vars rfl rfl htop hbrI hadd hjmp hdone hnw hbv
          (by omega) ⟨f, hf', hfr⟩
          (fun m => ∀ A, fbase c E.fn + s1.cur ≤ A → A < fbase c E.fn + s2.cur → m.get! A = m2.get! A)
          (fun ist' t' h => hlimv ist'.mem ist'.world t' h)
          (fun m m' hk h A a1 a2 => by
            rw [← h A a1 a2]
            have hle : fbase c E.fn ≤ A := by omega
            refine hk A (.inr ⟨hle, a2, fun hin => ?_⟩)
            have hlt : A - fbase c E.fn < topOf E.prog
                ((x, ({ ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } } : VarInfo)) :: E.vars) :=
              inVars_lt_top hin
            have : topOf E.prog ((x, ({ ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } } : VarInfo)) :: E.vars) ≤
                s.cur + W.bits / 8 := Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩
            omega)
          (fun m v hm h A a1 a2 => by
            rw [← h A a1 a2]
            show (wr m (fbase c E.fn + s.cur) (W.bits / 8) v).get! A = m.get! A
            exact wr_get_out _ _ _ _ _ (by omega) (by omega) (by omega))
          hbody j (by omega) av.toNat lst (.int W av) env { ist with mem := m2 } t2 hav
          (by rw [UInt64.ofNat_toNat]; exact hrelb) (fun _ _ _ => rfl) (by rw [sz2, sz1]; exact hsz)
        have r02 := r1.trans r2
        have hk02 : Keep c E s.cur ist.mem m2 := by
          refine Keep.above hf' hfr (fun A hA => ?_)
          rw [hag2 A (by omega)]
          exact hwr A (by omega)
        cases hL : Lang.Sem.forLoop j E.prog lst ((x, .int W av) :: env) x W av.toNat bv.toNat body with
        | fuel => trivial
        | trap lst' =>
          simp only [hL] at hF ⊢
          obtain ⟨ist', he, hw'⟩ := hF
          exact ⟨ist', r02.ends he, hw'⟩
        | ok lst' env' o =>
          simp only [hL] at hF ⊢
          obtain ⟨hnb, v1, v2, envT', rfl, hS⟩ := hF
          have hk02' : Keep c
              { E with vars := (x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars,
                       loopEnd := some (s2.labels + 1) } s.cur ist.mem m2 :=
            hk02.weaken rfl rfl (Nat.le_refl _) (fun _ _ h => h.tail)
          have hS' := hS.pre r02 (by rw [sz2, sz1]) hk02'
          simp only [List.drop_succ_cons, List.drop_zero]
          cases o with
          | normal =>
            obtain ⟨ist', t', r, sz', hrel', hkeep⟩ := hS'
            refine ⟨ist', t', r, sz', ?_, ?_⟩
            · exact (SRel.congr (E' := { E with vars := [(x, { ty := .int W, at_ := .static { area := .frame E.fn, off := s.cur } })] ++ E.vars })
                hrel' rfl rfl rfl).pop (pre' := 1) rfl htopv (by omega)
            · refine hkeep.weaken rfl rfl (Nat.le_refl _) (fun o ho hin => ?_)
              obtain ⟨y, info, sl, hmem, hat, h1', h2'⟩ := hin
              rcases List.mem_cons.mp hmem with he | hr
              · cases he
                simp only [Storage.static.injEq] at hat
                subst hat
                simp only at h1'
                omega
              · exact ⟨y, info, sl, hr, hat, h1', h2'⟩
          | brk => exact absurd rfl hnb
          | ret v => exact hS'

end

end Ember.Proof.IRSim
