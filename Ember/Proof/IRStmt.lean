import Ember.Proof.IRJump

/-!
# Ember.Proof.IRStmt — the lowering is right about statements (plan M7.1)

The definitions (`WTS`: what the proofs need of a checked statement;
`SSim`: the instructions for a statement do what `Lang.Sem.execS` does,
ending in related states), and the statements without a block inside:
declarations, assignments, `break`, `return`.

Outside: by-reference parameters (the stack has none).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 hasTy_int hasTy_bool hasTy_arr hasTy_record FieldOK TyOK IsPlace NoWriteL
  ReturnsL NoRef hasTy_zero)

/-! ## Well-typed statements -/

/-- Arguments of the parameters' types, all scalars. -/
def ArgsOK (g : Env) : List Ty → List Expr → Prop
  | [], [] => True
  | t :: ts, a :: as => WT g a ∧ g.tyOf a = .ok t ∧ t.isScalar = true ∧ ArgsOK g ts as
  | _, _ => False

/-- A destination for a result of type `ret`. -/
def DstOK (g : Env) (dst : Option Expr) (ret : Option Ty) : Prop :=
  match dst with
  | none => True
  | some d => IsPlace d ∧ Writable g d ∧ WT g d ∧ ∃ t, ret = some t ∧ g.tyOf d = .ok t ∧ t.isScalar = true

/-- A call or an effect whose result is the value of a declaration of type `ty`. -/
def InitOK (g : Env) (ty : Ty) : Init → Prop
  | .call f args => ∃ fd, g.prog.fn? f = some fd ∧ ArgsOK g (fd.params.map (·.ty)) args ∧ fd.ret = some ty
  | .eff e args => ArgsOK g e.sig.1 args ∧ e.sig.2 = some ty

/-- The lowering's environment after a statement, when `off` bytes of the frame were in use. -/
def envAfter (g : Env) (off : Nat) : Stmt → Env
  | .at _ s => envAfter g off s
  | .decl x ty _ => { g with vars := (x, { ty, at_ := .static { area := .frame g.fn, off } }) :: g.vars }
  | _ => g

mutual
/-- **What the proofs need of a checked statement**, in the lowering's
environment `g`, in a function returning `rt`; `il`: inside a loop. -/
def WTS (rt : Option Ty) : Bool → Env → Stmt → Prop
  | il, g, .at _ s => WTS rt il g s
  | _, g, .decl _ ty init =>
    TyOK g.prog ty ∧
      (match init with
       | some e => WT g e ∧ g.tyOf e = .ok ty ∧ ty.isScalar = true
       | none => True)
  | _, g, .assign l r =>
    IsPlace l ∧ Writable g l ∧ WT g l ∧ WT g r ∧ ∃ t, g.tyOf l = .ok t ∧ g.tyOf r = .ok t ∧ t.isScalar = true
  | il, g, .ite c t e => WT g c ∧ g.tyOf c = .ok .bool ∧ WTB rt il g t ∧ WTB rt il g e
  | _, g, .forRange x w lo hi body =>
    WT g lo ∧ WT g hi ∧ g.tyOf lo = .ok (.int (w.getD .w32)) ∧ g.tyOf hi = .ok (.int (w.getD .w32)) ∧
      NoWriteL x body ∧
      ∀ off l, WTB rt true
        { g with vars := (x, { ty := .int (w.getD .w32), at_ := .static { area := .frame g.fn, off } }) :: g.vars,
                 loopEnd := l } body
  | _, g, .loop n body => n < 2 ^ 32 ∧ ∀ l, WTB rt true { g with loopEnd := l } body
  | il, _, .brk => il = true
  | _, g, .ret v =>
    (match v with
     | none => rt = none
     | some e => WT g e ∧ ∃ t, rt = some t ∧ g.tyOf e = .ok t ∧ t.isScalar = true)
  | _, g, .call dst f args =>
    ∃ fd, g.prog.fn? f = some fd ∧ ArgsOK g (fd.params.map (·.ty)) args ∧ DstOK g dst fd.ret
  | _, g, .eff dst e args => ArgsOK g e.sig.1 args ∧ DstOK g dst e.sig.2

/-- A well-typed list of statements: as the lowering goes through it,
a declaration and the call that gives it its value being one. -/
def WTB (rt : Option Ty) : Bool → Env → List Stmt → Prop
  | _, _, [] => True
  | il, g, [s] => WTS rt il g s
  | il, g, s :: s2 :: rest =>
    match declCall? s s2 with
    | some (x, ty, i) =>
      TyOK g.prog ty ∧ InitOK g ty i ∧
        ∀ off, WTB rt il { g with vars := (x, { ty, at_ := .static { area := .frame g.fn, off } }) :: g.vars } rest
    | none => WTS rt il g s ∧ ∀ off, WTB rt il (envAfter g off s) (s2 :: rest)
end

/-- What the proofs need of a function: scalar parameters by value,
with different names; a well-typed body; a result on every path if it
has one. -/
structure FnOK (p : Prog) (fd : Lang.Fn) : Prop where
  params : ∀ prm, prm ∈ fd.params → prm.byRef = false ∧ prm.ty.isScalar = true
  names : (fd.params.map (·.name)).Nodup
  body : WTB fd.ret false (fnEnv p fd) fd.body
  returns : fd.ret.isSome = true → ReturnsL fd.body
  ret : ∀ t, fd.ret = some t → t.isScalar = true

def ProgOK (p : Prog) : Prop := ∀ f fd, p.fn? f = some fd → FnOK p fd

/-! ## What a statement does -/

/-- The globals and the world are related (the state between calls). -/
def GS (c : Ctx) (lp : Prog) (lst : Lang.Sem.St) (ist : St) : Prop :=
  ist.mem.size = 65536 ∧ ist.world = lst.world ∧ GRel lp c ist.mem lst.globals

theorem SRel.gs {c : Ctx} {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St}
    (h : SRel c E cur lst env ist) : GS c E.prog lst ist := ⟨h.size, h.world, h.glob⟩

/-- What a function leaves alone. -/
def KeepOut (c : Ctx) (lp : Prog) (fn : String) (m m' : ByteArray) : Prop :=
  ∀ A, Outside lp c fn A → m'.get! A = m.get! A

theorem Keep.out {c : Ctx} {E : Env} {cur : Nat} {m m' : ByteArray} (h : Keep c E cur m m') :
    KeepOut c E.prog E.fn m m' := fun A hA => h A (.inl hA)

theorem KeepOut.refl (c : Ctx) (lp : Prog) (fn : String) (m : ByteArray) : KeepOut c lp fn m m := fun _ _ => rfl

theorem KeepOut.trans {c : Ctx} {lp : Prog} {fn : String} {m1 m2 m3 : ByteArray} (h1 : KeepOut c lp fn m1 m2)
    (h2 : KeepOut c lp fn m2 m3) : KeepOut c lp fn m1 m3 := fun A hA => by rw [h2 A hA, h1 A hA]

/-- The result of a function with result type `rt`. -/
def RetOK (lp : Prog) (rt : Option Ty) (v : Option Val) : Prop :=
  match rt with
  | some t => ∃ x, v = some x ∧ HasTy lp t x
  | none => v = none

/-- **How the code for a statement ends**, for each way the statement
ends: on to `pc'` in related states; at the label of the loop's end; or
the function returns. -/
def SOut (c : Ctx) (f : IR.Fn) (rt : Option Ty) (E : Env) (cur : Nat) (ist : St) (tmps : Array Nat) (pc : Nat)
    (lst' : Lang.Sem.St) (env' : Lang.Sem.Env) (o : Lang.Sem.Out) (E' : Env) (cur' pc' : Nat) : Prop :=
  match o with
  | .normal => ∃ ist' tmps', Reach c f pc tmps ist pc' tmps' ist' ∧ tmps'.size = tmps.size ∧
      SRel c E' cur' lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem
  | .brk => ∃ l i ist' tmps', E.loopEnd = some l ∧ f.body[i]? = some (Instr.label l) ∧
      Reach c f pc tmps ist i tmps' ist' ∧ tmps'.size = tmps.size ∧ SRel c E' cur' lst' env' ist' ∧
      Keep c E cur ist.mem ist'.mem
  | .ret v => ∃ ist', Ends c f pc tmps ist (.ok (v.map Val.toNat) ist') ∧ GS c E.prog lst' ist' ∧
      KeepOut c E.prog E.fn ist.mem ist'.mem ∧ RetOK E.prog rt v

/-- **The code between `s` and `s'` simulates the statement**, for up to `N` units of fuel. -/
def SSim (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (stm : Stmt) (s : LS) (E' : Env)
    (s' : LS) : Prop :=
  ∀ n lst env ist tmps, n ≤ N → Ext s' sF → SRel c E s.cur lst env ist → tmps.size = f.tmps.size →
    (∀ l, E.loopEnd = some l → ∃ i : Nat, f.body[i]? = some (Instr.label l)) →
    match Lang.Sem.execS n E.prog lst env stm with
    | .fuel => True
    | .trap lst' => ∃ ist', Ends c f s.out.size tmps ist (.trap ist') ∧ ist'.world = lst'.world
    | .ok lst' env' o => SOut c f rt E s.cur ist tmps s.out.size lst' env' o E' s'.cur s'.out.size

/-- What `stmt` promises. -/
def SPost (c : Ctx) (f : IR.Fn) (sF : LS) (N : Nat) (rt : Option Ty) (E : Env) (stm : Stmt) (s : LS) (E' : Env)
    (s' : LS) : Prop :=
  Ext s s' ∧ E' = envAfter E s.cur stm ∧ s.cur ≤ s'.cur ∧ SSim c f sF N rt E stm s E' s'

/-! ## Memory after a store -/

theorem rd_zero (m : ByteArray) (a n : Nat) (ha : a + n ≤ 65536) (h : ∀ x, a ≤ x → x < a + n → m.get! x = 0) :
    rd m a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [rd, ih (a + 1) (by omega) (fun x h1 h2 => h x (by omega) (by omega)), Nat.mod_eq_of_lt (by omega),
      h a (Nat.le_refl _) (by omega)]
    rfl

theorem holds0_zero_field (m : ByteArray) (a : Nat) (t : Ty) : FieldOK t → a + sizeOf0 t ≤ 65536 →
    (∀ x, a ≤ x → x < a + sizeOf0 t → m.get! x = 0) →
    Holds0 m a t (match t with
      | .int w => Val.int w 0
      | .bool => .bool false
      | .arr (.int w) n => .arr (Array.replicate n (.int w 0))
      | .arr _ n => .arr (Array.replicate n (.bool false))
      | .record _ => .bool false) := by
  intro hf hb hz
  have hel : ∀ (el : Ty) (n : Nat) (z : Val), z.toNat = 0 → a + n * sizeOf0 el ≤ 65536 →
      (∀ x, a ≤ x → x < a + n * sizeOf0 el → m.get! x = 0) →
      Holds0 m a (.arr el n) (.arr (Array.replicate n z)) := by
    intro el n z hz0 hb' hz'
    simp only [Holds0]
    intro i hi
    have hi' : i < n := by simpa using hi
    have hle : (i + 1) * sizeOf0 el ≤ n * sizeOf0 el := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    rw [rd_zero m _ _ (by omega) (fun x h1 h2 => hz' x (by omega) (by omega))]
    simp [hz0]
  cases t with
  | int w => simp only [Holds0]; rw [rd_zero m a _ hb hz]; rfl
  | bool => simp only [Holds0]; rw [rd_zero m a _ hb hz]; rfl
  | record _ => exact absurd hf (by simp [FieldOK])
  | arr el n =>
    cases el with
    | int w => exact hel _ n _ rfl hb hz
    | bool => exact hel _ n _ rfl hb hz
    | arr _ _ => simp [FieldOK, Ty.isScalar] at hf
    | record _ => simp [FieldOK, Ty.isScalar] at hf

/-- Zero bytes are the zero value of every type. -/
theorem holds_zero (p : Prog) (ty : Ty) (hty : TyOK p ty) (m : ByteArray) (a : Nat) (hb : a + sizeOf p ty ≤ 65536)
    (hz : ∀ x, a ≤ x → x < a + sizeOf p ty → m.get! x = 0) : Holds p m a ty (zeroOf p ty) := by
  cases ty with
  | int w => exact holds0_zero_field m a (.int w) trivial hb hz
  | bool => exact holds0_zero_field m a .bool trivial hb hz
  | arr el n =>
    have hf : FieldOK (.arr el n) := hty
    rw [sizeOf_field p hf] at hb hz
    have := holds0_zero_field m a (.arr el n) hf hb hz
    cases el with
    | int w => exact this
    | bool => exact this
    | arr _ _ => simp [TyOK, Ty.isScalar] at hty
    | record _ => simp [TyOK, Ty.isScalar] at hty
  | record r =>
    obtain ⟨sd, hsd, hfld⟩ := hty
    refine ⟨sd, hsd, fun i hi hi' => ?_⟩
    simp only [hsd, Option.map_some, Option.getD_some, List.getElem_toArray, List.getElem_map]
    have hfi : FieldOK (sd.fields[i]).2 := hfld _ (List.getElem_mem hi')
    have hin := field_in p hsd hfld i hi'
    rw [sizeOf_field p hfi] at hin
    exact holds0_zero_field m (a + fldOff p sd.fields i) (sd.fields[i]).2 hfi (by omega)
      (fun x h1 h2 => hz x (by omega) (by omega))

/-- The bytes of a zero. -/
theorem wr_zero_get (m : ByteArray) (a n x : Nat) (ha : a + n ≤ m.size) (hm : m.size ≤ 65536) (h1 : a ≤ x)
    (h2 : x < a + n) : (wr m a n 0).get! x = 0 := by
  rw [wr_get m a n 0 x ha hm, if_pos ⟨h1, h2⟩]
  simp

/-! ## Stores -/

section
variable {c : Ctx} {fn : String} {f : IR.Fn} {sF : LS}

theorem step_store_some (c : Ctx) (ist : St) (tmps : Array Nat) (n : Nat) (p : Addr) (src : Opd) {A : Nat}
    (h : addr c ist tmps p = some A) (hb : inBound c ist tmps p = true) :
    step c ist tmps (.store n p src) = .next { ist with mem := wr ist.mem A n (opd c ist tmps n src) } tmps := by
  simp only [step, h, hb, if_true]

theorem step_store_none (c : Ctx) (ist : St) (tmps : Array Nat) (n : Nat) (p : Addr) (src : Opd)
    (h : addr c ist tmps p = none) : step c ist tmps (.store n p src) = .stop (.trap ist) := by
  simp only [step, h]

/-- An expression into a variable's slot. -/
theorem exprToSlot_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (e : Expr) (ty : Ty)
    (sl : Slot) (s : LS) (hw : WT E e) (hty : E.tyOf e = .ok ty) (hs : ty.isScalar = true) :
    wp (exprToSlot sl e) E (TPost c f sF E e ty (.slot sl) s) s := by
  unfold exprToSlot
  by_cases hc : hasCond e = true
  · rw [if_pos hc]
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t ht
    rw [hty] at ht
    cases ht
    exact wp_mono (expr_ok F e E s ty L hE hw hty hs) (fun o s1 h => movOpd_ok F e ty s s1 o (.slot sl) h)
  · rw [if_neg hc]
    refine exprTo_ok F e E s ty (.slot sl) L hE hw hty hs (fun cnd a b h => ?_)
    subst h
    simp [hasCond] at hc

/-- **A scalar stored at a place**: the assignment, in related states. -/
theorem wr_place {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St} {e : Expr} {ty : Ty}
    {lv : Val} {A : Nat} (hpl : PlaceAt c E cur lst env ist e ty lv A) (hsz : ist.mem.size = 65536)
    (hs : ty.isScalar = true) (hw : Writable E e) {v : Val} (hv : HasTy E.prog ty v) :
    ∃ lst' env', Lang.Sem.assign E.prog lst env e v = some (lst', env') ∧
      SRel c E cur lst' env' { ist with mem := wr ist.mem A (sizeOf E.prog ty) v.toNat } ∧
      Keep c E cur ist.mem (wr ist.mem A (sizeOf E.prog ty) v.toNat) ∧ lst'.world = lst.world := by
  have hb := hpl.bound
  refine hpl.upd hw v _ hv (by rw [wr_size]; exact hsz)
    (fun x hx => wr_get_out _ _ _ _ _ (by omega) (by omega) hx) ?_
  rw [holds_scalar hs, rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (toNat_lt hv hs)]

/-- A place without a value cannot be assigned. -/
theorem assign_none (p : Prog) (st : Lang.Sem.St) (env : Lang.Sem.Env) (e : Expr) (v : Val)
    (h : Lang.Sem.evalE p st env e = none) : Lang.Sem.assign p st env e v = none := by
  cases ha : Lang.Sem.assign p st env e v with
  | none => rfl
  | some r =>
    obtain ⟨u, hu, _⟩ := Ember.Proof.CSim.update_some p st env e _ r ha
    rw [h] at hu
    cases hu

theorem Final.fit (F : Final c fn f sF) {E : Env} (hfn : E.fn = fn) {s : LS} (hx : Ext s sF) {k : Nat}
    (hk : k ≤ s.max) : ∃ f', c.prog.fn? E.fn = some f' ∧ k ≤ f'.frame :=
  ⟨f, by rw [hfn]; exact F.fn, by have := hx.max; have := F.frame; omega⟩

/-- A store into the frame, above what was in use. -/
theorem Keep.above {E : Env} {cur top : Nat} {m m' : ByteArray} {f' : IR.Fn} (hf : c.prog.fn? E.fn = some f')
    (htop : top ≤ f'.frame)
    (hm : ∀ A, A < fbase c E.fn + cur ∨ fbase c E.fn + top ≤ A → m'.get! A = m.get! A) : Keep c E cur m m' := by
  intro A hA
  apply hm
  rcases hA with ⟨_, hnf, _⟩ | ⟨a1, a2, _⟩
  · by_cases hin : fbase c E.fn ≤ A ∧ A < fbase c E.fn + f'.frame
    · exact absurd ⟨f', hf, hin.1, hin.2⟩ hnf
    · omega
  · exact .inl a2

/-- What `assign` promises. -/
def ASem (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (l r : Expr) (s s' : LS) : Prop :=
  ∀ cur lst env ist tmps, Ext s' sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
    match Lang.Sem.evalE E.prog lst env r with
    | none => Ends c f s.out.size tmps ist (.trap ist)
    | some v =>
      match Lang.Sem.assign E.prog lst env l v with
      | none => Ends c f s.out.size tmps ist (.trap ist)
      | some (lst', env') => ∃ ist' tmps', Reach c f s.out.size tmps ist s'.out.size tmps' ist' ∧
          tmps'.size = tmps.size ∧ SRel c E cur lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem

def APost (c : Ctx) (f : IR.Fn) (sF : LS) (E : Env) (l r : Expr) (s : LS) (_ : Unit) (s' : LS) : Prop :=
  Ext s s' ∧ s'.cur = s.cur ∧ ASem c f sF E l r s s'

/-- The end of every path of `assign`: the value is in hand, the place is known. -/
theorem assign_end {E : Env} {cur : Nat} {lst : Lang.Sem.St} {env : Lang.Sem.Env} {ist : St} {l : Expr} {ty : Ty}
    {lv v : Val} {A : Nat} {a e : Nat} {tmps t' : Array Nat}
    (hpl : PlaceAt c E cur lst env ist l ty lv A) (hsz : ist.mem.size = 65536) (hs : ty.isScalar = true)
    (hw : Writable E l) (hv : HasTy E.prog ty v)
    (r : Reach c f a tmps ist e t' { ist with mem := wr ist.mem A (sizeOf E.prog ty) v.toNat })
    (hts : t'.size = tmps.size) :
    match Lang.Sem.assign E.prog lst env l v with
    | none => Ends c f a tmps ist (.trap ist)
    | some (lst', env') => ∃ ist' tmps', Reach c f a tmps ist e tmps' ist' ∧
        tmps'.size = tmps.size ∧ SRel c E cur lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem := by
  obtain ⟨lst', env', ha, hrel', hkeep, _⟩ := wr_place hpl hsz hs hw hv
  rw [ha]
  exact ⟨_, t', r, hts, hrel', hkeep⟩

theorem assign_sem (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (l r : Expr) (s : LS)
    (hw : IsPlace l ∧ Writable E l ∧ WT E l ∧ WT E r ∧
      ∃ t, E.tyOf l = .ok t ∧ E.tyOf r = .ok t ∧ t.isScalar = true) :
    wp (assign l r) E (APost c f sF E l r s) s := by
  obtain ⟨_, hwr, hwl, hwrr, t, htl, htr, hs⟩ := hw
  unfold IR.assign
  simp only [wp_bind, wp_tyOf, wp_size]
  intro t' ht'
  rw [htr] at ht'
  cases ht'
  -- the two paths for a place that is not a variable of its own
  have hrest : wp (if (!canTrap l) = true then do
        let a ← place l
        match a.1.root, a.1.idx with
        | .static sl, none => exprToSlot { sl with off := sl.off + a.1.off } r
        | _, _ => do
          let o ← expr r
          emit (.store (sizeOf E.prog t) a.1 o)
      else do
        let o ← expr r
        let a ← place l
        storeTo (sizeOf E.prog t) a.1 o) E (APost c f sF E l r s) s := by
    by_cases hct : (!canTrap l) = true
    · rw [if_pos hct]
      simp only [Bool.not_eq_true'] at hct
      simp only [wp_bind]
      refine wp_mono (place_ok F l E s t L hE hwl htl) ?_
      intro a s1 ⟨hx1, hc1, hat, ⟨⟨sl, hroot⟩, hidx⟩, hs1⟩
      -- the place, which has a value
      have hplace : ∀ (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (tmps : Array Nat),
          Ext s1 sF → SRel c E cur lst env ist → tmps.size = f.tmps.size →
          ∃ lv, Runs c f ist s.out.size s1.out.size s.tmps.size tmps
            (fun t1 => ∃ A, addr c ist t1 a.1 = some A ∧ inBound c ist t1 a.1 = true ∧
              PlaceAt c E cur lst env ist l t lv A) := by
        intro cur lst env ist tmps hxF hrel hsz
        obtain ⟨lv, hlv⟩ := noTrap L hrel l t hwl htl hct
        have hp := hs1 cur lst env ist tmps hxF hrel hsz
        simp only [hlv] at hp
        exact ⟨lv, hp⟩
      cases hi : a.1.idx with
      | none =>
        simp only [hroot]
        refine wp_mono (exprToSlot_ok F L hE r t _ s1 hwrr htr hs) ?_
        intro _ s2 ⟨hx2, hc2, hs2⟩
        refine ⟨hx1.trans hx2, by rw [hc2, hc1], ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        obtain ⟨lv, t1, r1, sz1, ag1, A, hA, hin, hpl⟩ := hplace cur lst env ist tmps (hx2.trans hxF) hrel hsz
        rw [addr_static c ist t1 hroot hi] at hA
        cases hA
        have h2 := hs2 cur lst env ist t1 hxF hrel (by rw [sz1]; exact hsz)
        cases hev : Lang.Sem.evalE E.prog lst env r with
        | none => simp only [hev] at h2 ⊢; exact r1.ends h2
        | some v =>
          simp only [hev] at h2 ⊢
          obtain ⟨t2, sz2, _, r2⟩ := h2
          rw [setDst_slot] at r2
          exact assign_end hpl hrel.size hs hwr (evalE_hasTy E lst env (hrel.typed L) r v t hwrr hev htr)
            (r1.trans r2) (by rw [sz2, sz1])
      | some ix =>
        simp only [hroot, wp_bind]
        refine wp_mono (expr_ok F r E s1 t L hE hwrr htr hs) ?_
        intro o s2 ⟨hx2, hc2, ho2, hs2⟩
        rw [wp_emit]
        refine ⟨hx1.trans (hx2.trans (Ext.emit _ _)), by rw [← hc1, ← hc2], ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
        obtain ⟨lv, t1, r1, sz1, ag1, A, hA, hin, hpl⟩ := hplace cur lst env ist tmps (hx2.trans hxF2) hrel hsz
        have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [sz1]; exact hsz)
        simp only [Array.size_push]
        cases hev : Lang.Sem.evalE E.prog lst env r with
        | none => simp only [hev] at h2 ⊢; exact r1.ends h2
        | some v =>
          simp only [hev] at h2 ⊢
          obtain ⟨t2, r2, sz2, ag2, ho⟩ := h2
          have hA2 : addr c ist t2 a.1 = some A := by
            rw [addr_agree c ist (fun x hx t ht => (hidx x hx t ht).2) ag2]
            exact hA
          have hin2 : inBound c ist t2 a.1 = true := by
            rw [inBound_agree c ist (fun x hx t ht => (hidx x hx t ht).2) ag2]
            exact hin
          refine assign_end hpl hrel.size hs hwr (evalE_hasTy E lst env (hrel.typed L) r v t hwrr hev htr)
            ((r1.trans r2).trans (Reach.next (F.emitted hxF rfl) ?_)) (by rw [sz2, sz1])
          rw [step_store_some c ist t2 _ _ _ hA2 hin2, ho]
    · rw [if_neg hct]
      simp only [wp_bind]
      refine wp_mono (expr_ok F r E s t L hE hwrr htr hs) ?_
      intro o s1 ⟨hx1, hc1, ho1, hs1⟩
      refine wp_mono (place_ok F l E s1 t L hE hwl htl) ?_
      intro a s2 ⟨hx2, hc2, hat, ⟨⟨sl, hroot⟩, hidx⟩, hs2⟩
      -- the value, then the place
      have hboth : ∀ (ins : Instr) (cur : Nat) (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St)
          (tmps : Array Nat), Ext { s2 with out := s2.out.push ins } sF → SRel c E cur lst env ist →
          tmps.size = f.tmps.size →
          (∀ t2 A, addr c ist t2 a.1 = some A → inBound c ist t2 a.1 = true → ∀ v, opd c ist t2 (sizeOf E.prog t) o = v →
            step c ist t2 ins = .next { ist with mem := wr ist.mem A (sizeOf E.prog t) v } t2) →
          (∀ t2, addr c ist t2 a.1 = none → step c ist t2 ins = .stop (.trap ist)) →
          match Lang.Sem.evalE E.prog lst env r with
          | none => Ends c f s.out.size tmps ist (.trap ist)
          | some v =>
            match Lang.Sem.assign E.prog lst env l v with
            | none => Ends c f s.out.size tmps ist (.trap ist)
            | some (lst', env') => ∃ ist' tmps', Reach c f s.out.size tmps ist (s2.out.size + 1) tmps' ist' ∧
                tmps'.size = tmps.size ∧ SRel c E cur lst' env' ist' ∧ Keep c E cur ist.mem ist'.mem := by
        intro ins cur lst env ist tmps hxF hrel hsz hsome hnone
        have hxF2 : Ext s2 sF := (Ext.emit _ _).trans hxF
        have h1 := hs1 cur lst env ist tmps (hx2.trans hxF2) hrel hsz
        have hb := F.emitted hxF rfl
        cases hev : Lang.Sem.evalE E.prog lst env r with
        | none => simp only [hev] at h1 ⊢; exact h1
        | some v =>
          simp only [hev] at h1 ⊢
          obtain ⟨t1, r1, sz1, ag1, ho⟩ := h1
          have h2 := hs2 cur lst env ist t1 hxF2 hrel (by rw [sz1]; exact hsz)
          cases hel : Lang.Sem.evalE E.prog lst env l with
          | none =>
            rw [assign_none _ _ _ _ _ hel]
            simp only [hel] at h2
            rcases h2 with h2 | h2
            · exact r1.ends h2
            · exact r1.ends (h2.ends (fun t2 _ _ hA => Ends.stop hb (hnone t2 hA) (by simp)))
          | some lv =>
            simp only [hel] at h2
            obtain ⟨t2, r2, sz2, ag2, A, hA, hin, hpl⟩ := h2
            have ho2 : opd c ist t2 (sizeOf E.prog t) o = v.toNat := by
              rw [opd_agree c ist _ (fun t ht => (ho1.1 t ht).2) ag2]
              exact ho
            exact assign_end hpl hrel.size hs hwr (evalE_hasTy E lst env (hrel.typed L) r v t hwrr hev htr)
              ((r1.trans r2).trans (Reach.next hb (hsome t2 A hA hin _ ho2))) (by rw [sz2, sz1])
      unfold storeTo
      cases hi : a.1.idx with
      | none =>
        simp only [hroot, wp_emit]
        refine ⟨hx1.trans (hx2.trans (Ext.emit _ _)), by rw [← hc1, ← hc2], ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        simp only [Array.size_push]
        refine hboth _ cur lst env ist tmps hxF hrel hsz (fun t2 A hA hin v hv => ?_) (fun t2 hA => ?_)
        · rw [addr_static c ist t2 hroot hi] at hA
          cases hA
          rw [step_mov, hv]
          rfl
        · rw [addr_static c ist t2 hroot hi] at hA
          cases hA
      | some ix =>
        simp only [hroot, wp_emit]
        refine ⟨hx1.trans (hx2.trans (Ext.emit _ _)), by rw [← hc1, ← hc2], ?_⟩
        intro cur lst env ist tmps hxF hrel hsz
        simp only [Array.size_push]
        refine hboth _ cur lst env ist tmps hxF hrel hsz (fun t2 A hA hin v hv => ?_) (fun t2 hA => ?_)
        · rw [step_store_some c ist t2 _ _ _ hA hin, hv]
        · exact step_store_none c ist t2 _ _ _ hA
  cases l with
  | var x =>
    simp only [plainSlot, wp_bind, wp_varInfo]
    intro info hinfo
    obtain ⟨sl, hat⟩ := hE.varInfo hinfo
    have hti : info.ty = t := by
      simp only [Env.tyOf, hinfo, Except.ok.injEq] at htl
      exact htl
    subst hti
    simp only [hat, wp_pure]
    refine wp_mono (exprToSlot_ok F L hE r info.ty sl s hwrr htr hs) ?_
    intro _ s1 ⟨hx1, hc1, hs1⟩
    refine ⟨hx1, hc1, ?_⟩
    intro cur lst env ist tmps hxF hrel hsz
    have h1 := hs1 cur lst env ist tmps hxF hrel hsz
    obtain ⟨_, lv, _, hlv, _⟩ := hrel.var L hinfo
    have hpl := PlaceAt.var L hrel hinfo hat hlv
    cases hev : Lang.Sem.evalE E.prog lst env r with
    | none => simp only [hev] at h1 ⊢; exact h1
    | some v =>
      simp only [hev] at h1 ⊢
      obtain ⟨t1, sz1, _, r1⟩ := h1
      rw [setDst_slot] at r1
      exact assign_end hpl hrel.size hs hwr (evalE_hasTy E lst env (hrel.typed L) r v _ hwrr hev htr) r1 sz1
  | field b fld => simp only [plainSlot, wp_pure]; exact hrest
  | index b i => simp only [plainSlot, wp_pure]; exact hrest
  | lit _ _ => simp only [plainSlot, wp_pure]; exact hrest
  | blit _ => simp only [plainSlot, wp_pure]; exact hrest
  | bin _ _ _ => simp only [plainSlot, wp_pure]; exact hrest
  | un _ _ => simp only [plainSlot, wp_pure]; exact hrest
  | cast _ _ => simp only [plainSlot, wp_pure]; exact hrest
  | cond _ _ _ => simp only [plainSlot, wp_pure]; exact hrest

/-! ## Statements without a block inside -/

theorem step_zero (c : Ctx) (ist : St) (tmps : Array Nat) (sl : Slot) (n : Nat) :
    step c ist tmps (.zero sl n) = .next { ist with mem := wr ist.mem (c.layout.addr sl) n 0 } tmps := rfl

theorem step_ret (c : Ctx) (ist : St) (tmps : Array Nat) (v : Option (Nat × Opd)) :
    step c ist tmps (.ret v) = .stop (.ok (v.map fun a => opd c ist tmps a.1 a.2) ist) := rfl

/-- An assignment. -/
theorem assign_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (N : Nat) (rt : Option Ty)
    (l r : Expr) (s : LS)
    (hw : IsPlace l ∧ Writable E l ∧ WT E l ∧ WT E r ∧
      ∃ t, E.tyOf l = .ok t ∧ E.tyOf r = .ok t ∧ t.isScalar = true) :
    wp (do IR.assign l r; read) E (SPost c f sF N rt E (.assign l r) s) s := by
  simp only [wp_bind, wp_read]
  refine wp_mono (assign_sem F L hE l r s hw) ?_
  intro _ s1 ⟨hx1, hc1, hs1⟩
  refine ⟨hx1, rfl, by rw [hc1]; exact Nat.le_refl _, ?_⟩
  intro n lst env ist tmps hn hxF hrel hsz hend
  cases n with
  | zero => rw [Lang.Sem.execS]; trivial
  | succ k =>
    simp only [Lang.Sem.execS]
    have h1 := hs1 s.cur lst env ist tmps hxF hrel hsz
    cases hev : Lang.Sem.evalE E.prog lst env r with
    | none => simp only [hev] at h1 ⊢; exact ⟨ist, h1, hrel.world⟩
    | some v =>
      simp only [hev] at h1 ⊢
      cases ha : Lang.Sem.assign E.prog lst env l v with
      | none => simp only [ha] at h1 ⊢; exact ⟨ist, h1, hrel.world⟩
      | some p =>
        obtain ⟨lst', env'⟩ := p
        simp only [ha] at h1 ⊢
        obtain ⟨ist', t', r1, sz1, hrel', hkeep⟩ := h1
        exact ⟨ist', t', r1, sz1, by rw [hc1]; exact hrel', hkeep⟩

/-- `break`. -/
theorem brk_ok (F : Final c fn f sF) {E : Env} (N : Nat) (rt : Option Ty) (s : LS) :
    wp brkStmt E (SPost c f sF N rt E .brk s) s := by
  unfold brkStmt
  simp only [wp_bind, wp_read]
  cases hl : E.loopEnd with
  | none => exact trivial
  | some l =>
    simp only [wp_bind, wp_emit, wp_pure]
    refine ⟨Ext.emit _ _, rfl, Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      obtain ⟨i, hi⟩ := hend l hl
      exact ⟨l, i, ist, tmps, hl, hi, Reach.goto (F.emitted hxF rfl) (step_jmp c ist tmps l) (F.label hi), rfl, hrel,
        Keep.refl _⟩

/-- `return`. -/
theorem ret_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (N : Nat) (rt : Option Ty)
    (v : Option Expr) (s : LS)
    (hw : match v with
      | none => rt = none
      | some e => WT E e ∧ ∃ t, rt = some t ∧ E.tyOf e = .ok t ∧ t.isScalar = true) :
    wp (retStmt v) E (SPost c f sF N rt E (.ret v) s) s := by
  unfold retStmt
  cases v with
  | none =>
    simp only [wp_bind, wp_emit, wp_read]
    refine ⟨Ext.emit _ _, rfl, Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      refine ⟨ist, Ends.stop (F.emitted hxF rfl) (step_ret c ist tmps none) (by simp), hrel.gs, KeepOut.refl _ _ _ _, ?_⟩
      simp only at hw
      subst hw
      rfl
  | some e =>
    obtain ⟨hwe, t, hrt, hte, hs⟩ := hw
    simp only [wp_bind, wp_tyOf, wp_size]
    intro t' ht'
    rw [hte] at ht'
    cases ht'
    refine wp_mono (expr_ok F e E s t L hE hwe hte hs) ?_
    intro o s1 ⟨hx1, hc1, ho1, hs1⟩
    simp only [wp_emit, wp_read]
    refine ⟨hx1.trans (Ext.emit _ _), rfl, by rw [hc1]; exact Nat.le_refl _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      have h1 := hs1 s.cur lst env ist tmps ((Ext.emit _ _).trans hxF) hrel hsz
      cases hev : Lang.Sem.evalE E.prog lst env e with
      | none => simp only [hev] at h1 ⊢; exact ⟨ist, h1, hrel.world⟩
      | some x =>
        simp only [hev] at h1 ⊢
        refine ⟨ist, h1.ends (fun t1 _ _ ho => ?_), hrel.gs, KeepOut.refl _ _ _ _, ?_⟩
        · have := Ends.stop (c := c) (F.emitted hxF rfl) (step_ret c ist t1 (some (sizeOf E.prog t, o))) (by simp)
          simpa only [Option.map_some, ho] using this
        · subst hrt
          exact ⟨x, rfl, evalE_hasTy E lst env (hrel.typed L) e x t hwe hev hte⟩

/-- A declaration. -/
theorem decl_ok (F : Final c fn f sF) {E : Env} (L : LayOK E.prog c) (hE : EnvOK E) (hfn : E.fn = fn) (N : Nat)
    (rt : Option Ty) (x : String) (ty : Ty) (init : Option Expr) (s : LS)
    (hw : TyOK E.prog ty ∧
      (match init with
       | some e => WT E e ∧ E.tyOf e = .ok ty ∧ ty.isScalar = true
       | none => True)) :
    wp (declStmt x ty init) E (SPost c f sF N rt E (.decl x ty init) s) s := by
  obtain ⟨hty, hinit⟩ := hw
  unfold declStmt
  simp only [wp_bind, wp_read, wp_size, wp_allocLocal]
  -- the value is in the new bytes: the states are related
  have hpush : ∀ (lst : Lang.Sem.St) (env : Lang.Sem.Env) (ist : St) (s2 : LS) (v : Val) (m' : ByteArray),
      Ext { s with cur := s.cur + sizeOf E.prog ty, max := Nat.max s.max (s.cur + sizeOf E.prog ty) } s2 →
      Ext s2 sF → SRel c E s.cur lst env ist → HasTy E.prog ty v → m'.size = 65536 →
      (∀ A, A < fbase c E.fn + s.cur ∨ fbase c E.fn + s.cur + sizeOf E.prog ty ≤ A →
        m'.get! A = ist.mem.get! A) →
      Holds E.prog m' (fbase c E.fn + s.cur) ty v →
      SRel c { E with vars := (x, { ty, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars }
        (s.cur + sizeOf E.prog ty) lst ((x, v) :: env) { ist with mem := m' } ∧ Keep c E s.cur ist.mem m' := by
    intro lst env ist s2 v m' hx2 hxF hrel hv hsz' hm hh
    obtain ⟨f', hf', hfit⟩ := F.fit hfn (hx2.trans hxF) (k := s.cur + sizeOf E.prog ty) (Nat.le_max_right _ _)
    exact ⟨hrel.push L x ty v hsz' hty hv ⟨f', hf', hfit⟩ hm hh,
      Keep.above hf' hfit (fun A hA => hm A (by omega))⟩
  -- the frame is inside memory
  have hbound : ∀ (s2 : LS),
      Ext { s with cur := s.cur + sizeOf E.prog ty, max := Nat.max s.max (s.cur + sizeOf E.prog ty) } s2 →
      Ext s2 sF → fbase c E.fn + s.cur + sizeOf E.prog ty ≤ 65536 := by
    intro s2 hx2 hxF
    obtain ⟨f', hf', hfit⟩ := F.fit hfn (hx2.trans hxF) (k := s.cur + sizeOf E.prog ty) (Nat.le_max_right _ _)
    have := L.fbound _ _ hf'
    omega
  cases init with
  | some e =>
    obtain ⟨hwe, hte, hs⟩ := hinit
    simp only []
    refine wp_mono (exprToSlot_ok F L hE e ty _ _ hwe hte hs) ?_
    intro _ s2 ⟨hx2, hc2, hs2⟩
    rw [wp_pure]
    refine ⟨(Ext.alloc s _).trans hx2, rfl, by rw [hc2]; exact Nat.le_add_right _ _, ?_⟩
    intro n lst env ist tmps hn hxF hrel hsz hend
    cases n with
    | zero => rw [Lang.Sem.execS]; trivial
    | succ k =>
      simp only [Lang.Sem.execS]
      have h2 := hs2 s.cur lst env ist tmps hxF hrel hsz
      cases hev : Lang.Sem.evalE E.prog lst env e with
      | none => simp only [hev] at h2 ⊢; exact ⟨ist, h2, hrel.world⟩
      | some v =>
        simp only [hev] at h2 ⊢
        obtain ⟨t1, sz1, _, r1⟩ := h2
        rw [setDst_slot, addr_frame] at r1
        have hv := evalE_hasTy E lst env (hrel.typed L) e v ty hwe hev hte
        have hb := hbound s2 hx2 hxF
        have hms := hrel.size
        obtain ⟨hrel', hkeep⟩ := hpush lst env ist s2 v
          (wr ist.mem (fbase c E.fn + s.cur) (sizeOf E.prog ty) v.toNat) hx2 hxF hrel hv (by rw [wr_size]; exact hms)
          (fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA)
          (by rw [holds_scalar hs, rd_wr _ _ _ _ (by omega) (by omega), Nat.mod_eq_of_lt (toNat_lt hv hs)])
        exact ⟨_, t1, r1, sz1, by rw [hc2]; exact hrel', hkeep⟩
  | none =>
    -- zeroes
    have hzero : ∀ (ins : Instr),
        (∀ (ist : St) (tmps : Array Nat), step c ist tmps ins = .next
          { ist with mem := wr ist.mem (fbase c E.fn + s.cur) (sizeOf E.prog ty) 0 } tmps) →
        wp (emit ins) { E with } (fun _ s2 => SPost c f sF N rt E (.decl x ty none) s
          { E with vars := (x, { ty, at_ := .static { area := .frame E.fn, off := s.cur } }) :: E.vars } s2)
          { s with cur := s.cur + sizeOf E.prog ty, max := Nat.max s.max (s.cur + sizeOf E.prog ty) } := by
      intro ins hstep
      rw [wp_emit]
      have hx2 := Ext.emit { s with cur := s.cur + sizeOf E.prog ty, max := Nat.max s.max (s.cur + sizeOf E.prog ty) } ins
      refine ⟨(Ext.alloc s _).trans hx2, rfl, Nat.le_add_right _ _, ?_⟩
      intro n lst env ist tmps hn hxF hrel hsz hend
      cases n with
      | zero => rw [Lang.Sem.execS]; trivial
      | succ k =>
        simp only [Lang.Sem.execS]
        have hb := hbound _ hx2 hxF
        have hms := hrel.size
        simp only [Array.size_push]
        obtain ⟨hrel', hkeep⟩ := hpush lst env ist _ (zeroOf E.prog ty)
          (wr ist.mem (fbase c E.fn + s.cur) (sizeOf E.prog ty) 0) hx2 hxF hrel (hasTy_zero _ _ hty)
          (by rw [wr_size]; exact hms) (fun A hA => wr_get_out _ _ _ _ _ (by omega) (by omega) hA)
          (holds_zero _ _ hty _ _ hb (fun A a1 a2 => wr_zero_get _ _ _ _ (by omega) (by omega) a1 a2))
        exact ⟨_, tmps, Reach.next (F.emitted hxF rfl) (hstep ist tmps), rfl, hrel', hkeep⟩
    simp only []
    by_cases hsc : ty.isScalar = true
    · rw [if_pos hsc]
      refine wp_mono (hzero _ (fun ist tmps => ?_)) (fun _ s2 h => by rw [wp_pure]; exact h)
      rw [step_mov, setDst_slot, addr_frame, opd_const]
      simp [modN, Step.set]
    · rw [if_neg hsc]
      refine wp_mono (hzero _ (fun ist tmps => ?_)) (fun _ s2 h => by rw [wp_pure]; exact h)
      rw [step_zero, addr_frame]

end

end Ember.Proof.IRSim
