import Ember.Proof.IRCheck

/-!
# Ember.Proof.IRInit — the initial states are related (plan M7.1)

`IR.initial` stores the bytes `lowerGlobal` made of every global's
initial value at the global's address.  `init_rel`: the memory that
gives holds, for every global, the value `Lang.initOf` gives.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.CSim (HasTy HasTy0 FieldOK TyOK hasTy_zero hasTy_mask mask_toNat mask_lt mod_pow_bits)

/-! ## Bytes in memory -/

@[simp] theorem storeBytes_size : ∀ (bs : List UInt8) (m : ByteArray) (a : Nat), (storeBytes m a bs).size = m.size
  | [], _, _ => rfl
  | b :: bs, m, a => by rw [storeBytes, storeBytes_size bs, size_set]

theorem storeBytes_get : ∀ (bs : List UInt8) (m : ByteArray) (a x : Nat), a + bs.length ≤ m.size →
    (storeBytes m a bs).get! x = if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else m.get! x
  | [], m, a, x, _ => by
    rw [storeBytes, if_neg (by simp)]
  | b :: bs, m, a, x, h => by
    simp only [List.length_cons] at h
    rw [storeBytes, storeBytes_get bs _ (a + 1) x (by rw [size_set]; omega), get_set]
    by_cases h1 : a + 1 ≤ x ∧ x < a + 1 + bs.length
    · rw [if_pos h1, if_pos (by simp only [List.length_cons]; omega)]
      rw [show x - a = (x - (a + 1)) + 1 by omega]
      rfl
    · rw [if_neg h1]
      by_cases h2 : a = x
      · subst h2
        rw [if_pos ⟨rfl, by omega⟩, if_pos (by simp only [List.length_cons]; omega)]
        simp
      · rw [if_neg (by omega), if_neg (by simp only [List.length_cons]; omega)]

/-- The address of a global in a layout. -/
def gAt (l : Layout) (g : IR.Global) : Nat := (l.globals.lookup g.name).getD 0

/-- The region of a global holds `x`. -/
def InG (l : Layout) (g : IR.Global) (x : Nat) : Prop := gAt l g ≤ x ∧ x < gAt l g + g.size

/-- **The initial memory**: the bytes of every global with an initial
value, and nothing else changed. -/
theorem initMem_get (l : Layout) : ∀ (gs : List IR.Global) (m : ByteArray), m.size = 65536 →
    (∀ g, g ∈ gs → gAt l g + g.size ≤ 65536 ∧ ∀ b, g.init = some b → b.size = g.size) →
    gs.Pairwise (fun g h => ∀ x, InG l g x → ¬ InG l h x) →
    (initMem l gs m).size = 65536 ∧
      (∀ x, (∀ g, g ∈ gs → ¬ InG l g x) → (initMem l gs m).get! x = m.get! x) ∧
      ∀ g, g ∈ gs → ∀ x, InG l g x → (initMem l gs m).get! x =
        (match g.init with
         | some b => b.data.toList.getD (x - gAt l g) 0
         | none => m.get! x)
  | [], m, hm, _, _ => ⟨hm, fun _ _ => rfl, fun g hg => by simp at hg⟩
  | g :: gs, m, hm, hb, hp => by
    obtain ⟨hpg, hps⟩ := List.pairwise_cons.mp hp
    have hbg := hb g (by simp)
    -- the first global
    have hstep : ∃ m1 : ByteArray, initMem l (g :: gs) m = initMem l gs m1 ∧ m1.size = 65536 ∧
        (∀ x, ¬ InG l g x → m1.get! x = m.get! x) ∧
        (∀ x, InG l g x → m1.get! x = (match g.init with
          | some b => b.data.toList.getD (x - gAt l g) 0
          | none => m.get! x)) := by
      cases hi : g.init with
      | none =>
        refine ⟨m, ?_, hm, fun _ _ => rfl, fun _ _ => rfl⟩
        simp only [initMem, List.foldl_cons, hi]
      | some b =>
        have hsz := hbg.2 b hi
        have hlen : b.data.toList.length = g.size := by rw [← hsz, Array.length_toList]; rfl
        refine ⟨storeBytes m (gAt l g) b.data.toList, ?_, by rw [storeBytes_size]; exact hm, fun x hx => ?_, fun x hx => ?_⟩
        · simp only [initMem, List.foldl_cons, hi, gAt]
        · rw [storeBytes_get _ _ _ _ (by rw [hlen, hm]; exact hbg.1), if_neg (by rw [hlen]; exact hx)]
        · rw [storeBytes_get _ _ _ _ (by rw [hlen, hm]; exact hbg.1), if_pos (by rw [hlen]; exact hx)]
    obtain ⟨m1, he, hm1, hout, hin⟩ := hstep
    obtain ⟨h1, h2, h3⟩ := initMem_get l gs m1 hm1 (fun h hh => hb h (by simp [hh])) hps
    rw [he]
    refine ⟨h1, fun x hx => ?_, fun h hh x hx => ?_⟩
    · rw [h2 x (fun h hh => hx h (by simp [hh])), hout x (hx g (by simp))]
    · rcases List.mem_cons.mp hh with rfl | hh'
      · rw [h2 x (fun k hk hkx => hpg k hk x hx hkx)]
        exact hin x hx
      · rw [h3 h hh' x hx]
        cases h.init with
        | some b => rfl
        | none => exact hout x (fun hgx => hpg h hh' x hgx hx)

/-! ## Numbers and their bytes -/

/-- A number read from its base-256 digits. -/
theorem rd_digits (m : ByteArray) : ∀ (e A v : Nat), A + e ≤ 65536 →
    (∀ k, k < e → (m.get! (A + k)).toNat = v / 256 ^ k % 256) → rd m A e = v % 256 ^ e
  | 0, A, v, _, _ => by simp [rd, Nat.mod_one]
  | e + 1, A, v, hA, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    rw [rd, Nat.mod_eq_of_lt (by omega), h0,
      rd_digits m e (A + 1) (v / 256) (by omega) (fun k hk => by
        have := h (k + 1) (by omega)
        rw [show A + 1 + k = A + (k + 1) by omega, this, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]),
      Nat.pow_succ', Nat.mod_mul]

theorem bytesLE_length (v e : Nat) : (bytesLE v e).length = e := by simp [bytesLE]

theorem bytesLE_getD (v e k : Nat) (hk : k < e) : ((bytesLE v e).getD k 0).toNat = v / 256 ^ k % 256 := by
  simp only [bytesLE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, pow256]
  omega

/-- The bytes of the `i`-th of several numbers. -/
theorem flat_getD (e : Nat) : ∀ (vs : List Nat) (i k : Nat), k < e →
    ((vs.flatMap (bytesLE · e)).getD (i * e + k) 0).toNat = vs.getD i 0 / 256 ^ k % 256
  | [], i, k, _ => by simp
  | v :: vs, 0, k, hk => by
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [bytesLE_length]; exact hk)]
    have := bytesLE_getD v e k hk
    simp only [List.getD_eq_getElem?_getD] at this
    simpa using this
  | v :: vs, i + 1, k, hk => by
    have ih := flat_getD e vs i k hk
    simp only [List.flatMap_cons, List.getD_eq_getElem?_getD] at ih ⊢
    rw [List.getElem?_append_right (by rw [bytesLE_length, Nat.add_mul]; omega), bytesLE_length,
      show (i + 1) * e + k - e = i * e + k by rw [Nat.add_mul]; omega]
    simpa using ih

/-! ## What `lowerGlobal` stores -/

/-- The size of an element, for an array; of the value itself otherwise. -/
def elemOf (lp : Prog) : Ty → Nat
  | .arr el _ => sizeOf lp el
  | t => sizeOf lp t

theorem all_zero_getD : ∀ (bs : List UInt8) (j : Nat), bs.all (· == 0) = true → bs.getD j 0 = 0
  | [], _, _ => by simp
  | b :: bs, 0, h => by simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h; simpa using h.1
  | b :: bs, j + 1, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using all_zero_getD bs j h.2

theorem append_zeros_getD (bs : List UInt8) (n j : Nat) : (bs ++ List.replicate n 0).getD j 0 = bs.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : j < bs.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (show bs.length ≤ j by omega)]
    by_cases h2 : j - bs.length < n
    · simp [List.getElem?_replicate, h2]
    · simp [List.getElem?_replicate, h2]

theorem lowerGlobal_init (lp : Prog) (g : Global) :
    (lowerGlobal lp g).init =
      if ((g.init.flatMap (bytesLE · (elemOf lp g.ty))).take (sizeOf lp g.ty)).all (· == 0) = true then none
      else some (ByteArray.mk (((g.init.flatMap (bytesLE · (elemOf lp g.ty))).take (sizeOf lp g.ty)) ++
        List.replicate (sizeOf lp g.ty -
          ((g.init.flatMap (bytesLE · (elemOf lp g.ty))).take (sizeOf lp g.ty)).length) 0).toArray) := by
  obtain ⟨name, ty, init, cst⟩ := g
  cases ty <;> rfl

/-- The bytes of a global, as `lowerGlobal` makes them. -/
theorem lowerGlobal_bytes (lp : Prog) (g : Global) :
    (∀ b, (lowerGlobal lp g).init = some b → b.size = sizeOf lp g.ty) ∧
    ∀ j, j < sizeOf lp g.ty →
      (match (lowerGlobal lp g).init with
       | some b => b.data.toList.getD j 0
       | none => 0) = (g.init.flatMap (bytesLE · (elemOf lp g.ty))).getD j 0 := by
  have htake : ∀ j, j < sizeOf lp g.ty →
      ((g.init.flatMap (bytesLE · (elemOf lp g.ty))).take (sizeOf lp g.ty)).getD j 0 =
        (g.init.flatMap (bytesLE · (elemOf lp g.ty))).getD j 0 := by
    intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj, if_true]
  rw [lowerGlobal_init]
  by_cases hz : ((g.init.flatMap (bytesLE · (elemOf lp g.ty))).take (sizeOf lp g.ty)).all (· == 0) = true
  · rw [if_pos hz]
    refine ⟨fun b hb => (by cases hb), fun j hj => ?_⟩
    rw [← htake j hj, all_zero_getD _ j hz]
  · rw [if_neg hz]
    refine ⟨fun b hb => ?_, fun j hj => ?_⟩
    · simp only [Option.some.injEq] at hb
      subst hb
      simp only [ByteArray.size, List.size_toArray, List.length_append, List.length_replicate, List.length_take]
      omega
    · simp only [List.toList_toArray]
      rw [append_zeros_getD, htake j hj]

/-! ## The values -/

/-- What the proofs need of a global's initial value. -/
def GlobalOK (p : Prog) (g : Global) : Prop :=
  TyOK p g.ty ∧
    match g.ty with
    | .int _ => g.init.length ≤ 1
    | .bool => g.init.length ≤ 1 ∧ ∀ v, v ∈ g.init → v ≤ 1
    | .arr .bool _ => ∀ v, v ∈ g.init → v ≤ 1
    | .arr _ _ => True
    | .record _ => g.init = []

/-- The `i`-th of several numbers stored one after the other. -/
theorem rd_elem (m : ByteArray) (a : Nat) (vs : List Nat) (e i size : Nat)
    (hreg : ∀ j, j < size → m.get! (a + j) = (vs.flatMap (bytesLE · e)).getD j 0) (hi : (i + 1) * e ≤ size)
    (ha : a + size ≤ 65536) : rd m (a + i * e) e = vs.getD i 0 % 256 ^ e := by
  rw [Nat.add_mul, Nat.one_mul] at hi
  refine rd_digits m e (a + i * e) (vs.getD i 0) (by omega) (fun k hk => ?_)
  rw [show a + i * e + k = a + (i * e + k) by omega, hreg _ (by omega)]
  exact flat_getD e vs i k hk

theorem getD_le_one (vs : List Nat) (h : ∀ v, v ∈ vs → v ≤ 1) (i : Nat) : vs.getD i 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : vs[i]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hv)

/-- **The bytes `lowerGlobal` stores are the value `initOf` gives.** -/
theorem holds_init (lp : Prog) (g : Global) (hok : GlobalOK lp g) (m : ByteArray) (a : Nat)
    (ha : a + sizeOf lp g.ty ≤ 65536)
    (hreg : ∀ j, j < sizeOf lp g.ty → m.get! (a + j) = (g.init.flatMap (bytesLE · (elemOf lp g.ty))).getD j 0) :
    Holds lp m a g.ty (initOf lp g) ∧ HasTy lp g.ty (initOf lp g) := by
  obtain ⟨name, ty, init, cst⟩ := g
  obtain ⟨hty, hinit⟩ := hok
  simp only at hty hinit ha hreg ⊢
  cases ty with
  | int w =>
    have h0 := rd_elem m a init (w.bits / 8) 0 (w.bits / 8) hreg (by omega) ha
    simp only [Nat.zero_mul, Nat.add_zero, pow256, bits8] at h0
    rcases init with _ | ⟨v, _ | ⟨v2, r⟩⟩
    · refine ⟨?_, ⟨rfl, Nat.two_pow_pos _⟩⟩
      show rd m a (w.bits / 8) = _
      rw [h0]
      simp [initOf, zeroOf, Val.toNat]
    · refine ⟨?_, hasTy_mask _ _ _⟩
      show rd m a (w.bits / 8) = _
      rw [h0]
      simp only [initOf, Val.toNat, mask_toNat, UInt64.toNat_ofNat', List.getD_cons_zero]
      exact (mod_pow_bits w v).symm
    · simp at hinit
  | bool =>
    have h0 := rd_elem m a init 1 0 1 hreg (by omega) ha
    simp only [Nat.zero_mul, Nat.add_zero, Nat.pow_one] at h0
    rcases init with _ | ⟨v, _ | ⟨v2, r⟩⟩
    · refine ⟨?_, trivial⟩
      show rd m a 1 = _
      rw [h0]
      simp [initOf, zeroOf, Val.toNat]
    · refine ⟨?_, trivial⟩
      show rd m a 1 = _
      rw [h0]
      have hv := hinit.2 v (by simp)
      simp only [initOf, Val.toNat, List.getD_cons_zero]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl <;> rfl
    · simp at hinit
  | arr el n =>
    cases el with
    | int w =>
      refine ⟨?_, ⟨by simp [initOf], fun x hx => ?_⟩⟩
      · simp only [initOf, Holds, Holds0]
        intro i hi
        have hi' : i < n := by simpa using hi
        have := rd_elem m a init (w.bits / 8) i (n * (w.bits / 8)) hreg (Nat.mul_le_mul_right _ (by omega)) ha
        simp only [pow256, bits8] at this
        simp only [sizeOf0, this, Array.getElem_map, Array.getElem_range, Val.toNat, mask_toNat, UInt64.toNat_ofNat']
        exact (mod_pow_bits w _).symm
      · simp only [initOf, Array.mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact ⟨rfl, mask_lt _ _⟩
    | bool =>
      refine ⟨?_, ⟨by simp [initOf], fun x hx => ?_⟩⟩
      · simp only [initOf, Holds, Holds0]
        intro i hi
        have hi' : i < n := by simpa using hi
        have := rd_elem m a init 1 i (n * 1) hreg (Nat.mul_le_mul_right _ (by omega)) ha
        simp only [Nat.pow_one, Nat.mul_one] at this
        simp only [sizeOf0, Nat.mul_one, this, Array.getElem_map, Array.getElem_range, Val.toNat]
        have hv := getD_le_one init hinit i
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h | h <;> rw [h] <;> rfl
      · simp only [initOf, Array.mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx
        trivial
    | arr _ _ => simp [TyOK, Ty.isScalar] at hty
    | record _ => simp [TyOK, Ty.isScalar] at hty
  | record r =>
    subst hinit
    have hi : initOf lp { name, ty := .record r, init := [], const := cst } = zeroOf lp (.record r) := rfl
    rw [hi]
    refine ⟨holds_zero lp _ hty m a ha (fun x h1 h2 => ?_), hasTy_zero _ _ hty⟩
    have := hreg (x - a) (by omega)
    rw [show a + (x - a) = x by omega] at this
    simpa using this

theorem lookup_map_name {α : Type} (F : Global → α) : ∀ (l : List Global), (l.map (·.name)).Nodup →
    ∀ g, g ∈ l → (l.map fun g => (g.name, F g)).lookup g.name = some (F g)
  | [], _, _, h => by simp at h
  | x :: t, hn, g, hg => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.map_cons, List.lookup]
    rcases List.mem_cons.mp hg with rfl | hg'
    · simp
    · have hne : (g.name == x.name) = false := by
        cases hc : g.name == x.name
        · rfl
        · rw [beq_iff_eq] at hc
          exact absurd (List.mem_map.mpr ⟨g, hg', hc⟩) hn.1
      simp only [hne]
      exact lookup_map_name F t hn.2 g hg'

/-- **The initial states are related.** -/
theorem init_rel {lp : Prog} {q : IR.Prog} (hq : q.globals = lp.globals.map (lowerGlobal lp))
    (hG : ∀ g, g ∈ lp.globals → GlobalOK lp g) (c : Ctx) (L : LayOK lp c) (inputs : Array Trace.Input) :
    GS c lp (Lang.Sem.initial lp inputs)
      { mem := initMem c.layout q.globals (ByteArray.mk (Array.replicate 65536 0)),
        world := { inputs, framed := lp.framed } } := by
  have hm0 : (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).size = 65536 := by simp [ByteArray.size]
  have hz0 : ∀ x, (ByteArray.mk (Array.replicate 65536 (0 : UInt8))).get! x = 0 := by
    intro x
    simp only [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hat : ∀ g : Global, gAt c.layout (lowerGlobal lp g) = gaddr c g.name := by
    intro g
    simp [gAt, gaddr, Layout.addr, Layout.areaAddr, lowerGlobal_name]
  have hmem := initMem_get c.layout q.globals _ hm0
    (by
      intro G hGm
      rw [hq, List.mem_map] at hGm
      obtain ⟨g, hg, rfl⟩ := hGm
      rw [hat, lowerGlobal_size]
      exact ⟨L.gbound g hg, (lowerGlobal_bytes lp g).1⟩)
    (by
      rw [hq, List.pairwise_map]
      have hnd : lp.globals.Pairwise (fun a b => a.name ≠ b.name) := List.pairwise_map.mp L.names
      refine hnd.imp_of_mem (fun {a b} ha hb hne x hx hx' => ?_)
      unfold InG at hx hx'
      rw [hat, lowerGlobal_size] at hx hx'
      have := L.gapart a b ha hb hne
      omega)
  refine ⟨hmem.1, rfl, ⟨by simp [Lang.Sem.initial, List.map_map], fun g hg => ?_⟩⟩
  have hok := hG g hg
  have hGm : lowerGlobal lp g ∈ q.globals := by rw [hq]; exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have hreg : ∀ j, j < sizeOf lp g.ty →
      (initMem c.layout q.globals (ByteArray.mk (Array.replicate 65536 0))).get! (gaddr c g.name + j) =
        (g.init.flatMap (bytesLE · (elemOf lp g.ty))).getD j 0 := by
    intro j hj
    have h1 := hmem.2.2 _ hGm (gaddr c g.name + j) (by unfold InG; rw [hat, lowerGlobal_size]; omega)
    have h2 := (lowerGlobal_bytes lp g).2 j hj
    rw [h1, hat, ← h2]
    cases (lowerGlobal lp g).init with
    | none => exact hz0 _
    | some b => simp
  obtain ⟨hh, hv⟩ := holds_init lp g hok _ (gaddr c g.name) (L.gbound g hg) hreg
  exact ⟨initOf lp g, lookup_map_name (initOf lp) lp.globals L.names g hg, hok.1, hv, hh, fun _ => rfl⟩

end Ember.Proof.IRSim
