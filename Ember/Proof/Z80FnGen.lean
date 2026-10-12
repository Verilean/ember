import Ember.Proof.Z80Fn

/-!
# Ember.Proof.Z80FnGen — the generation of a function gives `FnGen` (plan M7.3)

`genFn_ok`: when `Codegen.genFnCode` ends in the state whose items are
in the image, and `jumpsOk` accepts it, the function has a `FnGen` —
given `FnStatic`, what checks on the program are to establish of the
function (its operands can be read, its destinations written, its body
ends with a jump or a return, …).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The temporaries assigned before the instruction `pc`: those assigned
since the last label. -/
def dtAt (body : Array IR.Instr) : Nat → Nat → Prop
  | 0 => fun _ => False
  | pc + 1 =>
    match body[pc]? with
    | some i => dtNext (dtAt body pc) i
    | none => dtAt body pc

/-- What the function needs of the program. -/
structure FnStatic (Z : ZCtx) (E : GEnv) : Prop where
  need : ∀ pc i, E.fn.body[pc]? = some i → Need Z (envAt E pc i) (dtAt E.fn.body pc) i
  covered : ∀ i, i ∈ E.fn.body.toList → Covered i = true
  falls : ∀ pc i, E.fn.body[pc]? = some i → canFall i = true → pc + 1 < E.fn.body.size
  nonempty : 0 < E.fn.body.size
  labels : ∀ pc l, E.fn.body[pc]? = some (.label l) → E.fn.body.findIdx? (· == .label l) = some pc
  lay : FnLay Z E
  depth : Z.rtK + 2 ≤ Z.depth E.fn.name
  regParam : ∀ n sl, E.fn.regParam = some (n, sl) → (n = 1 ∨ n = 2) ∧ Wr Z E n (.slot sl)

/-- The parameter in a register, as a destination. -/
def regDst (f : IR.Fn) : Option (Nat × Dst) := f.regParam.map fun p => (p.1, Dst.slot p.2)

theorem genFnCode_eq (f : IR.Fn) (isEntry ann : Bool) :
    genFnCode f isEntry ann = (do
      if isEntry then modify fun s => { s with out := s.out.push (.label "f_entry") }
      modify fun s => { s with out := s.out.push (.label (fnLabel f.name)) }
      retStore (regDst f)
      genBody f ann 0 f.body.toList) := by
  unfold genFnCode regDst
  generalize f.regParam = rp
  cases rp with
  | none => rfl
  | some p => rfl

theorem setRet_arg (c : IR.Ctx) (f : IR.Fn) (st : IR.Sem.St) (tmps : Array Nat) (v : Nat) :
    IR.Sem.setRet c st tmps (regDst f) (some v) = (stArg c f st v, tmps) := by
  unfold regDst stArg
  generalize f.regParam = rp
  cases rp with
  | none => rfl
  | some p => rfl

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS}

theorem Chain.ext : ∀ (r : List IR.Instr) (k : Nat) (dt : Nat → Prop) (s s' : GS),
    Chain Z E base sF k dt s r s' → GExt s s'
  | [], _, _, _, _, h => by cases h; exact GExt.refl _
  | _ :: r, k, _, _, _, ⟨_, h1, h2⟩ => h1.ext.trans (Chain.ext r (k + 1) _ _ _ h2)

/-- **The generation of a function.** -/
theorem genFn_ok (ok : Z.OK) (hrt : RtOK Z) (S : FnStatic Z E) (F : GFinal Z base sF) (hJ : jumpsOk sF = true)
    (isEntry ann : Bool) (s0 : GS) (h0 : s0.out = #[]) (hr0 : s0.regs = {}) :
    wpg (genFnCode E.fn isEntry ann) E (fun _ s' => s' = sF → ∃ G : FnGen, G.OK Z E.fn) s0 := by
  have main : ∀ (sa : GS) (jl : Nat), sa.regs = {} → sa.out[jl]? = some (Item.label (fnLabel E.fn.name)) →
      sa.out.size = jl + 1 →
      wpg (do retStore (regDst E.fn); genBody E.fn ann 0 E.fn.body.toList) E
        (fun _ s' => s' = sF → ∃ G : FnGen, G.OK Z E.fn) sa := by
    intro sa jl hra hjl hsz
    simp only [wpg_bind]
    have hsz12 : ∀ n d, regDst E.fn = some (n, d) → n = 1 ∨ n = 2 ∨ n = 4 := by
      intro n d h
      unfold regDst at h
      cases hp : E.fn.regParam with
      | none => rw [hp] at h; cases h
      | some p =>
        rw [hp] at h
        cases h
        rcases (S.regParam p.1 p.2 hp).1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    have hwr : ∀ n d, regDst E.fn = some (n, d) → Wr Z E n d := by
      intro n d h
      unfold regDst at h
      cases hp : E.fn.regParam with
      | none => rw [hp] at h; cases h
      | some p =>
        rw [hp] at h
        cases h
        exact (S.regParam p.1 p.2 hp).2
    refine wpg_mono (retStore_ok (dt := fun _ => False) ok S.lay F hrt.wide S.depth (regDst E.fn) hsz12 sa) ?_
    intro _ sb ⟨hxb, hs⟩
    refine wpg_mono (genBody_ok ok S.lay F hrt S.depth ann E.fn.body.toList 0 (fun _ => False) sb S.covered) ?_
    intro _ s' hch heq
    subst heq
    have hxbF : GExt sb s' := Chain.ext _ _ _ _ _ hch
    obtain ⟨gs, dts, hg, hd, hl, hall⟩ := Chain.fns _ _ _ _ _ hch
    simp only [Nat.zero_add, Array.length_toList, Array.getElem?_toList] at hl hall
    have hdts : ∀ j, j ≤ E.fn.body.size → dts j = dtAt E.fn.body j := by
      intro j
      induction j with
      | zero => intro _; exact hd
      | succ j ih =>
        intro hj
        have hb : E.fn.body[j]? = some E.fn.body[j] := Array.getElem?_eq_getElem (by omega)
        rw [(hall j _ hb).2, ih (by omega)]
        simp only [dtAt, hb]
    refine ⟨⟨E, base, s', gs, dtAt E.fn.body⟩, ⟨rfl, F, hJ, hl, rfl, fun pc i hb => ?_, S.need, S.falls, S.nonempty,
      S.labels, fun st v s ent => ?_⟩⟩
    · have hlt : pc < E.fn.body.size := by
        rcases Nat.lt_or_ge pc E.fn.body.size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hb; cases hb
      obtain ⟨h1, _⟩ := hall pc i hb
      rw [hdts pc (by omega)] at h1
      exact ⟨h1, by simp only [dtAt, hb]⟩
    · -- from the entry to the first instruction
      obtain ⟨ad, hsym, hpc⟩ := ent.pc
      have hk : Z.items[base + jl]? = some (Item.label (fnLabel E.fn.name)) := F.at (hxb.trans hxbF) hjl
      obtain ⟨T, hT, hsymT, _⟩ := label_at ok hk ent.img
      have hTad : T = ad := by
        unfold ZCtx.sym at hsym hsymT
        rw [hsym] at hsymT
        exact (Option.some.inj hsymT).symm
      have hat : At Z.addrs (base + sa.out.size) s := by
        have := at_skip ok.placed hk (fun _ => rfl) ⟨T, hT, by rw [hpc, hTad]⟩
        rw [hsz, ← Nat.add_assoc]
        exact this
      have R0 : Rel Z E ⟨s.sp, s.mem⟩ (fun _ => False) sa.regs st (Array.replicate E.fn.tmps.size 0) s := by
        rw [hra]
        exact ⟨ent.img, ent.run, ent.mem, fun _ h => h.elim, ent.rs, ent.msz, ent.isz, by simp, rfl, ent.room,
          fun _ _ _ => rfl, fun _ _ => rfl, fun o ho => (by cases ho), fun o ho => (by cases ho),
          fun n o h => (by cases h), fun sl h => (by cases h), fun sl h => (by cases h),
          fun n sl h => (by cases h), fun n o h => (by cases h)⟩
      obtain ⟨s', st', hat', R'⟩ := hs hxbF hwr _ st _ s (some v) R0 hat (by
        intro n d h
        unfold regDst at h
        cases hp : E.fn.regParam with
        | none => rw [hp] at h; cases h
        | some p =>
          rw [hp] at h
          cases h
          exact ent.arg p.1 p.2 hp)
      rw [setRet_arg] at R'
      refine ⟨s', st', ?_, ?_⟩
      · show At Z.addrs (base + (gs 0).out.size) s'
        rw [hg]
        exact hat'
      · show Rel Z E _ _ (gs 0).regs _ _ s'
        rw [hg]
        exact R'.dt_none
  rw [genFnCode_eq]
  cases isEntry with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [wpg_bind, wpg_modify]
    exact main _ 0 hr0 (by simp [h0]) (by simp [h0])
  | true =>
    simp only [if_true]
    rw [wpg_bind, wpg_modify, wpg_bind, wpg_modify]
    exact main _ 1 hr0 (by simp [h0]) (by simp [h0])

end

/-- info: 'Ember.Proof.Z80Gen.genFn_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms genFn_ok

end Ember.Proof.Z80Gen
