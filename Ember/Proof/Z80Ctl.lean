import Ember.Proof.Z80CmpI

/-!
# Ember.Proof.Z80Ctl — jumps, branches and labels of the IR (plan M7.3)

The generator records, at every jump, what the registers held, and at
every label what it takes them to hold from there on; `Codegen.jumpsOk`
checks the two against each other once the function is generated.  So:

* `jump_le`: what is assumed after a label was held at every jump to it;
* `Rel.weaken`: the states still agree when the tracker claims less;
* `jmp_ok`, `br_ok`, `label_ok`: the code of the three instructions.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- Everything `r'` claims, `r` claims. -/
def RegsLe (r' r : Regs) : Prop :=
  (∀ o, o ∈ r'.a → o ∈ r.a) ∧ (∀ o, o ∈ r'.hl → o ∈ r.hl) ∧ ∀ n o, r'.acc = some (n, o) → r.acc = some (n, o)

theorem RegsLe.refl (r : Regs) : RegsLe r r := ⟨fun _ h => h, fun _ h => h, fun _ _ h => h⟩

theorem Regs.le_spec {x y : Regs} (h : x.le y = true) : RegsLe x y := by
  simp only [Regs.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun n o hn => ?_⟩
  rcases h3 with h3 | h3
  · rw [hn] at h3
    cases h3
  · rw [hn] at h3
    exact (beq_iff_eq.mp h3).symm

theorem lookup_of_mem {α : Type} : ∀ (l : List (Nat × α)), (l.map (·.1)).Nodup → ∀ k v, (k, v) ∈ l →
    l.lookup k = some v
  | [], _, _, _, h => by cases h
  | (k0, v0) :: t, hn, k, v, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with he | hm
    · cases he
      simp [List.lookup]
    · have hne : (k == k0) = false := by
        cases hk : k == k0
        · rfl
        · rw [beq_iff_eq] at hk
          subst hk
          exact absurd (List.mem_map.mpr ⟨(k, v), hm, rfl⟩) hn.1
      simp only [List.lookup, hne]
      exact lookup_of_mem t hn.2 k v hm

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS} {dt : Nat → Prop} {fr : Fr}

/-- The states still agree when the tracker claims less. -/
theorem Rel.weaken {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (h : RegsLe regs' regs) : Rel Z E fr dt regs' ist tmps s :=
  R.regs_only rfl rfl rfl rfl (fun o ho hown => R.ra o (h.1 o ho) hown) (fun o ho hown => R.rhl o (h.2.1 o ho) hown)
    (fun sl hsl hown => R.ina sl (h.1 _ hsl) hown) (fun sl hsl hown => R.inhl sl (h.2.1 _ hsl) hown) h.2.2

/-- What is assumed after a label was held at every recorded jump to it. -/
theorem jump_le (hJ : jumpsOk sF = true) {l : Nat} {r : Regs} (h : (l, r) ∈ sF.jumps) :
    ∃ rl, sF.labelRegs.lookup l = some rl ∧ RegsLe rl r := by
  simp only [jumpsOk, Bool.and_eq_true, List.all_eq_true] at hJ
  have := hJ.1 (l, r) h
  simp only at this
  cases hl : sF.labelRegs.lookup l with
  | none => simp [hl] at this
  | some rl =>
    simp only [hl] at this
    exact ⟨rl, rfl, Regs.le_spec this⟩

/-- What was recorded at a label is what is looked up for it. -/
theorem label_lookup (hJ : jumpsOk sF = true) {l : Nat} {rl : Regs} (h : (l, rl) ∈ sF.labelRegs) :
    sF.labelRegs.lookup l = some rl := by
  simp only [jumpsOk, Bool.and_eq_true, decide_eq_true_eq] at hJ
  exact lookup_of_mem _ hJ.2 l rl h

/-- **Arriving at a label**, by a jump or from the instruction before:
the states agree for what the generator assumes after the label. -/
theorem arrive (hJ : jumpsOk sF = true) {l : Nat} {r rl : Regs} (hj : (l, r) ∈ sF.jumps)
    (hl : (l, rl) ∈ sF.labelRegs) {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt r ist tmps s) : Rel Z E fr dt rl ist tmps s := by
  obtain ⟨rl', h1, h2⟩ := jump_le hJ hj
  rw [label_lookup hJ hl] at h1
  cases h1
  exact R.weaken h2

/-- The name of a label of the function in the image. -/
def lname (E : GEnv) (l : Nat) : String := s!"l_{sanitize E.fn.name}_{l}"

theorem wpg_localLabel (l : Nat) (s : GS) (Q : String → GS → Prop) :
    wpg (localLabel l) E Q s ↔ Q (lname E l) s := Iff.rfl

theorem wpg_jumpTo (l : Nat) (s : GS) (Q : Unit → GS → Prop)
    (h : ∀ s1 : GS, s1.out = s.out → s1.regs = s.regs → s1.labelRegs = s.labelRegs →
      s1.jumps = (l, s.regs) :: s.jumps → Q () s1) : wpg (jumpTo l) E Q s := by
  unfold jumpTo
  rw [wpg_modify]
  exact h _ rfl rfl rfl rfl

/-- **`jmp`**: the CPU is at the label's item, the states agreeing as at the jump. -/
theorem jmp_ok (ok : Z.OK) (F : GFinal Z base sF) (l : Nat) (s0 : GS) :
    wpg (genInstr (.jmp l)) E (fun _ s1 => GExt s0 s1 ∧ (l, s0.regs) ∈ s1.jumps ∧
      (GExt s1 sF → ∀ fr ist tmps s j, Z.items[j]? = some (.label (lname E l)) →
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ At Z.addrs j s' ∧ Rel Z E fr dt s0.regs ist tmps s')) s0 := by
  simp only [genInstr, wpg_bind, wpg_localLabel, wpg_ins]
  refine wpg_jumpTo l _ _ (fun s1 ho hr hl hj => ?_)
  rw [wpg_modify]
  refine ⟨⟨by simp [ho], by simp [hj], by simp [hl]⟩, by simp [hj], fun hx fr ist tmps s j hlab R hat => ?_⟩
  have hk : Z.items[base + s0.out.size]? = some (.ins ⟨.jp, [.imm (.sym (lname E l))]⟩) :=
    F.at hx (by simp [ho])
  obtain ⟨s', st, at', _, hS, hK⟩ := jp_step ok hk hlab R.mach hat
  exact ⟨s', st, at', R.keep hS hK.1 (hl_congr hK.2.2.2.2.2.2.1 hK.2.2.2.2.2.2.2.1)⟩

/-- **`br`**: at the label's item when the comparison holds, at the next item when not. -/
theorem br_ok (ok : Z.OK) (F : GFinal Z base sF) (op : Cmp) (n : Nat) (hn : n = 1 ∨ n = 2) (a b : Opd) (l : Nat)
    (s0 : GS) :
    wpg (genInstr (.br op n a b l)) E (fun _ s1 => GExt s0 s1 ∧ (l, s1.regs) ∈ s1.jumps ∧
      (GExt s1 sF → ∀ fr ist tmps s j, Z.items[j]? = some (.label (lname E l)) → Rd Z E dt n a → Rd Z E dt n b →
        Rel Z E fr dt s0.regs ist tmps s → At Z.addrs (base + s0.out.size) s →
        ∃ s', Steps Z.inp s s' ∧ Rel Z E fr dt s1.regs ist tmps s' ∧
          (if IR.cmpOp op (IR.Sem.opd Z.c ist tmps n a) (IR.Sem.opd Z.c ist tmps n b) then At Z.addrs j s'
           else At Z.addrs (base + s1.out.size) s'))) s0 := by
  simp only [genInstr, wpg_bind]
  refine wpg_mono (genFlags_ok (dt := dt) ok F op n hn a b s0) ?_
  intro _ s1 ⟨hx1, hf⟩
  simp only [wpg_localLabel, wpg_ins]
  refine wpg_jumpTo l _ _ (fun s2 ho hr hl hj => ?_)
  refine ⟨hx1.trans ⟨by simp [ho], by simp [hj], by simp [hl]⟩, by rw [hj, hr]; simp,
    fun hx fr ist tmps s j hlab hra hrb R hat => ?_⟩
  have hx1F : GExt { s1 with out := s1.out.push (.ins ⟨.jp, [condOf op, .imm (.sym (lname E l))]⟩) } sF :=
    GExt.trans ⟨by simp [ho], by simp [hj], by simp [hl]⟩ hx
  obtain ⟨s', st1, at1, R1, hfl⟩ := hf ((GExt.push _ _).trans hx1F) trivial fr ist tmps s hra hrb R hat
  have hk : Z.items[base + s1.out.size]? = some (.ins ⟨.jp, [condOf op, .imm (.sym (lname E l))]⟩) :=
    F.at hx1F (by simp)
  obtain ⟨s'', st2, _, hS, hK, hcase⟩ := jp_cc_step ok op hk hlab R1.mach at1
  refine ⟨s'', st1.trans st2, ?_, ?_⟩
  · rw [hr]
    exact R1.keep hS hK.1 (hl_congr hK.2.2.2.2.2.2.1 hK.2.2.2.2.2.2.2.1)
  · rw [cond_of hfl] at hcase
    have hsz : s2.out.size = s1.out.size + 1 := by rw [ho]; simp
    rw [hsz, ← Nat.add_assoc]
    exact hcase

/-- Is the label reached from the instruction before it? -/
def prevFalls (body : Array IR.Instr) (l : Nat) : Bool :=
  (body.findIdx? (· == .label l)).getD 0 == 0 ||
    ((body[(body.findIdx? (· == .label l)).getD 0 - 1]?).map canFall).getD true

/-- **A label**: its item, what the generator assumes after it, and — when
the instruction before can go on to it — the record of that way there. -/
theorem label_ok (l : Nat) (s0 : GS) :
    wpg (genInstr (.label l)) E (fun _ s1 => GExt s0 s1 ∧ s1.out = s0.out.push (.label (lname E l)) ∧
      (l, s1.regs) ∈ s1.labelRegs ∧ (prevFalls E.fn.body l = true → (l, s0.regs) ∈ s1.jumps)) s0 := by
  simp only [genInstr, genLabel, wpg_bind, wpg_localLabel, wpg_modify, wpg_get, wpg_read]
  refine ⟨⟨by simp, ?_, by simp⟩, trivial, by simp, fun h => ?_⟩
  · show s0.jumps <:+ (if _ then _ else _)
    split
    · exact List.suffix_cons _ _
    · exact List.suffix_refl _
  · have h' : ((E.fn.body.findIdx? (· == .label l)).getD 0 == 0 ||
        ((E.fn.body[(E.fn.body.findIdx? (· == .label l)).getD 0 - 1]?).map canFall).getD true) = true := h
    show (l, s0.regs) ∈ (if _ then _ else _)
    rw [if_pos h']
    simp

end

end Ember.Proof.Z80Gen
