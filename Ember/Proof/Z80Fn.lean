import Ember.Proof.Z80Ins
import Ember.Proof.IRFuel

/-!
# Ember.Proof.Z80Fn — a function's code does what the function does (plan M7.3)

* `Chain`, `genBody_ok`: the generator's states before and after every
  instruction of a body, each pair with the promise `Ins` of its
  instruction; `Chain.fns` gives them as functions of the index;
* `FnGen`: those states for a function, with what the function needs of
  the program;
* `exec_ok`: from an instruction of the body with the states agreeing,
  the code has the outcome of `IR.Sem.exec` — by induction on the fuel,
  given the same of the functions called with less fuel;
* `fn_ok`: every function, entered as `Entry` says, has the outcome of
  `IR.Sem.callF`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

/-- The environment the `k`-th instruction is generated in. -/
def envAt (E : GEnv) (k : Nat) (i : IR.Instr) : GEnv :=
  { E with next := E.fn.body[k + 1]?, atTarget := targetOf E.fn i }

section
variable {Z : ZCtx} {E : GEnv} {base : Nat} {sF : GS}

theorem wpg_withReader {α : Type} (g : GEnv → GEnv) (m : GM α) (Q : α → GS → Prop) (s : GS) :
    wpg (withReader g m) E Q s ↔ wpg m (g E) Q s := Iff.rfl

/-- The relation looks at the function and its temporaries only. -/
theorem Rel.env {E E' : GEnv} (h1 : E'.fn = E.fn) (h2 : E'.spilled = E.spilled) (h3 : E'.tmpOff = E.tmpOff)
    {fr : Fr} {dt : Nat → Prop} {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) : Rel Z E' fr dt regs ist tmps s := by
  cases E
  cases E'
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨R.img, R.run, R.mem, R.tmp, R.rs, R.msz, R.isz, R.tsz, R.sp, R.room, R.stk, R.out, R.ra, R.rhl, R.racc,
    R.ina, R.inhl, R.inacc, R.nacc⟩

theorem FnLay.env {E E' : GEnv} (h1 : E'.fn = E.fn) (h2 : E'.spilled = E.spilled) (h3 : E'.tmpOff = E.tmpOff)
    (L : FnLay Z E) : FnLay Z E' := by
  cases E
  cases E'
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨L.area, L.bound, L.ram, L.nodata, L.nostack, L.noacc, L.inwr, L.nort, L.apart⟩

theorem Rel.toAt {fr : Fr} {dt : Nat → Prop} {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (k : Nat) (i : IR.Instr) (R : Rel Z E fr dt regs ist tmps s) : Rel Z (envAt E k i) fr dt regs ist tmps s :=
  R.env (E := E) (E' := envAt E k i) rfl rfl rfl

theorem Rel.ofAt {fr : Fr} {dt : Nat → Prop} {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    {k : Nat} {i : IR.Instr} (R : Rel Z (envAt E k i) fr dt regs ist tmps s) : Rel Z E fr dt regs ist tmps s :=
  R.env (E := envAt E k i) (E' := E) rfl rfl rfl

theorem Rel.dt_none {fr : Fr} {dt : Nat → Prop} {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) : Rel Z E fr (fun _ => False) regs ist tmps s :=
  ⟨R.img, R.run, R.mem, fun _ h => h.elim, R.rs, R.msz, R.isz, R.tsz, R.sp, R.room, R.stk, R.out, R.ra, R.rhl,
    R.racc, R.ina, R.inhl, R.inacc, R.nacc⟩

/-! ## The body, instruction by instruction -/

/-- One instruction of the body: the generator goes from `s` to `s1`,
perhaps with a comment first. -/
def Step1 (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) (k : Nat) (dt : Nat → Prop) (i : IR.Instr)
    (s s1 : GS) : Prop :=
  ∃ sc, (sc = s ∨ ∃ t, sc = { s with out := s.out.push (.comment t) }) ∧
    Ins Z (envAt E k i) base sF dt i sc () s1

def Chain (Z : ZCtx) (E : GEnv) (base : Nat) (sF : GS) : Nat → (Nat → Prop) → GS → List IR.Instr → GS → Prop
  | _, _, s, [], s' => s' = s
  | k, dt, s, i :: r, s' =>
    ∃ s1, Step1 Z E base sF k dt i s s1 ∧ Chain Z E base sF (k + 1) (dtNext dt i) s1 r s'

theorem genBody_ok (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) (hrt : RtOK Z)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) (ann : Bool) :
    ∀ (r : List IR.Instr) (k : Nat) (dt : Nat → Prop) (s : GS), (∀ i, i ∈ r → Covered i = true) →
      wpg (genBody E.fn ann k r) E (fun _ s' => Chain Z E base sF k dt s r s') s
  | [], _, _, _, _ => rfl
  | i :: r, k, dt, s, hc => by
    have hi := hc i (List.mem_cons_self ..)
    have hr : ∀ j, j ∈ r → Covered j = true := fun j hj => hc j (List.mem_cons_of_mem _ hj)
    have hT' : FnLay Z (envAt E k i) := hT.env (E := E) (E' := envAt E k i) rfl rfl rfl
    cases ann with
    | false =>
      simp only [genBody, Bool.false_eq_true, if_false, wpg_bind, wpg_withReader]
      refine wpg_mono (ins_ok (E := envAt E k i) (dt := dt) ok hT' F hrt hdep i hi s) ?_
      intro _ s1 h1
      refine wpg_mono (genBody_ok ok hT F hrt hdep false r (k + 1) (dtNext dt i) s1 hr) ?_
      intro _ s' h2
      exact ⟨s1, ⟨s, Or.inl rfl, h1⟩, h2⟩
    | true =>
      simp only [genBody, if_true, wpg_bind, wpg_modify, wpg_withReader]
      refine wpg_mono (ins_ok (E := envAt E k i) (dt := dt) ok hT' F hrt hdep i hi _) ?_
      intro _ s1 h1
      refine wpg_mono (genBody_ok ok hT F hrt hdep true r (k + 1) (dtNext dt i) s1 hr) ?_
      intro _ s' h2
      exact ⟨s1, ⟨_, Or.inr ⟨_, rfl⟩, h1⟩, h2⟩

/-- The states of a chain, by the index of the instruction. -/
theorem Chain.fns : ∀ (r : List IR.Instr) (k : Nat) (dt : Nat → Prop) (s s' : GS),
    Chain Z E base sF k dt s r s' →
    ∃ (gs : Nat → GS) (dts : Nat → Nat → Prop), gs k = s ∧ dts k = dt ∧ gs (k + r.length) = s' ∧
      ∀ j i, r[j]? = some i →
        Step1 Z E base sF (k + j) (dts (k + j)) i (gs (k + j)) (gs (k + j + 1)) ∧
          dts (k + j + 1) = dtNext (dts (k + j)) i
  | [], k, dt, s, s', h => by
    cases h
    exact ⟨fun _ => s, fun _ => dt, rfl, rfl, rfl, fun j i hj => by cases hj⟩
  | i0 :: r, k, dt, s, s', h => by
    obtain ⟨s1, hstep, hch⟩ := h
    obtain ⟨gs, dts, hg, hd, hl, hall⟩ := Chain.fns r (k + 1) (dtNext dt i0) s1 s' hch
    refine ⟨fun n => if n ≤ k then s else gs n, fun n => if n ≤ k then dt else dts n, by simp, by simp, ?_, ?_⟩
    · have : ¬ (k + (i0 :: r).length ≤ k) := by simp
      simp only [this, if_false]
      rw [← hl]
      congr 1
      simp only [List.length_cons]
      omega
    · intro j i hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [Nat.add_zero, Nat.le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false, hg, hd]
        exact ⟨hstep, trivial⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        obtain ⟨h1, h2⟩ := hall j i hj
        have e1 : k + (j + 1) = k + 1 + j := by omega
        simp only [e1, show ¬ (k + 1 + j ≤ k) by omega, show ¬ (k + 1 + j + 1 ≤ k) by omega, if_false]
        exact ⟨h1, h2⟩

/-! ## A function -/

/-- The generation of a function: its environment, where its items are
in the image, and the generator's state and the temporaries assigned
before each instruction of the body. -/
structure FnGen where
  E : GEnv
  base : Nat
  sF : GS
  gs : Nat → GS
  dts : Nat → Nat → Prop

structure FnGen.OK (G : FnGen) (Z : ZCtx) (f : IR.Fn) : Prop where
  fn : G.E.fn = f
  F : GFinal Z G.base G.sF
  jumps : jumpsOk G.sF = true
  last : G.gs f.body.size = G.sF
  dt0 : G.dts 0 = fun _ => False
  step : ∀ pc i, f.body[pc]? = some i →
    Step1 Z G.E G.base G.sF pc (G.dts pc) i (G.gs pc) (G.gs (pc + 1)) ∧ G.dts (pc + 1) = dtNext (G.dts pc) i
  need : ∀ pc i, f.body[pc]? = some i → Need Z (envAt G.E pc i) (G.dts pc) i
  /-- The body ends with an instruction that does not go on (it is not empty). -/
  falls : ∀ pc i, f.body[pc]? = some i → canFall i = true → pc + 1 < f.body.size
  nonempty : 0 < f.body.size
  /-- A label is in the body once. -/
  labels : ∀ pc l, f.body[pc]? = some (.label l) → f.body.findIdx? (· == .label l) = some pc
  /-- From the entry to the first instruction: the parameter in a register is stored. -/
  entry : ∀ st v s, Entry Z f st v s →
    ∃ s', Steps s s' ∧ At Z.addrs (G.base + (G.gs 0).out.size) s' ∧
      Rel Z G.E ⟨s.sp, s.mem⟩ (fun _ => False) (G.gs 0).regs (stArg Z.c f st v)
        (Array.replicate f.tmps.size 0) s'

theorem Ins.ext {dt : Nat → Prop} {i : IR.Instr} {s0 s1 : GS} (h : Ins Z E base sF dt i s0 () s1) : GExt s0 s1 :=
  h.1

theorem Ins.other {dt : Nat → Prop} {i : IR.Instr} {s0 s1 : GS} (hn : ∀ l, i ≠ .label l)
    (h : Ins Z E base sF dt i s0 () s1) :
    GExt s1 sF → Need Z E dt i → ∀ fr ist tmps s w, Rel Z E fr dt s0.regs ist tmps s →
      At Z.addrs (base + s0.out.size) s → Z.wrel ist.world w →
      MAfter Z E base fr dt i s1 ist tmps s w (IR.Sem.step Z.c ist tmps i) := by
  cases i <;> first | exact h.2 | exact absurd rfl (hn _)

theorem Step1.ext {k : Nat} {dt : Nat → Prop} {i : IR.Instr} {s s1 : GS} (h : Step1 Z E base sF k dt i s s1) :
    GExt s s1 := by
  obtain ⟨sc, hsc, hins⟩ := h
  rcases hsc with rfl | ⟨t, rfl⟩
  · exact hins.ext
  · exact (GExt.push _ _).trans hins.ext

/-- The comment before an instruction is passed. -/
theorem Step1.start (ok : Z.OK) (F : GFinal Z base sF) {k : Nat} {dt : Nat → Prop} {i : IR.Instr} {s s1 : GS}
    (h : Step1 Z E base sF k dt i s s1) (hx : GExt s1 sF) :
    ∃ sc, Ins Z (envAt E k i) base sF dt i sc () s1 ∧ sc.regs = s.regs ∧
      ∀ c : Cpu, At Z.addrs (base + s.out.size) c → At Z.addrs (base + sc.out.size) c := by
  obtain ⟨sc, hsc, hins⟩ := h
  rcases hsc with rfl | ⟨t, rfl⟩
  · exact ⟨_, hins, rfl, fun c h => h⟩
  · refine ⟨_, hins, rfl, fun c hat => ?_⟩
    have hk : Z.items[base + s.out.size]? = some (.comment t) := F.at (hins.ext.trans hx) (by simp)
    have := at_skip ok.placed hk (fun _ => rfl) hat
    simpa [Nat.add_assoc] using this

theorem FnGen.OK.mono {G : FnGen} {f : IR.Fn} (GK : G.OK Z f) :
    ∀ d pc, pc + d ≤ f.body.size → GExt (G.gs pc) (G.gs (pc + d))
  | 0, pc, _ => GExt.refl _
  | d + 1, pc, h => by
    have hlt : pc + d < f.body.size := by omega
    have := (GK.step (pc + d) _ (Array.getElem?_eq_getElem hlt)).1.ext
    exact (GK.mono d pc (by omega)).trans this

theorem FnGen.OK.toF {G : FnGen} {f : IR.Fn} (GK : G.OK Z f) {pc : Nat} (h : pc ≤ f.body.size) :
    GExt (G.gs pc) G.sF := by
  have := GK.mono (f.body.size - pc) pc (by omega)
  rwa [show pc + (f.body.size - pc) = f.body.size by omega, GK.last] at this

theorem canFall_of_next {c : IR.Ctx} {st st' : IR.Sem.St} {tmps tmps' : Array Nat} {i : IR.Instr}
    (h : IR.Sem.step c st tmps i = .next st' tmps') : canFall i = true := by
  cases i <;> first | rfl | (cases h)

theorem canFall_of_call {c : IR.Ctx} {st st1 : IR.Sem.St} {tmps : Array Nat} {i : IR.Instr} {g : String}
    {ret : Option (Nat × Dst)} (h : IR.Sem.step c st tmps i = .call g st1 ret) : canFall i = true := by
  cases i <;> first | rfl | (cases h)

theorem labelAt_spec {f : IR.Fn} {l i : Nat} (h : IR.Sem.labelAt f l = some i) :
    f.body[i]? = some (.label l) := by
  unfold IR.Sem.labelAt at h
  obtain ⟨hlt, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  rw [Array.getElem?_eq_getElem hlt]
  cases hb : f.body[i] with
  | label l' =>
    rw [hb] at hp
    have : l' = l := by simpa [IR.Sem.isLabel] using hp
    rw [this]
  | _ => rw [hb] at hp; cases hp

theorem Outcome.steps {f : IR.Fn} {fr : Fr} {s s' : Cpu} {w w' : Z.W} {res : IR.Sem.Res}
    (h1 : WSteps Z (s, w) (s', w')) (h : Outcome Z f fr s' w' res) : Outcome Z f fr s w res := by
  cases res with
  | ok r st =>
    obtain ⟨s'', w'', v, st2, hw, hv, hr⟩ := h
    exact ⟨s'', w'', v, h1.trans st2, hw, hv, hr⟩
  | trap st =>
    obtain ⟨s'', w'', st2, hw, ht⟩ := h
    exact ⟨s'', w'', h1.trans st2, hw, ht⟩
  | fuel => trivial
  | bad => trivial

/-- After the label at `pc`: the states agree for what the generator
assumes there, however the label was reached. -/
theorem FnGen.OK.label (ok : Z.OK) {G : FnGen} {f : IR.Fn} (GK : G.OK Z f) {pc l : Nat}
    (hb : f.body[pc]? = some (.label l)) :
    ∃ jl : Nat, Z.items[jl]? = some (Item.label (lname G.E l)) ∧
      (∀ c : Cpu, At Z.addrs jl c → At Z.addrs (G.base + (G.gs (pc + 1)).out.size) c) ∧
      (∀ c : Cpu, At Z.addrs (G.base + (G.gs pc).out.size) c → At Z.addrs jl c) ∧
      (∀ fr dt r ist tmps s, (l, r) ∈ G.sF.jumps → Rel Z G.E fr dt r ist tmps s →
        Rel Z G.E fr (G.dts (pc + 1)) (G.gs (pc + 1)).regs ist tmps s) ∧
      ((pc = 0 ∨ ∃ i', f.body[pc - 1]? = some i' ∧ canFall i' = true) → (l, (G.gs pc).regs) ∈ G.sF.jumps) := by
  have hlt : pc < f.body.size := by
    rcases Nat.lt_or_ge pc f.body.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hb; cases hb
  obtain ⟨hstep, hdt⟩ := GK.step pc _ hb
  have hxF : GExt (G.gs (pc + 1)) G.sF := GK.toF (by omega)
  obtain ⟨sc, hins, hregs, hstart⟩ := hstep.start ok GK.F hxF
  obtain ⟨hx, hout, hlr, hfall⟩ := hins
  have hout' : (G.gs (pc + 1)).out = sc.out.push (Item.label (lname G.E l)) := hout
  have hk : Z.items[G.base + sc.out.size]? = some (Item.label (lname G.E l)) :=
    GK.F.at hxF (by rw [hout']; simp)
  refine ⟨G.base + sc.out.size, hk, fun c hat => ?_, hstart, fun fr dt r ist tmps s hj R => ?_, fun hprev => ?_⟩
  · have := at_skip ok.placed hk (fun _ => rfl) hat
    rw [hout']
    simpa [Nat.add_assoc] using this
  · rw [hdt]
    exact (arrive GK.jumps hj (hxF.labels.subset hlr) R).dt_none
  · refine hxF.jumps.subset ?_
    rw [← hregs]
    refine hfall ?_
    have hfind := GK.labels pc l hb
    have hfn : (envAt G.E pc (IR.Instr.label l)).fn.body = f.body := by rw [← GK.fn]; rfl
    rw [hfn]
    unfold prevFalls
    rw [hfind]
    rcases hprev with rfl | ⟨i', hi', hcf⟩
    · rfl
    · simp [hi', hcf]

/-- **The body from an instruction on.**  `hcal`: the functions called, with less fuel. -/
theorem exec_ok (ok : Z.OK) {G : FnGen} {f : IR.Fn} (GK : G.OK Z f) :
    ∀ k, (∀ m, m < k → ∀ g st1, Callee Z g st1 (IR.Sem.callF m Z.c g st1)) →
      ∀ pc tmps ist s w fr, pc < f.body.size → (pc = 0 ∨ ∃ i', f.body[pc - 1]? = some i' ∧ canFall i' = true) →
        At Z.addrs (G.base + (G.gs pc).out.size) s → Rel Z G.E fr (G.dts pc) (G.gs pc).regs ist tmps s →
        Z.wrel ist.world w → Outcome Z f fr s w (IR.Sem.exec k Z.c f pc tmps ist) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hcal pc tmps ist s w fr hlt hprev hat R hw
    cases k with
    | zero =>
      rw [exec_zero]
      trivial
    | succ k =>
      have hb : f.body[pc]? = some f.body[pc] := Array.getElem?_eq_getElem hlt
      rw [exec_succ]
      simp only [hb]
      generalize f.body[pc] = i at hb
      have ihk := ih k (Nat.lt_succ_self k) (fun m hm => hcal m (by omega))
      by_cases hlab : ∃ l, i = .label l
      · -- a label
        obtain ⟨l, rfl⟩ := hlab
        obtain ⟨jl, _, hafter, hbefore, harr, hfall⟩ := GK.label ok hb
        have hlt' := GK.falls pc _ hb rfl
        show Outcome Z f fr s w (IR.Sem.exec k Z.c f (pc + 1) tmps ist)
        exact ihk (pc + 1) tmps ist s w fr hlt' (Or.inr ⟨_, by simpa using hb, rfl⟩) (hafter s (hbefore s hat))
          (harr fr _ _ ist tmps s (hfall hprev) R) hw
      · have hnl : ∀ l, i ≠ .label l := fun l h => hlab ⟨l, h⟩
        obtain ⟨hstep, hdt⟩ := GK.step pc i hb
        have hxF : GExt (G.gs (pc + 1)) G.sF := GK.toF (by omega)
        obtain ⟨sc, hins, hregs, hstart⟩ := hstep.start ok GK.F hxF
        have hA := hins.other hnl hxF (GK.need pc i hb) fr ist tmps s w
          ((show Rel Z G.E fr (G.dts pc) sc.regs ist tmps s by rw [hregs]; exact R).toAt pc i) (hstart s hat) hw
        cases hs : IR.Sem.step Z.c ist tmps i with
        | next ist' tmps' =>
          rw [hs] at hA
          obtain ⟨s', w', st, hw', hat', R'⟩ := hA
          have hlt' := GK.falls pc i hb (canFall_of_next hs)
          refine Outcome.steps st (ihk (pc + 1) tmps' ist' s' w' fr hlt'
            (Or.inr ⟨i, by simpa using hb, canFall_of_next hs⟩) hat' ?_ hw')
          rw [hdt]
          exact R'.ofAt
        | goto l =>
          rw [hs] at hA
          show Outcome Z f fr s w (match IR.Sem.labelAt f l with
            | some i => IR.Sem.exec k Z.c f i tmps ist
            | none => .bad)
          cases hl : IR.Sem.labelAt f l with
          | none => trivial
          | some i' =>
            have hbl := labelAt_spec hl
            obtain ⟨jl, hjl, hafter, _, harr, _⟩ := GK.label ok hbl
            obtain ⟨s', r, st, hat', hj, R'⟩ := hA jl hjl
            have hlt' := GK.falls i' _ hbl rfl
            show Outcome Z f fr s w (IR.Sem.exec k Z.c f i' tmps ist)
            cases k with
            | zero =>
              rw [exec_zero]
              trivial
            | succ k' =>
              rw [exec_succ]
              simp only [hbl]
              show Outcome Z f fr s w (IR.Sem.exec k' Z.c f (i' + 1) tmps ist)
              refine Outcome.steps st (ih k' (by omega) (fun m hm => hcal m (by omega)) (i' + 1) tmps ist s' w fr hlt'
                (Or.inr ⟨_, by simpa using hbl, rfl⟩) (hafter s' hat') ?_ hw)
              exact harr fr _ r ist tmps s' (hxF.jumps.subset hj) R'.ofAt
        | call g st1 ret =>
          rw [hs] at hA
          have hA' := hA _ (hcal k (Nat.lt_succ_self k) g st1)
          show Outcome Z f fr s w (match IR.Sem.callF k Z.c g st1 with
            | .ok r st2 => IR.Sem.exec k Z.c f (pc + 1) (IR.Sem.setRet Z.c st2 tmps ret r).2
                (IR.Sem.setRet Z.c st2 tmps ret r).1
            | .trap st2 => .trap st2
            | .fuel => .fuel
            | .bad => .bad)
          cases hr : IR.Sem.callF k Z.c g st1 with
          | fuel => trivial
          | bad => trivial
          | trap st2 =>
            rw [hr] at hA'
            exact hA'
          | ok r st2 =>
            rw [hr] at hA'
            obtain ⟨s', w', st, hw', hat', R'⟩ := hA'
            have hlt' := GK.falls pc i hb (canFall_of_call hs)
            refine Outcome.steps st (ihk (pc + 1) _ _ s' w' fr hlt'
              (Or.inr ⟨i, by simpa using hb, canFall_of_call hs⟩) hat' ?_ (by rw [setRet_world]; exact hw'))
            rw [hdt]
            exact R'.ofAt
        | stop r =>
          rw [hs] at hA
          show Outcome Z f fr s w r
          cases r with
          | fuel => trivial
          | bad => trivial
          | trap st' => exact hA
          | ok r st' =>
            obtain ⟨s', w', v, st, hw', hi, hret⟩ := hA
            refine ⟨s', w', v, st, hw', ?_, ?_⟩
            · rw [← hi]
              exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb)
            · have hfn : (envAt G.E pc i).fn = f := GK.fn
              rw [hfn] at hret
              exact hret

/-- **Every function**: entered as `Entry` says, its code has the
outcome of `IR.Sem.callF`. -/
theorem fn_ok (ok : Z.OK) (hG : ∀ g gf, Z.c.prog.fn? g = some gf → gf.dead = false → ∃ G : FnGen, G.OK Z gf) :
    ∀ k g st1, Callee Z g st1 (IR.Sem.callF k Z.c g st1) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro g st1 gf st v s w hgf hlive hst1 ent hw
    cases k with
    | zero =>
      rw [callF_zero]
      trivial
    | succ k =>
      rw [callF_succ]
      simp only [hgf]
      obtain ⟨G, GK⟩ := hG g gf hgf hlive
      obtain ⟨s', st', hat, R⟩ := GK.entry st v s ent
      rw [hst1]
      refine Outcome.steps (Steps.lift ok st' w) (exec_ok ok GK k (fun m hm => ih m (by omega)) 0 _ _ s' w _
        GK.nonempty (Or.inl rfl) hat ?_ (by rw [stArg_world]; exact hw))
      rw [GK.dt0]
      exact R

end

/-- info: 'Ember.Proof.Z80Gen.fn_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_ok

end Ember.Proof.Z80Gen
