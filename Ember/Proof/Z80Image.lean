import Ember.Proof.Z80PlanOf
import Ember.Proof.Z80Rt

/-!
# Ember.Proof.Z80Image — an image, checked: its functions do what the IR's do (plan M7.3)

`ImgIn`: a program's IR, the layout, and the items of an image.
`ImgIn.check` computes what the theorems about generated code take of
them: the environments the functions are generated in, `okB` and
`fnStaticB` of the plan made for them, that the assembler accepts the
items, that the items `genProg` gives are among them, the plan's labels,
the symbols of the areas and of the accumulator (where an instruction
names it), that the image is below 64 K.  The program has no wide
constant (the literal pool is not checked yet).

`ImgIn.ok`: when the check passes (for a term, by the kernel), the
setting of the proofs holds of the image (`ZCtx.OK`) for any machine
that an instruction without I/O leaves alone, and — given the routines
of the runtime the image calls (`RtOK`) — every function, entered as
`Entry` says, returns as `IR.Sem.callF` does or reaches `rt_trap`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

structure ImgIn where
  ir : IR.Prog
  layout : IR.Layout
  dropReasons : List String := []
  notes : List String := []
  ramStart : Nat
  stackLo : Nat
  stackHi : Nat
  acc : Nat
  rtK : Nat
  rt : Ivs
  items : List Item
  /-- Where the generated items start in the image. -/
  genOff : Nat

namespace ImgIn

def ctx (I : ImgIn) : IR.Ctx :=
  { prog := I.ir, layout := I.layout, dropReasons := I.dropReasons, notes := I.notes }

def planIn (I : ImgIn) (envs : List (IR.Fn × Array Bool × Option (Array Bool))) : PlanIn :=
  { c := I.ctx, envs, ramStart := I.ramStart, stackLo := I.stackLo, stackHi := I.stackHi, acc := I.acc,
    rtK := I.rtK, rt := I.rt, labels := ["rt_trap"] }

/-- The environments of the functions (none when the generator fails). -/
def envs (I : ImgIn) : List (IR.Fn × Array Bool × Option (Array Bool)) :=
  match progEnvs I.ir false (sharedBytes I.ir) with
  | .ok es => es
  | .error _ => []

def plan (I : ImgIn) : Plan := mkPlan (I.planIn I.envs)

def isLab (l : String) : Item → Bool
  | .label x => x == l
  | _ => false

/-- The instruction does not name the accumulator. -/
def noAcc : Item → Bool
  | .ins i =>
    (match i.immVal? with
     | some (.sym s _) => s != "rt_acc"
     | _ => true)
  | _ => true

def check (I : ImgIn) : Bool :=
  match progEnvs I.ir false (sharedBytes I.ir), genProg I.ir false (sharedBytes I.ir), assemble I.items with
  | .ok envs, .ok c, .ok a =>
    let P := mkPlan (I.planIn envs)
    planCheck (I.planIn envs) && (P.labels.all fun l => I.items.any (isLab l)) && P.lits.isEmpty &&
    (I.layout.globals.all fun e => a.labels.reverse.lookup (areaSym (.global e.1)) == some e.2) &&
    (I.layout.frames.all fun e => a.labels.reverse.lookup (areaSym (.frame e.1)) == some e.2) &&
    decide ((I.items.drop I.genOff).take c.items.length = c.items) &&
    (I.items.all noAcc || a.labels.reverse.lookup "rt_acc" == some I.acc) &&
    decide (a.bytes.size < 65536)
  | _, _, _ => false

/-- The machine around the CPU, with the image. -/
def around (I : ImgIn) (a : Assembled) (addrs : List Nat) (W : Type) (bus : W → UInt16 → UInt8)
    (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop) : Around :=
  { items := I.items, a, addrs, W, bus, dev, wrel }

theorem mem_label {items : List Item} {l : String} (h : items.any (isLab l) = true) :
    ∃ j : Nat, items[j]? = some (Item.label l) := by
  obtain ⟨it, hm, hi⟩ := List.any_eq_true.mp h
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hm
  cases it with
  | label x =>
    have : x = l := by simpa [isLab] using hi
    subst this
    exact ⟨j, by rw [List.getElem?_eq_getElem hj, hget]⟩
  | _ => cases hi

/-- **An image the check accepts.** -/
theorem ok (I : ImgIn) (h : I.check = true) :
    ∃ (a : Assembled) (addrs : List Nat), assemble I.items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ (W : Type) (bus : W → UInt16 → UInt8) (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop),
        (∀ w, dev w .none = w) →
        (I.plan.toZ (I.around a addrs W bus dev wrel)).OK ∧
        (RtOK (I.plan.toZ (I.around a addrs W bus dev wrel)) →
          ∀ k g st1, Callee (I.plan.toZ (I.around a addrs W bus dev wrel)) g st1 (IR.Sem.callF k I.ctx g st1)) := by
  unfold check at h
  cases he : progEnvs I.ir false (sharedBytes I.ir) with
  | error e => rw [he] at h; cases h
  | ok es =>
    cases hg : genProg I.ir false (sharedBytes I.ir) with
    | error e => rw [he, hg] at h; cases h
    | ok c =>
      cases ha : assemble I.items with
      | error e => rw [he, hg, ha] at h; cases h
      | ok a =>
        rw [he, hg, ha] at h
        have henvs : I.envs = es := by unfold envs; rw [he]
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
          List.isEmpty_iff] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨hplan, hlab⟩, hlits⟩, hglob⟩, hfr⟩, hsub⟩, hacc⟩, hsize⟩ := h
        obtain ⟨addrs, hpl⟩ := placed_of_assemble ha
        refine ⟨a, addrs, rfl, hsize, fun W bus dev wrel quiet => ?_⟩
        have hP : I.plan = mkPlan (I.planIn es) := by unfold plan; rw [henvs]
        rw [hP]
        have hok : ((mkPlan (I.planIn es)).toZ (I.around a addrs W bus dev wrel)).OK := by
          refine plan_ok (planCheck_ok hplan) _ hpl quiet (fun ar ad har => ?_) (fun href => ?_)
          · cases ar with
            | global g => exact hglob (g, ad) (lookup_mem har)
            | frame f => exact hfr (f, ad) (lookup_mem har)
          · rcases hacc with hacc | hacc
            · obtain ⟨k, i, off, hk, hi⟩ := href
              have := hacc _ (List.mem_of_getElem? hk)
              simp [noAcc, hi] at this
            · exact hacc
        refine ⟨hok, fun hrt => ?_⟩
        have hitems : ∀ (j : Nat) it, c.items[j]? = some it → I.items[I.genOff + j]? = some it := by
          intro j it hj
          have hlt : j < c.items.length := by
            rcases Nat.lt_or_ge j c.items.length with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none h'] at hj; cases hj
          rw [← hsub, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
          exact hj
        exact prog_ok (Z := (mkPlan (I.planIn es)).toZ (I.around a addrs W bus dev wrel)) hok hrt (ann := false)
          hg hitems he (planCheck_static hplan _ (fun l hl => mem_label (hlab l hl))
            (fun n v hv => by rw [hlits] at hv; cases hv))

end ImgIn

end Ember.Proof.Z80Gen
