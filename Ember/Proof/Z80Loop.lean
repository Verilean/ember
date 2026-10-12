import Ember.Proof.Z80LoopIR
import Ember.Z80.Runtime

/-!
# Ember.Proof.Z80Loop — the loopback program: `FnStatic` of its functions, built (plan M7.3)

For the loopback program (`Loop.ir`) with the layout of its image for
the board, what the theorems about generated code assume of the program
is established, by the kernel:

* `progEnvs_eq`: the environments its four functions are generated in
  (their second pass) — no temporary has a slot; the stores of `main` to
  its frame and of `slip_send` to the byte at 6 are left out;
* `plan_checked`: `okB` of the plan made for them, and `fnStaticB` of
  each function in its environment;
* `loop_static`: so each has `FnStatic`; `loop_ok`: so, in an image that
  holds the generated items, each does what the IR's function does
  (`prog_ok`).

What `loop_ok` still takes: of the image, that the items are placed, the
areas have their symbols, `rt_trap` is there; of the machine, that it is
quiet; of the runtime, `RtOK`.  The image of the build is not connected
here: `build` runs passes over the items (`retThreading`, `sweep`,
`peephole`, `packHigh`, `relax`) that `loop_ok` does not speak of.

The layout is the one `Codegen.build` computes for the board (a
`#guard`); the accumulator, which this image does not have, is given
eight bytes above it.
-/

namespace Ember.Proof.Z80Gen.Loop
open Ember.Z80 Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

def layout : IR.Layout :=
  { globals := [("buf", 33033), ("len", 33329), ("esc", 33331), ("over", 33332)],
    frames := [("slip_send", 33336), ("slip_store", 33336), ("loop_rx", 33335), ("main", 33333)],
    top := 33343 }

/-- The layout is the one of the image for the board. -/
def layoutIsBuilt : Bool :=
  match Codegen.build ir (Runtime.board 0 ["oversize-frame"] []) (Runtime.boardHead 0x8000)
      (reserved := (Runtime.boardCells 0x8000).2) with
  | .ok img => img.layout.globals == layout.globals && img.layout.frames == layout.frames &&
      img.layout.top == layout.top
  | .error _ => false

#guard layoutIsBuilt

def ctx : IR.Ctx := { prog := ir, layout, dropReasons := ["oversize-frame"] }

/-- RAM from `0x8000`: the cells of the board's runtime, the globals,
the frames; eight bytes for the accumulator; the stack up to the top. -/
def planIn (envs : List (IR.Fn × Array Bool × Option (Array Bool))) : PlanIn :=
  { c := ctx, envs, ramStart := 0x8000, stackLo := 33351, stackHi := 65536, acc := 33343, rtK := 32,
    rt := [(0x8000, 33033)], labels := ["rt_trap"] }

def isLab (l : String) : Item → Bool
  | .label x => x == l
  | _ => false

/-- Everything the kernel is to compute: the environments are found,
the plan passes, and the generated items have the plan's labels (but
`rt_trap`, which is of the runtime). -/
def check : Bool :=
  match progEnvs ir, genProg ir with
  | .ok envs, .ok c => planCheck (planIn envs) &&
      (mkPlan (planIn envs)).labels.all fun l => l == "rt_trap" || c.items.any (isLab l)
  | _, _ => false

theorem check_true : check = true := by decide +kernel

/-- The environments of the four functions. -/
def envs : List (IR.Fn × Array Bool × Option (Array Bool)) :=
  match progEnvs ir with
  | .ok es => es
  | .error _ => []

theorem progEnvs_eq : progEnvs ir = .ok envs := by
  have h := check_true
  unfold check at h
  unfold envs
  cases hp : progEnvs ir with
  | error e => rw [hp] at h; cases h
  | ok es => rfl

/-- The environments, as they are. -/
theorem envs_eq : envs.map (fun e => (e.1.name, e.2.1, e.2.2)) =
    [("slip_send", #[], some #[true, false, true, false, true, false, false]),
     ("slip_store", #[], some #[true]), ("loop_rx", #[], some #[true]), ("main", #[], some #[false, false])] := by
  decide +kernel

def plan : Plan := mkPlan (planIn envs)

theorem plan_checked : planCheck (planIn envs) = true := by
  have h := check_true
  unfold check at h
  rw [progEnvs_eq] at h
  cases hg : genProg ir with
  | error e => rw [hg] at h; cases h
  | ok c =>
    rw [hg] at h
    exact (Bool.and_eq_true _ _ |>.mp h).1

/-- The labels of the plan are in an image that holds the generated items and `rt_trap`. -/
theorem plan_labels (M : Around) {c : Compiled} (hgen : genProg ir = .ok c) {off : Nat}
    (hitems : ∀ j it, c.items[j]? = some it → M.items[off + j]? = some it)
    (htrap : ∃ j : Nat, M.items[j]? = some (Item.label "rt_trap")) : Labels plan M := by
  have h := check_true
  unfold check at h
  rw [progEnvs_eq, hgen] at h
  have h2 := (Bool.and_eq_true _ _ |>.mp h).2
  intro l hl
  have := List.all_eq_true.mp h2 l hl
  rcases Bool.or_eq_true _ _ |>.mp this with h3 | h3
  · have : l = "rt_trap" := by simpa using h3
    rw [this]
    exact htrap
  · obtain ⟨it, hm, hi⟩ := List.any_eq_true.mp h3
    cases it with
    | label x =>
      have : x = l := by simpa [isLab] using hi
      subst this
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hm
      exact ⟨off + j, hitems j _ (by rw [List.getElem?_eq_getElem hj, hget])⟩
    | _ => cases hi

/-- **`FnStatic` of the functions of the loopback program**, each in the
environment it is generated in. -/
theorem loop_static (M : Around) (hlab : Labels plan M) :
    ∀ e, e ∈ envs → FnStatic (plan.toZ M) (genEnv e.1 e.2.1 e.2.2) :=
  planCheck_static plan_checked M hlab

/-- **The functions of the loopback program do what the IR's do**, in
an image that holds the items `genProg` gives for it. -/
theorem loop_ok (M : Around) (placed : Placed M.items 0 M.a M.addrs) (quiet : ∀ w, M.dev w .none = w)
    (areas : ∀ ar ad, layout.areaAddr ar = some ad → (plan.toZ M).sym (areaSym ar) ad)
    (accSym : (plan.toZ M).sym "rt_acc" 33343) (hrt : RtOK (plan.toZ M))
    {c : Compiled} (hgen : genProg ir = .ok c) {off : Nat}
    (hitems : ∀ j it, c.items[j]? = some it → M.items[off + j]? = some it)
    (htrap : ∃ j : Nat, M.items[j]? = some (Item.label "rt_trap")) :
    ∀ k g st1, Callee (plan.toZ M) g st1 (IR.Sem.callF k ctx g st1) :=
  prog_ok (Z := plan.toZ M) (plan_ok (planCheck_ok plan_checked) M placed quiet areas accSym) hrt (ann := false)
    hgen hitems progEnvs_eq (loop_static M (plan_labels M hgen hitems htrap))

/-- info: 'Ember.Proof.Z80Gen.Loop.loop_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_ok

end Ember.Proof.Z80Gen.Loop
