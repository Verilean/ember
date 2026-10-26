import Ember.Proof.IRLower
import Ember.Proof.Driver
import Ember.Proof.CNet
import Ember.Net.Loop
import Ember.Net.Eth

/-!
# Ember.Proof.IRNet — the IR of the stack does what the Spec does (plan M7.1)

`Ember.Proof.Driver` (M5.6): the stack in Ember, run by `Lang.Sem` from
its initial state, never traps and transmits and drops what the Spec
does.  `Ember.Proof.IRLower`: the IR `IR.lower` returns, run by
`Ember.Z80.IR.Sem`, does what `Lang.Sem` does.  Together (`stack_ir`):
**the IR of the SLIP build, called again and again from its initial
state, never traps and transmits and drops what the Spec does.**

The program-specific facts are computed (`#guard`): the checkers
`progOkB` and `irOkB` accept every build of the stack, with the layout
`Ember.Z80.IR.Sem.run` gives it.
-/

namespace Ember.Proof.IRSim
open Ember Ember.Lang Ember.Z80 Ember.Z80.IR.Sem
open Ember.Z80.IR hiding rd wr effect run Prog Fn Global
open Ember.Proof.Refine (mainIter kept specKept witems later main_fn TcpAll TcpReasons)

theorem mainIter_eq (p : Prog) (he : p.entry = "main") (fuel : Nat) :
    ∀ (j : Nat) (st : Lang.Sem.St), mainIter fuel p j st = callIter fuel p j st
  | 0, _ => rfl
  | j + 1, st => by
    rw [mainIter, callIter, he]
    cases Lang.Sem.call fuel p st "main" [] with
    | ok v st' => exact mainIter_eq p he fuel j st'
    | trap _ => rfl
    | fuel => rfl

/-- **The IR of the stack.**  For the checked SLIP build `p`, the IR
`q` that `IR.lower` returns for it and a layout `l` the checker accepts:
once every item of the input has been read, the calls of the entry
function — as `Ember.Z80.IR.Sem.run` makes them — have all ended
normally (no trap), and the kept lines of the trace (transmissions and
drops, each with the number of its input) are those of the Spec's
steps. -/
theorem stack_ir (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (hentry : p.entry = "main") (hg : p.globals = Net.prog.globals) (hs : p.structs = Net.prog.structs)
    (hf : p.framed = Net.prog.framed) (hok : progOkB p = true) (q : IR.Prog) (hl : lower p = .ok q)
    (l : Layout) (hir : irOkB p l = true) (inputs : Array Trace.Input) (j : Nat)
    (hj : (later inputs 0).length ≤ j + 1) :
    ∃ m ist', irIter m (irCtx p q l) (j + 1) (irInit p q l inputs) = some ist' ∧
      kept ist'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems ist'.world = [] := by
  obtain ⟨st', w', hit, _, hk, hwi⟩ := Refine.main_run_all p hP hR hp inputs 0 j hj
  rw [mainIter_eq p hentry, ← CSim.initial_congr p Net.prog hg hs hf] at hit
  obtain ⟨m, ist', hci, hw⟩ := lower_iter hl l hok hir inputs _ (j + 1) st' hit
  exact ⟨m, ist', hci, by rw [hw]; exact hk, by rw [hw]; exact hwi⟩

/-- info: 'Ember.Proof.IRSim.stack_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stack_ir

/-- The context's layout and the state of `stack_ir` are those `IR.Sem.run` starts from. -/
theorem irInit_eq (p : Prog) (q : IR.Prog) (inputs : Array Trace.Input) :
    (IR.initial q inputs p.framed).1 = (IR.initial q #[] p.framed).1 ∧
      irInit p q (IR.initial q inputs p.framed).1 inputs =
        { mem := (IR.initial q inputs p.framed).2.mem, world := (IR.initial q inputs p.framed).2.world } :=
  ⟨rfl, rfl⟩

/-! ## The programs -/

/-- The checkers accept the program, with the layout `IR.Sem.run` gives
the IR `IR.lower` returns for it. -/
def covered (p : Prog) : Bool :=
  match lower p with
  | .ok q => progOkB p && irOkB p (IR.initial q #[] p.framed).1
  | .error _ => false

-- the checked SLIP build is the program of `stack_ir` …
#guard (Net.prog.check.toOption.map fun q =>
  q.entry == "main" && q.globals == Net.prog.globals && q.structs == Net.prog.structs &&
    q.framed == Net.prog.framed) == some true
-- … and is covered, as are the loopback program and the Ethernet builds (for `lower_iter`)
#guard (Net.prog.check.toOption.map covered) == some true
#guard (Net.Loop.prog.check.toOption.map covered) == some true
#guard (Net.Eth.prog.check.toOption.map covered) == some true
#guard (Net.Eth.progDhcp.check.toOption.map covered) == some true

end Ember.Proof.IRSim
