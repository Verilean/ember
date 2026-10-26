import Ember.Proof.CCheck
import Ember.Proof.Driver
import Ember.Net.Loop
import Ember.Net.Eth

/-!
# Ember.Proof.CNet — the emitted C of the stack does what the Spec does (plan M5.8)

`Ember.Proof.Driver` (M5.6): the stack in Ember, run by `Lang.Sem` from
its initial state, never traps and transmits and drops what the Spec
does.  `Ember.Proof.CProgram`: the emitted C, run by `Ember.C.Sem`, does
what `Lang.Sem` does.  Together (`stack_c`): **the C emitted for the
SLIP build, called again and again from its initial state under the C
semantics, never traps, is never undefined, and transmits and drops what
the Spec does.**

The program-specific facts are computed (`#guard`): the checked stack is
the program the theorems are about, the checker `progOkB` accepts it for
every profile, and it compiles.
-/

namespace Ember.Proof.CSim
open Ember Ember.Lang Ember.C
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

theorem zeroOf_congr (p q : Prog) (hs : p.structs = q.structs) : zeroOf p = zeroOf q := by
  funext t
  cases t with
  | record r => simp only [zeroOf, Prog.struct?, hs]
  | int _ => rfl
  | bool => rfl
  | arr _ _ => rfl

theorem initial_congr (p q : Prog) (hg : p.globals = q.globals) (hs : p.structs = q.structs)
    (hf : p.framed = q.framed) (inputs : Array Trace.Input) :
    Lang.Sem.initial p inputs = Lang.Sem.initial q inputs := by
  have hi : Lang.initOf p = Lang.initOf q := by
    funext g
    unfold Lang.initOf
    rw [zeroOf_congr p q hs]
  simp only [Lang.Sem.initial, hg, hf, hi]

/-- **The emitted C of the stack.**  For the checked SLIP build `p` and
options without a name prefix: once every item of the input has been
read, the calls of the entry function — as `Ember.C.Sem.run` makes them —
have all ended normally (no trap, nothing undefined), and the kept lines
of the trace (transmissions and drops, each with the number of its
input) are those of the Spec's steps. -/
theorem stack_c (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (hp : p.fn? "main" = some main_fn)
    (hentry : p.entry = "main") (hg : p.globals = Net.prog.globals) (hs : p.structs = Net.prog.structs)
    (hf : p.framed = Net.prog.framed) (o : Opts) (hpre : o.namePrefix = "") (hb : o.bugDropCast = false)
    (h16 : 16 ≤ o.profile.intBits) (hok : progOkB p o = true) (u : CUnit) (hc : compile p o = .ok u)
    (inputs : Array Trace.Input) (j : Nat) (hj : (later inputs 0).length ≤ j + 1) :
    ∃ m cst', cIter m (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) (j + 1)
        (C.Sem.initial (C.Sem.CProg.ofUnit u o.profile o.entryName p.dropReasons p.notes) inputs p.framed)
          = some cst' ∧
      kept cst'.world = specKept inputs.toList 0 (Spec.State.init {}) ∧ witems cst'.world = [] := by
  obtain ⟨st', w', hit, _, hk, hwi⟩ := Refine.main_run_all p hP hR hp inputs 0 j hj
  obtain ⟨hPok, hG, fd, hE, hpar⟩ := progOkB_sound hok
  have hy := hygU_of_prefix o hpre
  have hrel0 := init_rel hc hy hb h16 hG inputs
  rw [mainIter_eq p hentry, ← initial_congr p Net.prog hg hs hf] at hit
  obtain ⟨m, cst', hci, hG'⟩ := iter_sim hc hy hb h16 hPok fd hE hpar _ (j + 1) _ st' _ hrel0 hit
  exact ⟨m, cst', hci, by rw [hG'.world]; exact hk, by rw [hG'.world]; exact hwi⟩

/-- info: 'Ember.Proof.CSim.stack_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stack_c

/-! ## The programs -/

/-- The checker accepts the program for every profile, and it compiles. -/
def covered (q : Prog) : Bool :=
  Profile.all.all fun prof =>
    progOkB q { profile := prof } && (compile q { profile := prof }).toOption.isSome && decide (16 ≤ prof.intBits)

-- the checked SLIP build is the program of `stack_c` …
#guard (Net.prog.check.toOption.map fun q =>
  q.entry == "main" && q.globals == Net.prog.globals && q.structs == Net.prog.structs &&
    q.framed == Net.prog.framed) == some true
-- … and is covered, as are the loopback program and the Ethernet builds (for `iter_sim`)
#guard (Net.prog.check.toOption.map covered) == some true
#guard (Net.Loop.prog.check.toOption.map covered) == some true
#guard (Net.Eth.prog.check.toOption.map covered) == some true
#guard (Net.Eth.progDhcp.check.toOption.map covered) == some true

end Ember.Proof.CSim
