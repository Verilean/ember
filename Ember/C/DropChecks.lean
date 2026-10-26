import Ember.C.Compile

/-!
# Ember.C.DropChecks — the bounds checks taken out of emitted C (M5.9)

`C.compile` checks every index it cannot show in range by its form
(`indexSafe`): before the access, `if (t >= n) { ember_trap("…"); }`.
`dropUnit` takes those statements out of every function of a unit, and
nothing else: the temporary the check read stays, and so does the
access through it.

This is not a pass of `compile`, and nothing runs it on a program by
default.  It is sound only where the run of the checked C never traps:
`Ember.Proof.CDrop.dropUnit_iter` — a run of the calls of the entry
function that ends normally in the checked unit ends the same way in the
unit without checks — and for the SLIP build of the stack that is what
M5.6 proves of the Ember program (every index in range, so no call
traps), carried to C by M5.8: `Ember.Proof.CDrop.stack_c_dropped`.  The
tools apply it to that program only (`Ember.Tools.Emit.proved`).
-/

namespace Ember.C

/-- A bounds check as `placeIndex` emits it. -/
def isCheck : CStmt → Bool
  | .ite (.bin ">=" _ _) [.expr (.call "ember_trap" [.str _])] [] => true
  | _ => false

mutual
def dropS : CStmt → CStmt
  | .ite c t e => .ite c (dropL t) (dropL e)
  | .forUp t i lo hi body => .forUp t i lo hi (dropL body)
  | .block ss => .block (dropL ss)
  | s => s

def dropL : List CStmt → List CStmt
  | [] => []
  | s :: rest => if isCheck s then dropL rest else dropS s :: dropL rest
end

def dropFn (f : CFn) : CFn := { f with body := dropL f.body }

/-- The unit with every bounds check taken out. -/
def dropUnit (u : CUnit) : CUnit := { u with fns := u.fns.map dropFn }

mutual
/-- The bounds checks in a statement. -/
def checksS : CStmt → Nat
  | .ite c t e => (if isCheck (.ite c t e) then 1 else 0) + checksL t + checksL e
  | .forUp _ _ _ _ body => checksL body
  | .block ss => checksL ss
  | _ => 0

def checksL : List CStmt → Nat
  | [] => 0
  | s :: rest => checksS s + checksL rest
end

/-- The bounds checks in a unit. -/
def checksUnit (u : CUnit) : Nat := (u.fns.map fun f => checksL f.body).sum

/-- `emitC` without the bounds checks: for a program whose runs are
proved never to trap (the tools allow the SLIP build only). -/
def emitDroppedC (p : Ember.Lang.Prog) (o : Opts := {}) : Except String String := do
  let p ← match p.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let u ← compile p o
  return (dropUnit u).print ++ "\n" ++ tables p o

end Ember.C
