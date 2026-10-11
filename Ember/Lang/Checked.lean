import Lean
import Ember.Lang.Types

/-!
# Ember.Lang.Checked — a checked function as a term (plan M5.4)

The type checker (`Prog.check`) fills in what the surface syntax leaves
open — the width of a literal, the type of a `for` counter — and it is
`partial`, so the kernel cannot run it.  A proof about a function needs
the checked AST as a term: `checked_fn% P, "f"` runs the checker while
elaborating and inserts function `f` of program `P` as a literal.

The literal is what the checker returned at that moment; `Ember/Proof`
re-checks the equality with `#guard` next to every use, so a change of
the source or of the checker cannot leave a stale term behind.
-/

namespace Ember.Lang
open Lean Elab Term Meta

deriving instance ToExpr for Width
deriving instance ToExpr for Ty
deriving instance ToExpr for BinOp
deriving instance ToExpr for UnOp
deriving instance ToExpr for Expr
deriving instance ToExpr for Effect
deriving instance ToExpr for Span
deriving instance ToExpr for Stmt
deriving instance ToExpr for Param
deriving instance ToExpr for Fn

/-- Function `f` of program `P` after type checking. -/
elab "checked_fn% " p:term ", " f:str : term => do
  let e ← elabTerm p (some (mkConst ``Prog))
  let prog ← unsafe evalExpr Prog (mkConst ``Prog) e
  match prog.check with
  | .error err => throwError "{err}"
  | .ok q =>
    match q.fn? f.getString with
    | some fd => return toExpr fd
    | none => throwError "no function {f.getString}"

deriving instance BEq for Fn

end Ember.Lang
