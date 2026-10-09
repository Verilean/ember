/-!
# Ember.C.Ast — the C subset the emitter produces

Close to CompCert's Clight: expressions have no side effects (calls are
statements), every operation is written with explicit casts, and there
are no compound literals, VLAs or designated initialisers, so SDCC
accepts it.  `Ember.C.Semantics` (M5.7) will give this AST a meaning;
the printer (`Ember.C.Print`) is trusted.
-/

namespace Ember.C

inductive CTy where
  | uint (bits : Nat)   -- uintN_t
  | unsigned            -- unsigned int (as wide as int)
  | bool                -- _Bool via <stdbool.h>
  | void
  | strct (name : String)
  | ptr (t : CTy)
  | arr (t : CTy) (n : Nat)
  deriving Inhabited, BEq, Repr

inductive CExpr where
  | var   (x : String)
  /-- An unsigned literal with its C suffix (`u`, `UL`, `ULL`). -/
  | lit   (n : Nat) (suffix : String)
  | blit  (b : Bool)
  | bin   (op : String) (a b : CExpr)
  | un    (op : String) (a : CExpr)
  | cast  (t : CTy) (a : CExpr)
  | cond  (c a b : CExpr)
  | index (a i : CExpr)
  | dot   (a : CExpr) (f : String)
  | arrow (a : CExpr) (f : String)
  | addr  (a : CExpr)
  | call  (f : String) (args : List CExpr)
  | str   (s : String)
  deriving Inhabited, BEq, Repr

inductive CStmt where
  | decl   (t : CTy) (x : String) (init : Option CExpr)
  /-- `T x = {0};` for arrays and structs. -/
  | declZero (t : CTy) (x : String)
  | assign (l r : CExpr)
  | expr   (e : CExpr)
  | ite    (c : CExpr) (t e : List CStmt)
  /-- `for (T i = lo; i < hi; i = (T)(i + 1u))` -/
  | forUp  (t : CTy) (i : String) (lo hi : CExpr) (body : List CStmt)
  | brk
  | ret    (e : Option CExpr)
  | block  (ss : List CStmt)
  | line   (n : Nat) (file : String)
  | comment (s : String)
  deriving Inhabited, BEq, Repr

structure CFn where
  name   : String
  ret    : CTy
  params : List (CTy × String)
  body   : List CStmt
  static : Bool := true
  deriving Inhabited, Repr

structure CGlobal where
  ty     : CTy
  name   : String
  const  : Bool := false
  static : Bool := true
  /-- Initialiser list (`{1, 2, 3}` or a single value). -/
  init   : Option (List CExpr) := none
  deriving Inhabited, Repr

structure CUnit where
  header  : List String := []
  structs : List (String × List (CTy × String)) := []
  globals : List CGlobal := []
  fns     : List CFn := []
  deriving Inhabited, Repr

end Ember.C
