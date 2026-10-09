import Ember.Lang.Syntax

/-!
# Ember.Lang.Pretty — programs back to surface syntax

For reports (shrunk fuzzer cases, `ember-emit --ember`).  The output is
readable Ember; literals carry their width as a cast.
-/

namespace Ember.Lang

partial def Expr.pretty : Expr → String
  | .lit v (some w) => s!"({v} : {w.name})"
  | .lit v none => toString v
  | .blit b => if b then "true" else "false"
  | .var x => x
  | .field e f => s!"{e.pretty}.{f}"
  | .index e i => s!"{e.pretty}[{i.pretty}]"
  | .bin op a b => s!"({a.pretty} {op.symbol} {b.pretty})"
  | .un .bnot a => s!"(~~~{a.pretty})"
  | .un .neg a => s!"(-{a.pretty})"
  | .un .lnot a => s!"(!{a.pretty})"
  | .cast w a => s!"({a.pretty} : {w.name})"
  | .cond c a b => s!"(if {c.pretty} then {a.pretty} else {b.pretty})"

def indentStr (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

partial def Stmt.pretty (n : Nat) : Stmt → List String
  | .at _ s => s.pretty n
  | .decl x t none => [indentStr n ++ s!"let mut {x} : {t}"]
  | .decl x t (some e) => [indentStr n ++ s!"let mut {x} : {t} := {e.pretty}"]
  | .assign l r => [indentStr n ++ s!"{l.pretty} := {r.pretty}"]
  | .ite c t e =>
    [indentStr n ++ s!"if {c.pretty} then"] ++ (if t.isEmpty then [indentStr (n+1) ++ "-- nothing"] else t.flatMap (·.pretty (n+1))) ++
    (if e.isEmpty then [] else [indentStr n ++ "else"] ++ e.flatMap (·.pretty (n+1)))
  | .forRange i w lo hi b =>
    [indentStr n ++ s!"for {i}{(w.map (" : " ++ ·.name)).getD ""} in [{lo.pretty}, {hi.pretty}) do"] ++ b.flatMap (·.pretty (n+1))
  | .loop m b => [indentStr n ++ s!"loop (max := {m}) do"] ++ b.flatMap (·.pretty (n+1))
  | .brk => [indentStr n ++ "break"]
  | .ret none => [indentStr n ++ "return"]
  | .ret (some e) => [indentStr n ++ s!"return {e.pretty}"]
  | .call d f as =>
    let c := s!"{f}({", ".intercalate (as.map Expr.pretty)})"
    [indentStr n ++ (match d with | some d => s!"{d.pretty} ← {c}" | none => c)]
  | .eff d e as =>
    let c := s!"{e.name}({", ".intercalate (as.map Expr.pretty)})"
    [indentStr n ++ (match d with | some d => s!"{d.pretty} ← {c}" | none => c)]

def Fn.pretty (f : Fn) : String :=
  let ps := f.params.map fun p => s!"({p.name} : {if p.byRef then "ref " else ""}{p.ty})"
  let r := (f.ret.map (" : " ++ toString ·)).getD ""
  "\n".intercalate ((s!"ember def {f.name} {" ".intercalate ps}{r} := do") :: f.body.flatMap (·.pretty 1))

def Prog.pretty (p : Prog) : String :=
  let ss := p.structs.map fun s => s!"ember struct {s.name} where " ++ " ".intercalate (s.fields.map fun (f, t) => s!"{f} : {t}")
  let gs := p.globals.map fun g =>
    s!"ember {if g.const then "const" else "global"} {g.name} : {g.ty}" ++ (if g.init.isEmpty then "" else s!" := {g.init}")
  "\n".intercalate (ss ++ gs ++ [""] ++ p.fns.map Fn.pretty)

end Ember.Lang
