import Ember.C.Ast

/-!
# Ember.C.Print — C AST to text (trusted, kept small)

Every compound expression is parenthesised; no precedence reasoning.
-/

namespace Ember.C

partial def CTy.base : CTy → String
  | .uint n => s!"uint{n}_t"
  | .unsigned => "unsigned"
  | .bool => "bool"
  | .void => "void"
  | .strct n => s!"struct {n}"
  | .ptr t => t.base ++ " *"
  | .arr t _ => t.base

/-- A declaration `T x` / `T x[n]` / `T *x`. -/
partial def CTy.declare (t : CTy) (x : String) : String :=
  match t with
  | .arr el n => s!"{el.declare x}[{n}]"
  | .ptr el => s!"{el.base} *{x}"
  | t => s!"{t.base} {x}"

def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString)) ""

partial def CExpr.print : CExpr → String
  | .var x => x
  | .lit n s => s!"{n}{s}"
  | .blit b => if b then "true" else "false"
  | .bin op a b => s!"({a.print} {op} {b.print})"
  | .un op a => s!"({op}{a.print})"
  | .cast t a => s!"(({t.base}){a.print})"
  | .cond c a b => s!"({c.print} ? {a.print} : {b.print})"
  | .index a i => s!"{a.print}[{i.print}]"
  | .dot a f => s!"{a.print}.{f}"
  | .arrow a f => s!"{a.print}->{f}"
  | .addr a => s!"(&{a.print})"
  | .call f as => s!"{f}({", ".intercalate (as.map CExpr.print)})"
  | .str s => s!"\"{escape s}\""

def ind (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

partial def CStmt.print (n : Nat) : CStmt → List String
  | .decl t x none => [ind n ++ t.declare x ++ ";"]
  | .decl t x (some e) => [ind n ++ t.declare x ++ " = " ++ e.print ++ ";"]
  | .declZero t x => [ind n ++ t.declare x ++ " = {0};"]
  | .assign l r => [ind n ++ l.print ++ " = " ++ r.print ++ ";"]
  | .expr e => [ind n ++ e.print ++ ";"]
  | .ite c t [] => [ind n ++ s!"if ({c.print}) " ++ "{"] ++ t.flatMap (·.print (n+1)) ++ [ind n ++ "}"]
  | .ite c t e => [ind n ++ s!"if ({c.print}) " ++ "{"] ++ t.flatMap (·.print (n+1)) ++
      [ind n ++ "} else {"] ++ e.flatMap (·.print (n+1)) ++ [ind n ++ "}"]
  | .forUp t i lo hi body =>
      [ind n ++ s!"for ({t.declare i} = {lo.print}; {i} < {hi.print}; {i} = (({t.base})({i} + 1u))) " ++ "{"] ++
      body.flatMap (·.print (n+1)) ++ [ind n ++ "}"]
  | .brk => [ind n ++ "break;"]
  | .ret none => [ind n ++ "return;"]
  | .ret (some e) => [ind n ++ s!"return {e.print};"]
  | .block ss => [ind n ++ "{"] ++ ss.flatMap (·.print (n+1)) ++ [ind n ++ "}"]
  | .line k f => [s!"#line {k} \"{escape f}\""]
  | .comment s => [ind n ++ s!"/* {s} */"]

def CFn.signature (f : CFn) : String :=
  let ps := if f.params.isEmpty then "void" else ", ".intercalate (f.params.map fun (t, x) => t.declare x)
  (if f.static then "static " else "") ++ f.ret.declare f.name ++ "(" ++ ps ++ ")"

def CGlobal.print (g : CGlobal) : String :=
  let q := (if g.static then "static " else "") ++ (if g.const then "const " else "")
  let i := match g.init with
    | none => ""
    | some [e] => match g.ty with
      | .arr _ _ => " = {" ++ e.print ++ "}"
      | _ => " = " ++ e.print
    | some es => " = {" ++ ", ".intercalate (es.map CExpr.print) ++ "}"
  q ++ g.ty.declare g.name ++ i ++ ";"

def CUnit.print (u : CUnit) : String := Id.run do
  let mut ls : Array String := u.header.toArray
  for (n, fs) in u.structs do
    ls := ls.push (s!"struct {n} " ++ "{")
    for (t, f) in fs do ls := ls.push ("  " ++ t.declare f ++ ";")
    ls := ls.push "};"
  if !u.structs.isEmpty then ls := ls.push ""
  for g in u.globals do ls := ls.push g.print
  ls := ls.push ""
  for f in u.fns do ls := ls.push (f.signature ++ ";")
  for f in u.fns do
    ls := ls.push ""
    ls := ls.push (f.signature ++ " {")
    for s in f.body do ls := ls ++ (s.print 1).toArray
    ls := ls.push "}"
  return "\n".intercalate ls.toList ++ "\n"

end Ember.C
