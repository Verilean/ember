import Lean
import Ember.Lang.Syntax

/-!
# Ember.Lang.Surface — `ember def` syntax (M2.4)

```
ember struct Tcb where
  st : u8
  pending : [u8; 256]

ember global buf : [u8; 296]
ember const MTU : u16 := 296

ember def ip_checksum (buf : ref [u8; 296]) (off len : u16) : u16 := do
  let mut sum : u16 := 0
  for i in [0, len / 2) do
    sum := add1 (sum, ...)
  return ~~~ sum
```

Each command defines a Lean constant holding the AST (`Fn`, `Global`,
`StructDef`), so programs are assembled as ordinary Lean values.  Every
statement carries its span in the Lean source file, which the
interpreter's errors and the emitted C's `#line` directives point at.

Expressions follow Lean's precedences (`<<<` binds tighter than `+`).
Literals take their width from context (`x + 1`); elsewhere write
`(1 : u16)`.  `a.b` is field `b` of record `a`.  Calls and effects are
statements: `f(a, b)`, `x ← f(a)`, `let y : u16 ← input.next()`.
-/

namespace Ember.Lang.Surface
open Lean Elab Command Term Meta

declare_syntax_cat ember_ty
declare_syntax_cat ember_expr
declare_syntax_cat ember_stmt (behavior := both)

syntax ident : ember_ty
syntax "[" ember_ty "; " num "]" : ember_ty

syntax:max ident : ember_expr
syntax:max num : ember_expr
syntax:max "(" ember_expr ")" : ember_expr
syntax:max "(" ember_expr " : " ember_ty ")" : ember_expr
syntax:max ember_expr:max noWs "[" ember_expr "]" : ember_expr
syntax:max ember_expr:max noWs "[" ember_expr "]" noWs "." ident : ember_expr
syntax:75 "~~~" ember_expr:75 : ember_expr
syntax:75 "!" ember_expr:75 : ember_expr
syntax:75 "-" ember_expr:75 : ember_expr
syntax:75 ember_expr:75 " <<< " ember_expr:76 : ember_expr
syntax:75 ember_expr:75 " >>> " ember_expr:76 : ember_expr
syntax:70 ember_expr:70 " * " ember_expr:71 : ember_expr
syntax:70 ember_expr:70 " / " ember_expr:71 : ember_expr
syntax:70 ember_expr:70 " % " ember_expr:71 : ember_expr
syntax:65 ember_expr:65 " + " ember_expr:66 : ember_expr
syntax:65 ember_expr:65 " - " ember_expr:66 : ember_expr
syntax:58 ember_expr:58 " &&& " ember_expr:59 : ember_expr
syntax:58 ember_expr:58 " ^^^ " ember_expr:59 : ember_expr
syntax:55 ember_expr:55 " ||| " ember_expr:56 : ember_expr
syntax:50 ember_expr:51 " == " ember_expr:51 : ember_expr
syntax:50 ember_expr:51 " != " ember_expr:51 : ember_expr
syntax:50 ember_expr:51 " < " ember_expr:51 : ember_expr
syntax:50 ember_expr:51 " <= " ember_expr:51 : ember_expr
syntax:50 ember_expr:51 " > " ember_expr:51 : ember_expr
syntax:50 ember_expr:51 " >= " ember_expr:51 : ember_expr
syntax:35 ember_expr:36 " && " ember_expr:35 : ember_expr
syntax:30 ember_expr:31 " || " ember_expr:30 : ember_expr
syntax:20 "if " ember_expr " then " ember_expr " else " ember_expr : ember_expr

syntax ember_seq := many1Indent(ember_stmt ";"?)
syntax ember_args := "(" ember_expr,* ")"

syntax "let " ("mut ")? ident " : " ember_ty " := " ember_expr : ember_stmt
syntax "let " ("mut ")? ident " : " ember_ty " ← " ident ember_args : ember_stmt
syntax "let " ("mut ")? ident " : " ember_ty : ember_stmt
syntax ident ember_args : ember_stmt
syntax ember_expr " ← " ident ember_args : ember_stmt
syntax ember_expr " := " ember_expr : ember_stmt
syntax "if " ember_expr " then " ember_seq (" else " ember_seq)? : ember_stmt
syntax "for " ident (" : " ember_ty)? " in " "[" ember_expr ", " ember_expr ")" " do " ember_seq : ember_stmt
syntax (name := loopStmt) &"loop" "(" &"max" " := " num ")" " do " ember_seq : ember_stmt
syntax "break" : ember_stmt
syntax "return" (ppSpace colGt ember_expr)? : ember_stmt

syntax ember_param := "(" ident+ " : " (&"ref")? ember_ty ")"

syntax (name := emberDef) (docComment)? "ember " "def " ident ember_param* (" : " ember_ty)? " := " " do " ember_seq : command
syntax (name := emberGlobal) (docComment)? "ember " &"global" ident " : " ember_ty (" := " "[" num,* "]")? : command
syntax (name := emberGlobalScalar) (docComment)? "ember " &"global" ident " : " ember_ty " := " num : command
syntax (name := emberConst) (docComment)? "ember " &"const" ident " : " ember_ty " := " num : command
syntax (name := emberConstArr) (docComment)? "ember " &"const" ident " : " ember_ty " := " "[" num,* "]" : command
syntax (name := emberStruct) (docComment)? "ember " &"struct" ident " where " (ppLine ident " : " ember_ty)* : command

/-! ## Translation to AST terms -/

abbrev TM := CommandElabM

def strLit (s : String) : Term := Syntax.mkStrLit s
def natLit (n : Nat) : Term := Syntax.mkNumLit (toString n)

/-- The source file, relative to the working directory when below it, so
spans (and the emitted `#line`s) do not depend on the checkout path. -/
def relFileName : TM String := do
  let file ← getFileName
  let cwd := (← IO.currentDir).toString ++ "/"
  return if file.startsWith cwd then (file.drop cwd.length).toString else file

def spanOf (stx : Syntax) : TM Term := do
  let fm ← getFileMap
  let file ← relFileName
  let some pos := stx.getPos? | `(({} : Ember.Lang.Span))
  let p := fm.toPosition pos
  `(({ file := $(strLit file), line := $(natLit p.line), col := $(natLit (p.column + 1)) } : Ember.Lang.Span))

def mkList (xs : Array Term) : TM Term := `([$xs,*])

partial def tyT (stx : TSyntax `ember_ty) : TM Term := do
  match stx with
  | `(ember_ty| $id:ident) =>
    match id.getId.toString with
    | "u8" => `(Ember.Lang.Ty.int .w8)
    | "u16" => `(Ember.Lang.Ty.int .w16)
    | "u32" => `(Ember.Lang.Ty.int .w32)
    | "u64" => `(Ember.Lang.Ty.int .w64)
    | "bool" => `(Ember.Lang.Ty.bool)
    | n => `(Ember.Lang.Ty.record $(strLit n))
  | `(ember_ty| [$t; $n]) => `(Ember.Lang.Ty.arr $(← tyT t) $n)
  | _ => throwErrorAt stx "bad Ember type"

def widthOf (stx : TSyntax `ember_ty) : TM Term := do
  match stx with
  | `(ember_ty| $id:ident) =>
    match id.getId.toString with
    | "u8" => `(Ember.Lang.Width.w8)
    | "u16" => `(Ember.Lang.Width.w16)
    | "u32" => `(Ember.Lang.Width.w32)
    | "u64" => `(Ember.Lang.Width.w64)
    | _ => throwErrorAt stx "expected an integer type (u8, u16, u32, u64)"
  | _ => throwErrorAt stx "expected an integer type"

/-- `a.b.c` → field chain on variable `a`. -/
def dotted (n : Name) : TM Term := do
  let comps := n.componentsRev.reverse.map (·.toString)
  match comps with
  | [] => throwError "empty name"
  | x :: fs => fs.foldlM (fun acc f => `(Ember.Lang.Expr.field $acc $(strLit f))) (← `(Ember.Lang.Expr.var $(strLit x)))

def binT (op : Name) (a b : Term) : TM Term :=
  `(Ember.Lang.Expr.bin $(mkIdent op) $a $b)

partial def exprT (stx : TSyntax `ember_expr) : TM Term := do
  let bin (op : Name) (a b : TSyntax `ember_expr) : TM Term := do binT op (← exprT a) (← exprT b)
  match stx with
  | `(ember_expr| $id:ident) =>
    match id.getId.toString with
    | "true" => `(Ember.Lang.Expr.blit Bool.true)
    | "false" => `(Ember.Lang.Expr.blit Bool.false)
    | _ => dotted id.getId
  | `(ember_expr| $n:num) => `(Ember.Lang.Expr.lit $n none)
  | `(ember_expr| ($e)) => exprT e
  | `(ember_expr| ($e : $t)) => `(Ember.Lang.Expr.cast $(← widthOf t) $(← exprT e))
  | `(ember_expr| $a[$i]) => `(Ember.Lang.Expr.index $(← exprT a) $(← exprT i))
  | `(ember_expr| $a[$i].$f) => `(Ember.Lang.Expr.field (Ember.Lang.Expr.index $(← exprT a) $(← exprT i)) $(strLit f.getId.toString))
  | `(ember_expr| ~~~ $a) => `(Ember.Lang.Expr.un .bnot $(← exprT a))
  | `(ember_expr| ! $a) => `(Ember.Lang.Expr.un .lnot $(← exprT a))
  | `(ember_expr| - $a) => `(Ember.Lang.Expr.un .neg $(← exprT a))
  | `(ember_expr| $a <<< $b) => bin ``Ember.Lang.BinOp.shl a b
  | `(ember_expr| $a >>> $b) => bin ``Ember.Lang.BinOp.shr a b
  | `(ember_expr| $a * $b) => bin ``Ember.Lang.BinOp.mul a b
  | `(ember_expr| $a / $b) => bin ``Ember.Lang.BinOp.div a b
  | `(ember_expr| $a % $b) => bin ``Ember.Lang.BinOp.mod a b
  | `(ember_expr| $a + $b) => bin ``Ember.Lang.BinOp.add a b
  | `(ember_expr| $a - $b) => bin ``Ember.Lang.BinOp.sub a b
  | `(ember_expr| $a &&& $b) => bin ``Ember.Lang.BinOp.band a b
  | `(ember_expr| $a ^^^ $b) => bin ``Ember.Lang.BinOp.bxor a b
  | `(ember_expr| $a ||| $b) => bin ``Ember.Lang.BinOp.bor a b
  | `(ember_expr| $a == $b) => bin ``Ember.Lang.BinOp.eq a b
  | `(ember_expr| $a != $b) => bin ``Ember.Lang.BinOp.ne a b
  | `(ember_expr| $a < $b) => bin ``Ember.Lang.BinOp.lt a b
  | `(ember_expr| $a <= $b) => bin ``Ember.Lang.BinOp.le a b
  | `(ember_expr| $a > $b) => bin ``Ember.Lang.BinOp.gt a b
  | `(ember_expr| $a >= $b) => bin ``Ember.Lang.BinOp.ge a b
  | `(ember_expr| $a && $b) => bin ``Ember.Lang.BinOp.land a b
  | `(ember_expr| $a || $b) => bin ``Ember.Lang.BinOp.lor a b
  | `(ember_expr| if $c then $a else $b) => `(Ember.Lang.Expr.cond $(← exprT c) $(← exprT a) $(← exprT b))
  | _ => throwErrorAt stx "unsupported Ember expression"

def argsT (stx : TSyntax `Ember.Lang.Surface.ember_args) : TM Term := do
  match stx with
  | `(ember_args| ($as,*)) => mkList (← as.getElems.mapM exprT)
  | _ => throwErrorAt stx "bad arguments"

/-- A call statement: an effect when the name is one (`out.byte`), else a function. -/
def callT (dst : Term) (f : Ident) (args : TSyntax `Ember.Lang.Surface.ember_args) : TM Term := do
  let name := f.getId.toString
  let as ← argsT args
  match Ember.Lang.Effect.ofName? name with
  | some _ => `(Ember.Lang.Stmt.eff $dst ((Ember.Lang.Effect.ofName? $(strLit name)).get!) $as)
  | none => `(Ember.Lang.Stmt.call $dst $(strLit name) $as)

mutual

partial def seqT (stx : TSyntax `Ember.Lang.Surface.ember_seq) : TM Term := do
  match stx with
  | `(ember_seq| $[$ss $[;]?]*) => mkList (← ss.mapM stmtT)
  | _ => throwErrorAt stx "bad statement sequence"

partial def stmtT (stx : TSyntax `ember_stmt) : TM Term := do
  let sp ← spanOf stx
  let s ← match stx with
    | `(ember_stmt| let $[mut]? $x:ident : $t := $e) =>
      `(Ember.Lang.Stmt.decl $(strLit x.getId.toString) $(← tyT t) (some $(← exprT e)))
    | `(ember_stmt| let $[mut]? $x:ident : $t ← $f:ident $as:ember_args) => do
      let decl ← `(Ember.Lang.Stmt.decl $(strLit x.getId.toString) $(← tyT t) none)
      let c ← callT (← `(some (Ember.Lang.Expr.var $(strLit x.getId.toString)))) f as
      -- a declaration followed by the call: two statements
      return ← `([Ember.Lang.Stmt.at $sp $decl, Ember.Lang.Stmt.at $sp $c])
    | `(ember_stmt| let $[mut]? $x:ident : $t) =>
      `(Ember.Lang.Stmt.decl $(strLit x.getId.toString) $(← tyT t) none)
    | `(ember_stmt| $f:ident $as:ember_args) => callT (← `(none)) f as
    | `(ember_stmt| $d:ember_expr ← $f:ident $as:ember_args) => callT (← `(some $(← exprT d))) f as
    | `(ember_stmt| $l:ember_expr := $r) => `(Ember.Lang.Stmt.assign $(← exprT l) $(← exprT r))
    | `(ember_stmt| if $c then $t $[else $e]?) =>
      let et ← match e with
        | some e => seqT e
        | none => `([])
      `(Ember.Lang.Stmt.ite $(← exprT c) (List.flatten $(← seqT t)) (List.flatten $et))
    | `(ember_stmt| for $i:ident $[: $t]? in [$lo, $hi) do $b) =>
      let w ← match t with
        | some t => `(some $(← widthOf t))
        | none => `(none)
      `(Ember.Lang.Stmt.forRange $(strLit i.getId.toString) $w $(← exprT lo) $(← exprT hi) (List.flatten $(← seqT b)))
    | `(ember_stmt| break) => `(Ember.Lang.Stmt.brk)
    | `(ember_stmt| return) => `(Ember.Lang.Stmt.ret none)
    | `(ember_stmt| return $e) => `(Ember.Lang.Stmt.ret (some $(← exprT e)))
    | _ =>
      if stx.raw.getKind == ``loopStmt then
        let n : TSyntax `num := ⟨stx.raw[4]⟩
        let b : TSyntax `Ember.Lang.Surface.ember_seq := ⟨stx.raw[7]⟩
        `(Ember.Lang.Stmt.loop $n (List.flatten $(← seqT b)))
      else throwErrorAt stx "unsupported Ember statement"
  `([Ember.Lang.Stmt.at $sp $s])

end

/-! ## Commands -/

def paramsT (ps : Array (TSyntax `Ember.Lang.Surface.ember_param)) : TM Term := do
  let mut out : Array Term := #[]
  for p in ps do
    match p with
    | `(ember_param| ($xs* : $[ref%$r]? $t)) =>
      for x in xs do
        let byRef ← if r.isSome then `(Bool.true) else `(Bool.false)
        out := out.push (← `(({ name := $(strLit x.getId.toString), ty := $(← tyT t), byRef := $byRef } : Ember.Lang.Param)))
    | _ => throwErrorAt p "bad parameter"
  mkList out

elab_rules : command
  | `($[$doc?:docComment]? ember def $f:ident $ps:ember_param* $[: $rt]? := do $body) => do
    let ret ← match rt with
      | some t => `(some $(← tyT t))
      | none => `(none)
    let sp ← spanOf f
    let defn ← `($[$doc?:docComment]? def $f : Ember.Lang.Fn :=
      { name := $(strLit f.getId.toString), params := $(← paramsT ps), ret := $ret,
        body := List.flatten $(← seqT body), span := $sp })
    elabCommand defn

elab_rules : command
  | `($[$doc?:docComment]? ember global $x:ident : $t $[:= [$vs,*]]?) => do
    let init ← match vs with
      | some vs => `([$(vs.getElems),*])
      | none => `([])
    elabCommand (← `($[$doc?:docComment]? def $x : Ember.Lang.Global :=
      { name := $(strLit x.getId.toString), ty := $(← tyT t), init := $init }))

elab_rules : command
  | `($[$doc?:docComment]? ember global $x:ident : $t := $v:num) => do
    elabCommand (← `($[$doc?:docComment]? def $x : Ember.Lang.Global :=
      { name := $(strLit x.getId.toString), ty := $(← tyT t), init := [$v] }))

elab_rules : command
  | `($[$doc?:docComment]? ember const $x:ident : $t := $v:num) => do
    elabCommand (← `($[$doc?:docComment]? def $x : Ember.Lang.Global :=
      { name := $(strLit x.getId.toString), ty := $(← tyT t), init := [$v], const := true }))

elab_rules : command
  | `($[$doc?:docComment]? ember const $x:ident : $t := [$vs,*]) => do
    elabCommand (← `($[$doc?:docComment]? def $x : Ember.Lang.Global :=
      { name := $(strLit x.getId.toString), ty := $(← tyT t), init := [$(vs.getElems),*], const := true }))

elab_rules : command
  | `($[$doc?:docComment]? ember struct $x:ident where $[$fs : $ts]*) => do
    let mut fields : Array Term := #[]
    for (f, t) in fs.zip ts do
      fields := fields.push (← `(($(strLit f.getId.toString), $(← tyT t))))
    elabCommand (← `($[$doc?:docComment]? def $x : Ember.Lang.StructDef :=
      { name := $(strLit x.getId.toString), fields := $(← mkList fields) }))

end Ember.Lang.Surface
