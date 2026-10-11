/-!
# Ember.Lang.Syntax — the abstract syntax of Ember (M2.1)

Ember is deliberately small (design §2.2):

* types: `u8 u16 u32 u64 bool`, fixed arrays of scalars `[τ; n]`, and
  named records of scalars and arrays.  No pointers: a function may take
  an array or a record *by reference*; two references in one call never
  name overlapping storage (checked), so there is no aliasing;
* expressions are side-effect free and total: arithmetic is modulo 2^w,
  a shift by ≥ w gives 0, division and remainder by zero give 0, and
  both operands of every operator (including `&&`, `||` and `if … then
  … else`) are evaluated — an out-of-range array read anywhere in an
  expression is an error;
* statements: `let`, assignment, `if`, bounded loops (`for i in [lo,
  hi)` and `loop (max := n)`), `break`, `return`, calls, effects; no
  recursion;
* effects are explicit statements (`Effect`), recorded by the semantics
  as a trace and served by an input oracle.

Source spans are attached to statements (`Stmt.at`); an expression's
location is that of its statement.  Hand-built ASTs may omit spans.
-/

namespace Ember.Lang

inductive Width where
  | w8 | w16 | w32 | w64
  deriving Inhabited, BEq, Repr, DecidableEq, Hashable

def Width.bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

def Width.modulus (w : Width) : Nat := 2 ^ w.bits

def Width.ofBits? : Nat → Option Width
  | 8 => some .w8 | 16 => some .w16 | 32 => some .w32 | 64 => some .w64 | _ => none

def Width.name (w : Width) : String := s!"u{w.bits}"

inductive Ty where
  | int  (w : Width)
  | bool
  | arr  (elem : Ty) (n : Nat)
  | record (name : String)
  deriving Inhabited, BEq, Repr

def Ty.u8 : Ty := .int .w8
def Ty.u16 : Ty := .int .w16
def Ty.u32 : Ty := .int .w32
def Ty.u64 : Ty := .int .w64

def Ty.isScalar : Ty → Bool
  | .int _ | .bool => true
  | _ => false

partial def Ty.toString : Ty → String
  | .int w => w.name
  | .bool => "bool"
  | .arr e n => s!"[{e.toString}; {n}]"
  | .record n => n

instance : ToString Ty := ⟨Ty.toString⟩

inductive BinOp where
  | add | sub | mul | div | mod
  | band | bor | bxor | shl | shr
  | eq | ne | lt | le | gt | ge
  | land | lor
  deriving Inhabited, BEq, Repr, DecidableEq

def BinOp.symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .band => "&&&" | .bor => "|||" | .bxor => "^^^" | .shl => "<<<" | .shr => ">>>"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .land => "&&" | .lor => "||"

def BinOp.isCompare : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def BinOp.isLogic : BinOp → Bool
  | .land | .lor => true
  | _ => false

def BinOp.isShift : BinOp → Bool
  | .shl | .shr => true
  | _ => false

inductive UnOp where
  | bnot  -- `~~~`, bitwise complement
  | neg   -- `-`, two's complement negation modulo 2^w
  | lnot  -- `!`, on bool
  deriving Inhabited, BEq, Repr, DecidableEq

inductive Expr where
  /-- Integer literal; the width is filled in by the type checker when
  the surface syntax left it open. -/
  | lit   (v : Nat) (w : Option Width)
  | blit  (b : Bool)
  | var   (x : String)
  | field (e : Expr) (f : String)
  | index (e : Expr) (i : Expr)
  | bin   (op : BinOp) (a b : Expr)
  | un    (op : UnOp) (a : Expr)
  /-- Zero-extend or truncate an integer to `w`; `bool` casts to 0/1. -/
  | cast  (w : Width) (a : Expr)
  | cond  (c a b : Expr)
  deriving Inhabited, BEq, Repr

/-- Effects: everything a program does besides computing. -/
inductive Effect where
  /-- Next input item: a byte `0x00..0xFF`, `0x0100` for a tick,
  `0xFFFF` when there is nothing left.  Returns `u16`. -/
  | inputNext
  /-- Append a byte to the frame being transmitted. -/
  | outByte
  /-- The frame being transmitted is complete. -/
  | outEnd
  /-- Diagnostic: `drop reason=<name>` for a reason code (`Prog.dropReasons`). -/
  | drop
  /-- Diagnostic: `note <name> <value>` for a note code (`Prog.notes`). -/
  | note
  | mmioRead32
  | mmioWrite32
  /-- The runtime's receive ring (on the host it is the input oracle). -/
  | ringPop
  /-- Next input item of a link that delivers whole frames (Ethernet):
  as `input.next`, and `0x0200` after the last byte of each frame.
  A program uses either this or `input.next`. -/
  | inputFrame
  deriving Inhabited, BEq, Repr, DecidableEq

def Effect.name : Effect → String
  | .inputNext => "input.next" | .outByte => "out.byte" | .outEnd => "out.end"
  | .drop => "trace.drop" | .note => "trace.note"
  | .mmioRead32 => "mmio.read32" | .mmioWrite32 => "mmio.write32" | .ringPop => "ring.pop"
  | .inputFrame => "input.frame"

def Effect.all : List Effect :=
  [.inputNext, .outByte, .outEnd, .drop, .note, .mmioRead32, .mmioWrite32, .ringPop, .inputFrame]

def Effect.ofName? (s : String) : Option Effect := Effect.all.find? (·.name == s)

/-- Argument types and result type of an effect. -/
def Effect.sig : Effect → List Ty × Option Ty
  | .inputNext => ([], some .u16)
  | .outByte => ([.u8], none)
  | .outEnd => ([], none)
  | .drop => ([.u8], none)
  | .note => ([.u8, .u32], none)
  | .mmioRead32 => ([.u32], some .u32)
  | .mmioWrite32 => ([.u32, .u32], none)
  | .ringPop => ([], some .u16)
  | .inputFrame => ([], some .u16)

structure Span where
  file : String := ""
  line : Nat := 0
  col  : Nat := 0
  deriving Inhabited, BEq, Repr

def Span.toString (s : Span) : String :=
  if s.line == 0 then "<no span>" else s!"{s.file}:{s.line}:{s.col}"

inductive Stmt where
  /-- A local variable; arrays and records start zeroed, scalars too when
  `init` is absent. -/
  | decl  (x : String) (ty : Ty) (init : Option Expr)
  | assign (lhs : Expr) (rhs : Expr)
  | ite   (c : Expr) (t e : List Stmt)
  /-- `for i in [lo, hi)`: bounds evaluated once; `i` is read-only.  The
  width of `i` is inferred by the checker when absent. -/
  | forRange (i : String) (w : Option Width) (lo hi : Expr) (body : List Stmt)
  /-- At most `max` iterations; `break` leaves early. -/
  | loop  (max : Nat) (body : List Stmt)
  | brk
  | ret   (e : Option Expr)
  | call  (dst : Option Expr) (f : String) (args : List Expr)
  | eff   (dst : Option Expr) (e : Effect) (args : List Expr)
  | at    (sp : Span) (s : Stmt)
  deriving Inhabited, BEq, Repr

structure Param where
  name  : String
  ty    : Ty
  byRef : Bool := false
  deriving Inhabited, BEq, Repr

structure Fn where
  name   : String
  params : List Param := []
  ret    : Option Ty := none
  body   : List Stmt
  span   : Span := {}
  deriving Inhabited, BEq, Repr

structure StructDef where
  name   : String
  fields : List (String × Ty)
  deriving Inhabited, BEq, Repr

structure Global where
  name  : String
  ty    : Ty
  /-- Initial value: one number for a scalar, one per element for an
  array (missing elements are 0); records start zeroed. -/
  init  : List Nat := []
  /-- Constants cannot be assigned; the emitter makes them `static const`. -/
  const : Bool := false
  deriving Inhabited, BEq, Repr

structure Prog where
  structs : List StructDef := []
  globals : List Global := []
  fns     : List Fn
  /-- Called repeatedly by the driver while input remains. -/
  entry   : String := "main"
  /-- Names of the `trace.drop` reason codes, by index. -/
  dropReasons : List String := []
  /-- Names of the `trace.note` codes, by index. -/
  notes : List String := []
  deriving Inhabited, BEq, Repr

def Prog.fn? (p : Prog) (f : String) : Option Fn := p.fns.find? (·.name == f)

mutual
/-- Does the statement use the effect `e`?  (Structural, so that proofs can compute it.) -/
def Stmt.usesEffect (e : Effect) : Stmt → Bool
  | .eff _ e' _ => e == e'
  | .ite _ t f => Stmt.usesEffectL e t || Stmt.usesEffectL e f
  | .forRange _ _ _ _ b => Stmt.usesEffectL e b
  | .loop _ b => Stmt.usesEffectL e b
  | .at _ s => Stmt.usesEffect e s
  | _ => false
def Stmt.usesEffectL (e : Effect) : List Stmt → Bool
  | [] => false
  | s :: r => Stmt.usesEffect e s || Stmt.usesEffectL e r
end

/-- Does the program read its input frame by frame (`input.frame`)? -/
def Prog.framed (p : Prog) : Bool := p.fns.any fun f => Stmt.usesEffectL .inputFrame f.body
def Prog.global? (p : Prog) (g : String) : Option Global := p.globals.find? (·.name == g)
def Prog.struct? (p : Prog) (s : String) : Option StructDef := p.structs.find? (·.name == s)

/-- Strip span wrappers. -/
def Stmt.core : Stmt → Stmt
  | .at _ s => s.core
  | s => s

/-! Small constructors used by hand-built ASTs and the generator. -/

namespace Expr
def u8 (n : Nat) : Expr := .lit n (some .w8)
def u16 (n : Nat) : Expr := .lit n (some .w16)
def u32 (n : Nat) : Expr := .lit n (some .w32)
def u64 (n : Nat) : Expr := .lit n (some .w64)
instance : Add Expr := ⟨.bin .add⟩
instance : Sub Expr := ⟨.bin .sub⟩
instance : Mul Expr := ⟨.bin .mul⟩
end Expr

end Ember.Lang
