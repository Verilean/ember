import Ember.Lang.Eval
import Ember.C.Compile

/-!
# Ember.Z80.IR — the linear intermediate representation (plan M6.3)

Between Ember and Z80 code.  What it makes explicit:

* **sizes**: every operation says how many bytes it works on (1, 2, 4,
  8; a `bool` is one byte, 0 or 1);
* **storage**: every variable is at a fixed place — a global, or an
  offset in the frame of its function.  Ember has no recursion, so
  frames are static (`Ember.Z80.Frame` lays them out); a by-reference
  parameter is a two-byte slot holding an address;
* **control**: labels, jumps and compare-and-branch;
* **checks**: an index is checked where the address is formed
  (`Index.len`), a failed check is a trap.

Temporaries (`tmp`) are function-local values without a place; the code
generator keeps one in a register when its use follows its definition
and gives it a frame slot otherwise.

`lower` translates a checked program.  Expressions are evaluated
strictly, as the interpreter does; `&&` and `||` jump early only when
the skipped operand cannot trap.  Unsigned comparisons are reduced to
`eq ne lt ge` by swapping operands.
-/

namespace Ember.Z80.IR
open Ember.Lang

inductive Area where
  | global (g : String)
  | frame (f : String)
  deriving BEq, Repr, Inhabited, Hashable

structure Slot where
  area : Area
  off : Nat := 0
  deriving BEq, Repr, Inhabited

inductive Opd where
  | const (v : Nat)
  | slot (s : Slot)
  | tmp (t : Nat)
  deriving BEq, Repr, Inhabited

inductive Dst where
  | slot (s : Slot)
  | tmp (t : Nat)
  deriving BEq, Repr, Inhabited

def Dst.opd : Dst → Opd
  | .slot s => .slot s
  | .tmp t => .tmp t

inductive Bin where
  | add | sub | mul | div | mod | and | or | xor
  deriving BEq, Repr, Inhabited, DecidableEq

def Bin.commutes : Bin → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- Unsigned comparisons. -/
inductive Cmp where
  | eq | ne | lt | ge
  deriving BEq, Repr, Inhabited, DecidableEq

def Cmp.negate : Cmp → Cmp
  | .eq => .ne | .ne => .eq | .lt => .ge | .ge => .lt

/-- A dynamic index: `size` bytes (1 or 2), times `scale`; with `len`,
a trap unless it is below. -/
structure Index where
  opd : Opd
  size : Nat
  scale : Nat
  len : Option Nat
  deriving BEq, Repr, Inhabited

inductive Root where
  | static (s : Slot)
  /-- The address stored in the two bytes at `p`. -/
  | ptr (p : Slot)
  deriving BEq, Repr, Inhabited

/-- `root + off + idx · scale`. -/
structure Addr where
  root : Root
  off : Nat := 0
  idx : Option Index := none
  deriving BEq, Repr, Inhabited

inductive Instr where
  | mov (n : Nat) (dst : Dst) (src : Opd)
  | bin (op : Bin) (n : Nat) (dst : Dst) (a b : Opd)
  /-- Shift by `amt` (of `m` bytes); the result is 0 from `8·n` on. -/
  | shift (left : Bool) (n : Nat) (dst : Dst) (a : Opd) (m : Nat) (amt : Opd)
  | not (n : Nat) (dst : Dst) (a : Opd)
  | neg (n : Nat) (dst : Dst) (a : Opd)
  /-- Zero-extend (`n > m`) or truncate (`n < m`). -/
  | ext (n : Nat) (dst : Dst) (m : Nat) (src : Opd)
  /-- `dst` (one byte) := `a op b`, operands of `n` bytes. -/
  | cmp (op : Cmp) (n : Nat) (dst : Dst) (a b : Opd)
  | br (op : Cmp) (n : Nat) (a b : Opd) (target : Nat)
  | jmp (target : Nat)
  | label (l : Nat)
  | load (n : Nat) (dst : Dst) (p : Addr)
  | store (n : Nat) (p : Addr) (src : Opd)
  /-- The address itself, two bytes. -/
  | lea (dst : Dst) (p : Addr)
  | zero (s : Slot) (bytes : Nat)
  /-- `reg`: the argument that travels in a register (see `Fn.regParam`). -/
  | call (f : String) (ret : Option (Nat × Dst)) (reg : Option (Nat × Opd) := none)
  | eff (e : Effect) (args : List (Nat × Opd)) (ret : Option (Nat × Dst))
  | ret (v : Option (Nat × Opd))
  | trap
  deriving BEq, Repr, Inhabited

structure Fn where
  name : String
  /-- The parameter passed in a register (`A` or `HL`): its size and slot.
  The function stores it on entry. -/
  regParam : Option (Nat × Slot) := none
  /-- Bytes of parameters and locals (temporaries come on top). -/
  frame : Nat
  body : Array Instr
  /-- Size of every temporary. -/
  tmps : Array Nat
  /-- Functions whose bodies were copied into this one: their frames are
  in use while this function runs. -/
  inlined : List String := []
  /-- Every call was replaced by the body: no code of its own is needed
  (the frame still is). -/
  dead : Bool := false
  deriving Inhabited, Repr

structure Global where
  name : String
  size : Nat
  /-- Initial bytes, when not all zero. -/
  init : Option ByteArray := none
  const : Bool := false
  deriving Inhabited

structure Prog where
  globals : List Global
  fns : List Fn
  entry : String
  deriving Inhabited

def Prog.fn? (p : Prog) (f : String) : Option Fn := p.fns.find? (·.name == f)

def Fn.calls (f : Fn) : List String :=
  f.body.toList.filterMap fun i => match i with | .call g _ _ => some g | _ => none

/-- The functions whose frames are live while `f` runs, one level down. -/
def Fn.callees (f : Fn) : List String := (f.calls ++ f.inlined).eraseDups

/-! ## Text -/

def Slot.text (s : Slot) : String :=
  let b := match s.area with | .global g => g | .frame f => s!"{f}.frame"
  if s.off == 0 then b else s!"{b}+{s.off}"

def Opd.text : Opd → String
  | .const v => toString v
  | .slot s => s!"[{s.text}]"
  | .tmp t => s!"t{t}"

def Dst.text (d : Dst) : String := d.opd.text

def Addr.text (a : Addr) : String :=
  let r := match a.root with | .static s => s.text | .ptr p => s!"*[{p.text}]"
  let o := if a.off == 0 then "" else s!"+{a.off}"
  let i := match a.idx with
    | none => ""
    | some x => s!"+{x.opd.text}:{x.size}" ++ (if x.scale == 1 then "" else s!"*{x.scale}") ++
        (match x.len with | some n => s!"<{n}" | none => "")
  s!"[{r}{o}{i}]"

def Instr.text : Instr → String
  | .mov n d s => s!"  {d.text} := {s.text}  :{n}"
  | .bin op n d a b => s!"  {d.text} := {(toString (repr op)).splitOn "." |>.getLast!} {a.text}, {b.text}  :{n}"
  | .shift l n d a m amt => s!"  {d.text} := {if l then "shl" else "shr"} {a.text}, {amt.text}:{m}  :{n}"
  | .not n d a => s!"  {d.text} := not {a.text}  :{n}"
  | .neg n d a => s!"  {d.text} := neg {a.text}  :{n}"
  | .ext n d m s => s!"  {d.text} := ext {s.text}:{m}  :{n}"
  | .cmp op n d a b => s!"  {d.text} := {(toString (repr op)).splitOn "." |>.getLast!} {a.text}, {b.text}  :{n}"
  | .br op n a b l => s!"  if {(toString (repr op)).splitOn "." |>.getLast!} {a.text}, {b.text} :{n} goto L{l}"
  | .jmp l => s!"  goto L{l}"
  | .label l => s!"L{l}:"
  | .load n d p => s!"  {d.text} := {p.text}  :{n}"
  | .store n p s => s!"  {p.text} := {s.text}  :{n}"
  | .lea d p => s!"  {d.text} := &{p.text}"
  | .zero s n => s!"  zero [{s.text}], {n}"
  | .call f r reg =>
    let a := match reg with | some (n, o) => s!"({o.text}:{n})" | none => ""
    (match r with | some (n, d) => s!"  {d.text} := call {f}{a}  :{n}" | none => s!"  call {f}{a}")
  | .eff e args r =>
    let a := ", ".intercalate (args.map fun (n, o) => s!"{o.text}:{n}")
    (match r with | some (n, d) => s!"  {d.text} := {e.name}({a})  :{n}" | none => s!"  {e.name}({a})")
  | .ret none => "  ret"
  | .ret (some (n, o)) => s!"  ret {o.text}  :{n}"
  | .trap => "  trap"

def Fn.text (f : Fn) : String :=
  s!"fn {f.name} (frame {f.frame}):\n" ++ "\n".intercalate (f.body.toList.map Instr.text) ++ "\n"

def Prog.text (p : Prog) : String := "\n".intercalate (p.fns.map Fn.text)

/-! ## Layout of types -/

partial def sizeOf (p : Lang.Prog) : Ty → Nat
  | .int w => w.bits / 8
  | .bool => 1
  | .arr el n => n * sizeOf p el
  | .record r => ((p.struct? r).map (·.fields)).getD [] |>.foldl (fun acc (_, t) => acc + sizeOf p t) 0

def fieldOff (p : Lang.Prog) (r f : String) : Option (Nat × Ty) := Id.run do
  let mut off := 0
  for (g, t) in ((p.struct? r).map (·.fields)).getD [] do
    if g == f then return some (off, t)
    off := off + sizeOf p t
  return none

/-- The parameter that travels in a register: the last one that is one or
two bytes by value. -/
def regParamOf (p : Lang.Prog) (f : Lang.Fn) : Option String :=
  (f.params.reverse.find? fun prm => !prm.byRef && sizeOf p prm.ty ≤ 2).map (·.name)

/-- Offsets of the parameters in the frame, and the bytes they take: a
by-reference parameter is an address. -/
def paramSlots (p : Lang.Prog) (f : Lang.Fn) : List (Lang.Param × Nat) × Nat := Id.run do
  let mut off := 0
  let mut out := #[]
  for prm in f.params do
    out := out.push (prm, off)
    off := off + (if prm.byRef then 2 else sizeOf p prm.ty)
  return (out.toList, off)

/-! ## Lowering -/

inductive Storage where
  | static (s : Slot)
  | ref (p : Slot)
  deriving Inhabited

structure VarInfo where
  ty : Ty
  at_ : Storage
  deriving Inhabited

structure Env where
  prog : Lang.Prog
  fn : String
  vars : List (String × VarInfo) := []
  /-- Label of the end of the innermost loop. -/
  loopEnd : Option Nat := none
  /-- The declaration being lowered is assigned by the next statement (a
  call or an effect that does not read it): no need to zero it. -/
  noZero : Bool := false

structure LS where
  out : Array Instr := #[]
  tmps : Array Nat := #[]
  labels : Nat := 0
  /-- Bytes of the frame in use, and the most that ever were. -/
  cur : Nat := 0
  max : Nat := 0
  trapLabel : Option Nat := none

abbrev LM := ReaderT Env (StateT LS (Except String))

def err (msg : String) : LM α := do throw s!"{(← read).fn}: {msg}"
def emit (i : Instr) : LM Unit := modify fun s => { s with out := s.out.push i }

def newTmp (n : Nat) : LM Nat := do
  let s ← get
  set { s with tmps := s.tmps.push n }
  return s.tmps.size

def newLabel : LM Nat := do
  let s ← get
  set { s with labels := s.labels + 1 }
  return s.labels

def allocLocal (n : Nat) : LM Slot := do
  let s ← get
  let cur := s.cur + n
  set { s with cur, max := Nat.max s.max cur }
  return { area := .frame (← read).fn, off := s.cur }

/-- Locals of a block give their bytes back at its end. -/
def inScope (m : LM α) : LM α := do
  let mark := (← get).cur
  let r ← m
  modify fun s => { s with cur := mark }
  return r

def trapLabel : LM Nat := do
  if let some l := (← get).trapLabel then return l
  let l ← newLabel
  modify fun s => { s with trapLabel := some l }
  return l

def varInfo (x : String) : LM VarInfo := do
  let e ← read
  if let some v := e.vars.lookup x then return v
  match e.prog.global? x with
  | some g => return { ty := g.ty, at_ := .static { area := .global x } }
  | none => err s!"unknown variable {x}"

partial def tyOf (e : Expr) : LM Ty := do
  match e with
  | .lit _ (some w) => return .int w
  | .lit _ none => err "untyped literal (program not checked)"
  | .blit _ => return .bool
  | .var x => return (← varInfo x).ty
  | .field b f =>
    let .record r ← tyOf b | err "field of a non-record"
    match fieldOff (← read).prog r f with
    | some (_, t) => return t
    | none => err s!"no field {f}"
  | .index b _ =>
    let .arr el _ ← tyOf b | err "index of a non-array"
    return el
  | .bin op a _ => if op.isCompare || op.isLogic then return .bool else tyOf a
  | .un _ a => tyOf a
  | .cast w _ => return .int w
  | .cond _ a _ => tyOf a

def size (t : Ty) : LM Nat := do return sizeOf (← read).prog t

/-- The value of a closed expression (no variables), as its bytes. -/
def closed? (e : Expr) : Option Nat :=
  match C.closedVal e with
  | some (.int _ v) => some v.toNat
  | some (.bool b) => some (if b then 1 else 0)
  | _ => none

/-- Can evaluating the expression trap?  (An index that is not a constant.) -/
partial def canTrap : Expr → Bool
  | .index b i => (closed? i).isNone || canTrap b
  | .field b _ => canTrap b
  | .bin _ a b => canTrap a || canTrap b
  | .un _ a => canTrap a
  | .cast _ a => canTrap a
  | .cond c a b => canTrap c || canTrap a || canTrap b
  | _ => false

def isSimple : Opd → Bool
  | .tmp _ => false
  | _ => true

mutual

/-- Where a place is. -/
partial def place (e : Expr) : LM (Addr × Ty) := do
  match e with
  | .var x =>
    let v ← varInfo x
    match v.at_ with
    | .static s => return ({ root := .static s }, v.ty)
    | .ref p => return ({ root := .ptr p }, v.ty)
  | .field b f =>
    let (a, t) ← place b
    let .record r := t | err "field of a non-record"
    let some (off, ft) := fieldOff (← read).prog r f | err s!"no field {f}"
    return ({ a with off := a.off + off }, ft)
  | .index b i =>
    let (a, t) ← place b
    let .arr el n := t | err "index of a non-array"
    let scale ← size el
    if a.idx.isSome then err "nested arrays"
    if let some v := closed? i then
      if v < n then return ({ a with off := a.off + v * scale }, el)
      -- a constant index out of range: the trap, and any address after it
      emit .trap
      return (a, el)
    let .int iw ← tyOf i | err "non-integer index"
    let m := iw.bits / 8
    let o ← expr i
    if m ≤ 2 then
      let len := if n ≥ 2 ^ iw.bits then none else some n
      return ({ a with idx := some { opd := o, size := m, scale, len } }, el)
    -- a wide index: compared as it is, then its low two bytes
    emit (.br .ge m o (.const n) (← trapLabel))
    let lowOpd ← match o with
      | .slot s => pure (Opd.slot s)
      | o =>
        let t ← newTmp 2
        emit (.ext 2 (.tmp t) m o)
        pure (.tmp t)
    return ({ a with idx := some { opd := lowOpd, size := 2, scale, len := none } }, el)
  | _ => err "not a place"

/-- The expression as an operand: a constant or a variable as it is,
anything else in a new temporary. -/
partial def expr (e : Expr) : LM Opd := do
  if let some v := closed? e then return .const v
  -- a constant is its value
  if let .var x := e then
    let env ← read
    if (env.vars.lookup x).isNone then
      if let some g := env.prog.global? x then
        if g.const && g.ty.isScalar then
          return .const (match g.init with | [v] => v % 2 ^ (8 * sizeOf env.prog g.ty) | _ => 0)
  match e with
  | .var _ | .field _ _ | .index _ _ =>
    let (a, t) ← place e
    match a.root, a.idx with
    | .static s, none => return .slot { s with off := s.off + a.off }
    | _, _ =>
      let d ← newTmp (← size t)
      emit (.load (← size t) (.tmp d) a)
      return .tmp d
  | .cast w a =>
    let n := w.bits / 8
    let m ← size (← tyOf a)
    -- `(x >>> 8k : narrower)` of a variable is its bytes from `k` on
    if let .bin .shr x k := a then
      if let some kv := closed? k then
        if kv % 8 == 0 && kv / 8 + n ≤ m then
          if let .slot s ← expr x then return .slot { s with off := s.off + kv / 8 }
    let o ← expr a
    -- the low bytes of a variable are the variable (little-endian)
    match o with
    | .slot s => if n ≤ m then return .slot s
    | .tmp _ => if n == m then return o
    | _ => pure ()
    let d ← newTmp n
    emit (.ext n (.tmp d) m o)
    return .tmp d
  | _ =>
    let d ← newTmp (← size (← tyOf e))
    exprTo (.tmp d) e
    return .tmp d

/-- Evaluate into `dst`. -/
partial def exprTo (dst : Dst) (e : Expr) : LM Unit := do
  let n ← size (← tyOf e)
  if let some v := closed? e then emit (.mov n dst (.const v)); return
  if let .const v ← (match e with | .var _ => expr e | _ => pure (Opd.tmp 0)) then
    emit (.mov n dst (.const v)); return
  match e with
  | .lit .. | .blit _ => err "literal not closed"
  | .var _ | .field _ _ | .index _ _ =>
    let (a, _) ← place e
    match a.root, a.idx with
    | .static s, none => emit (.mov n dst (.slot { s with off := s.off + a.off }))
    | _, _ => emit (.load n dst a)
  | .bin op a b =>
    let m ← size (← tyOf a)
    -- the right operand first: the left one is then the value computed last
    let ob ← expr b
    let oa ← expr a
    let arith (k : Bin) : LM Unit :=
      -- a temporary on the left, where the code generator has it at hand
      if k.commutes && isSimple oa && !isSimple ob then emit (.bin k n dst ob oa) else emit (.bin k n dst oa ob)
    -- by a power of two: a shift or a mask
    let pow2 (o : Opd) : Option Nat := match o with
      | .const v => if v > 0 && v &&& (v - 1) == 0 then some v.log2 else none
      | _ => none
    let scaled (k : Bin) : LM Unit :=
      match k, pow2 oa, pow2 ob with
      | .mul, _, some s => emit (.shift true n dst oa 1 (.const s))
      | .mul, some s, none => emit (.shift true n dst ob 1 (.const s))
      | .div, _, some s => emit (.shift false n dst oa 1 (.const s))
      | .mod, _, some s => emit (.bin .and n dst oa (.const (2 ^ s - 1)))
      | k, _, _ => arith k
    match op with
    | .add => arith .add | .sub => arith .sub | .mul => scaled .mul
    | .div => scaled .div | .mod => scaled .mod
    | .band | .land => arith .and
    | .bor | .lor => arith .or
    | .bxor => arith .xor
    | .shl | .shr =>
      let sm ← size (← tyOf b)
      emit (.shift (op == .shl) n dst oa sm ob)
    | .eq => emit (.cmp .eq m dst oa ob)
    | .ne => emit (.cmp .ne m dst oa ob)
    | .lt => emit (.cmp .lt m dst oa ob)
    | .ge => emit (.cmp .ge m dst oa ob)
    | .le => emit (.cmp .ge m dst ob oa)
    | .gt => emit (.cmp .lt m dst ob oa)
  | .un op a =>
    let o ← expr a
    match op with
    | .lnot => emit (.bin .xor 1 dst o (.const 1))
    | .bnot => emit (.not n dst o)
    | .neg => emit (.neg n dst o)
  | .cast _ a =>
    let m ← size (← tyOf a)
    let o ← expr a
    if n == m then emit (.mov n dst o)
    else if n < m then
      match o with
      | .slot s => emit (.mov n dst (.slot s))
      | o => emit (.ext n dst m o)
    else emit (.ext n dst m o)
  | .cond c a b =>
    -- strict: all three are evaluated
    let oc ← expr c
    let oa ← expr a
    let ob ← expr b
    let l ← newLabel
    -- `dst` may be one of the operands' places only if it is a temporary
    -- of its own, which it is: conditionals into variables go through one
    emit (.mov n dst ob)
    emit (.br .eq 1 oc (.const 0) l)
    emit (.mov n dst oa)
    emit (.label l)

end

/-- Jump to `target` when the condition is `sense`. -/
partial def condJump (e : Expr) (sense : Bool) (target : Nat) : LM Unit := do
  if let some v := closed? e then
    if (v != 0) == sense then emit (.jmp target)
    return
  match e with
  | .un .lnot a => condJump a (!sense) target
  | .bin op a b =>
    if op.isCompare then
      let m ← size (← tyOf a)
      let ob ← expr b
      let oa ← expr a
      let (k, x, y) : Cmp × Opd × Opd := match op with
        | .eq => (.eq, oa, ob) | .ne => (.ne, oa, ob)
        | .lt => (.lt, oa, ob) | .ge => (.ge, oa, ob)
        | .le => (.ge, ob, oa) | _ => (.lt, ob, oa)
      -- `0 < y` is `y ≠ 0`, `0 ≥ y` is `y = 0`
      let (k, x, y) := match k, x with
        | .lt, .const 0 => (Cmp.ne, y, Opd.const 0)
        | .ge, .const 0 => (Cmp.eq, y, Opd.const 0)
        | _, _ => (k, x, y)
      emit (.br (if sense then k else k.negate) m x y target)
    else if op.isLogic && !canTrap b then
      -- skipping `b` is not observable
      let isAnd := op == .land
      if isAnd != sense then
        -- and/false, or/true: either operand decides
        condJump a sense target
        condJump b sense target
      else
        let skip ← newLabel
        condJump a (!sense) skip
        condJump b sense target
        emit (.label skip)
    else
      let o ← expr e
      emit (.br (if sense then .ne else .eq) 1 o (.const 0) target)
  | _ =>
    let o ← expr e
    emit (.br (if sense then .ne else .eq) 1 o (.const 0) target)

/-- A conditional expression must not write its destination before its
operands are read; anything else may compute straight into a variable. -/
partial def hasCond : Expr → Bool
  | .cond .. => true
  | .bin _ a b => hasCond a || hasCond b
  | .un _ a => hasCond a
  | .cast _ a => hasCond a
  | .index b i => hasCond b || hasCond i
  | .field b _ => hasCond b
  | _ => false

/-- Evaluate into a variable's slot. -/
def exprToSlot (s : Slot) (e : Expr) : LM Unit := do
  if hasCond e then
    let n ← size (← tyOf e)
    let o ← expr e
    emit (.mov n (.slot s) o)
  else exprTo (.slot s) e

def counterSize (n : Nat) : Nat := if n < 256 then 1 else if n < 65536 then 2 else 4

/-- Store a call's or an effect's result: the destination is evaluated
after the call, as the interpreter does. -/
def withResult (dst : Option Expr) (n : Option Nat) (mk : Option (Nat × Dst) → Instr) : LM Unit := do
  match dst, n with
  | some d, some n =>
    -- only the address of a plain variable is known before the call
    let simple ← match d with
      | .var x => match (← varInfo x).at_ with
        | .static s => pure (some s)
        | _ => pure none
      | _ => pure none
    match simple with
    | some s => emit (mk (some (n, .slot s)))
    | none =>
      let t ← newTmp n
      emit (mk (some (n, .tmp t)))
      let (a, _) ← place d
      match a.root, a.idx with
      | .static s, none => emit (.mov n (.slot { s with off := s.off + a.off }) (.tmp t))
      | _, _ => emit (.store n a (.tmp t))
  | _, _ => emit (mk none)

partial def mentions (x : String) : Expr → Bool
  | .var y => x == y
  | .field b _ => mentions x b
  | .index b i => mentions x b || mentions x i
  | .bin _ a b => mentions x a || mentions x b
  | .un _ a => mentions x a
  | .cast _ a => mentions x a
  | .cond c a b => mentions x c || mentions x a || mentions x b
  | _ => false

mutual

partial def block (ss : List Stmt) : LM Unit := inScope do
  let mut env ← read
  let mut rest := ss
  while !rest.isEmpty do
    let s := rest.head!
    rest := rest.tail!
    let noZero := match s.core, rest.head?.map Stmt.core with
      | .decl x ty none, some (.call (some (.var y)) _ args) => ty.isScalar && x == y && !args.any (mentions x)
      | .decl x ty none, some (.eff (some (.var y)) _ args) => ty.isScalar && x == y && !args.any (mentions x)
      | _, _ => false
    env ← withReader (fun _ => { env with noZero }) (stmt s)

/-- One statement; returns the environment for what follows. -/
partial def stmt (s : Stmt) : LM Env := do
  let env ← read
  match s with
  | .at _ s => stmt s
  | .decl x ty init =>
    let n ← size ty
    let slot ← allocLocal n
    match init, ty.isScalar with
    | some e, _ => exprToSlot slot e
    | none, true => unless env.noZero do emit (.mov n (.slot slot) (.const 0))
    | none, false => emit (.zero slot n)
    return { env with vars := (x, { ty, at_ := .static slot }) :: env.vars, noZero := false }
  | .assign l r =>
    let n ← size (← tyOf r)
    -- the value first, then the place (its index may trap)
    let plain ← match l with
      | .var x => match (← varInfo x).at_ with
        | .static s => pure (some s)
        | _ => pure none
      | _ => pure none
    match plain with
    | some s => exprToSlot s r
    | none =>
      if !canTrap l then
        -- a fixed place (a field, a constant index): forming it cannot
        -- trap, so the value may be computed straight into it
        let (a, _) ← place l
        match a.root, a.idx with
        | .static s, none => exprToSlot { s with off := s.off + a.off } r
        | _, _ =>
          let o ← expr r
          emit (.store n a o)
      else
        let o ← expr r
        let (a, _) ← place l
        match a.root, a.idx with
        | .static s, none => emit (.mov n (.slot { s with off := s.off + a.off }) o)
        | _, _ => emit (.store n a o)
    return env
  | .ite c t e =>
    let lElse ← newLabel
    condJump c false lElse
    block t
    if e.isEmpty then
      emit (.label lElse)
    else
      let lEnd ← newLabel
      emit (.jmp lEnd)
      emit (.label lElse)
      block e
      emit (.label lEnd)
    return env
  | .forRange x w lo hi body =>
    let w := w.getD .w32
    let n := w.bits / 8
    inScope do
      let i ← allocLocal n
      exprToSlot i lo
      let limit ← match closed? hi with
        | some v => pure (Opd.const v)
        | none =>
          let h ← allocLocal n
          exprToSlot h hi
          pure (.slot h)
      let top ← newLabel
      let done ← newLabel
      emit (.label top)
      emit (.br .ge n (.slot i) limit done)
      let inner : Env := { env with vars := (x, { ty := .int w, at_ := .static i }) :: env.vars, loopEnd := some done }
      withReader (fun _ => inner) (block body)
      emit (.bin .add n (.slot i) (.slot i) (.const 1))
      emit (.jmp top)
      emit (.label done)
    return env
  | .loop max body =>
    if max == 0 then return env
    let n := counterSize max
    inScope do
      let k ← allocLocal n
      emit (.mov n (.slot k) (.const max))
      let top ← newLabel
      let done ← newLabel
      emit (.label top)
      withReader (fun _ => { env with loopEnd := some done }) (block body)
      emit (.bin .sub n (.slot k) (.slot k) (.const 1))
      emit (.br .ne n (.slot k) (.const 0) top)
      emit (.label done)
    return env
  | .brk =>
    let some l := env.loopEnd | err "break outside a loop"
    emit (.jmp l)
    return env
  | .ret none => emit (.ret none); return env
  | .ret (some e) =>
    let n ← size (← tyOf e)
    let o ← expr e
    emit (.ret (some (n, o)))
    return env
  | .call dst f args =>
    let some fd := env.prog.fn? f | err s!"unknown function {f}"
    let (slots, _) := paramSlots env.prog fd
    let inReg := regParamOf env.prog fd
    let mut regArg : Option Expr := none
    for ((prm, off), a) in slots.zip args do
      let ps : Slot := { area := .frame f, off }
      if prm.byRef then
        let (addr, _) ← place a
        emit (.lea (.slot ps) addr)
      else if inReg == some prm.name then regArg := some a
      else exprToSlot ps a
    -- the register argument last: nothing is computed after it
    let reg ← regArg.mapM fun a => do return (← size (← tyOf a), ← expr a)
    let rn ← fd.ret.mapM size
    withResult dst rn (fun r => Instr.call f r reg)
    return env
  | .eff dst e args =>
    let mut os := #[]
    for (t, a) in e.sig.1.zip args do
      os := os.push (← size t, ← expr a)
    let rn ← e.sig.2.mapM size
    withResult dst rn (Instr.eff e os.toList)
    return env

end

/-- Drop what cannot run (after a `ret`, `jmp` or `trap`, up to the next
label), jumps to the next instruction, and labels nothing jumps to. -/
partial def cleanup (body : Array Instr) : Array Instr := Id.run do
  let mut out : Array Instr := #[]
  let mut dead := false
  for i in body do
    match i with
    | .label _ => dead := false; out := out.push i
    | _ =>
      if dead then continue
      out := out.push i
      match i with
      | .ret _ | .jmp _ | .trap => dead := true
      | _ => pure ()
  -- `jmp L` right before `L:`
  let mut out2 : Array Instr := #[]
  for k in [0:out.size] do
    match out[k]!, out[k + 1]? with
    | .jmp l, some (.label m) => if l != m then out2 := out2.push out[k]!
    | i, _ => out2 := out2.push i
  let targets := out2.toList.filterMap fun i => match i with
    | .jmp l | .br _ _ _ _ l => some l
    | _ => none
  let out3 := out2.filter fun i => match i with
    | .label l => targets.contains l
    | _ => true
  if out3.size < body.size then cleanup out3 else out3

def slotsOverlap (a : Slot) (an : Nat) (b : Slot) (bn : Nat) : Bool :=
  a.area == b.area && a.off < b.off + bn && b.off < a.off + an

/-- An index check is dropped where a comparison on the way already
established it: after `if x ≥ C goto …` falls through, `x < C` holds
until `x` may have changed (an assignment to it; for a variable also any
call, effect or store through an address; any label). -/
def dropChecks (body : Array Instr) : Array Instr := Id.run do
  -- operand, its size, and the bound below which it is
  let mut facts : List (Opd × Nat × Nat) := []
  let mut out : Array Instr := #[]
  for i in body do
    let known (p : Addr) : Addr :=
      match p.idx with
      | some x =>
        match x.len with
        | some n => if facts.any (fun (o, sz, c) => o == x.opd && sz == x.size && c ≤ n) then { p with idx := some { x with len := none } } else p
        | none => p
      | none => p
    let i' := match i with
      | .load n d p => Instr.load n d (known p)
      | .store n p src => .store n (known p) src
      | .lea d p => .lea d (known p)
      | i => i
    out := out.push i'
    let written (d : Dst) (n : Nat) (fs : List (Opd × Nat × Nat)) : List (Opd × Nat × Nat) :=
      fs.filter fun (o, sz, _) => match o, d with
        | .tmp t, .tmp u => t != u
        | .slot a, .slot b => !slotsOverlap a sz b n
        | _, _ => true
    let noSlots (fs : List (Opd × Nat × Nat)) : List (Opd × Nat × Nat) :=
      fs.filter fun (o, _, _) => match o with | .slot _ => false | _ => true
    facts := match i with
      | .label _ | .jmp _ | .ret _ | .trap => []
      | .br .ge n x (.const c) _ => (match x with | .const _ => facts | x => (x, n, c) :: facts)
      | .br .. => facts
      | .mov n d _ | .bin _ n d _ _ | .shift _ n d _ _ _ | .not n d _ | .neg n d _ | .ext n d _ _ | .load n d _ =>
        written d n facts
      | .cmp _ _ d _ _ => written d 1 facts
      | .lea d _ => written d 2 facts
      | .store .. | .zero .. => noSlots facts
      | .call _ r _ | .eff _ _ r =>
        let fs := noSlots facts
        (match r with | some (n, d) => written d n fs | none => fs)
  return out

def lowerFn (p : Lang.Prog) (f : Lang.Fn) : Except String Fn := do
  let (slots, psize) := paramSlots p f
  let vars := slots.map fun (prm, off) =>
    let s : Slot := { area := .frame f.name, off }
    (prm.name, ({ ty := prm.ty, at_ := if prm.byRef then .ref s else .static s } : VarInfo))
  let env : Env := { prog := p, fn := f.name, vars := vars.reverse }
  let act : LM Unit := do
    block f.body
    -- a function without a result may run off its end
    emit (.ret none)
    if let some l := (← get).trapLabel then
      emit (.label l)
      emit .trap
  let ((), st) ← (act.run env).run { cur := psize, max := psize }
  let regParam := (regParamOf p f).bind fun x =>
    (slots.find? (·.1.name == x)).map fun (prm, off) => (sizeOf p prm.ty, ({ area := .frame f.name, off } : Slot))
  return { name := f.name, regParam, frame := st.max, body := dropChecks (cleanup st.out), tmps := st.tmps }

/-! ## Inlining

A call is replaced by the callee's body when the callee is called from
one place only, or is tiny.  Frames are static, so the copy keeps using
the callee's frame: no variable is renamed, only labels and
temporaries. -/

def Opd.shift (tb : Nat) : Opd → Opd
  | .tmp t => .tmp (t + tb)
  | o => o

def Dst.shift (tb : Nat) : Dst → Dst
  | .tmp t => .tmp (t + tb)
  | d => d

def Addr.shift (tb : Nat) (a : Addr) : Addr :=
  { a with idx := a.idx.map fun x => { x with opd := x.opd.shift tb } }

/-- An instruction of the callee inside the caller: labels from `lb`,
temporaries from `tb`; `ret` stores the result and jumps to `done`. -/
def Instr.inlined (lb tb : Nat) (result : Option (Nat × Dst)) (done : Nat) : Instr → List Instr
  | .mov n d s => [.mov n (d.shift tb) (s.shift tb)]
  | .bin op n d a b => [.bin op n (d.shift tb) (a.shift tb) (b.shift tb)]
  | .shift l n d a m amt => [.shift l n (d.shift tb) (a.shift tb) m (amt.shift tb)]
  | .not n d a => [.not n (d.shift tb) (a.shift tb)]
  | .neg n d a => [.neg n (d.shift tb) (a.shift tb)]
  | .ext n d m s => [.ext n (d.shift tb) m (s.shift tb)]
  | .cmp op n d a b => [.cmp op n (d.shift tb) (a.shift tb) (b.shift tb)]
  | .br op n a b l => [.br op n (a.shift tb) (b.shift tb) (l + lb)]
  | .jmp l => [.jmp (l + lb)]
  | .label l => [.label (l + lb)]
  | .load n d p => [.load n (d.shift tb) (p.shift tb)]
  | .store n p s => [.store n (p.shift tb) (s.shift tb)]
  | .lea d p => [.lea (d.shift tb) (p.shift tb)]
  | .zero s n => [.zero s n]
  | .call f r reg => [.call f (r.map fun (n, d) => (n, d.shift tb)) (reg.map fun (n, o) => (n, o.shift tb))]
  | .eff e args r => [.eff e (args.map fun (n, o) => (n, o.shift tb)) (r.map fun (n, d) => (n, d.shift tb))]
  | .ret v =>
    (match result, v with
      | some (n, d), some (_, o) => [Instr.mov n d (o.shift tb)]
      | _, _ => []) ++ [.jmp done]
  | .trap => [.trap]

def Fn.maxLabel (f : Fn) : Nat :=
  f.body.foldl (fun m i => match i with
    | .label l | .jmp l | .br _ _ _ _ l => Nat.max m l
    | _ => m) 0

partial def inlineCalls (p : Prog) (small : Nat := 3) : Prog := Id.run do
  let sites (g : String) : Nat := p.fns.foldl (fun n f => n + (f.calls.filter (· == g)).length) 0
  -- callees before callers
  let mut order : List String := []
  let rec visit (f : String) (seen : List String) : List String :=
    if seen.contains f then seen
    else
      let seen := (((p.fn? f).map Fn.calls).getD []).foldl (fun acc g => visit g acc) seen
      if seen.contains f then seen else seen ++ [f]
  for f in p.fns do order := visit f.name order
  let mut done : List Fn := []
  for name in order do
    let some f := p.fn? name | continue
    let mut body : Array Instr := #[]
    let mut tmps := f.tmps
    let mut nextLabel := f.maxLabel + 1
    let mut inl := f.inlined
    for i in f.body do
      match i with
      | .call g ret reg =>
        match done.find? (·.name == g) with
        | some gf =>
          if sites g == 1 || gf.body.size ≤ small then
            if let (some (n, o), some (_, sl)) := (reg, gf.regParam) then body := body.push (.mov n (.slot sl) o)
            let lb := nextLabel
            let stop := lb + gf.maxLabel + 1
            nextLabel := stop + 1
            let tb := tmps.size
            tmps := tmps ++ gf.tmps
            for j in gf.body do body := body ++ (j.inlined lb tb ret stop).toArray
            body := body.push (.label stop)
            inl := g :: (gf.inlined ++ inl)
          else body := body.push i
        | none => body := body.push i
      | i => body := body.push i
    done := { f with body := cleanup body, tmps, inlined := inl.eraseDups } :: done
  let fns := p.fns.filterMap fun f => done.find? (·.name == f.name)
  let called (g : String) : Bool := fns.any fun f => f.calls.contains g
  { p with fns := fns.map fun f => { f with dead := f.name != p.entry && !called f.name } }

def bytesLE (v n : Nat) : List UInt8 := (List.range n).map fun k => UInt8.ofNat ((v >>> (8 * k)) % 256)

def lowerGlobal (p : Lang.Prog) (g : Lang.Global) : Global :=
  let size := sizeOf p g.ty
  let elem := match g.ty with
    | .arr el _ => sizeOf p el
    | t => sizeOf p t
  let bytes := (g.init.flatMap fun v => bytesLE v elem).take size
  let init := if bytes.all (· == 0) then none
    else some (ByteArray.mk (bytes ++ List.replicate (size - bytes.length) 0).toArray)
  { name := g.name, size, init, const := g.const }

/-- Lower a checked program. -/
def lower (p : Lang.Prog) (inline := false) : Except String Prog := do
  let q : Prog := { globals := p.globals.map (lowerGlobal p), fns := ← p.fns.mapM (lowerFn p), entry := p.entry }
  return if inline then inlineCalls q else q

end Ember.Z80.IR
