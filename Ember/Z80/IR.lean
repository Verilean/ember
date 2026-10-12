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
  deriving DecidableEq, Repr, Inhabited, Hashable

structure Slot where
  area : Area
  off : Nat := 0
  deriving DecidableEq, Repr, Inhabited

inductive Opd where
  | const (v : Nat)
  | slot (s : Slot)
  | tmp (t : Nat)
  deriving DecidableEq, Repr, Inhabited

inductive Dst where
  | slot (s : Slot)
  | tmp (t : Nat)
  deriving DecidableEq, Repr, Inhabited

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

/-- Bytes of a type without records. -/
def sizeOf0 : Ty → Nat
  | .int w => w.bits / 8
  | .bool => 1
  | .arr el n => n * sizeOf0 el
  | .record _ => 0

/-- Bytes of a type (records do not nest). -/
def sizeOf (p : Lang.Prog) : Ty → Nat
  | .int w => w.bits / 8
  | .bool => 1
  | .arr el n => n * sizeOf p el
  | .record r => ((p.struct? r).map (·.fields)).getD [] |>.foldl (fun acc (_, t) => acc + sizeOf0 t) 0

/-- Offset and type of the field `f` among `fs`, the first of which is at `off`. -/
def fieldOffIn (p : Lang.Prog) : List (String × Ty) → String → Nat → Option (Nat × Ty)
  | [], _, _ => none
  | (g, t) :: rest, f, off => if g == f then some (off, t) else fieldOffIn p rest f (off + sizeOf p t)

def fieldOff (p : Lang.Prog) (r f : String) : Option (Nat × Ty) :=
  fieldOffIn p (((p.struct? r).map (·.fields)).getD []) f 0

/-- Offsets of parameters from `off` on, and the first byte after them: a
by-reference parameter is an address. -/
def paramSlotsFrom (p : Lang.Prog) : List Lang.Param → Nat → List (Lang.Param × Nat) × Nat
  | [], off => ([], off)
  | prm :: rest, off =>
    let r := paramSlotsFrom p rest (off + (if prm.byRef then 2 else sizeOf p prm.ty))
    ((prm, off) :: r.1, r.2)

/-- Offsets of the parameters in the frame, and the bytes they take. -/
def paramSlots (p : Lang.Prog) (f : Lang.Fn) : List (Lang.Param × Nat) × Nat := paramSlotsFrom p f.params 0

/-- The parameter that travels in a register, with its offset: the last
one that is one or two bytes by value. -/
def regParamOf (p : Lang.Prog) (f : Lang.Fn) : Option (Lang.Param × Nat) :=
  (paramSlots p f).1.reverse.find? fun x => !x.1.byRef && sizeOf p x.1.ty ≤ 2

/-! ## Lowering

The functions below are written so that they can be reasoned about
(`Ember/Proof/IR*.lean`): the primitives of the monad are plain
functions, and every `match` and `if` is in tail position. -/

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

structure LS where
  out : Array Instr := #[]
  tmps : Array Nat := #[]
  labels : Nat := 0
  /-- Bytes of the frame in use, and the most that ever were. -/
  cur : Nat := 0
  max : Nat := 0
  trapLabel : Option Nat := none

abbrev LM := ReaderT Env (StateT LS (Except String))

def err {α : Type} (msg : String) : LM α := fun e _ => .error s!"{e.fn}: {msg}"

def emit (i : Instr) : LM Unit := fun _ s => .ok ((), { s with out := s.out.push i })

def newTmp (n : Nat) : LM Nat := fun _ s => .ok (s.tmps.size, { s with tmps := s.tmps.push n })

def newLabel : LM Nat := fun _ s => .ok (s.labels, { s with labels := s.labels + 1 })

def allocLocal (n : Nat) : LM Slot := fun e s =>
  .ok ({ area := .frame e.fn, off := s.cur }, { s with cur := s.cur + n, max := Nat.max s.max (s.cur + n) })

/-- Locals of a block give their bytes back at its end. -/
def inScope {α : Type} (m : LM α) : LM α := fun e s =>
  match m e s with
  | .ok (r, s') => .ok (r, { s' with cur := s.cur })
  | .error msg => .error msg

def trapLabel : LM Nat := fun _ s =>
  match s.trapLabel with
  | some l => .ok (l, s)
  | none => .ok (s.labels, { s with labels := s.labels + 1, trapLabel := some s.labels })

/-- What only reads the environment, as an action. -/
def pureE {α : Type} (m : Env → Except String α) : LM α := fun e s =>
  match m e with
  | .ok a => .ok (a, s)
  | .error msg => .error msg

def Env.err {α : Type} (e : Env) (msg : String) : Except String α := .error s!"{e.fn}: {msg}"

def Env.varInfo (e : Env) (x : String) : Except String VarInfo :=
  match e.vars.lookup x with
  | some v => .ok v
  | none =>
    match e.prog.global? x with
    | some g => .ok { ty := g.ty, at_ := .static { area := .global x } }
    | none => e.err s!"unknown variable {x}"

def varInfo (x : String) : LM VarInfo := pureE (·.varInfo x)

/-- Type of an expression of a checked program. -/
def Env.tyOf (g : Env) : Expr → Except String Ty
  | .lit _ (some w) => .ok (.int w)
  | .lit _ none => g.err "untyped literal (program not checked)"
  | .blit _ => .ok .bool
  | .var x =>
    match g.varInfo x with
    | .ok v => .ok v.ty
    | .error m => .error m
  | .field b f =>
    match g.tyOf b with
    | .ok (.record r) =>
      match fieldOff g.prog r f with
      | some (_, t) => .ok t
      | none => g.err s!"no field {f}"
    | .ok _ => g.err "field of a non-record"
    | .error m => .error m
  | .index b _ =>
    match g.tyOf b with
    | .ok (.arr el _) => .ok el
    | .ok _ => g.err "index of a non-array"
    | .error m => .error m
  | .bin op a _ => if op.isCompare || op.isLogic then .ok .bool else g.tyOf a
  | .un _ a => g.tyOf a
  | .cast w _ => .ok (.int w)
  | .cond _ a _ => g.tyOf a

def tyOf (e : Expr) : LM Ty := pureE (·.tyOf e)

def size (t : Ty) : LM Nat := fun e s => .ok (sizeOf e.prog t, s)

/-- The value of a closed expression (no variables), as its bytes. -/
def closed? (e : Expr) : Option Nat :=
  match C.closedVal e with
  | some (.int _ v) => some v.toNat
  | some (.bool b) => some (if b then 1 else 0)
  | _ => none

/-- Can evaluating the expression trap?  (An index that is not a literal:
the checker has a literal index within the array.) -/
def canTrap : Expr → Bool
  | .index b i => (match i with | .lit _ _ => false | _ => true) || canTrap b
  | .field b _ => canTrap b
  | .bin _ a b => canTrap a || canTrap b
  | .un _ a => canTrap a
  | .cast _ a => canTrap a
  | .cond c a b => canTrap c || canTrap a || canTrap b
  | _ => false

def isSimple : Opd → Bool
  | .tmp _ => false
  | _ => true

/-- Where a variable is. -/
def placeVar (x : String) : LM (Addr × Ty) := do
  let v ← varInfo x
  match v.at_ with
  | .static s => pure ({ root := .static s }, v.ty)
  | .ref p => pure ({ root := .ptr p }, v.ty)

/-- The value of a constant global, when `x` is one. -/
def Env.constVar? (env : Env) (x : String) : Option Nat :=
  match env.vars.lookup x with
  | some _ => none
  | none =>
    match env.prog.global? x with
    | some g =>
      if g.const && g.ty.isScalar then
        some (match g.init with | [v] => v % 2 ^ (8 * sizeOf env.prog g.ty) | _ => 0)
      else none
    | none => none

def constVar? (x : String) : LM (Option Nat) := fun e s => .ok (e.constVar? x, s)

/-- A place loaded into a new temporary. -/
def loadTmp (r : Addr × Ty) : LM Opd := do
  let n ← size r.2
  let d ← newTmp n
  emit (.load n (.tmp d) r.1)
  pure (.tmp d)

/-- A place as an operand: its slot, or a temporary loaded from it. -/
def loadPlace (r : Addr × Ty) : LM Opd :=
  match r.1.root, r.1.idx with
  | .static s, none => pure (.slot { s with off := s.off + r.1.off })
  | _, _ => loadTmp r

/-- A place's value into `dst`. -/
def movPlace (n : Nat) (dst : Dst) (r : Addr × Ty) : LM Unit :=
  match r.1.root, r.1.idx with
  | .static s, none => emit (.mov n dst (.slot { s with off := s.off + r.1.off }))
  | _, _ => emit (.load n dst r.1)

/-- A variable as an operand. -/
def varOpd (x : String) : LM Opd := do
  match (← constVar? x) with
  | some v => pure (.const v)
  | none => do loadPlace (← placeVar x)

/-- `o` (of `m` bytes) in a new temporary of `n`. -/
def extTmp (n m : Nat) (o : Opd) : LM Opd := do
  let d ← newTmp n
  emit (.ext n (.tmp d) m o)
  pure (.tmp d)

/-- The low two bytes of a wide index. -/
def lowIdx (m : Nat) (o : Opd) : LM Opd :=
  match o with
  | .slot s => pure (.slot s)
  | .const v => extTmp 2 m (.const v)
  | .tmp t => extTmp 2 m (.tmp t)

/-- A cast of an operand: the low bytes of a variable are the variable
(little-endian). -/
def castOpd (n m : Nat) (o : Opd) : LM Opd :=
  match o with
  | .slot s => if n ≤ m then pure (.slot s) else extTmp n m (.slot s)
  | .tmp t => if n == m then pure (.tmp t) else extTmp n m (.tmp t)
  | .const v => extTmp n m (.const v)

def pow2? : Opd → Option Nat
  | .const v => if v == 2 ^ v.log2 then some v.log2 else none
  | _ => none

/-- A temporary on the left, where the code generator has it at hand. -/
def arithI (k : Bin) (n : Nat) (dst : Dst) (oa ob : Opd) : Instr :=
  if k.commutes && isSimple oa && !isSimple ob then .bin k n dst ob oa else .bin k n dst oa ob

/-- By a power of two: a shift or a mask. -/
def scaledI (k : Bin) (n : Nat) (dst : Dst) (oa ob : Opd) : Instr :=
  match k, pow2? oa, pow2? ob with
  | .mul, _, some s => .shift true n dst oa 1 (.const s)
  | .mul, some s, none => .shift true n dst ob 1 (.const s)
  | .div, _, some s => .shift false n dst oa 1 (.const s)
  | .mod, _, some s => .bin .and n dst oa (.const (2 ^ s - 1))
  | k, _, _ => arithI k n dst oa ob

/-- The instruction of a binary operator: the result has `n` bytes, the
operands of a comparison `m`, a shift amount `sm`. -/
def binI (op : BinOp) (n m sm : Nat) (dst : Dst) (oa ob : Opd) : Instr :=
  match op with
  | .add => arithI .add n dst oa ob
  | .sub => arithI .sub n dst oa ob
  | .mul => scaledI .mul n dst oa ob
  | .div => scaledI .div n dst oa ob
  | .mod => scaledI .mod n dst oa ob
  | .band => arithI .and n dst oa ob
  | .land => arithI .and n dst oa ob
  | .bor => arithI .or n dst oa ob
  | .lor => arithI .or n dst oa ob
  | .bxor => arithI .xor n dst oa ob
  | .shl => .shift true n dst oa sm ob
  | .shr => .shift false n dst oa sm ob
  | .eq => .cmp .eq m dst oa ob
  | .ne => .cmp .ne m dst oa ob
  | .lt => .cmp .lt m dst oa ob
  | .ge => .cmp .ge m dst oa ob
  | .le => .cmp .ge m dst ob oa
  | .gt => .cmp .lt m dst ob oa

def unI (op : UnOp) (n : Nat) (dst : Dst) (o : Opd) : Instr :=
  match op with
  | .lnot => .bin .xor 1 dst o (.const 1)
  | .bnot => .not n dst o
  | .neg => .neg n dst o

def castI (n m : Nat) (dst : Dst) (o : Opd) : Instr :=
  if n == m then .mov n dst o
  else if n < m then
    match o with
    | .slot s => .mov n dst (.slot s)
    | o => .ext n dst m o
  else .ext n dst m o

mutual

/-- Where a place is. -/
def place (e : Expr) : LM (Addr × Ty) :=
  match e with
  | .var x => placeVar x
  | .field b f => do
    let r ← place b
    match r.2 with
    | .record rn => do
      let env ← read
      match fieldOff env.prog rn f with
      | some (off, ft) => pure ({ r.1 with off := r.1.off + off }, ft)
      | none => err s!"no field {f}"
    | _ => err "field of a non-record"
  | .index b i => do
    let r ← place b
    match r.2 with
    | .arr el n => do
      let scale ← size el
      if r.1.idx.isSome then err "nested arrays"
      else
        match closed? i with
        | some v =>
          if v < n then pure ({ r.1 with off := r.1.off + v * scale }, el)
          else do
            -- a constant index out of range: the trap, and any address after it
            emit .trap
            pure (r.1, el)
        | none => do
          let it ← tyOf i
          match it with
          | .int iw => do
            let o ← expr i
            if iw.bits / 8 ≤ 2 then
              pure ({ r.1 with idx := some { opd := o, size := iw.bits / 8, scale,
                                             len := if n ≥ 2 ^ iw.bits then none else some n } }, el)
            else do
              -- a wide index: compared as it is, then its low two bytes
              let tl ← trapLabel
              emit (.br .ge (iw.bits / 8) o (.const n) tl)
              let low ← lowIdx (iw.bits / 8) o
              pure ({ r.1 with idx := some { opd := low, size := 2, scale, len := none } }, el)
          | _ => err "non-integer index"
    | _ => err "index of a non-array"
  | .lit _ _ => err "not a place"
  | .blit _ => err "not a place"
  | .bin _ _ _ => err "not a place"
  | .un _ _ => err "not a place"
  | .cast _ _ => err "not a place"
  | .cond _ _ _ => err "not a place"
termination_by 3 * SizeOf.sizeOf e

/-- The expression as an operand: a constant or a variable as it is,
anything else in a new temporary. -/
def expr (e : Expr) : LM Opd :=
  match closed? e with
  -- a constant is its value
  | some v => pure (.const v)
  | none =>
    match e with
    | .var x => varOpd x
    | .field b f => do loadPlace (← place (.field b f))
    | .index b i => do loadPlace (← place (.index b i))
    | .cast w a => do
      let m ← size (← tyOf a)
      -- `(x >>> 8k : narrower)` of a variable is its bytes from `k` on
      let short ← (match a with
        | .bin .shr x k =>
          match closed? k with
          | some kv =>
            if kv % 8 == 0 && kv / 8 + w.bits / 8 ≤ m then do
              let o ← expr x
              match o with
              | .slot s => pure (some (Opd.slot { s with off := s.off + kv / 8 }))
              | _ => pure none
            else pure none
          | none => pure none
        | _ => pure none)
      match short with
      | some o => pure o
      | none => do
        let o ← expr a
        castOpd (w.bits / 8) m o
    | .lit v w => do
      let d ← newTmp (← size (← tyOf (.lit v w)))
      exprTo (.tmp d) (.lit v w)
      pure (.tmp d)
    | .blit b => do
      let d ← newTmp (← size (← tyOf (.blit b)))
      exprTo (.tmp d) (.blit b)
      pure (.tmp d)
    | .bin op a b => do
      let d ← newTmp (← size (← tyOf (.bin op a b)))
      exprTo (.tmp d) (.bin op a b)
      pure (.tmp d)
    | .un op a => do
      let d ← newTmp (← size (← tyOf (.un op a)))
      exprTo (.tmp d) (.un op a)
      pure (.tmp d)
    | .cond c a b => do
      let d ← newTmp (← size (← tyOf (.cond c a b)))
      exprTo (.tmp d) (.cond c a b)
      pure (.tmp d)
termination_by 3 * SizeOf.sizeOf e + 2

/-- Evaluate into `dst`. -/
def exprTo (dst : Dst) (e : Expr) : LM Unit := do
  let n ← size (← tyOf e)
  match closed? e with
  | some v => emit (.mov n dst (.const v))
  | none =>
    match e with
    | .lit _ _ => err "literal not closed"
    | .blit _ => err "literal not closed"
    | .var x => do
      let o ← varOpd x
      match o with
      | .const v => emit (.mov n dst (.const v))
      | _ => do movPlace n dst (← placeVar x)
    | .field b f => do movPlace n dst (← place (.field b f))
    | .index b i => do movPlace n dst (← place (.index b i))
    | .bin op a b => do
      let m ← size (← tyOf a)
      -- the right operand first: the left one is then the value computed last
      let ob ← expr b
      let oa ← expr a
      let sm ← (if op.isShift then (do size (← tyOf b)) else pure 0)
      emit (binI op n m sm dst oa ob)
    | .un op a => do
      let o ← expr a
      emit (unI op n dst o)
    | .cast _ a => do
      let m ← size (← tyOf a)
      let o ← expr a
      emit (castI n m dst o)
    | .cond c a b => do
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
termination_by 3 * SizeOf.sizeOf e + 1

end

/-- Jump to `target` when the value of `e` (a `bool`) is `sense`. -/
def boolJump (e : Expr) (sense : Bool) (target : Nat) : LM Unit := do
  let o ← expr e
  emit (.br (if sense then .ne else .eq) 1 o (.const 0) target)

/-- A comparison as one of `eq ne lt ge`, with its operands in order. -/
def cmpOf (op : BinOp) (oa ob : Opd) : Cmp × Opd × Opd :=
  match op with
  | .eq => (.eq, oa, ob)
  | .ne => (.ne, oa, ob)
  | .lt => (.lt, oa, ob)
  | .ge => (.ge, oa, ob)
  | .le => (.ge, ob, oa)
  | _ => (.lt, ob, oa)

/-- `0 < y` is `y ≠ 0`, `0 ≥ y` is `y = 0`. -/
def cmpZero (r : Cmp × Opd × Opd) : Cmp × Opd × Opd :=
  match r.1, r.2.1 with
  | .lt, .const 0 => (Cmp.ne, r.2.2, Opd.const 0)
  | .ge, .const 0 => (Cmp.eq, r.2.2, Opd.const 0)
  | _, _ => r

/-- The branch of a comparison. -/
def cmpBr (op : BinOp) (sense : Bool) (m : Nat) (oa ob : Opd) (target : Nat) : Instr :=
  .br (if sense then (cmpZero (cmpOf op oa ob)).1 else (cmpZero (cmpOf op oa ob)).1.negate) m
    (cmpZero (cmpOf op oa ob)).2.1 (cmpZero (cmpOf op oa ob)).2.2 target

/-- Jump to `target` when the condition is `sense`. -/
def condJump (e : Expr) (sense : Bool) (target : Nat) : LM Unit :=
  match closed? e with
  | some v => if (v != 0) == sense then emit (.jmp target) else pure ()
  | none =>
    match e with
    | .un op a =>
      match op with
      | .lnot => condJump a (!sense) target
      | .bnot => boolJump (.un .bnot a) sense target
      | .neg => boolJump (.un .neg a) sense target
    | .bin op a b =>
      if op.isCompare then do
        let m ← size (← tyOf a)
        let ob ← expr b
        let oa ← expr a
        emit (cmpBr op sense m oa ob target)
      else if op.isLogic && !canTrap b then
        -- skipping `b` is not observable
        if (op == .land) != sense then do
          -- and/false, or/true: either operand decides
          condJump a sense target
          condJump b sense target
        else do
          let skip ← newLabel
          condJump a (!sense) skip
          condJump b sense target
          emit (.label skip)
      else boolJump (.bin op a b) sense target
    | .lit v w => boolJump (.lit v w) sense target
    | .blit b => boolJump (.blit b) sense target
    | .var x => boolJump (.var x) sense target
    | .field b f => boolJump (.field b f) sense target
    | .index b i => boolJump (.index b i) sense target
    | .cast w a => boolJump (.cast w a) sense target
    | .cond c a b => boolJump (.cond c a b) sense target

/-- A conditional expression must not write its destination before its
operands are read; anything else may compute straight into a variable. -/
def hasCond : Expr → Bool
  | .cond .. => true
  | .bin _ a b => hasCond a || hasCond b
  | .un _ a => hasCond a
  | .cast _ a => hasCond a
  | .index b i => hasCond b || hasCond i
  | .field b _ => hasCond b
  | _ => false

/-- Evaluate into a variable's slot. -/
def exprToSlot (s : Slot) (e : Expr) : LM Unit :=
  if hasCond e then do
    let n ← size (← tyOf e)
    let o ← expr e
    emit (.mov n (.slot s) o)
  else exprTo (.slot s) e

def counterSize (n : Nat) : Nat := if n < 256 then 1 else if n < 65536 then 2 else 4

/-- The slot of a place that is a variable with an address of its own. -/
def plainSlot (e : Expr) : LM (Option Slot) :=
  match e with
  | .var x => do
    let v ← varInfo x
    match v.at_ with
    | .static s => pure (some s)
    | .ref _ => pure none
  | _ => pure none

/-- `o` to the place `a`. -/
def storeTo (n : Nat) (a : Addr) (o : Opd) : LM Unit :=
  match a.root, a.idx with
  | .static s, none => emit (.mov n (.slot { s with off := s.off + a.off }) o)
  | _, _ => emit (.store n a o)

/-- Store a call's or an effect's result: the destination is evaluated
after the call, as the interpreter does. -/
def withResult (dst : Option Expr) (n : Option Nat) (mk : Option (Nat × Dst) → Instr) : LM Unit :=
  match dst, n with
  | some d, some n => do
    -- only the address of a plain variable is known before the call
    let simple ← plainSlot d
    match simple with
    | some s => emit (mk (some (n, .slot s)))
    | none => do
      let t ← newTmp n
      emit (mk (some (n, .tmp t)))
      let r ← place d
      storeTo n r.1 (.tmp t)
  | _, _ => emit (mk none)

def mentions (x : String) : Expr → Bool
  | .var y => x == y
  | .field b _ => mentions x b
  | .index b i => mentions x b || mentions x i
  | .bin _ a b => mentions x a || mentions x b
  | .un _ a => mentions x a
  | .cast _ a => mentions x a
  | .cond c a b => mentions x c || mentions x a || mentions x b
  | _ => false

/-- A declaration with its value. -/
def declStmt (x : String) (ty : Ty) (init : Option Expr) : LM Env := do
  let env ← read
  let n ← size ty
  let slot ← allocLocal n
  let _ ← (match init with
    | some e => exprToSlot slot e
    | none => if ty.isScalar then emit (.mov n (.slot slot) (.const 0)) else emit (.zero slot n))
  pure { env with vars := (x, { ty, at_ := .static slot }) :: env.vars }

def assign (l r : Expr) : LM Unit := do
  let n ← size (← tyOf r)
  -- the value first, then the place (its index may trap)
  let plain ← plainSlot l
  match plain with
  | some s => exprToSlot s r
  | none =>
    if !canTrap l then do
      -- a fixed place (a field, a constant index): forming it cannot
      -- trap, so the value may be computed straight into it
      let a ← place l
      match a.1.root, a.1.idx with
      | .static s, none => exprToSlot { s with off := s.off + a.1.off } r
      | _, _ => do
        let o ← expr r
        emit (.store n a.1 o)
    else do
      let o ← expr r
      let a ← place l
      storeTo n a.1 o

/-- The upper bound of a `for`: a constant, or a slot of its own. -/
def forLimit (n : Nat) (hi : Expr) : LM Opd :=
  match closed? hi with
  | some v => pure (.const v)
  | none => do
    let h ← allocLocal n
    exprToSlot h hi
    pure (.slot h)

def brkStmt : LM Env := do
  let env ← read
  match env.loopEnd with
  | some l => do
    emit (.jmp l)
    pure env
  | none => err "break outside a loop"

def retStmt (v : Option Expr) : LM Env :=
  match v with
  | none => do
    emit (.ret none)
    read
  | some e => do
    let n ← size (← tyOf e)
    let o ← expr e
    emit (.ret (some (n, o)))
    read

/-- The arguments of a call, into the callee's frame; the one that
travels in a register (the parameter at offset `inReg`) is returned
(`reg`: found so far). -/
def callArgs (f : String) (inReg : Option Nat) : List ((Lang.Param × Nat) × Expr) → Option Expr →
    LM (Option Expr)
  | [], reg => pure reg
  | ((prm, off), a) :: rest, reg =>
    if prm.byRef then do
      let r ← place a
      emit (.lea (.slot { area := .frame f, off }) r.1)
      callArgs f inReg rest reg
    else if inReg == some off then callArgs f inReg rest (some a)
    else do
      exprToSlot { area := .frame f, off } a
      callArgs f inReg rest reg

/-- A call up to its instruction, which is still to be given the place
of the result (whose size is returned). -/
def callInstr (f : String) (args : List Expr) : LM (Option Nat × (Option (Nat × Dst) → Instr)) := do
  let env ← read
  match env.prog.fn? f with
  | none => err s!"unknown function {f}"
  | some fd => do
    let regArg ← callArgs f ((regParamOf env.prog fd).map (·.2)) ((paramSlots env.prog fd).1.zip args) none
    -- the register argument last: nothing is computed after it
    let reg ← (match regArg with
      | some a => do
        let n ← size (← tyOf a)
        let o ← expr a
        pure (some (n, o))
      | none => pure none)
    let rn ← (match fd.ret with
      | some t => do pure (some (← size t))
      | none => pure none)
    pure (rn, fun r => Instr.call f r reg)

def effArgs : List (Ty × Expr) → LM (List (Nat × Opd))
  | [] => pure []
  | (t, a) :: rest => do
    let n ← size t
    let o ← expr a
    let os ← effArgs rest
    pure ((n, o) :: os)

def effInstr (e : Effect) (args : List Expr) : LM (Option Nat × (Option (Nat × Dst) → Instr)) := do
  let os ← effArgs (e.sig.1.zip args)
  let rn ← (match e.sig.2 with
    | some t => do pure (some (← size t))
    | none => pure none)
  pure (rn, Instr.eff e os)

/-- A call or an effect whose result goes to a variable declared just before. -/
inductive Init where
  | call (f : String) (args : List Expr)
  | eff (e : Effect) (args : List Expr)

/-- `s` declares a variable without a value and `next` assigns it from a
call or an effect that does not read it: the two are one declaration
with that value, and the variable need not be zeroed first. -/
def declCall? (s : Stmt) (next : Stmt) : Option (String × Ty × Init) :=
  match s.core, next.core with
  | .decl x ty none, .call (some (.var y)) f args =>
    if ty.isScalar && x == y && !args.any (mentions x) then some (x, ty, .call f args) else none
  | .decl x ty none, .eff (some (.var y)) e args =>
    if ty.isScalar && x == y && !args.any (mentions x) then some (x, ty, .eff e args) else none
  | _, _ => none

/-- A declaration with a call's or an effect's result as its value. -/
def declCall (x : String) (ty : Ty) (i : Init) : LM Env := do
  let env ← read
  let n ← size ty
  let slot ← allocLocal n
  let r ← (match i with
    | .call f args => callInstr f args
    | .eff e args => effInstr e args)
  let _ ← (match r.1 with
    | some rn => emit (r.2 (some (rn, .slot slot)))
    | none => emit (r.2 none))
  pure { env with vars := (x, { ty, at_ := .static slot }) :: env.vars }

mutual

/-- The statements of a block, in the environment `env` (each statement
yields the environment of the next). -/
def blockFrom (env : Env) : List Stmt → LM Unit
  | [] => pure ()
  | [s] => do
    let _ ← withReader (fun _ => env) (stmt s)
    pure ()
  | s :: s2 :: rest =>
    match declCall? s s2 with
    | some (x, ty, i) => do
      let env' ← withReader (fun _ => env) (declCall x ty i)
      blockFrom env' rest
    | none => do
      let env' ← withReader (fun _ => env) (stmt s)
      blockFrom env' (s2 :: rest)

/-- One statement; returns the environment for what follows. -/
def stmt : Stmt → LM Env
  | .at _ s => stmt s
  | .decl x ty init => declStmt x ty init
  | .assign l r => do
    assign l r
    read
  | .ite c t e => do
    let env ← read
    let lElse ← newLabel
    condJump c false lElse
    inScope (blockFrom env t)
    if e.isEmpty then do
      emit (.label lElse)
      pure env
    else do
      let lEnd ← newLabel
      emit (.jmp lEnd)
      emit (.label lElse)
      inScope (blockFrom env e)
      emit (.label lEnd)
      pure env
  | .forRange x w lo hi body => do
    let env ← read
    inScope (do
      let i ← allocLocal ((w.getD .w32).bits / 8)
      exprToSlot i lo
      let limit ← forLimit ((w.getD .w32).bits / 8) hi
      let top ← newLabel
      let done ← newLabel
      emit (.label top)
      emit (.br .ge ((w.getD .w32).bits / 8) (.slot i) limit done)
      inScope (blockFrom { env with vars := (x, { ty := .int (w.getD .w32), at_ := .static i }) :: env.vars,
                                    loopEnd := some done } body)
      emit (.bin .add ((w.getD .w32).bits / 8) (.slot i) (.slot i) (.const 1))
      emit (.jmp top)
      emit (.label done))
    pure env
  | .loop max body => do
    let env ← read
    if max == 0 then pure env
    else do
      inScope (do
        let k ← allocLocal (counterSize max)
        emit (.mov (counterSize max) (.slot k) (.const max))
        let top ← newLabel
        let done ← newLabel
        emit (.label top)
        inScope (blockFrom { env with loopEnd := some done } body)
        emit (.bin .sub (counterSize max) (.slot k) (.slot k) (.const 1))
        emit (.br .ne (counterSize max) (.slot k) (.const 0) top)
        emit (.label done))
      pure env
  | .brk => brkStmt
  | .ret v => retStmt v
  | .call dst f args => do
    let r ← callInstr f args
    withResult dst r.1 r.2
    read
  | .eff dst e args => do
    let r ← effInstr e args
    withResult dst r.1 r.2
    read

end

/-- A block: its locals give their bytes back at its end. -/
def block (ss : List Stmt) : LM Unit := inScope fun e => blockFrom e ss e

/-- The elements a mask keeps. -/
def sel {α : Type} : List Bool → List α → List α
  | true :: ks, x :: xs => x :: sel ks xs
  | false :: ks, _ :: xs => sel ks xs
  | _, _ => []

/-- What can run: not what follows a `ret`, `jmp` or `trap`, up to the next label. -/
def deadMask : Bool → List Instr → List Bool
  | _, [] => []
  | dead, i :: r =>
    match i with
    | .label _ => true :: deadMask false r
    | .ret _ | .jmp _ | .trap => (!dead) :: deadMask true r
    | _ => (!dead) :: deadMask dead r

/-- Not a `jmp L` right before `L:`. -/
def jmpMask : List Instr → List Bool
  | [] => []
  | i :: r =>
    (match i, r with
     | .jmp l, .label m :: _ => l != m
     | _, _ => true) :: jmpMask r

/-- Where an instruction may jump to. -/
def Instr.target? : Instr → Option Nat
  | .jmp l | .br _ _ _ _ l => some l
  | _ => none

def targetsOf (body : List Instr) : List Nat := body.filterMap Instr.target?

/-- Not a label nothing jumps to. -/
def labelMask (targets : List Nat) (body : List Instr) : List Bool :=
  body.map fun i => match i with
    | .label l => targets.contains l
    | _ => true

/-- Drop what cannot run, jumps to the next instruction, and labels
nothing jumps to. -/
def cleanupPass (body : Array Instr) : Array Instr :=
  let a := sel (deadMask false body.toList) body.toList
  let b := sel (jmpMask a) a
  (sel (labelMask (targetsOf b) b) b).toArray

/-- `cleanupPass` until nothing more goes (every round that goes on is shorter). -/
def cleanupN : Nat → Array Instr → Array Instr
  | 0, body => body
  | n + 1, body =>
    let out := cleanupPass body
    if out.size < body.size then cleanupN n out else out

def cleanup (body : Array Instr) : Array Instr := cleanupN (body.size + 1) body

def slotsOverlap (a : Slot) (an : Nat) (b : Slot) (bn : Nat) : Bool :=
  a.area == b.area && a.off < b.off + bn && b.off < a.off + an

/-- What is known on the way: an operand, its size, and a bound it is below. -/
abbrev Facts := List (Opd × Nat × Nat)

/-- The address, without the check a fact makes needless. -/
def knownAddr (facts : Facts) (p : Addr) : Addr :=
  match p.idx with
  | some x =>
    match x.len with
    | some n =>
      if facts.any (fun (o, sz, c) => o == x.opd && sz == x.size && c ≤ n) then { p with idx := some { x with len := none } }
      else p
    | none => p
  | none => p

def knownInstr (facts : Facts) : Instr → Instr
  | .load n d p => .load n d (knownAddr facts p)
  | .store n p src => .store n (knownAddr facts p) src
  | .lea d p => .lea d (knownAddr facts p)
  | i => i

/-- The facts a write of `n` bytes to `d` leaves. -/
def written (d : Dst) (n : Nat) (fs : Facts) : Facts :=
  fs.filter fun (o, sz, _) => match o, d with
    | .tmp t, .tmp u => t != u
    | .slot a, .slot b => !slotsOverlap a sz b n
    | _, _ => true

def noSlots (fs : Facts) : Facts :=
  fs.filter fun (o, _, _) => match o with | .slot _ => false | _ => true

/-- The facts after an instruction, when it goes on to the next. -/
def factsAfter (facts : Facts) : Instr → Facts
  | .label _ | .jmp _ | .ret _ | .trap => []
  | .br op n x y _ =>
    (match op, y, x with
     | .ge, .const _, .const _ => facts
     | .ge, .const c, x => (x, n, c) :: facts
     | _, _, _ => facts)
  | .mov n d _ | .bin _ n d _ _ | .shift _ n d _ _ _ | .not n d _ | .neg n d _ | .ext n d _ _ | .load n d _ =>
    written d n facts
  | .cmp _ _ d _ _ => written d 1 facts
  | .lea d _ => written d 2 facts
  | .store .. | .zero .. => noSlots facts
  | .call _ r _ | .eff _ _ r =>
    (match r with
     | some (n, d) => written d n (noSlots facts)
     | none => noSlots facts)

def dropFrom (facts : Facts) : List Instr → List Instr
  | [] => []
  | i :: r => knownInstr facts i :: dropFrom (factsAfter facts i) r

/-- An index check is dropped where a comparison on the way already
established it: after `if x ≥ C goto …` falls through, `x < C` holds
until `x` may have changed (an assignment to it; for a variable also any
call, effect or store through an address; any label). -/
def dropChecks (body : Array Instr) : Array Instr := (dropFrom [] body.toList).toArray

/-- The trap that index checks jump to, when there is one. -/
def trapEpilogue : LM Unit := fun _ s =>
  match s.trapLabel with
  | some l => .ok ((), { s with out := (s.out.push (.label l)).push .trap })
  | none => .ok ((), s)

/-- The body of a function; one without a result may run off its end. -/
def lowerBody (ss : List Stmt) : LM Unit := do
  block ss
  emit (.ret none)
  trapEpilogue

def paramVars (fn : String) (slots : List (Lang.Param × Nat)) : List (String × VarInfo) :=
  slots.map fun (prm, off) =>
    (prm.name, { ty := prm.ty,
                 at_ := if prm.byRef then .ref { area := .frame fn, off } else .static { area := .frame fn, off } })

/-- The environment a function's body is lowered in. -/
def fnEnv (p : Lang.Prog) (f : Lang.Fn) : Env :=
  { prog := p, fn := f.name, vars := paramVars f.name (paramSlots p f).1 }

def regParamSlot (p : Lang.Prog) (f : Lang.Fn) : Option (Nat × Slot) :=
  (regParamOf p f).map fun x => (sizeOf p x.1.ty, ({ area := .frame f.name, off := x.2 } : Slot))

/-- A function as it is lowered, before `cleanup` and `dropChecks`. -/
def lowerFnRaw (p : Lang.Prog) (f : Lang.Fn) : Except String Fn :=
  match lowerBody f.body (fnEnv p f) { cur := (paramSlots p f).2, max := (paramSlots p f).2 } with
  | .ok (_, st) =>
    .ok { name := f.name, regParam := regParamSlot p f, frame := Nat.max st.max (paramSlots p f).2,
          body := st.out, tmps := st.tmps }
  | .error e => .error e

/-- The labels a body defines. -/
def labelsOf (body : Array Instr) : List Nat :=
  body.toList.filterMap fun i => match i with | .label l => some l | _ => none

/-- The function as lowered, once it is checked that no label is defined
twice (which the lowering never does; the proofs take it from here). -/
def lowerFnChecked (p : Lang.Prog) (f : Lang.Fn) : Except String Fn :=
  match lowerFnRaw p f with
  | .ok r => if (labelsOf r.body).Nodup then .ok r else .error s!"{f.name}: a label is defined twice"
  | .error e => .error e

/-- The body, tidied. -/
def tidy (r : Fn) : Fn := { r with body := dropChecks (cleanup r.body) }

def lowerFn (p : Lang.Prog) (f : Lang.Fn) : Except String Fn :=
  match lowerFnChecked p f with
  | .ok r => .ok (tidy r)
  | .error e => .error e

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

/-- The program as lowered, before the bodies are tidied (what
`Ember/Proof/IRSim.lean` is about). -/
def lowerRaw (p : Lang.Prog) : Except String Prog :=
  match p.fns.mapM (lowerFnChecked p) with
  | .ok fns => .ok { globals := p.globals.map (lowerGlobal p), fns, entry := p.entry }
  | .error e => .error e

/-- Lower a checked program. -/
def lower (p : Lang.Prog) (inline := false) : Except String Prog := do
  let q : Prog := { globals := p.globals.map (lowerGlobal p), fns := ← p.fns.mapM (lowerFn p), entry := p.entry }
  return if inline then inlineCalls q else q

end Ember.Z80.IR
