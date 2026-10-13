import Ember.Lang.Types
import Ember.Trace.Event
import Std.Data.HashMap

/-!
# Ember.Lang.Eval — the interpreter, which is the semantics (M2.3)

* arithmetic is modulo 2^w; a shift by ≥ w is 0; `/` and `%` by 0 are 0;
* every operand is evaluated (strict `&&`, `||`, `if-then-else`), so an
  out-of-range array read anywhere is an error, reported with the
  function and the statement path (`fn=f at stmt 3.2.1`);
* statements consume fuel; running out is an error;
* effects are served by a `World`: the input oracle (the inputs of a
  trace, byte by byte, ticks as `0x0100`, `0xFFFF` at the end) and the
  event log (`tx` frames, `drop`, `note`), attributed to the step of the
  input item consumed last.

The driver (`run`) calls the entry function while input remains — the
same loop the C harness runs.
-/

namespace Ember.Lang
open Ember.Trace

inductive Val where
  | int  (w : Width) (v : UInt64)
  | bool (b : Bool)
  | arr  (xs : Array Val)
  | record (name : String) (fs : Array Val)
  deriving Inhabited, BEq, Repr

def mask (w : Width) (v : UInt64) : UInt64 :=
  if w == .w64 then v else v &&& ((1 <<< w.bits.toUInt64) - 1)

def Val.toNat : Val → Nat
  | .int _ v => v.toNat
  | .bool b => if b then 1 else 0
  | _ => 0

def Val.toBool : Val → Bool
  | .bool b => b
  | .int _ v => v != 0
  | _ => false

partial def Val.toString : Val → String
  | .int _ v => s!"{v.toNat}"
  | .bool b => if b then "true" else "false"
  | .arr xs => "[" ++ ", ".intercalate (xs.toList.map Val.toString) ++ "]"
  | .record n fs => n ++ "{" ++ ", ".intercalate (fs.toList.map Val.toString) ++ "}"

inductive PathElem where
  | idx (i : Nat)
  | fld (i : Nat)
  deriving Inhabited, BEq, Repr

/-- A storage location: a cell of the store and a path into it. -/
structure Loc where
  cell : Nat
  path : List PathElem := []
  deriving Inhabited, BEq, Repr

partial def readPath : Val → List PathElem → Val
  | v, [] => v
  | .arr xs, .idx i :: r => readPath xs[i]! r
  | .record _ fs, .fld i :: r => readPath fs[i]! r
  | v, _ => v

partial def writePath : Val → List PathElem → Val → Val
  | _, [], x => x
  | .arr xs, .idx i :: r, x => .arr (xs.modify i (writePath · r x))
  | .record n fs, .fld i :: r, x => .record n (fs.modify i (writePath · r x))
  | v, _, _ => v

/-! ## The world: input oracle and event log -/

structure World where
  inputs : Array Input
  pos    : Nat := 0
  off    : Nat := 0
  /-- Index of the input item consumed last (its step). -/
  cur    : Nat := 0
  events : Array (Nat × Event) := #[]
  frame  : ByteArray := .empty
  mmio   : Std.HashMap UInt32 UInt32 := {}
  /-- The program reads frame by frame (`input.frame`): the end of a
  chunk is an item of its own, so an exhausted chunk is not skipped. -/
  framed : Bool := false
  deriving Inhabited

def World.done (w : World) : Bool := w.pos ≥ w.inputs.size

/-- Skip empty chunks (not for a framed program: there the end of a
chunk is still to be read). -/
def World.normalize (w : World) : World :=
  if w.framed then w else
  if h : w.pos < w.inputs.size then
    match w.inputs[w.pos] with
    | .rx b => if w.off ≥ b.size then { w with pos := w.pos + 1, off := 0 }.normalize else w
    | .tick => w
  else w
termination_by w.inputs.size - w.pos

def World.next (w : World) : UInt16 × World :=
  let w := w.normalize
  if h : w.pos < w.inputs.size then
    match w.inputs[w.pos] with
    | .tick => (0x0100, { w with cur := w.pos, pos := w.pos + 1, off := 0 }.normalize)
    | .rx b =>
      let v := (b.get! w.off).toUInt16
      (v, { w with cur := w.pos, off := w.off + 1 }.normalize)
  else (0xFFFF, w)

/-- `input.frame`: a byte, `0x0100` for a tick, `0x0200` at the end of a
chunk (of an empty one too), `0xFFFF` when nothing is left. -/
def World.nextFramed (w : World) : UInt16 × World :=
  if h : w.pos < w.inputs.size then
    match w.inputs[w.pos] with
    | .tick => (0x0100, { w with cur := w.pos, pos := w.pos + 1, off := 0 })
    | .rx b =>
      if w.off < b.size then ((b.get! w.off).toUInt16, { w with cur := w.pos, off := w.off + 1 })
      else (0x0200, { w with cur := w.pos, pos := w.pos + 1, off := 0 })
  else (0xFFFF, w)

def World.emit (w : World) (e : Event) : World :=
  { w with events := w.events.push (w.cur, e) }

/-! ## Machine -/

structure RunErr where
  fn   : String
  path : List Nat
  span : Span
  msg  : String
  deriving Inhabited, Repr

def RunErr.toString (e : RunErr) : String :=
  let p := ".".intercalate (e.path.map fun (n : Nat) => s!"{n}")
  s!"fn={e.fn} at stmt {p} ({e.span.toString}): {e.msg}"

instance : ToString RunErr := ⟨RunErr.toString⟩

structure Machine where
  prog    : Prog
  store   : Array Val := #[]
  globals : Std.HashMap String Nat := {}
  world   : World
  fuel    : Nat := 0
  deriving Inhabited

/-- Name → location, for the function being run. -/
abbrev Frame := List (String × Loc)

structure Pos where
  fn   : String := ""
  path : List Nat := []
  span : Span := {}

/-- Errors keep the machine state: events emitted before a trap stay in
the trace, as they do in the emitted C. -/
abbrev EvalM := ReaderT Pos (ExceptT RunErr (StateM Machine))

def fail (msg : String) : EvalM α := do
  let p ← read
  throw { fn := p.fn, path := p.path, span := p.span, msg }

def zeroOf (p : Prog) : Ty → Val
  | .int w => .int w 0
  | .bool => .bool false
  | .arr el n => .arr (Array.replicate n (match el with | .int w => .int w 0 | _ => .bool false))
  | .record r => .record r (((p.struct? r).map (·.fields)).getD [] |>.map (fun (_, t) =>
      match t with
      | .int w => Val.int w 0
      | .bool => .bool false
      | .arr (.int w) n => .arr (Array.replicate n (.int w 0))
      | .arr _ n => .arr (Array.replicate n (.bool false))
      | .record _ => .bool false) |>.toArray)

def initOf (p : Prog) (g : Global) : Val :=
  match g.ty, g.init with
  | .int w, [v] => .int w (mask w (UInt64.ofNat v))
  | .bool, [v] => .bool (v != 0)
  | .arr (.int w) n, vs => .arr ((Array.range n).map fun i => .int w (mask w (UInt64.ofNat (vs.getD i 0))))
  | .arr .bool n, vs => .arr ((Array.range n).map fun i => .bool (vs.getD i 0 != 0))
  | t, _ => zeroOf p t

def Machine.init (p : Prog) (inputs : Array Input) : Machine := Id.run do
  let mut m : Machine := { prog := p, world := { inputs, framed := p.framed } }
  for g in p.globals do
    m := { m with globals := m.globals.insert g.name m.store.size, store := m.store.push (initOf p g) }
  return m

/-- Overwrite a global (tests set up buffers this way). -/
def Machine.setGlobal (m : Machine) (x : String) (v : Val) : Machine :=
  match m.globals.get? x with
  | some c => { m with store := m.store.set! c v }
  | none => m

def Machine.global? (m : Machine) (x : String) : Option Val :=
  (m.globals.get? x).map (m.store[·]!)

def alloc (v : Val) : EvalM Loc := do
  let m ← get
  set { m with store := m.store.push v }
  return { cell := m.store.size }

def readLoc (l : Loc) : EvalM Val := do return readPath (← get).store[l.cell]! l.path

def writeLoc (l : Loc) (v : Val) : EvalM Unit :=
  modify fun m => { m with store := m.store.modify l.cell (writePath · l.path v) }

def lookupVar (fr : Frame) (x : String) : EvalM Loc := do
  if let some l := fr.lookup x then return l
  match (← get).globals.get? x with
  | some c => return { cell := c }
  | none => fail s!"unknown variable {x}"

def fieldIndex (r : String) (f : String) : EvalM Nat := do
  let some sd := (← get).prog.struct? r | fail s!"unknown record {r}"
  match sd.fields.findIdx? (·.1 == f) with
  | some i => return i
  | none => fail s!"no field {f}"

def binop (op : BinOp) (a b : Val) : EvalM Val := do
  match op, a, b with
  | .land, .bool x, .bool y => return .bool (x && y)
  | .lor, .bool x, .bool y => return .bool (x || y)
  | .eq, .bool x, .bool y => return .bool (x == y)
  | .ne, .bool x, .bool y => return .bool (x != y)
  | op, .int w x, .int _ y =>
    let r (v : UInt64) := Val.int w (mask w v)
    match op with
    | .add => return r (x + y)
    | .sub => return r (x - y)
    | .mul => return r (x * y)
    | .div => return r (if y == 0 then 0 else x / y)
    | .mod => return r (if y == 0 then 0 else x % y)
    | .band => return r (x &&& y)
    | .bor => return r (x ||| y)
    | .bxor => return r (x ^^^ y)
    | .shl => return r (if y.toNat ≥ w.bits then 0 else x <<< y)
    | .shr => return r (if y.toNat ≥ w.bits then 0 else x >>> y)
    | .eq => return .bool (x == y)
    | .ne => return .bool (x != y)
    | .lt => return .bool (x < y)
    | .le => return .bool (x ≤ y)
    | .gt => return .bool (x > y)
    | .ge => return .bool (x ≥ y)
    | _ => fail s!"bad operands for {op.symbol}"
  | _, _, _ => fail s!"bad operands for {op.symbol}"

/-- Recover a type from a value (locals are typed by their initial value). -/
partial def tyOfVal (p : Prog) : Val → Ty
  | .int w _ => .int w
  | .bool _ => .bool
  | .arr xs => .arr (if xs.size > 0 then tyOfVal p xs[0]! else .u8) xs.size
  | .record n _ => .record n

mutual

partial def placeLoc (fr : Frame) (e : Expr) : EvalM (Loc × Ty) := do
  match e with
  | .var x =>
    let l ← lookupVar fr x
    return (l, ← tyOfLoc fr x)
  | .field b f =>
    let (l, t) ← placeLoc fr b
    let .record r := t | fail "field of a non-record"
    let i ← fieldIndex r f
    let some sd := (← get).prog.struct? r | fail s!"unknown record {r}"
    return ({ l with path := l.path ++ [.fld i] }, sd.fields[i]!.2)
  | .index b i =>
    let (l, t) ← placeLoc fr b
    let .arr el n := t | fail "index of a non-array"
    let iv := (← eval fr i).toNat
    unless iv < n do fail s!"index {iv} out of bounds [0, {n})"
    return ({ l with path := l.path ++ [.idx iv] }, el)
  | _ => fail "not a place"

/-- Type of a variable (globals from the program, locals from the frame's
declared types). -/
partial def tyOfLoc (fr : Frame) (x : String) : EvalM Ty := do
  let m ← get
  if let some l := fr.lookup x then
    return tyOfVal m.prog (readPath m.store[l.cell]! l.path)
  match m.prog.global? x with
  | some g => return g.ty
  | none => fail s!"unknown variable {x}"

partial def eval (fr : Frame) (e : Expr) : EvalM Val := do
  match e with
  | .lit v (some w) => return .int w (mask w (UInt64.ofNat v))
  | .lit _ none => fail "untyped literal (program not checked)"
  | .blit b => return .bool b
  | .var _ | .field _ _ | .index _ _ => readLoc (← placeLoc fr e).1
  | .bin op a b =>
    let x ← eval fr a
    let y ← eval fr b
    binop op x y
  | .un op a =>
    match op, ← eval fr a with
    | .lnot, .bool b => return .bool !b
    | .bnot, .int w v => return .int w (mask w (~~~ v))
    | .neg, .int w v => return .int w (mask w (0 - v))
    | _, _ => fail "bad operand"
  | .cast w a =>
    match ← eval fr a with
    | .int _ v => return .int w (mask w v)
    | .bool b => return .int w (if b then 1 else 0)
    | _ => fail "bad cast"
  | .cond c a b =>
    let cv ← eval fr c
    let x ← eval fr a
    let y ← eval fr b
    return if cv.toBool then x else y

end

inductive Outcome where
  | normal | brk | ret (v : Option Val)
  deriving Inhabited

def tick : EvalM Unit := do
  let m ← get
  if m.fuel == 0 then fail "out of fuel"
  set { m with fuel := m.fuel - 1 }

def withStmt (i : Nat) (k : EvalM α) : EvalM α :=
  withReader (fun p => { p with path := p.path ++ [i] }) k

def effect (fr : Frame) (e : Effect) (args : List Expr) : EvalM (Option Val) := do
  let vs ← args.mapM (eval fr)
  let m ← get
  let w := m.world
  let set' (w : World) := set { m with world := w }
  match e with
  | .inputNext | .ringPop =>
    let (v, w') := w.next
    set' w'
    return some (.int .w16 v.toUInt64)
  | .inputFrame =>
    let (v, w') := w.nextFramed
    set' w'
    return some (.int .w16 v.toUInt64)
  | .outByte =>
    set' { w with frame := w.frame.push (vs[0]!.toNat.toUInt8) }
    return none
  | .outEnd =>
    set' { (w.emit (.tx w.frame)) with frame := .empty }
    return none
  | .drop =>
    let k := vs[0]!.toNat
    set' (w.emit (.drop (m.prog.dropReasons.getD k s!"code-{k}")))
    return none
  | .note =>
    let k := vs[0]!.toNat
    set' (w.emit (.note s!"{m.prog.notes.getD k s!"note-{k}"} {vs[1]!.toNat}"))
    return none
  | .mmioRead32 =>
    return some (.int .w32 ((w.mmio.get? vs[0]!.toNat.toUInt32).getD 0).toUInt64)
  | .mmioWrite32 =>
    set' { w with mmio := w.mmio.insert vs[0]!.toNat.toUInt32 vs[1]!.toNat.toUInt32 }
    return none

mutual

partial def call (f : String) (args : List Expr) (fr : Frame) : EvalM (Option Val) := do
  let some fd := (← get).prog.fn? f | fail s!"unknown function {f}"
  -- evaluate arguments in the caller's frame
  let mut binds : Frame := []
  let mut vals : Array (String × Val) := #[]
  for (prm, a) in fd.params.zip args do
    if prm.byRef then binds := (prm.name, (← placeLoc fr a).1) :: binds
    else vals := vals.push (prm.name, ← eval fr a)
  let mark := (← get).store.size
  for (x, v) in vals do binds := (x, ← alloc v) :: binds
  let r ← withReader (fun _ => { fn := f, path := [], span := fd.span }) (block binds fd.body)
  modify fun m => { m with store := m.store.extract 0 mark }
  match r with
  | (_, .ret v) => return v
  | _ => return none

/-- Run a block; locals declared in it are freed at its end. -/
partial def block (fr : Frame) (ss : List Stmt) : EvalM (Frame × Outcome) := do
  let mark := (← get).store.size
  let mut fr' := fr
  let mut out := Outcome.normal
  let mut i := 1
  for s in ss do
    let (f2, o) ← withStmt i (stmt fr' s)
    fr' := f2
    i := i + 1
    match o with
    | .normal => pure ()
    | o => out := o; break
  modify fun m => { m with store := m.store.extract 0 mark }
  return (fr, out)

partial def stmt (fr : Frame) (s : Stmt) : EvalM (Frame × Outcome) := do
  tick
  match s with
  | .at sp s => withReader (fun p => { p with span := sp }) (stmt fr s)
  | .decl x ty init =>
    let v ← match init with
      | some e => eval fr e
      | none => pure (zeroOf (← get).prog ty)
    return ((x, ← alloc v) :: fr, .normal)
  | .assign l r =>
    let v ← eval fr r
    let (loc, _) ← placeLoc fr l
    writeLoc loc v
    return (fr, .normal)
  | .ite c t e =>
    let (_, o) ← if (← eval fr c).toBool then block fr t else block fr e
    return (fr, o)
  | .forRange x w lo hi body =>
    let w := w.getD .w32
    let a := (← eval fr lo).toNat
    let b := (← eval fr hi).toNat
    let l ← alloc (.int w (UInt64.ofNat a))
    let fr' := (x, l) :: fr
    let mut out := Outcome.normal
    for v in [a:b] do
      writeLoc l (.int w (UInt64.ofNat v))
      let (_, o) ← block fr' body
      match o with
      | .brk => break
      | .ret v => out := .ret v; break
      | .normal => tick
    modify fun m => { m with store := m.store.pop }
    return (fr, out)
  | .loop n body =>
    let mut out := Outcome.normal
    for _ in [0:n] do
      let (_, o) ← block fr body
      match o with
      | .brk => break
      | .ret v => out := .ret v; break
      | .normal => tick
    return (fr, out)
  | .brk => return (fr, .brk)
  | .ret e => return (fr, .ret (← e.mapM (eval fr)))
  | .call dst f args =>
    let r ← call f args fr
    if let (some d, some v) := (dst, r) then
      writeLoc (← placeLoc fr d).1 v
    return (fr, .normal)
  | .eff dst e args =>
    let r ← effect fr e args
    if let (some d, some v) := (dst, r) then
      writeLoc (← placeLoc fr d).1 v
    return (fr, .normal)

end

/-- Call a function with by-value arguments from outside (tests, examples). -/
def Machine.callFn (m : Machine) (f : String) (args : List Val) (fuel : Nat := 1000000) :
    Except RunErr (Option Val × Machine) := do
  let lits := args.map fun v => match v with
    | .int w x => Expr.lit x.toNat (some w)
    | .bool b => .blit b
    | _ => .blit false
  let act : EvalM (Option Val) := call f lits []
  let (r, m') := ((act.run { fn := f }).run).run { m with fuel }
  return (← r, m')

/-- Call a function; on an error, also the machine as it was then. -/
def Machine.callFn' (m : Machine) (f : String) (fuel : Nat := 1000000) :
    Option RunErr × Machine :=
  let act : EvalM (Option Val) := call f [] []
  let (r, m') := ((act.run { fn := f }).run).run { m with fuel }
  match r with
  | .ok _ => (none, m')
  | .error e => (some e, m')

/-- Call the entry function once. -/
def Machine.step (m : Machine) (fuel : Nat := 1000000) : Except RunErr Machine := do
  let (_, m') ← m.callFn m.prog.entry [] fuel
  return m'

structure Result where
  trace : Trace
  /-- The run stopped with an error (a trap in the emitted C). -/
  error : Option RunErr := none
  machine : Machine

/-- The driver: call the entry function while input remains.  A call that
consumes nothing three times in a row ends the run. -/
def runMachine (m : Machine) (header : Header) (fuel : Nat := 1000000) : Result := Id.run do
  let mut m := m
  let mut idle := 0
  let mut err : Option RunErr := none
  while !m.world.normalize.done && idle < 3 do
    let before := (m.world.pos, m.world.off)
    let (e?, m') := m.callFn' m.prog.entry fuel
    m := m'
    if let some e := e? then err := some e; break
    idle := if (m.world.pos, m.world.off) == before then idle + 1 else 0
  let w := m.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    let e0 : Event := match w.inputs[i]! with | .rx b => .rx b | .tick => .tick
    lines := lines.push ⟨i, e0⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  if let some e := err then
    lines := lines.push ⟨w.cur, .note (trapNote (toString e))⟩
  return { trace := { header, lines }, error := err, machine := m }

/-- Check and run a program on the inputs of a trace. -/
def Prog.run (p : Prog) (inputs : Array Input) (header : Header := { impl := "interp" })
    (fuel : Nat := 1000000) : Except Err Result := do
  let p ← p.check
  return runMachine (Machine.init p inputs) header fuel

end Ember.Lang
