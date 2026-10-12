import Ember.Z80.Runtime
import Ember.Z80.Frame

/-!
# Ember.Z80.Codegen — IR to Z80 (plan M6.5)

One IR instruction at a time, with these conventions:

* a value of one byte is computed in `A`, of two bytes in `HL`, of four
  or eight bytes in the memory accumulator `rt_acc` (through the
  routines of `Ember.Z80.Runtime`);
* the second operand of an operation is an immediate, or memory (`(HL)`
  for 8 bits, loaded into `DE` for 16, pointed to by `HL` for wider
  ones); wide constants live in a literal pool;
* an address is formed in `HL` using `BC`, so that a value waiting in
  `A` or `DE` survives it.

The generator remembers which operand each of `A`, `HL` and the
accumulator holds (`Regs`) and skips a load when the value is at hand.
That is also how temporaries stay out of memory: a first pass generates
code as if every temporary had a frame slot and notes which ones are
ever *read* from their slot; the second pass gives slots (and stores)
only to those.  Labels, calls and stores through addresses forget what
they may have invalidated.
-/

namespace Ember.Z80.Codegen
open Ember.Z80.Asm (Arg Op Item Val)
open Ember.Z80.IR
open Ember.Lang (Effect)

def sanitize (s : String) : String :=
  String.join (s.toList.map fun c => if c.isAlphanum || c == '_' then String.singleton c else s!"_{c.toNat}_")

def fnLabel (f : String) : String := s!"f_{sanitize f}"

/-- Where the slots of a function's temporaries are: an area of their
own, apart from every variable (a frame under a name no function has). -/
def tmpArea (f : String) : Area := .frame (f ++ ".t")

def areaSym : Area → String
  | .global g => s!"g_{sanitize g}"
  | .frame f => s!"fr_{sanitize f}"

def slotVal (s : Slot) : Val := .sym (areaSym s.area) (Int.ofNat s.off)

/-- The operands whose value each register holds (several can be equal:
a constant just stored into a variable is both). -/
structure Regs where
  a : List Opd := []
  hl : List Opd := []
  acc : Option (Nat × Opd) := none
  deriving Inhabited, BEq

/-- Everything `x` claims, `y` claims. -/
def Regs.le (x y : Regs) : Bool :=
  x.a.all y.a.contains && x.hl.all y.hl.contains && (x.acc.isNone || x.acc == y.acc)

/-- What two paths agree on. -/
def Regs.meet (x y : Regs) : Regs :=
  { a := x.a.filter y.a.contains, hl := x.hl.filter y.hl.contains,
    acc := if x.acc == y.acc then x.acc else none }

structure GS where
  out : Array Item := #[]
  regs : Regs := {}
  /-- Temporaries read from their slot. -/
  missed : Array Bool := #[]
  /-- Wide constants: bytes and value. -/
  lits : Array (Nat × Nat) := #[]
  labels : Nat := 0
  /-- What the registers hold at the jumps to each label seen so far. -/
  atLabel : List (Nat × Regs) := []
  /-- The code being generated cannot be reached by falling through. -/
  dead : Bool := false
  /-- Offsets in the function's own frame at which a read from memory
  starts, and whether the address of anything in that frame is formed. -/
  reads : Array Bool := #[]
  addrTaken : Bool := false
  /-- A record of the jumps (the label and what the registers held) and of
  what the generator took the registers to hold after each label: checked
  against each other once the function is generated (`jumpsOk`). -/
  jumps : List (Nat × Regs) := []
  labelRegs : List (Nat × Regs) := []

structure GEnv where
  fn : IR.Fn
  /-- Which temporaries have a slot, and where in the frame. -/
  spilled : Array Bool
  tmpOff : Array Nat
  /-- The instruction after the current one, and (for a branch) the one
  at its target. -/
  next : Option IR.Instr := none
  atTarget : Option IR.Instr := none
  /-- Second pass: where reads of the own frame start.  A store to a
  place nothing reads from memory (its value was always at hand in a
  register) is left out. -/
  live : Option (Array Bool) := none

abbrev GM := ReaderT GEnv (StateT GS (Except String))

def ins (op : Op) (args : List Arg := []) : GM Unit :=
  modify fun s => { s with out := s.out.push (.ins { op, args }) }

def call (routine : String) : GM Unit := ins .call [.imm (.sym routine)]

def setRegs (f : Regs → Regs) : GM Unit := modify fun s => { s with regs := f s.regs }

/-- `m`, `k` times. -/
def rep : Nat → GM Unit → GM Unit
  | 0, _ => pure ()
  | k + 1, m => do m; rep k m

def n8 (v : Nat) : Arg := .imm (.num (Int.ofNat (v % 256)))
def n16 (v : Nat) : Arg := .imm (.num (Int.ofNat (v % 65536)))

def bits (n : Nat) : Nat := 8 * n

/-- Address of a variable or of a temporary's slot. -/
def noteRead (s : Slot) : GM Unit := do
  let e ← read
  if s.area == .frame e.fn.name then
    -- second pass: a read from memory is at a place the first pass saw read (stores there are made)
    match e.live with
    | some lv =>
      if !lv.getD s.off true then
        throw s!"{e.fn.name}: the two passes disagree on a read of the frame at {s.off}"
    | none => pure ()
    modify fun st => if s.off < st.reads.size then { st with reads := st.reads.set! s.off true } else st

def noteAddr (s : Slot) : GM Unit := do
  if s.area == .frame (← read).fn.name then modify fun st => { st with addrTaken := true }

/-- Must a store of `n` bytes at `s` be made? -/
def storeNeeded (s : Slot) (n : Nat) : GM Bool := do
  let e ← read
  if s.area != .frame e.fn.name then pure true
  else
    match e.live with
    | none => pure true
    | some lv => pure ((List.range n).any fun k => lv.getD (s.off + k) true)

def addrOf (o : Opd) : GM Val := do
  match o with
  | .slot s => do
    noteRead s
    pure (slotVal s)
  | .tmp t => do
    let e ← read
    if e.spilled[t]! then do
      modify fun s => { s with missed := s.missed.set! t true }
      pure (.sym (areaSym (tmpArea e.fn.name)) (Int.ofNat e.tmpOff[t]!))
    else throw s!"{e.fn.name}: temporary t{t} has no slot and is not at hand"
  | .const _ => throw "address of a constant"

/-- Address of an operand of `n` bytes; a constant is in the literal pool. -/
def ptrOf (n : Nat) (o : Opd) : GM Val := do
  match o with
  | .const v =>
    let v := v % 2 ^ bits n
    modify fun s => if s.lits.contains (n, v) then s else { s with lits := s.lits.push (n, v) }
    pure (.sym s!"lit{bits n}_{v}")
  | o => addrOf o

/-! ### Loading -/

def isSlot : Opd → Bool
  | .slot _ => true
  | _ => false

def loadA (o : Opd) : GM Unit := do
  let r := (← get).regs
  if r.a.contains o then pure ()
  -- the low byte of what `HL` holds
  else if r.hl.contains o && isSlot o then do
    ins .ld [.a, .l]
    setRegs fun r => { r with a := [o] }
  else do
    match o with
    | .const v => if v % 256 == 0 then ins .xor [.a] else ins .ld [.a, n8 v]
    | o => do
      let p ← addrOf o
      ins .ld [.a, .mem p]
    setRegs fun r => { r with a := [o] }

def loadHL (o : Opd) : GM Unit := do
  let r := (← get).regs
  if r.hl.contains o then pure ()
  else do
    match o with
    | .const v => ins .ld [.hl, n16 v]
    | o => do
      let p ← addrOf o
      ins .ld [.hl, .mem p]
    setRegs fun r => { r with hl := [o] }

def loadDE (o : Opd) : GM Unit := do
  let r := (← get).regs
  if r.hl.contains o then do
    ins .ld [.d, .h]
    ins .ld [.e, .l]
  else
    match o with
    | .const v => ins .ld [.de, n16 v]
    | o => do
      let p ← addrOf o
      ins .ld [.de, .mem p]

def loadAcc (n : Nat) (o : Opd) : GM Unit := do
  let r := (← get).regs
  if r.acc == some (n, o) then pure ()
  else do
    let p ← ptrOf n o
    ins .ld [.hl, .imm p]
    call s!"rt_ld{bits n}"
    setRegs fun _ => { acc := some (n, o) }

/-! ### Storing -/

def overlaps (o : Opd) (size : Nat) (s : Slot) (n : Nat) : Bool :=
  match o with
  | .slot t => t.area == s.area && t.off < s.off + n && s.off < t.off + size
  | _ => false

/-- A write of `n` bytes at `s`: forget what read them. -/
def killWrite (s : Slot) (n : Nat) : GM Unit :=
  setRegs fun r =>
    { a := r.a.filter fun o => !overlaps o 1 s n,
      hl := r.hl.filter fun o => !overlaps o 2 s n,
      acc := r.acc.filter fun (m, o) => !overlaps o m s n }

/-- A write somewhere: forget every variable. -/
def killSlots : GM Unit :=
  let keep (o : Opd) : Bool := match o with | .slot _ => false | _ => true
  setRegs fun r => { a := r.a.filter keep, hl := r.hl.filter keep, acc := r.acc.filter fun (_, o) => keep o }

def killAll : GM Unit := setRegs fun _ => {}

def tmpSlot (t : Nat) : GM (Option Val) := do
  let e ← read
  if e.spilled[t]! then pure (some (.sym (areaSym (tmpArea e.fn.name)) (Int.ofNat e.tmpOff[t]!)))
  else pure none

/-- A temporary is assigned: what held its old value no longer does. -/
def forget (o : Opd) : GM Unit :=
  setRegs fun r => { a := r.a.filter (· != o), hl := r.hl.filter (· != o), acc := r.acc.filter (·.2 != o) }

def storeA (d : Dst) : GM Unit := do
  match d with
  | .slot s => killWrite s 1; if ← storeNeeded s 1 then ins .ld [.mem (slotVal s), .a]
  | .tmp t =>
    forget (.tmp t)
    if let some v ← tmpSlot t then ins .ld [.mem v, .a]
  setRegs fun r => { r with a := d.opd :: r.a }

def storeHL (d : Dst) : GM Unit := do
  match d with
  | .slot s => killWrite s 2; if ← storeNeeded s 2 then ins .ld [.mem (slotVal s), .hl]
  | .tmp t =>
    forget (.tmp t)
    if let some v ← tmpSlot t then ins .ld [.mem v, .hl]
  setRegs fun r => { r with hl := d.opd :: r.hl }

def storeAcc (n : Nat) (d : Dst) : GM Unit := do
  match d with
  | .slot s =>
    killWrite s n
    if ← storeNeeded s n then
      ins .ld [.hl, .imm (slotVal s)]
      call s!"rt_st{bits n}"
  | .tmp t =>
    if let some v ← tmpSlot t then
      ins .ld [.hl, .imm v]
      call s!"rt_st{bits n}"
  -- the same in both passes, whether the temporary has a slot or not
  setRegs fun _ => { acc := some (n, d.opd) }

def store (n : Nat) (d : Dst) : GM Unit :=
  if n == 1 then storeA d else if n == 2 then storeHL d else storeAcc n d

def load (n : Nat) (o : Opd) : GM Unit :=
  if n == 1 then loadA o else if n == 2 then loadHL o else loadAcc n o

/-! ### Operations -/

def newLabel : GM String := do
  let s ← get
  set { s with labels := s.labels + 1 }
  return s!"x_{sanitize (← read).fn.name}_{s.labels}"

def localLabel (l : Nat) : GM String := do return s!"l_{sanitize (← read).fn.name}_{l}"

/-- The 8-bit ALU instruction with its operand. -/
def alu8 (op : Bin) (x : Arg) : GM Unit :=
  match op with
  | .add => ins .add [.a, x]
  | .sub => ins .sub [x]
  | .and => ins .and [x]
  | .or => ins .or [x]
  | .xor => ins .xor [x]
  | _ => throw "alu8"

def routine16 : Bin → String
  | .and => "rt_and16" | .or => "rt_or16" | .xor => "rt_xor16"
  | .mul => "rt_mul16" | .div => "rt_div16" | _ => "rt_mod16"

def routineW (op : Bin) (n : Nat) : String :=
  let name := match op with
    | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
    | .and => "and" | .or => "or" | .xor => "xor"
  s!"rt_{name}{bits n}"

/-- A byte of `HL` with a constant: nothing where the constant leaves the byte alone. -/
def logicConst (op : Bin) (reg : Arg) (m : Nat) : GM Unit :=
  if (if op == .and then m == 255 else m == 0) then pure ()
  else if op == .and && m == 0 then ins .ld [reg, n8 0]
  else if op == .or && m == 255 then ins .ld [reg, n8 255]
  else do
    ins .ld [.a, reg]
    alu8 op (n8 m)
    ins .ld [reg, .a]
    setRegs fun r => { r with a := [] }

/-- The second operand of an 8-bit routine into `E`, the first being in `A`. -/
def loadE (a b : Opd) : GM Unit :=
  match b with
  | .const v => ins .ld [.e, n8 v]
  | b =>
    if a == b then ins .ld [.e, .a]
    else do
      let p ← addrOf b
      ins .ld [.hl, .imm p]
      ins .ld [.e, .mhl]
      setRegs fun r => { r with hl := [] }

/-- `mul`, `div`, `mod` of one byte: `A := A op E` by a routine. -/
def bin8Rt (op : Bin) (a b : Opd) : GM Unit := do
  let r := (← get).regs
  if r.a.contains b && a != b then do
    ins .ld [.e, .a]
    loadA a
  else do
    loadA a
    loadE a b
  call (match op with | .mul => "rt_mul8" | .div => "rt_div8" | _ => "rt_mod8")

/-- The second operand of an 8-bit operation, the first being in `A`. -/
def alu8Opd (op : Bin) (a b : Opd) : GM Unit :=
  match b with
  | .const v =>
    if op == .add && v % 256 == 1 then ins .inc [.a]
    else if op == .sub && v % 256 == 1 then ins .dec [.a]
    else if op == .add && v % 256 == 255 then ins .dec [.a]
    else if op == .sub && v % 256 == 255 then ins .inc [.a]
    else alu8 op (n8 (v % 256))
  | b =>
    if a == b then alu8 op .a
    else do
      let p ← addrOf b
      ins .ld [.hl, .imm p]
      alu8 op .mhl
      setRegs fun r => { r with hl := [] }

/-- `add`, `sub`, `and`, `or`, `xor` of one byte, in `A`. -/
def bin8Alu (op : Bin) (a b : Opd) : GM Unit := do
  let r := (← get).regs
  if r.a.contains b && a != b then do
    ins .ld [.c, .a]
    setRegs fun r => { r with a := [] }
    loadA a
    alu8 op .c
  else do
    loadA a
    alu8Opd op a b

def bin8 (op : Bin) (a b : Opd) : GM Unit := do
  match op with
  | .mul | .div | .mod => bin8Rt op a b
  | _ => bin8Alu op a b
  setRegs fun r => { r with a := [] }

/-- A 16-bit operation with a constant, where that is shorter. -/
def bin16Const (op : Bin) (v : Nat) : GM Unit :=
  match op with
  | .add =>
    if v ≤ 3 then rep v (ins .inc [.hl])
    else if v ≥ 65533 then rep (65536 - v) (ins .dec [.hl])
    else do
      ins .ld [.de, n16 v]
      ins .add [.hl, .de]
  | .sub =>
    if v ≤ 3 then rep v (ins .dec [.hl])
    else do
      ins .ld [.de, n16 (65536 - v)]
      ins .add [.hl, .de]
  | _ => do
    -- byte by byte, and nothing where the constant leaves the byte alone
    logicConst op .l (v % 256)
    logicConst op .h (v / 256)

/-- A 16-bit operation, the operands in `HL` and `DE`. -/
def bin16Reg (op : Bin) : GM Unit :=
  match op with
  | .add => ins .add [.hl, .de]
  | .sub => do
    ins .or [.a]
    ins .sbc [.hl, .de]
  | .and | .or | .xor => do
    ins .ld [.a, .l]
    alu8 op .e
    ins .ld [.l, .a]
    ins .ld [.a, .h]
    alu8 op .d
    ins .ld [.h, .a]
    setRegs fun r => { r with a := [] }
  | op => do
    call (routine16 op)
    setRegs fun r => { r with a := [] }

/-- Is the constant handled without `DE`? -/
def small16 (op : Bin) : Bool :=
  match op with
  | .add | .sub | .and | .or | .xor => true
  | _ => false

def bin16 (op : Bin) (a b : Opd) : GM Unit := do
  let r := (← get).regs
  let bAtHand := r.hl.contains b && a != b
  if bAtHand then do
    ins .ex [.de, .hl]
    setRegs fun r => { r with hl := [] }
    loadHL a
  else loadHL a
  match b with
  | .const v =>
    if !bAtHand && small16 op then bin16Const op (v % 65536)
    else do
      if !bAtHand then loadDE b
      bin16Reg op
  | _ => do
    if !bAtHand then loadDE b
    bin16Reg op
  setRegs fun r => { r with hl := [] }

/-- Wider: the second operand by its address — a temporary at hand in
the accumulator is asked for there, and so gets its slot. -/
def binW (op : Bin) (n : Nat) (a b : Opd) : GM Unit := do
  let pb ← ptrOf n b
  loadAcc n a
  ins .ld [.hl, .imm pb]
  call (routineW op n)
  killAll

def genBin (op : Bin) (n : Nat) (a b : Opd) : GM Unit :=
  if n == 1 then bin8 op a b else if n == 2 then bin16 op a b else binW op n a b

/-- Shift count into `B`, from an operand of `m` bytes. -/
def countToB (m : Nat) (amt : Opd) : GM Unit := do
  if m == 1 then
    loadA amt
  else if m == 2 then
    loadHL amt
    call "rt_sat16"
  else
    loadAcc m amt
    call s!"rt_sat{bits m}"
    setRegs fun r => { r with hl := [] }
  ins .ld [.b, .a]
  if m != 1 then setRegs fun r => { r with a := [] }

def genShift (left : Bool) (n : Nat) (a : Opd) (m : Nat) (amt : Opd) : GM Unit := do
  let name := s!"rt_{if left then "shl" else "shr"}{bits n}"
  match amt with
  | .const k =>
    -- 0 < k < 8n here
    if n == 1 then
      loadA a
      if left && k ≤ 3 then rep k (ins .add [.a, .a])
      else if !left && k == 1 then ins .srl [.a]
      else
        ins .ld [.b, n8 k]
        call name
      setRegs fun r => { r with a := [] }
    else if n == 2 then
      loadHL a
      if left && k ≤ 4 then rep k (ins .add [.hl, .hl])
      else if left && k == 8 then
        ins .ld [.h, .l]
        ins .ld [.l, n8 0]
      else if !left && k == 8 then
        ins .ld [.l, .h]
        ins .ld [.h, n8 0]
      else if !left && k ≤ 2 then
        rep k (do
          ins .srl [.h]
          ins .rr [.l])
      else
        ins .ld [.b, n8 k]
        call name
      setRegs fun r => { r with hl := [] }
    else if n == 4 && k == 16 then
      loadAcc n a
      let lo : Arg := .mem (.sym "rt_acc")
      let hi : Arg := .mem (.sym "rt_acc" 2)
      ins .ld [.hl, if left then lo else hi]
      ins .ld [if left then hi else lo, .hl]
      ins .ld [.hl, n16 0]
      ins .ld [if left then lo else hi, .hl]
      killAll
    else
      loadAcc n a
      ins .ld [.b, n8 k]
      call name
      killAll
  | amt =>
    countToB m amt
    if n == 1 then
      loadA a
      call name
      setRegs fun r => { r with a := [] }
    else if n == 2 then
      loadHL a
      call name
      setRegs fun r => { r with hl := [] }
    else
      if (← get).regs.acc != some (n, a) then
        ins .push [.bc]
        loadAcc n a
        ins .pop [.bc]
      call name
      killAll

/-- Does the instruction read the operand? -/
def reads (i : IR.Instr) (o : Opd) : Bool :=
  let inAddr (p : Addr) : Bool := match p.idx with | some x => x.opd == o | none => false
  match i with
  | .mov _ _ s => s == o
  | .bin _ _ _ a b => a == o || b == o
  | .shift _ _ _ a _ amt => a == o || amt == o
  | .not _ _ a | .neg _ _ a => a == o
  | .ext _ _ _ s => s == o
  | .cmp _ _ _ a b | .br _ _ a b _ => a == o || b == o
  | .load _ _ p | .lea _ p => inAddr p
  | .store _ p s => s == o || inAddr p
  | .call _ _ reg => (reg.map (·.2 == o)).getD false
  | .eff _ args _ => args.any (·.2 == o)
  | .ret v => (v.map (·.2 == o)).getD false
  | _ => false

/-- Is the comparison a test for zero that only `Z` is wanted of? -/
def zeroTest (op : Cmp) (b : Opd) : Bool := b == .const 0 && (op == .eq || op == .ne)

/-- `cp` with the second operand, the first being in `A`. -/
def cp8Opd (a b : Opd) : GM Unit :=
  match b with
  | .const v => ins .cp [n8 v]
  | b =>
    if a == b then ins .cp [.a]
    else do
      let p ← addrOf b
      ins .ld [.hl, .imm p]
      ins .cp [.mhl]
      setRegs fun r => { r with hl := [] }

/-- One byte: `cp`, or `or a` for a test for zero. -/
def flags8 (op : Cmp) (a b : Opd) : GM Unit := do
  let r := (← get).regs
  if zeroTest op b then do
    loadA a
    ins .or [.a]
  else if r.a.contains b && a != b then do
    ins .ld [.c, .a]
    setRegs fun r => { r with a := [] }
    loadA a
    ins .cp [.c]
  else do
    loadA a
    cp8Opd a b

/-- The constant of an equality test of two bytes that is done in `A`, `HL` being kept. -/
def eqConst (op : Cmp) (b : Opd) : Option Nat :=
  match b with
  | .const v =>
    if (op == .eq || op == .ne) && (v % 65536 == 65535 || v % 65536 % 256 == 0 || v % 65536 / 256 == 0) then
      some (v % 65536)
    else none
  | _ => none

/-- `Z` exactly when `HL = v`, for the constants of `eqConst`. -/
def eqHL (v : Nat) : GM Unit :=
  if v == 65535 then do
    ins .ld [.a, .h]
    ins .and [.l]
    ins .inc [.a]
  else if v / 256 == 0 then do
    ins .ld [.a, .l]
    ins .xor [n8 v]
    ins .or [.h]
  else do
    ins .ld [.a, .h]
    ins .xor [n8 (v / 256)]
    ins .or [.l]

/-- Is `a` read again right after the comparison (here or at the branch target)? -/
def readAgain (e : GEnv) (a : Opd) : Bool :=
  (match a with | .const _ => false | _ => true) &&
    ((e.next.map (reads · a)).getD false || (e.atTarget.map (reads · a)).getD false)

/-- Two bytes: `HL − DE`; when `a` is read again right after, the
subtrahend is added back, which leaves both flags. -/
def sub16 (a b : Opd) : GM Unit := do
  let r := (← get).regs
  if r.hl.contains b && a != b then do
    ins .ex [.de, .hl]
    setRegs fun r => { r with hl := [] }
    loadHL a
  else do
    loadHL a
    loadDE b
  ins .or [.a]
  ins .sbc [.hl, .de]
  let e ← read
  if readAgain e a then ins .add [.hl, .de]
  else setRegs fun r => { r with hl := [] }

def flags16 (op : Cmp) (a b : Opd) : GM Unit :=
  if zeroTest op b then do
    loadHL a
    ins .ld [.a, .h]
    ins .or [.l]
    setRegs fun r => { r with a := [] }
  else
    match eqConst op b with
    | some v => do
      loadHL a
      eqHL v
      setRegs fun r => { r with a := [] }
    | none => sub16 a b

def flagsW (n : Nat) (a b : Opd) : GM Unit := do
  let pb ← ptrOf n b
  loadAcc n a
  ins .ld [.hl, .imm pb]
  call s!"rt_cmp{bits n}"
  setRegs fun r => { r with a := [], hl := [] }

/-- Flags of `a − b`: `Z` when equal, `C` when below (for `eq` and `ne`, `Z` alone). -/
def genFlags (op : Cmp) (n : Nat) (a b : Opd) : GM Unit :=
  if n == 1 then flags8 op a b else if n == 2 then flags16 op a b else flagsW n a b

def condOf : Cmp → Arg
  | .eq => .z | .ne => .nz | .lt => .c | .ge => .nc

def addOff (k : Nat) : GM Unit :=
  if k == 0 then pure ()
  else if k ≤ 3 then rep k (ins .inc [.hl])
  else do
    ins .ld [.bc, n16 k]
    ins .add [.hl, .bc]

/-- `HL` times `sc`, a power of two (`fuel`: at least its logarithm). -/
def scaleHL : Nat → Nat → GM Unit
  | 0, _ => pure ()
  | fuel + 1, sc =>
    if sc > 1 then do
      ins .add [.hl, .hl]
      scaleHL fuel (sc / 2)
    else pure ()

/-- A byte into `HL`, the upper byte zero.  Keeps `A`. -/
def loadHLByte (o : Opd) : GM Unit := do
  if (← get).regs.a.contains o then
    ins .ld [.l, .a]
    ins .ld [.h, n8 0]
  else
    match o with
    | .const v => ins .ld [.hl, n16 (v % 256)]
    | o =>
      -- two bytes read, the upper one dropped
      ins .ld [.hl, .mem (← addrOf o)]
      ins .ld [.h, n8 0]

/-- The check of an index is made in line for a fixed array of bytes:
`index − len` carries exactly when the index is too large, and the base
is then added with `len` on top. -/
def inlineLen (x : Index) (root : Root) : Option Nat :=
  match x.len, root with
  | some len, .static _ => if x.scale == 1 then some len else none
  | _, _ => none

/-- Trap unless the index in `HL` is below the length. -/
def genCheck (x : Index) (inline : Option Nat) : GM Unit :=
  match x.len, inline with
  | some len, some _ => do
    ins .ld [.bc, n16 (65536 - len)]
    ins .add [.hl, .bc]
    ins .jp [.c, .imm (.sym "rt_trap")]
  | some len, none => do
    ins .ld [.bc, n16 len]
    call "rt_bound"
  | none, _ => pure ()

/-- The address into `HL`.  Keeps `A` and `DE`. -/
def genAddr (p : Addr) : GM Unit := do
  match p.idx with
  | none =>
    match p.root with
    | .static s =>
      noteAddr s
      ins .ld [.hl, .imm (slotVal { s with off := s.off + p.off })]
    | .ptr q =>
      noteRead q
      ins .ld [.hl, .mem (slotVal q)]
      addOff p.off
  | some x =>
    if x.size == 2 then loadHL x.opd else loadHLByte x.opd
    genCheck x (inlineLen x p.root)
    scaleHL x.scale x.scale
    match p.root with
    | .static s =>
      noteAddr s
      ins .ld [.bc, .imm (slotVal { s with off := s.off + p.off + (inlineLen x p.root).getD 0 })]
      ins .add [.hl, .bc]
    | .ptr q =>
      noteRead q
      ins .ld [.bc, .mem (slotVal q)]
      ins .add [.hl, .bc]
      addOff p.off
  setRegs fun r => { r with hl := [] }

/-- Record the registers at a jump to `l`. -/
def jumpTo (l : Nat) : GM Unit :=
  modify fun s =>
    let r := match s.atLabel.lookup l with
      | some old => old.meet s.regs
      | none => s.regs
    { s with atLabel := (l, r) :: s.atLabel.filter (·.1 != l), jumps := (l, s.regs) :: s.jumps }

/-- At every jump the registers held what was assumed of them after its
label, and no label was generated twice. -/
def jumpsOk (s : GS) : Bool :=
  (s.jumps.all fun (l, r) =>
    match s.labelRegs.lookup l with
    | some rl => rl.le r
    | none => false) &&
  decide (s.labelRegs.map (·.1)).Nodup

def effectRoutine : Effect → String
  | .inputNext | .ringPop => "rt_input"
  -- (no Z80 platform has a framed link: the label is not defined)
  | .inputFrame => "rt_input_frame"
  | .outByte => "rt_out_byte" | .outEnd => "rt_out_end"
  | .drop => "rt_drop" | .note => "rt_note"
  | .mmioRead32 => "rt_mmio_read" | .mmioWrite32 => "rt_mmio_write"

/-- Can control go on from this instruction to the one after it? -/
def canFall : IR.Instr → Bool
  | .jmp _ | .ret _ | .trap => false
  | _ => true

/-- What the registers are taken to hold after a label: what every way
there agrees on; a jump from further down is not known yet, and then
nothing is. -/
def labelRegsOf (st : GS) (backward : Bool) (l : Nat) : Regs :=
  if backward then {}
  else
    match st.atLabel.lookup l, st.dead with
    | some r, true => r
    | some r, false => r.meet st.regs
    | none, false => st.regs
    | none, true => {}

def genLabel (l : Nat) : GM Unit := do
  let name ← localLabel l
  modify fun s => { s with out := s.out.push (.label name) }
  let st ← get
  let body := (← read).fn.body
  let here := (body.findIdx? (· == .label l)).getD 0
  let backward := (List.range body.size).any fun k => k > here && (match body[k]! with
    | .jmp m | .br _ _ _ _ m => m == l
    | _ => false)
  -- falling into the label from the instruction before it is a way there too
  let prevFalls := here == 0 || ((body[here - 1]?).map canFall).getD true
  modify fun s =>
    { s with regs := labelRegsOf st backward l, dead := false,
             labelRegs := (l, labelRegsOf st backward l) :: s.labelRegs,
             jumps := if prevFalls then (l, st.regs) :: s.jumps else s.jumps }

def genInstr (i : IR.Instr) : GM Unit := do
  match i with
  | .mov n d src =>
    load n src
    store n d
  | .bin op n d a b =>
    genBin op n a b
    store n d
  | .shift left n d a m amt =>
    match amt with
    | .const k =>
      if k ≥ bits n then load n (.const 0)
      else if k == 0 then load n a
      else genShift left n a m amt
    | _ => genShift left n a m amt
    store n d
  | .not n d a =>
    load n a
    if n == 1 then ins .cpl
    else if n == 2 then call "rt_not16"
    else call s!"rt_not{bits n}"
    if n == 1 then setRegs fun r => { r with a := [] }
    else if n == 2 then setRegs fun r => { r with a := [], hl := [] }
    else killAll
    store n d
  | .neg n d a =>
    load n a
    if n == 1 then ins .neg
    else if n == 2 then call "rt_neg16"
    else call s!"rt_neg{bits n}"
    if n == 1 then setRegs fun r => { r with a := [] }
    else if n == 2 then setRegs fun r => { r with a := [], hl := [] }
    else killAll
    store n d
  | .ext n d m src =>
    let r := (← get).regs
    if n < m then
      -- the low bytes: from the register that has the value, or from memory
      if m == 2 then
        if r.hl.contains src then ins .ld [.a, .l] else ins .ld [.a, .mem (← addrOf src)]
        setRegs fun r => { r with a := [] }
      else if r.acc == some (m, src) then
        if n == 1 then ins .ld [.a, .mem (.sym "rt_acc")]
        else if n == 2 then ins .ld [.hl, .mem (.sym "rt_acc")]
        else pure ()
        if n == 1 then setRegs fun r => { r with a := [] }
        else if n == 2 then setRegs fun r => { r with hl := [] }
        else setRegs fun r => { r with acc := none }
      else
        match src with
        | .const v => load n (.const (v % 2 ^ bits n))
        | src =>
          let p ← addrOf src
          if n == 1 then ins .ld [.a, .mem p]
          else if n == 2 then ins .ld [.hl, .mem p]
          else
            ins .ld [.hl, .imm p]
            call "rt_ld32"
          if n == 1 then setRegs fun r => { r with a := [] }
          else if n == 2 then setRegs fun r => { r with hl := [] }
          else killAll
    else if n == 2 then
      -- from one byte
      loadHLByte src
      setRegs fun r => { r with hl := [] }
    else
      if m == 1 then
        loadA src
        call "rt_acc_a"
      else if m == 2 then
        loadHL src
        call "rt_acc_hl"
      else
        loadAcc 4 src
        call "rt_zx32"
      killAll
    store n d
  | .cmp op n d a b =>
    genFlags op n a b
    match op with
    | .eq | .ne =>
      let l ← newLabel
      ins .ld [.a, n8 0]
      ins .jr [if op == .eq then .nz else .z, .imm (.sym l)]
      ins .inc [.a]
      modify fun s => { s with out := s.out.push (.label l) }
    | .lt =>
      ins .ld [.a, n8 0]
      ins .rla
    | .ge =>
      ins .sbc [.a, .a]
      ins .inc [.a]
    setRegs fun r => { r with a := [] }
    storeA d
  | .br op n a b l =>
    genFlags op n a b
    ins .jp [condOf op, .imm (.sym (← localLabel l))]
    jumpTo l
  | .jmp l =>
    ins .jp [.imm (.sym (← localLabel l))]
    jumpTo l
    modify fun s => { s with dead := true }
  | .label l => genLabel l
  | .load n d p =>
    genAddr p
    if n == 1 then
      ins .ld [.a, .mhl]
      setRegs fun r => { r with a := [] }
    else if n == 2 then
      ins .ld [.a, .mhl]
      ins .inc [.hl]
      ins .ld [.h, .mhl]
      ins .ld [.l, .a]
      setRegs fun r => { r with a := [], hl := [] }
    else
      call s!"rt_ld{bits n}"
      killAll
    store n d
  | .store n p src =>
    let r := (← get).regs
    if n == 1 then
      match src with
      | .const v =>
        genAddr p
        ins .ld [.mhl, n8 v]
      | src =>
        if r.a.contains src then
          genAddr p
          ins .ld [.mhl, .a]
        else
          genAddr p
          ins .ld [.a, .mem (← addrOf src)]
          ins .ld [.mhl, .a]
          setRegs fun r => { r with a := [src] }
    else if n == 2 then
      if r.hl.contains src then
        ins .ex [.de, .hl]
        setRegs fun r => { r with hl := [] }
        genAddr p
      else
        genAddr p
        loadDE src
      ins .ld [.mhl, .e]
      ins .inc [.hl]
      ins .ld [.mhl, .d]
    else
      if r.acc == some (n, src) then
        genAddr p
      else
        genAddr p
        ins .push [.hl]
        loadAcc n src
        ins .pop [.hl]
      call s!"rt_st{bits n}"
      setRegs fun r => { r with a := [], hl := [] }
    killSlots
  | .lea d p =>
    genAddr p
    storeHL d
  | .zero s n =>
    if n > 0 then
      ins .ld [.hl, .imm (slotVal s)]
      ins .ld [.bc, n16 n]
      call "rt_zero"
      setRegs fun r => { r with a := [], hl := [] }
      killWrite s n
  | .call f ret reg =>
    if let some (n, o) := reg then load n o
    call (fnLabel f)
    killAll
    if let some (n, d) := ret then store n d
  | .eff e args ret =>
    match e, args with
    | .outByte, [(_, o)] | .drop, [(_, o)] => loadA o
    | .note, [(_, code), (_, value)] =>
      loadAcc 4 value
      loadA code
    | .mmioRead32, [(_, addr)] => loadAcc 4 addr
    | .mmioWrite32, [(_, addr), (_, value)] =>
      loadAcc 4 addr
      call "rt_mmio_addr"
      killAll
      loadAcc 4 value
    | _, _ => pure ()
    call (effectRoutine e)
    killAll
    if let some (n, d) := ret then store n d
  | .ret v =>
    if let some (n, o) := v then load n o
    ins .ret
    modify fun s => { s with dead := true }
  | .trap =>
    ins .jp [.imm (.sym "rt_trap")]
    modify fun s => { s with dead := true }

/-- The slots of the temporaries, in their area (`tmpArea`): the offset
of each (whether it has a slot or not), and the bytes they take. -/
def tmpLayout (f : IR.Fn) (spilled : Array Bool) : Array Nat × Nat :=
  (List.range f.tmps.size).foldl
    (fun (acc : Array Nat × Nat) t => (acc.1.push acc.2, if spilled[t]! then acc.2 + f.tmps[t]! else acc.2))
    (#[], 0)

/-- The instruction a branch leads to, after its label. -/
def targetOf (f : IR.Fn) (i : IR.Instr) : Option IR.Instr :=
  match i with
  | .br _ _ _ _ l => (f.body.findIdx? (· == .label l)).bind fun j => f.body[j + 1]?
  | _ => none

/-- The instructions from the `k`-th on. -/
def genBody (f : IR.Fn) (annotate : Bool) : Nat → List IR.Instr → GM Unit
  | _, [] => pure ()
  | k, i :: r => do
    if annotate then modify fun s => { s with out := s.out.push (.comment i.text.trimAscii.toString) }
    withReader (fun e => { e with next := f.body[k + 1]?, atTarget := targetOf f i }) (genInstr i)
    genBody f annotate (k + 1) r

/-- A function: its labels, the register parameter to its slot (and at hand), its body. -/
def genFnCode (f : IR.Fn) (isEntry annotate : Bool) : GM Unit := do
  if isEntry then modify fun s => { s with out := s.out.push (.label "f_entry") }
  modify fun s => { s with out := s.out.push (.label (fnLabel f.name)) }
  match f.regParam with
  | some (n, sl) => store n (.slot sl)
  | none => pure ()
  genBody f annotate 0 f.body.toList

/-- One function with the given temporaries in slots: its items, and the
temporaries read from their slot. -/
def genFn (f : IR.Fn) (spilled : Array Bool) (lits : Array (Nat × Nat)) (isEntry := false)
    (live : Option (Array Bool) := none) (annotate := false) :
    Except String (Array Item × Array Bool × Array (Nat × Nat) × Nat × Option (Array Bool)) :=
  match ((genFnCode f isEntry annotate).run
      { fn := f, spilled, tmpOff := (tmpLayout f spilled).1, live }).run
      { missed := Array.replicate f.tmps.size false, lits, reads := Array.replicate f.frame false } with
  | .ok ((), st) =>
    if jumpsOk st then
      .ok (st.out, st.missed, st.lits, (tmpLayout f spilled).2, if st.addrTaken then none else some st.reads)
    else .error s!"{f.name}: the registers assumed after a label are not those at a jump to it"
  | .error e => .error e

structure Compiled where
  items : List Item
  /-- Bytes of the slots of every function's temporaries. -/
  tmps : List (String × Nat)
  lits : Array (Nat × Nat)

/-- A store to a byte of the frame that another function's frame shares
is made, read from memory or not: the byte is one the other function's
variable has, and the IR writes it. -/
def keepShared (shared : Nat → Bool) (live : Option (Array Bool)) : Option (Array Bool) :=
  live.map fun lv => lv.mapIdx fun k b => b || shared k

/-- One function, two passes: with a slot for every temporary to find
the temporaries read from their slot, then with slots for those only. -/
def genOne (p : IR.Prog) (annotate : Bool) (shared : String → Nat → Bool) (f : IR.Fn) (lits : Array (Nat × Nat)) :
    Except String (Array Item × Array (Nat × Nat) × Nat) :=
  match genFn f (Array.replicate f.tmps.size true) lits with
  | .error e => .error e
  | .ok (_, missed, _, _, live) =>
    match genFn f missed lits (f.name == p.entry) (keepShared (shared f.name) live) annotate with
    | .error e => .error e
    | .ok (code, missed2, lits2, size, _) =>
      match (List.range f.tmps.size).find? fun t => missed2[t]! && !missed[t]! with
      | some t => .error s!"{f.name}: the two passes disagree on t{t}"
      | none => .ok (code, lits2, size)

/-- The functions one after the other: items, bytes of temporaries, literals. -/
def genFns (p : IR.Prog) (annotate : Bool) (shared : String → Nat → Bool) :
    List IR.Fn → Array Item × Array (String × Nat) × Array (Nat × Nat) →
      Except String (Array Item × Array (String × Nat) × Array (Nat × Nat))
  | [], acc => .ok acc
  | f :: r, (items, frames, lits) =>
    if f.dead then genFns p annotate shared r (items, frames.push (f.name, 0), lits)
    else
      match genOne p annotate shared f lits with
      | .error e => .error e
      | .ok (code, lits2, size) => genFns p annotate shared r (items ++ code, frames.push (f.name, size), lits2)

/-- All functions: two passes each. -/
def genProg (p : IR.Prog) (annotate := false) (shared : String → Nat → Bool := fun _ _ => false) :
    Except String Compiled :=
  match genFns p annotate shared p.fns (#[], #[], #[]) with
  | .error e => .error e
  | .ok (items, frames, lits) => .ok { items := items.toList, tmps := frames.toList, lits }

/-! ## A whole image -/

def invert : Arg → Option Arg
  | .z => some .nz | .nz => some .z | .c => some .nc | .nc => some .c
  | .po => some .pe | .pe => some .po | .p => some .m | .m => some .p
  | _ => none

/-- `call f` + `ret` is a jump; a jump over a `ret` is a conditional `ret`. -/
partial def peephole (items : List Item) : List Item :=
  match items with
  | .ins { op := .call, args := [.imm v] } :: .ins { op := .ret, args := [] } :: rest =>
    .ins { op := .jp, args := [.imm v] } :: peephole rest
  | .ins { op := .call, args := [.imm v] } :: .label l :: rest =>
    -- labels in between: the `ret` stays for those who jump to it
    let afterLabels := rest.dropWhile fun it => match it with | .label _ => true | _ => false
    match afterLabels with
    | .ins { op := .ret, args := [] } :: _ => .ins { op := .jp, args := [.imm v] } :: peephole (.label l :: rest)
    | _ => items.head! :: peephole items.tail!
  | .ins { op := .jp, args := [cc, .imm (.sym l 0)] } :: .ins { op := .ret, args := [] } :: .label m :: rest =>
    match invert cc, l == m with
    | some inv, true => .ins { op := .ret, args := [inv] } :: peephole (.label m :: rest)
    | _, _ => items.head! :: peephole items.tail!
  | i :: rest => i :: peephole rest
  | [] => []

/-- Local labels nothing refers to, and what cannot be reached after an
unconditional `ret`, `jp` or `jr` up to the next label. -/
partial def sweep (items : List Item) : List Item := Id.run do
  let used := Runtime.symsOf items
  let isLocal (l : String) : Bool := l.startsWith "l_" || l.startsWith "x_"
  let mut out : Array Item := #[]
  let mut dead := false
  for it in items do
    match it with
    | .label l =>
      if isLocal l && !used.contains l then continue
      dead := false
      out := out.push it
    | .ins i =>
      if dead then continue
      out := out.push it
      match i.op, i.args with
      | .ret, [] | .jp, [_] | .jr, [_] => dead := true
      | _, _ => pure ()
    -- data and names are never dropped, and what follows data is
    -- reached some other way (the interrupt vector after the padding)
    | .db _ | .dw _ | .ds _ => dead := false; out := out.push it
    | _ => out := out.push it
  if out.size < items.length then sweep out.toList else out.toList

/-- A byte zero-extended into `HL` and then moved up: straight into `H`. -/
partial def packHigh : List Item → List Item
  | .ins { op := .ld, args := [.l, .a] } :: .ins { op := .ld, args := [.h, .imm (.num 0)] } ::
    .ins { op := .ld, args := [.h, .l] } :: .ins { op := .ld, args := [.l, .imm (.num 0)] } :: rest =>
    .ins { op := .ld, args := [.h, .a] } :: .ins { op := .ld, args := [.l, .imm (.num 0)] } :: packHigh rest
  | i :: rest => i :: packHigh rest
  | [] => []

/-- A jump whose target is a `ret` returns itself. -/
def retThreading (items : List Item) : List Item := Id.run do
  let arr := items.toArray
  let mut atRet : List String := []
  for k in [0:arr.size] do
    if let .label l := arr[k]! then
      -- past further labels at the same place
      let mut j := k + 1
      while (match arr[j]? with | some (.label _) => true | _ => false) do j := j + 1
      if arr[j]? == some (.ins { op := .ret, args := [] }) then atRet := l :: atRet
  return items.map fun it => match it with
    | .ins { op := .jp, args := [.imm (.sym l 0)] } =>
      if atRet.contains l then .ins { op := .ret, args := [] } else it
    | .ins { op := .jp, args := [cc, .imm (.sym l 0)] } =>
      if atRet.contains l && (invert cc).isSome then .ins { op := .ret, args := [cc] } else it
    | it => it

/-- The bytes of a function's frame (by their offsets) that the frame of
another function shares: the frames are overlaid along the call graph,
and which bytes two of them share does not depend on where the RAM starts. -/
def sharedBytes (p : IR.Prog) : String → Nat → Bool :=
  let frameSize (f : String) : Nat := ((p.fn? f).map (·.frame)).getD 0
  let l := IR.layout p frameSize 0
  fun f k =>
    match l.frames.lookup f with
    | none => true
    | some a => l.frames.any fun (g, b) => g != f && decide (b ≤ a + k) && decide (a + k < b + frameSize g)

structure Image where
  bytes : ByteArray
  origin : Nat := 0
  labels : List (String × Nat)
  items : List Item
  layout : Layout
  /-- Bytes of code and constants; bytes of RAM. -/
  codeSize : Nat
  ramSize : Nat

def litItems (lits : Array (Nat × Nat)) : List Item :=
  lits.toList.flatMap fun (n, v) =>
    [.label s!"lit{bits n}_{v}", .db (bytesLE v n |>.map fun b => .num (Int.ofNat b.toNat))]

/-- Program + runtime pieces + data, RAM from `ramStart`.  `platform` is
the start-up code and the effects (`Runtime.harness`, or a board's);
`head` comes first in the image (reset and interrupt vectors). -/
def build (p : IR.Prog) (platform : List Runtime.Piece) (head : List Item := [.ins { op := .jp, args := [.imm (.sym "rt_start")] }])
    (ramStart : Nat := 0x8000) (ramEnd : Nat := 0xFF00) (shorten := true) (reserved : Nat := 0)
    (annotate := false) (passes := true) : Except String Image := do
  let c ← genProg p annotate (sharedBytes p)
  let entry : List Item := []
  -- constants stay in ROM
  let roData : List Item := p.globals.filter (·.const) |>.flatMap fun g =>
    let bytes := (g.init.getD (ByteArray.mk (Array.replicate g.size 0))).toList
    [.label (areaSym (.global g.name)), .db (bytes.map fun b => .num (Int.ofNat b.toNat))]
  let initData : List Item := p.globals.filter (fun g => !g.const && g.init.isSome) |>.flatMap fun g =>
    [.label s!"init_{sanitize g.name}", .db ((g.init.getD .empty).toList.map fun b => .num (Int.ofNat b.toNat))]
  let user := head ++ entry ++ c.items
  -- start-up: clear the RAM in use, copy the initial values (`rt_init`
  -- is completed below, once the size of the RAM is known)
  let initCopy : List Item := p.globals.filter (fun g => !g.const && g.init.isSome) |>.flatMap fun g =>
    [.ins { op := .ld, args := [.hl, .imm (.sym s!"init_{sanitize g.name}")] },
     .ins { op := .ld, args := [.de, .imm (.sym (areaSym (.global g.name)))] },
     .ins { op := .ld, args := [.bc, n16 g.size] },
     .ins { op := .ldir }]
  let initCode : List Item :=
    [.label "rt_init",
     .ins { op := .ld, args := [.hl, .imm (.sym "rt_ram")] },
     .ins { op := .ld, args := [.bc, .imm (.sym "rt_ram_size")] },
     .ins { op := .call, args := [.imm (.sym "rt_zero")] }] ++ initCopy ++ [.ins { op := .ret }]
  let (rt, cells) ← Runtime.select (platform ++ Runtime.pieces) (user ++ initCode)
  -- RAM: the runtime's cells, then globals and frames
  -- (`reserved` bytes at the start of the RAM are the platform's own)
  let mut at_ := ramStart + reserved
  let mut equs : List Item := []
  for (n, sz) in cells do
    equs := equs ++ [.equ n at_]
    at_ := at_ + sz
  let frameSize (f : String) : Nat := ((p.fn? f).map (·.frame)).getD 0
  let vars := IR.layout p frameSize at_ (fun g => !g.const)
  validate p vars frameSize at_ ramEnd
  -- the slots of the temporaries: above every variable, overlaid along the call graph like the frames
  let tmpSize (f : String) : Nat := (c.tmps.lookup f).getD 0
  let noGlobals : IR.Prog := { p with globals := [] }
  let tmps := IR.layout noGlobals tmpSize vars.top
  validate noGlobals tmps tmpSize vars.top ramEnd
  let layout : Layout :=
    { globals := vars.globals, frames := vars.frames ++ tmps.frames.map fun (f, a) => (f ++ ".t", a),
      top := tmps.top }
  for (g, a) in layout.globals do equs := equs ++ [.equ (areaSym (.global g)) a]
  for (f, a) in layout.frames do equs := equs ++ [.equ (areaSym (.frame f)) a]
  equs := equs ++ [.equ "rt_ram" ramStart, .equ "rt_ram_size" (Nat.max 1 (layout.top - ramStart))]
  let all := equs ++ user ++ initCode ++ rt ++ litItems c.lits ++ roData ++ initData
  -- only the generated code and the runtime: data follows and stays
  -- `passes := false`: the items as generated and as the runtime has them, for the proofs
  let all := if passes then packHigh (peephole (sweep (retThreading all))) else all
  let all ← if shorten && passes then Asm.relax all else pure all
  let a ← Asm.assemble all
  if a.bytes.size > ramStart then throw s!"the image is {a.bytes.size} bytes: it does not fit below {ramStart}"
  -- the constants are where the assembler put them, in ROM: with them the layout has every global,
  -- as the IR's semantics takes it to
  let consts := (p.globals.filter (·.const)).filterMap fun g =>
    (a.labels.lookup (areaSym (.global g.name))).map fun ad => (g.name, ad)
  return { bytes := a.bytes, labels := a.labels, items := all,
           layout := { layout with globals := layout.globals ++ consts },
           codeSize := a.bytes.size, ramSize := layout.top - ramStart }

end Ember.Z80.Codegen
