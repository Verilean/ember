/-!
# Ember.Z80.Asm — a Z80 assembler (plan M6.2)

Instructions as data (`Instr`: a mnemonic and its operands), their
encoding, and a two-pass assembler over items with labels.  `encode`
accepts exactly the operand combinations the Z80 has and rejects the
rest with a message, so the own back end (M6.5) cannot emit an
instruction that does not exist.

Checked against `z88dk-z80asm`: every form `encode` accepts, with
several immediates and displacements, assembles to the same bytes
(`ember-z80 asm-check`).
-/

namespace Ember.Z80.Asm

/-- A number or a label (plus an offset), resolved by the assembler. -/
inductive Val where
  | num (n : Int)
  | sym (s : String) (off : Int := 0)
  deriving Inhabited, BEq, Repr

instance : OfNat Val n := ⟨.num n⟩

/-- An operand.  `c` is also the carry condition. -/
inductive Arg where
  | b | c | d | e | h | l | a
  | ixh | ixl | iyh | iyl
  | bc | de | hl | sp | af | af' | ix | iy
  | i | r
  /-- `(bc)`, `(de)`, `(hl)`, `(sp)`, `(ix)`, `(iy)`, `(c)`. -/
  | mbc | mde | mhl | msp | mix0 | miy0 | mc
  /-- `(ix+d)`, `(iy+d)`. -/
  | mix (d : Int) | miy (d : Int)
  /-- `(nn)`. -/
  | mem (v : Val)
  | imm (v : Val)
  | nz | z | nc | po | pe | p | m
  deriving Inhabited, BEq, Repr

inductive Op where
  | nop | halt | di | ei | exx | daa | cpl | neg | ccf | scf
  | rlca | rla | rrca | rra | rld | rrd
  | ldi | ldir | ldd | lddr | cpi | cpir | cpd | cpdr
  | ini | inir | ind | indr | outi | otir | outd | otdr
  | reti | retn
  | ld | push | pop | ex
  | add | adc | sub | sbc | and | xor | or | cp
  | inc | dec
  | rlc | rrc | rl | rr | sla | sra | sll | srl
  | bit | res | set
  | jp | jr | djnz | call | ret | rst
  | in | out | im
  deriving Inhabited, BEq, Repr, DecidableEq

structure Instr where
  op : Op
  args : List Arg := []
  deriving Inhabited, BEq, Repr

/-! ## Text (z88dk-z80asm's syntax) -/

def Val.text : Val → String
  | .num n => toString n
  | .sym s 0 => s
  | .sym s off => if off < 0 then s!"{s}-{-off}" else s!"{s}+{off}"

def disp (d : Int) : String := if d < 0 then s!"-{-d}" else s!"+{d}"

def Arg.text : Arg → String
  | .b => "b" | .c => "c" | .d => "d" | .e => "e" | .h => "h" | .l => "l" | .a => "a"
  | .ixh => "ixh" | .ixl => "ixl" | .iyh => "iyh" | .iyl => "iyl"
  | .bc => "bc" | .de => "de" | .hl => "hl" | .sp => "sp" | .af => "af" | .af' => "af'"
  | .ix => "ix" | .iy => "iy" | .i => "i" | .r => "r"
  | .mbc => "(bc)" | .mde => "(de)" | .mhl => "(hl)" | .msp => "(sp)"
  | .mix0 => "(ix)" | .miy0 => "(iy)" | .mc => "(c)"
  | .mix k => s!"(ix{disp k})" | .miy k => s!"(iy{disp k})"
  | .mem v => s!"({v.text})"
  | .imm v => v.text
  | .nz => "nz" | .z => "z" | .nc => "nc" | .po => "po" | .pe => "pe" | .p => "p" | .m => "m"

def Op.text (o : Op) : String :=
  let s := toString (repr o)
  (s.splitOn ".").getLast!

def Instr.text (i : Instr) : String :=
  if i.args.isEmpty then i.op.text else s!"{i.op.text} " ++ ",".intercalate (i.args.map Arg.text)

/-! ## Encoding -/

/-- Where labels are, and whether values are checked for range (the first
pass only needs sizes). -/
structure Env where
  resolve : String → Option Int := fun _ => none
  /-- Address of the instruction. -/
  pc : Int := 0
  /-- First pass: unknown labels are 0 and nothing is range-checked. -/
  sizing : Bool := false

abbrev Enc := ReaderT Env (Except String)

def bad (m : String) : Enc α := throw m

def value (v : Val) : Enc Int := do
  match v with
  | .num n => return n
  | .sym s off =>
    match (← read).resolve s with
    | some a => return a + off
    | none => if (← read).sizing then return 0 else bad s!"undefined label {s}"

def byteOf (n : Int) : UInt8 := UInt8.ofNat (n % 256).toNat

/-- An 8-bit immediate: −128 … 255. -/
def imm8 (v : Val) : Enc (List UInt8) := do
  let n ← value v
  if !(← read).sizing && (n < -128 || n > 255) then bad s!"{n} does not fit 8 bits"
  return [byteOf n]

/-- A 16-bit immediate or address, low byte first: −32768 … 65535. -/
def imm16 (v : Val) : Enc (List UInt8) := do
  let n ← value v
  if !(← read).sizing && (n < -32768 || n > 65535) then bad s!"{n} does not fit 16 bits"
  return [byteOf n, byteOf (n / 256)]

def disp8 (d : Int) : Enc UInt8 := do
  if d < -128 || d > 127 then bad s!"displacement {d} out of range"
  return byteOf d

/-- The target of a relative jump as its displacement byte. -/
def rel (v : Val) : Enc (List UInt8) := do
  let d := (← value v) - ((← read).pc + 2)
  if !(← read).sizing && (d < -128 || d > 127) then bad s!"relative jump of {d} out of range"
  return [byteOf d]

/-- An 8-bit operand place: prefix, register code (6 = memory), displacement. -/
structure Loc8 where
  pre : Option UInt8 := none
  code : Nat
  disp : Option UInt8 := none

def loc8? (x : Arg) : Enc (Option Loc8) := do
  match x with
  | .b => return some { code := 0 } | .c => return some { code := 1 }
  | .d => return some { code := 2 } | .e => return some { code := 3 }
  | .h => return some { code := 4 } | .l => return some { code := 5 }
  | .mhl => return some { code := 6 } | .a => return some { code := 7 }
  | .ixh => return some { pre := some 0xDD, code := 4 } | .ixl => return some { pre := some 0xDD, code := 5 }
  | .iyh => return some { pre := some 0xFD, code := 4 } | .iyl => return some { pre := some 0xFD, code := 5 }
  | .mix k => return some { pre := some 0xDD, code := 6, disp := some (← disp8 k) }
  | .miy k => return some { pre := some 0xFD, code := 6, disp := some (← disp8 k) }
  | .mix0 => return some { pre := some 0xDD, code := 6, disp := some 0 }
  | .miy0 => return some { pre := some 0xFD, code := 6, disp := some 0 }
  | _ => return none

def Loc8.isMem (x : Loc8) : Bool := x.code == 6
/-- `h`, `l` or `(hl)` without a prefix: what a prefix would change. -/
def Loc8.plainHL (x : Loc8) : Bool := x.pre.isNone && x.code ≥ 4 && x.code ≤ 6
/-- `ixh`, `ixl`, `iyh`, `iyl`. -/
def Loc8.half (x : Loc8) : Bool := x.pre.isSome && x.code != 6

def u8 (n : Nat) : UInt8 := UInt8.ofNat n

def Loc8.wrap (x : Loc8) (opcode : Nat) (tail : List UInt8 := []) : List UInt8 :=
  x.pre.toList ++ [u8 opcode] ++ x.disp.toList ++ tail

/-- `bc de hl sp` as 0–3; `ix`/`iy` in the place of `hl`, with a prefix. -/
def pair? (x : Arg) : Option (Option UInt8 × Nat) :=
  match x with
  | .bc => some (none, 0) | .de => some (none, 1) | .hl => some (none, 2) | .sp => some (none, 3)
  | .ix => some (some 0xDD, 2) | .iy => some (some 0xFD, 2)
  | _ => none

def cond? (x : Arg) : Option Nat :=
  match x with
  | .nz => some 0 | .z => some 1 | .nc => some 2 | .c => some 3
  | .po => some 4 | .pe => some 5 | .p => some 6 | .m => some 7
  | _ => none

def aluCode? : Op → Option Nat
  | .add => some 0 | .adc => some 1 | .sub => some 2 | .sbc => some 3
  | .and => some 4 | .xor => some 5 | .or => some 6 | .cp => some 7
  | _ => none

def rotCode? : Op → Option Nat
  | .rlc => some 0 | .rrc => some 1 | .rl => some 2 | .rr => some 3
  | .sla => some 4 | .sra => some 5 | .sll => some 6 | .srl => some 7
  | _ => none

def simple? : Op → Option (List UInt8)
  | .nop => some [0x00] | .halt => some [0x76] | .di => some [0xF3] | .ei => some [0xFB]
  | .exx => some [0xD9] | .daa => some [0x27] | .cpl => some [0x2F] | .ccf => some [0x3F] | .scf => some [0x37]
  | .rlca => some [0x07] | .rla => some [0x17] | .rrca => some [0x0F] | .rra => some [0x1F]
  | .neg => some [0xED, 0x44] | .retn => some [0xED, 0x45] | .reti => some [0xED, 0x4D]
  | .rrd => some [0xED, 0x67] | .rld => some [0xED, 0x6F]
  | .ldi => some [0xED, 0xA0] | .cpi => some [0xED, 0xA1] | .ini => some [0xED, 0xA2] | .outi => some [0xED, 0xA3]
  | .ldd => some [0xED, 0xA8] | .cpd => some [0xED, 0xA9] | .ind => some [0xED, 0xAA] | .outd => some [0xED, 0xAB]
  | .ldir => some [0xED, 0xB0] | .cpir => some [0xED, 0xB1] | .inir => some [0xED, 0xB2] | .otir => some [0xED, 0xB3]
  | .lddr => some [0xED, 0xB8] | .cpdr => some [0xED, 0xB9] | .indr => some [0xED, 0xBA] | .otdr => some [0xED, 0xBB]
  | _ => none

/-- An ALU operation on `A` with an 8-bit operand or an immediate. -/
def alu8 (k : Nat) (x : Arg) : Enc (List UInt8) := do
  match x with
  | .imm v => return [u8 (0xC6 + 8 * k)] ++ (← imm8 v)
  | _ =>
    let some s ← loc8? x | bad "operand"
    return s.wrap (0x80 + 8 * k + s.code)

def encodeLd (dst src : Arg) : Enc (List UInt8) := do
  match dst, src with
  | .a, .mbc => return [0x0A] | .a, .mde => return [0x1A]
  | .mbc, .a => return [0x02] | .mde, .a => return [0x12]
  | .a, .mem v => return [0x3A] ++ (← imm16 v)
  | .mem v, .a => return [0x32] ++ (← imm16 v)
  | .a, .i => return [0xED, 0x57] | .a, .r => return [0xED, 0x5F]
  | .i, .a => return [0xED, 0x47] | .r, .a => return [0xED, 0x4F]
  | .sp, .hl => return [0xF9] | .sp, .ix => return [0xDD, 0xF9] | .sp, .iy => return [0xFD, 0xF9]
  | _, _ => pure ()
  -- 16-bit
  if let some (pre, rr) := pair? dst then
    match src with
    | .imm v => return pre.toList ++ [u8 (0x01 + 16 * rr)] ++ (← imm16 v)
    | .mem v =>
      if rr == 2 then return pre.toList ++ [0x2A] ++ (← imm16 v)
      return [0xED, u8 (0x4B + 16 * rr)] ++ (← imm16 v)
    | _ => bad "ld: source of a 16-bit load"
  if let some (pre, rr) := pair? src then
    match dst with
    | .mem v =>
      if rr == 2 then return pre.toList ++ [0x22] ++ (← imm16 v)
      return [0xED, u8 (0x43 + 16 * rr)] ++ (← imm16 v)
    | _ => bad "ld: destination of a 16-bit load"
  -- 8-bit
  let some d ← loc8? dst | bad "ld: destination"
  match src with
  | .imm v => return d.wrap (0x06 + 8 * d.code) (← imm8 v)
  | _ =>
    let some s ← loc8? src | bad "ld: source"
    if d.isMem && s.isMem then bad "ld: memory to memory"
    -- one prefix serves the whole instruction: with `(ix+d)` the other
    -- operand is a plain register (and `h`, `l` stay `h`, `l`); with
    -- `ixh`/`ixl` the other may not be `h`, `l`, `(hl)` or of the other
    -- index register
    let pre ← match d.pre, s.pre with
      | none, none => pure none
      | some p, none =>
        if d.isMem then pure (some p)
        else if s.plainHL then bad "ld: index half with h, l or (hl)" else pure (some p)
      | none, some p =>
        if s.isMem then pure (some p)
        else if d.plainHL then bad "ld: index half with h, l or (hl)" else pure (some p)
      | some p, some q =>
        if d.isMem || s.isMem then bad "ld: index half with indexed memory"
        else if p != q then bad "ld: ix with iy" else pure (some p)
    return pre.toList ++ [u8 (0x40 + 8 * d.code + s.code)] ++ d.disp.toList ++ s.disp.toList

def encode' (i : Instr) : Enc (List UInt8) := do
  if let some bs := simple? i.op then
    if i.args.isEmpty then return bs else bad "no operands expected"
  match i.op, i.args with
  | .ld, [dst, src] => encodeLd dst src
  | .push, [x] | .pop, [x] =>
    let base := if i.op == .push then 0xC5 else 0xC1
    match x with
    | .bc => return [u8 base] | .de => return [u8 (base + 0x10)]
    | .hl => return [u8 (base + 0x20)] | .af => return [u8 (base + 0x30)]
    | .ix => return [0xDD, u8 (base + 0x20)] | .iy => return [0xFD, u8 (base + 0x20)]
    | _ => bad "push/pop: operand"
  | .ex, [.de, .hl] => return [0xEB]
  | .ex, [.af, .af'] => return [0x08]
  | .ex, [.msp, .hl] => return [0xE3]
  | .ex, [.msp, .ix] => return [0xDD, 0xE3]
  | .ex, [.msp, .iy] => return [0xFD, 0xE3]
  -- 16-bit arithmetic
  | .add, [.hl, x] | .add, [.ix, x] | .add, [.iy, x] =>
    let some (pre, _) := pair? i.args.head! | bad "add"
    let some (pre', rr) := pair? x | bad "add: 16-bit operand"
    -- the operand in the `hl` place is the destination itself
    if rr == 2 && pre' != pre then bad "add: hl with an index register"
    return pre.toList ++ [u8 (0x09 + 16 * rr)]
  | .adc, [.hl, x] | .sbc, [.hl, x] =>
    let some (none, rr) := pair? x | bad "adc/sbc: 16-bit operand"
    return [0xED, u8 ((if i.op == .adc then 0x4A else 0x42) + 16 * rr)]
  -- 8-bit arithmetic: `add a,x`, `adc a,x`, `sbc a,x`; `sub x`, `and x`, …
  | .add, [.a, x] => alu8 0 x
  | .adc, [.a, x] => alu8 1 x
  | .sbc, [.a, x] => alu8 3 x
  | .sub, [x] | .and, [x] | .xor, [x] | .or, [x] | .cp, [x] =>
    let some k := aluCode? i.op | bad "alu"
    alu8 k x
  | .inc, [x] | .dec, [x] =>
    let dec := i.op == .dec
    if let some (pre, rr) := pair? x then
      return pre.toList ++ [u8 ((if dec then 0x0B else 0x03) + 16 * rr)]
    let some d ← loc8? x | bad "inc/dec: operand"
    return d.wrap ((if dec then 0x05 else 0x04) + 8 * d.code)
  | .rlc, [x] | .rrc, [x] | .rl, [x] | .rr, [x] | .sla, [x] | .sra, [x] | .sll, [x] | .srl, [x] =>
    let some k := rotCode? i.op | bad "rotate"
    let some d ← loc8? x | bad "rotate: operand"
    if d.half then bad "rotate: index half"
    return d.pre.toList ++ [0xCB] ++ d.disp.toList ++ [u8 (8 * k + d.code)]
  | .bit, [.imm (.num n), x] | .res, [.imm (.num n), x] | .set, [.imm (.num n), x] =>
    if n < 0 || n > 7 then bad "bit number"
    let some d ← loc8? x | bad "bit: operand"
    if d.half then bad "bit: index half"
    let base := match i.op with | .bit => 0x40 | .res => 0x80 | _ => 0xC0
    return d.pre.toList ++ [0xCB] ++ d.disp.toList ++ [u8 (base + 8 * n.toNat + d.code)]
  | .jp, [.mhl] => return [0xE9]
  | .jp, [.mix0] => return [0xDD, 0xE9]
  | .jp, [.miy0] => return [0xFD, 0xE9]
  | .jp, [.imm v] => return [0xC3] ++ (← imm16 v)
  | .jp, [cc, .imm v] =>
    let some k := cond? cc | bad "jp: condition"
    return [u8 (0xC2 + 8 * k)] ++ (← imm16 v)
  | .jr, [.imm v] => return [0x18] ++ (← rel v)
  | .jr, [cc, .imm v] =>
    let some k := cond? cc | bad "jr: condition"
    if k > 3 then bad "jr: only nz, z, nc, c"
    return [u8 (0x20 + 8 * k)] ++ (← rel v)
  | .djnz, [.imm v] => return [0x10] ++ (← rel v)
  | .call, [.imm v] => return [0xCD] ++ (← imm16 v)
  | .call, [cc, .imm v] =>
    let some k := cond? cc | bad "call: condition"
    return [u8 (0xC4 + 8 * k)] ++ (← imm16 v)
  | .ret, [] => return [0xC9]
  | .ret, [cc] =>
    let some k := cond? cc | bad "ret: condition"
    return [u8 (0xC0 + 8 * k)]
  | .rst, [.imm (.num n)] =>
    if n < 0 || n > 56 || n % 8 != 0 then bad "rst: address"
    return [u8 (0xC7 + n.toNat)]
  | .in, [.a, .mem v] => return [0xDB] ++ (← imm8 v)
  | .in, [x, .mc] =>
    let some d ← loc8? x | bad "in: register"
    if d.pre.isSome || d.isMem then bad "in: register"
    return [0xED, u8 (0x40 + 8 * d.code)]
  | .out, [.mem v, .a] => return [0xD3] ++ (← imm8 v)
  | .out, [.mc, x] =>
    let some d ← loc8? x | bad "out: register"
    if d.pre.isSome || d.isMem then bad "out: register"
    return [0xED, u8 (0x41 + 8 * d.code)]
  | .im, [.imm (.num 0)] => return [0xED, 0x46]
  | .im, [.imm (.num 1)] => return [0xED, 0x56]
  | .im, [.imm (.num 2)] => return [0xED, 0x5E]
  | _, _ => bad "no such instruction"

/-- The bytes of one instruction at `pc`. -/
def encode (i : Instr) (env : Env := {}) : Except String (List UInt8) :=
  match (encode' i).run env with
  | .ok bs => .ok bs
  | .error e => .error s!"{i.text}: {e}"

/-! ## Programs -/

inductive Item where
  | ins (i : Instr)
  | label (name : String)
  | db (vs : List Val)
  | dw (vs : List Val)
  /-- `n` bytes of zero. -/
  | ds (n : Nat)
  /-- A name for a number (an address in RAM). -/
  | equ (name : String) (value : Nat)
  /-- For listings only. -/
  | comment (text : String)
  deriving Inhabited, BEq, Repr

def Item.text : Item → String
  | .ins i => "  " ++ i.text
  | .label n => n ++ ":"
  | .db vs => "  defb " ++ ",".intercalate (vs.map Val.text)
  | .dw vs => "  defw " ++ ",".intercalate (vs.map Val.text)
  | .ds n => s!"  defs {n}"
  | .equ n v => s!"  defc {n} = {v}"
  | .comment t => s!"; {t}"

def Item.encode (it : Item) (env : Env) : Except String (List UInt8) :=
  match it with
  | .ins i => Asm.encode i env
  | .label _ | .equ .. | .comment _ => .ok []
  | .db vs => (vs.mapM imm8).run env |>.map List.flatten
  | .dw vs => (vs.mapM imm16).run env |>.map List.flatten
  | .ds n => .ok (List.replicate n 0)

structure Assembled where
  origin : Nat
  bytes : ByteArray
  labels : List (String × Nat)
  /-- Address of every item, for listings. -/
  addrs : Array Nat

/-- The first pass: the address of every item, then the address after
the last; the labels, the latest first. -/
def place : List Item → Nat → List (String × Nat) → Except String (List Nat × List (String × Nat))
  | [], pc, labels => .ok ([pc], labels)
  | it :: r, pc, labels =>
    match it with
    | .label n =>
      if labels.any (·.1 == n) then .error s!"label {n} defined twice"
      else (place r pc ((n, pc) :: labels)).map fun x => (pc :: x.1, x.2)
    | .equ n v =>
      if labels.any (·.1 == n) then .error s!"label {n} defined twice"
      else (place r pc ((n, v) :: labels)).map fun x => (pc :: x.1, x.2)
    | _ =>
      match it.encode { sizing := true, pc := Int.ofNat pc } with
      | .ok bs => (place r (pc + bs.length) labels).map fun x => (pc :: x.1, x.2)
      | .error e => .error e

/-- The second pass: every item at its address.  That an item has the
size the first pass gave it is checked, not assumed. -/
def emit (resolve : String → Option Int) : List Item → List Nat → Except String (List UInt8)
  | [], _ => .ok []
  | it :: r, a :: a' :: as =>
    match it.encode { resolve, pc := Int.ofNat a } with
    | .ok bs =>
      if a' != a + bs.length then .error s!"{it.text}: its size changed between the passes"
      else (emit resolve r (a' :: as)).map (bs ++ ·)
    | .error e => .error e
  | _ :: _, _ => .error "assemble: an item without an address"

/-- Two passes: sizes do not depend on label values. -/
def assemble (items : List Item) (origin : Nat := 0) : Except String Assembled :=
  match place items origin [] with
  | .error e => .error e
  | .ok (addrs, labels) =>
    if addrs.getLast?.getD origin > 0x10000 then .error s!"program ends at {addrs.getLast?.getD origin}"
    else
      match emit (fun s => (labels.lookup s).map Int.ofNat) items addrs with
      | .ok bytes =>
        .ok { origin, bytes := ByteArray.mk bytes.toArray, labels := labels.reverse, addrs := addrs.dropLast.toArray }
      | .error e => .error e

/-- The environment an item at `pc` was encoded in. -/
def Assembled.env (a : Assembled) (pc : Nat) : Env :=
  { resolve := fun s => (a.labels.reverse.lookup s).map Int.ofNat, pc := Int.ofNat pc }

def source (items : List Item) (origin : Nat := 0) : String :=
  s!"  org {origin}\n" ++ "\n".intercalate (items.map Item.text) ++ "\n"

/-! ## Shorter jumps -/

/-- Turn `jp` into `jr` where the target is near (`jr` has no `po pe p m`).
Repeated until nothing changes: a shorter jump only brings targets closer. -/
partial def relax (items : List Item) (origin : Nat := 0) : Except String (List Item) := do
  let a ← assemble items origin
  let resolve (s : String) : Option Int := (a.labels.lookup s).map Int.ofNat
  let mut out := #[]
  let mut changed := false
  let mut k := 0
  for it in items do
    let pc := Int.ofNat a.addrs[k]!
    k := k + 1
    let near (v : Val) : Bool :=
      match v with
      | .sym s off =>
        match resolve s with
        -- measured from the `jp`: the `jr` in its place ends one byte earlier
        | some t => let d := t + off - (pc + 2); d ≥ -128 && d ≤ 127
        | none => false
      | .num _ => false
    match it with
    | .ins { op := .jp, args := [.imm v] } =>
      if near v then out := out.push (.ins { op := .jr, args := [.imm v] }); changed := true
      else out := out.push it
    | .ins { op := .jp, args := [cc, .imm v] } =>
      if near v && (cc == .nz || cc == .z || cc == .nc || cc == .c) then
        out := out.push (.ins { op := .jr, args := [cc, .imm v] }); changed := true
      else out := out.push it
    | _ => out := out.push it
  if changed then relax out.toList origin else return items

/-! ## Reading the text back

The syntax `Item.text` prints, with comments (`;`) and hexadecimal
numbers (`0x…`): the runtime routines are written in it. -/

def opNames : List (String × Op) :=
  [.nop, .halt, .di, .ei, .exx, .daa, .cpl, .neg, .ccf, .scf, .rlca, .rla, .rrca, .rra, .rld, .rrd,
   .ldi, .ldir, .ldd, .lddr, .cpi, .cpir, .cpd, .cpdr, .ini, .inir, .ind, .indr, .outi, .otir, .outd, .otdr,
   .reti, .retn, .ld, .push, .pop, .ex, .add, .adc, .sub, .sbc, .and, .xor, .or, .cp, .inc, .dec,
   .rlc, .rrc, .rl, .rr, .sla, .sra, .sll, .srl, .bit, .res, .set, .jp, .jr, .djnz, .call, .ret, .rst,
   .in, .out, .im].map fun o => (o.text, o)

def argNames : List (String × Arg) :=
  [Arg.b, .c, .d, .e, .h, .l, .a, .ixh, .ixl, .iyh, .iyl, .bc, .de, .hl, .sp, .af, .af', .ix, .iy, .i, .r,
   .mbc, .mde, .mhl, .msp, .mix0, .miy0, .mc, .nz, .z, .nc, .po, .pe, .p, .m].map fun x => (x.text, x)

def parseNat (s : String) : Option Nat :=
  if s.startsWith "0x" then
    (s.drop 2).foldl (fun acc ch => acc.bind fun v =>
      if ch.isDigit then some (v * 16 + (ch.toNat - 48))
      else if 'a' ≤ ch && ch ≤ 'f' then some (v * 16 + (ch.toNat - 87))
      else if 'A' ≤ ch && ch ≤ 'F' then some (v * 16 + (ch.toNat - 55))
      else none) (if s.length > 2 then some 0 else none)
  else s.toNat?

/-- `123`, `0x7B`, `-5`, `name`, `name+3`, `name-3`. -/
def parseVal (s : String) : Except String Val := do
  let s := s.trimAscii.toString
  if s.isEmpty then throw "empty operand"
  if let some n := parseNat s then return .num n
  if s.startsWith "-" then
    if let some n := parseNat (s.drop 1).toString then return .num (-(Int.ofNat n))
  let cut (sep : Char) : Option (String × String) :=
    match s.splitOn (String.singleton sep) with
    | [a, b] => if a.isEmpty then none else some (a.trimAscii.toString, b.trimAscii.toString)
    | _ => none
  if let some (a, b) := cut '+' then
    if let some n := parseNat b then return .sym a n
    throw s!"bad offset in {s}"
  if let some (a, b) := cut '-' then
    if let some n := parseNat b then return .sym a (-(Int.ofNat n))
    throw s!"bad offset in {s}"
  return .sym s

def parseArg (s : String) : Except String Arg := do
  let s := s.trimAscii.toString
  if let some x := argNames.lookup s then return x
  if s.startsWith "(" && s.endsWith ")" then
    let inner := ((s.drop 1).dropEnd 1).trimAscii.toString
    for (name, mk) in [("ix", Arg.mix), ("iy", Arg.miy)] do
      if inner.startsWith name then
        let rest := (inner.drop 2).trimAscii.toString
        if rest.startsWith "+" then
          if let some n := parseNat (rest.drop 1).trimAscii.toString then return mk n
        if rest.startsWith "-" then
          if let some n := parseNat (rest.drop 1).trimAscii.toString then return mk (-(Int.ofNat n))
    return .mem (← parseVal inner)
  return .imm (← parseVal s)

partial def parseLine (line : String) : Except String (List Item) := do
  let line := ((line.splitOn ";").head!).trimAscii.toString
  if line.isEmpty then return []
  -- `name:` in front
  if let [l, rest] := line.splitOn ":" then
    if !l.isEmpty && l.all (fun ch => ch.isAlphanum || ch == '_') then
      return .label l :: (← parseLine rest)
  let (word, rest) := match line.splitOn " " with
    | w :: r => (w, (" ".intercalate r).trimAscii.toString)
    | [] => (line, "")
  let operands := if rest.isEmpty then [] else rest.splitOn ","
  match word with
  | "defb" => return [.db (← operands.mapM parseVal)]
  | "defw" => return [.dw (← operands.mapM parseVal)]
  | "defs" =>
    match parseNat rest with
    | some n => return [.ds n]
    | none => throw s!"defs: {rest}"
  | "defc" =>
    match rest.splitOn "=" with
    | [n, v] =>
      match parseNat v.trimAscii.toString with
      | some x => return [.equ n.trimAscii.toString x]
      | none => throw s!"defc: {rest}"
    | _ => throw s!"defc: {rest}"
  | "org" => return []
  | _ =>
    let some op := opNames.lookup word | throw s!"unknown mnemonic {word}"
    return [.ins { op, args := ← operands.mapM parseArg }]

def parse (src : String) : Except String (List Item) := do
  let mut out := #[]
  let mut n := 1
  for line in src.splitOn "\n" do
    match parseLine line with
    | .ok items => out := out ++ items.toArray
    | .error e => throw s!"line {n}: {e}: {line}"
    n := n + 1
  return out.toList

/-! ## Every form, for the comparison with another assembler -/

def allOps : List Op :=
  [.nop, .halt, .di, .ei, .exx, .daa, .cpl, .neg, .ccf, .scf, .rlca, .rla, .rrca, .rra, .rld, .rrd,
   .ldi, .ldir, .ldd, .lddr, .cpi, .cpir, .cpd, .cpdr, .ini, .inir, .ind, .indr, .outi, .otir, .outd, .otdr,
   .reti, .retn, .ld, .push, .pop, .ex, .add, .adc, .sub, .sbc, .and, .xor, .or, .cp, .inc, .dec,
   .rlc, .rrc, .rl, .rr, .sla, .sra, .sll, .srl, .bit, .res, .set, .jp, .call, .ret, .rst, .in, .out, .im]

def argPool : List Arg :=
  [.b, .c, .d, .e, .h, .l, .a, .ixh, .ixl, .iyh, .iyl, .bc, .de, .hl, .sp, .af, .af', .ix, .iy, .i, .r,
   .mbc, .mde, .mhl, .msp, .mix0, .miy0, .mc,
   .mix 0, .mix 5, .mix (-3), .mix 127, .mix (-128), .miy 1, .miy (-1), .miy 100,
   .mem 0, .mem 0x12, .mem 0x1234, .mem 0xFFFF,
   .imm 0, .imm 1, .imm 2, .imm 7, .imm 8, .imm 0x12, .imm 56, .imm 0xFF, .imm 0x1234, .imm 0xFFFF,
   .imm (.num (-1)), .imm (.num (-128)),
   .nz, .z, .nc, .po, .pe, .p, .m]

/-- Every instruction `encode` accepts over the operand pool, and relative
jumps to labels on both sides. -/
def allForms : List Item := Id.run do
  let mut out : Array Item := #[]
  let mut k := 0
  for op in allOps do
    let cands : List (List Arg) :=
      [[]] ++ argPool.map (fun x => [x]) ++ argPool.flatMap fun x => argPool.map fun y => [x, y]
    for args in cands do
      let i : Instr := { op, args }
      if (encode i).isOk then out := out.push (.ins i)
    -- a short jump backwards over each group
    out := out ++ #[.label s!"g{k}", .ins { op := .nop },
      .ins { op := .jr, args := [.imm (.sym s!"g{k}")] }]
    k := k + 1
  let jumps : List Instr :=
    [{ op := .jr, args := [.imm (.sym "fwd")] }, { op := .jr, args := [.nz, .imm (.sym "fwd")] },
     { op := .jr, args := [.z, .imm (.sym "near")] }, { op := .jr, args := [.nc, .imm (.sym "near")] },
     { op := .jr, args := [.c, .imm (.sym "near")] }, { op := .djnz, args := [.imm (.sym "near")] },
     { op := .jp, args := [.imm (.sym "fwd" 3)] }, { op := .call, args := [.pe, .imm (.sym "near" (-2))] }]
  out := out.push (.label "near")
  for j in jumps do out := out.push (.ins j)
  out := out ++ #[.label "fwd", .db [1, .num (-1), 255], .dw [.sym "near", 0x1234], .ds 3,
    .ins { op := .djnz, args := [.imm (.sym "near")] }, .ins { op := .ld, args := [.hl, .imm (.sym "fwd")] },
    .ins { op := .ld, args := [.a, .mem (.sym "fwd" 1)] }]
  return out.toList

end Ember.Z80.Asm
