import Ember.Proof.Z80PassChk

/-!
# Ember.Proof.Z80PassAbs — what `A`'s registers hold where the runs meet (plan M7.3)

What the segments take of `A`'s run at a meeting point (`Need` of
`Z80PassMaster`) — the bytes read and written through `HL`, `DE` in the
RAM `[lo, hi)`, the address a routine of the runtime is called with
there — is a fact about `A`'s registers.  In the stack's image these are
set a few instructions before, in a line of the code with no label in
it: `ld hl,v`; or an index checked as the generator checks it
(`ld bc,-n; add hl,bc; jp c,rt_trap; ld bc,base+n; add hl,bc`); or
compared (`or a; sbc hl,de; add hl,de; jp nc,…`); and in `rt_zero`, from
its one call, through its `ldir`.

`AS`: what is known of `HL` (under each value of the carry), `DE`, `BC`
— an interval of each — and of the sums `HL + BC`, `DE + BC`; or nothing
(`none`).  `absF`: an ordinary instruction's effect on it; `absJ`: a
conditional jump (or return) not taken; `ldirIter`: a round of `ldir`
that goes on.  A list of these, one per item of `A`, is checked by a
walk (`absOK` at each item, `tgtOK` at the rows that go to a label).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Gen

/-! ## Intervals -/

/-- The numbers from `i.1` to `i.2` (none when `i.2 < i.1`). -/
abbrev Itv := Nat × Nat

def Itv.top : Itv := (0, 65535)
def Itv.emp : Itv := (1, 0)
def Itv.isEmp (i : Itv) : Bool := i.2 < i.1

/-- `v` in `i`. -/
def Itv.In (v : Nat) (i : Itv) : Prop := i.1 ≤ v ∧ v ≤ i.2

/-- `x` in `y`. -/
def Itv.le (x y : Itv) : Bool := x.isEmp || (y.1 ≤ x.1 && x.2 ≤ y.2)

/-- The smallest interval with both. -/
def Itv.hull (a b : Itv) : Itv :=
  if a.isEmp then b else if b.isEmp then a else (min a.1 b.1, max a.2 b.2)

/-- One number. -/
def Itv.one? (i : Itv) : Option Nat := if i.1 = i.2 then some i.1 else none

/-- A number, or everything when it is not one of 16 bits. -/
def Itv.cst (v : Option Int) : Itv :=
  match v with
  | some n => if 0 ≤ n ∧ n < 65536 then (n.toNat, n.toNat) else Itv.top
  | none => Itv.top

/-- The sums of two of 16 bits: those below `65536` (no carry), those at or above less `65536` (carry). -/
def Itv.add (x y : Itv) : Itv × Itv :=
  if x.isEmp || y.isEmp then (Itv.emp, Itv.emp) else
  ((if x.1 + y.1 ≤ 65535 then (x.1 + y.1, min (x.2 + y.2) 65535) else Itv.emp),
    (if 65536 ≤ x.2 + y.2 then (max (x.1 + y.1) 65536 - 65536, x.2 + y.2 - 65536) else Itv.emp))

/-- The differences `x - y - c`: those at or above 0 (no borrow), those below plus `65536` (borrow). -/
def Itv.sub (x y : Itv) (c : Nat) : Itv × Itv :=
  if x.isEmp || y.isEmp then (Itv.emp, Itv.emp) else
  ((if y.1 + c ≤ x.2 then (x.1 - (y.2 + c), x.2 - (y.1 + c)) else Itv.emp),
    (if x.1 < y.2 + c then (65536 - (y.2 + c - x.1), 65536 - max 1 (y.1 + c - x.2)) else Itv.emp))

def Itv.inc (i : Itv) : Itv := if i.isEmp then Itv.emp else if i.2 < 65535 then (i.1 + 1, i.2 + 1) else Itv.top
def Itv.dec (i : Itv) : Itv := if i.isEmp then Itv.emp else if 0 < i.1 then (i.1 - 1, i.2 - 1) else Itv.top

/-- Inside `[lo, hi)`, with `n` bytes from each. -/
def Itv.within (i : Itv) (lo hi n : Nat) : Bool := i.isEmp || (lo ≤ i.1 && i.2 + n ≤ hi)

/-! ## What is known of the registers -/

/-- `HL` when the carry is clear, when it is set; `DE`; `BC`; `HL + BC`, `DE + BC`. -/
structure AF where
  h0 : Itv
  h1 : Itv
  de : Itv
  bc : Itv
  hb : Option Nat := none
  db : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

def AF.top : AF := ⟨Itv.top, Itv.top, Itv.top, Itv.top, none, none⟩

/-- `none`: nothing known. -/
abbrev AS := Option AF

def AF.hl (a : AF) : Itv := a.h0.hull a.h1

/-- What is known, of a CPU. -/
def AF.Sat (a : AF) (s : Cpu) : Prop :=
  (s.flag FC = false → Itv.In s.hl.toNat a.h0) ∧ (s.flag FC = true → Itv.In s.hl.toNat a.h1) ∧
    Itv.In s.de.toNat a.de ∧ Itv.In s.bc.toNat a.bc ∧
    (∀ v, a.hb = some v → s.hl.toNat + s.bc.toNat = v) ∧ (∀ v, a.db = some v → s.de.toNat + s.bc.toNat = v)

def ASat : AS → Cpu → Prop
  | none, _ => True
  | some a, s => a.Sat s

/-- Nothing known as `none`. -/
def AF.norm (a : AF) : AS := if a = AF.top then none else some a

/-- `HL + BC` known, or from one number of each. -/
def AF.hbD (a : AF) : Option Nat :=
  match a.hb with
  | some v => some v
  | none => match a.hl.one?, a.bc.one? with
    | some p, some q => some (p + q)
    | _, _ => none

def AF.dbD (a : AF) : Option Nat :=
  match a.db with
  | some v => some v
  | none => match a.de.one?, a.bc.one? with
    | some p, some q => some (p + q)
    | _, _ => none

/-- **What `x` knows, `y` knows**. -/
def AF.le (x y : AF) : Bool :=
  x.h0.le y.h0 && x.h1.le y.h1 && x.de.le y.de && x.bc.le y.bc &&
    (y.hb.isNone || y.hb == x.hbD) && (y.db.isNone || y.db == x.dbD)

def AS.le : AS → AS → Bool
  | _, none => true
  | none, some y => AF.top.le y
  | some x, some y => x.le y

/-- `HL`, from the sum `HL + BC` when it is known. -/
def AF.hlR (a : AF) : Itv :=
  match a.hb with
  | some v => if !a.bc.isEmp && a.bc.2 ≤ v then (v - a.bc.2, v - a.bc.1) else a.hl
  | none => a.hl

def AF.deR (a : AF) : Itv :=
  match a.db with
  | some v => if !a.bc.isEmp && a.bc.2 ≤ v then (v - a.bc.2, v - a.bc.1) else a.de
  | none => a.de

/-! ## What an ordinary instruction leaves of it -/

/-- The forms that leave the carry. -/
def Form.keepsCF : Form → Bool
  | .stA _ | .stHL _ | .stDEA | .stHLA | .stHLN _ | .ldAN _ | .ldADE | .ldAHL | .ldDENN _ | .ldHLNN _
  | .decBC | .decHL | .di | .exDEHL | .incDE | .incHL | .ldAB | .ldAC | .ldAH | .ldAL | .ldAI _ | .ldBI _
  | .ldBCI _ | .ldCA | .ldCI _ | .ldDH | .ldDEI _ | .ldEL | .ldHA | .ldHL2 | .ldHI _ | .ldHLI _ | .ldLA
  | .ldLI _ | .outA _ => true
  | _ => false

/-- The forms that clear the carry. -/
def Form.clearsCF : Form → Bool
  | .andM | .orM | .andC | .andL | .andN _ | .orA | .orC | .orD | .orE | .orH | .orL | .orN _ | .xorA
  | .xorN _ => true
  | _ => false

/-- The forms that leave `DE`. -/
def Form.keepsDE : Form → Bool
  | .ldDENN _ | .ldDEI _ | .ldDH | .ldEL | .incDE | .exDEHL => false
  | _ => true

/-- The forms that leave `BC`. -/
def Form.keepsBC : Form → Bool
  | .decB | .decBC | .decC | .incB | .incC | .ldBI _ | .ldBCI _ | .ldCA | .ldCI _ => false
  | _ => true

/-- What an instruction leaves known, by what it leaves of the registers and the carry. -/
def absG (f : Form) (a : AF) : AF :=
  let h : Itv × Itv :=
    if f.writesH || f.writesL then (Itv.top, Itv.top)
    else if f.keepsCF then (a.h0, a.h1)
    else if f.clearsCF then (a.hl, Itv.emp)
    else (a.hl, a.hl)
  { h0 := h.1, h1 := h.2, de := if f.keepsDE then a.de else Itv.top, bc := if f.keepsBC then a.bc else Itv.top,
    hb := if f.writesH || f.writesL || !f.keepsBC then none else a.hb,
    db := if !f.keepsDE || !f.keepsBC then none else a.db }

/-- The forms `absF` has an effect of their own for. -/
def Form.special : Form → Bool
  | .ldHLI _ | .ldBCI _ | .ldDEI _ | .addHLBC | .addHLDE | .sbcHLDE | .incHL | .decHL | .decBC | .incDE
  | .exDEHL | .ldDH | .ldEL => true
  | _ => false

/-- **What an ordinary instruction leaves known** (`la`: `A`'s labels, for its operand). -/
def absF (la : List (String × Nat)) : Form → AF → AF
  | .ldHLI v, a => let i := Itv.cst (valOf la v); { a with h0 := i, h1 := i, hb := none }
  | .ldBCI v, a => { a with bc := Itv.cst (valOf la v), hb := none, db := none }
  | .ldDEI v, a => { a with de := Itv.cst (valOf la v), db := none }
  | .addHLBC, a => let r := Itv.add a.hl a.bc; { a with h0 := r.1, h1 := r.2, hb := none }
  | .addHLDE, a => let r := Itv.add a.hl a.de; { a with h0 := r.1, h1 := r.2, hb := none }
  | .sbcHLDE, a =>
    let r0 := Itv.sub a.h0 a.de 0
    let r1 := Itv.sub a.h1 a.de 1
    { a with h0 := r0.1.hull r1.1, h1 := r0.2.hull r1.2, hb := none }
  | .incHL, a => { a with h0 := a.h0.inc, h1 := a.h1.inc, hb := none }
  | .decHL, a => { a with h0 := a.h0.dec, h1 := a.h1.dec, hb := none }
  | .decBC, a => { a with bc := a.bc.dec, hb := none, db := none }
  | .incDE, a => { a with de := a.de.inc, db := none }
  | .exDEHL, a => { a with h0 := a.de, h1 := a.de, de := a.hl, hb := a.db, db := a.hb }
  | .ldDH, a =>
    { a with de := (match a.hl.one? with | some p => (p / 256 * 256, p / 256 * 256 + 255) | none => Itv.top),
             db := none }
  | .ldEL, a =>
    { a with de := (match a.hl.one? with
        | some p => if a.de.1 / 256 = a.de.2 / 256 ∧ a.de.2 < 65536 then (a.de.1 / 256 * 256 + p % 256, a.de.1 / 256 * 256 + p % 256)
            else Itv.top
        | none => Itv.top),
             db := none }
  | f, a => absG f a

def absT (la : List (String × Nat)) (f : Form) (a : AS) : AS := (absF la f (a.getD AF.top)).norm

/-- **A conditional jump or return not taken**: the carry as the condition says. -/
def absJ (cc : Arg) (a : AS) : AS :=
  match a with
  | none => none
  | some a =>
    match cc with
    | .c => some { a with h1 := Itv.emp }
    | .nc => some { a with h0 := Itv.emp }
    | _ => some a

/-- **A round of `ldir` that goes on** (`BC` not 1 before it). -/
def ldirIter (a : AS) : AS :=
  match a with
  | none => none
  | some a =>
    let ok : Bool := !a.bc.isEmp && 1 ≤ a.bc.1
    let lim (o : Option Nat) : Option Nat := if ok then o.bind (fun v => if v ≤ 65535 then some v else none) else none
    some ⟨Itv.inc a.h0, Itv.inc a.h1, Itv.inc a.de,
      (if a.bc.isEmp then Itv.emp else if 1 ≤ a.bc.1 then (max 1 (a.bc.1 - 1), a.bc.2 - 1) else Itv.top),
      lim a.hb, lim a.db⟩

/-! ## What is checked -/

def AS.hlR (a : AS) : Itv := (a.getD AF.top).hlR
def AS.deR (a : AS) : Itv := (a.getD AF.top).deR

/-- The item before is `ld hl,l` of a label `l` of `A` (a literal in ROM). -/
def litPrev (tA : List (String × Nat × List Item)) : Option Item → Bool
  | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => !notLabel tA l
  | _ => false

/-- **What the segment at a meeting point takes, from what is known there**: the bytes read or
written at `HL`, `DE` in `[lo, hi)`; for a call of a routine through `HL` not given a literal of
`A` (`prev`, `tA`), the four bytes at `HL`. -/
def needOK (tA : List (String × Nat × List Item)) (lo hi : Nat) (prev : Option Item) (it : Item) (a : AS) : Bool :=
  match it with
  | .ins i =>
    (!(i.args.contains .mhl) || a.hlR.within lo hi 1) && (!(i.args.contains .mde) || a.deR.within lo hi 1) &&
    (!(decide (i = ⟨.ldir, []⟩)) || (a.hlR.within lo hi 1 && a.deR.within lo hi 1)) &&
    (match i with
      | ⟨.call, [.imm (.sym f 0)]⟩ => (ptrRoutine f).isNone || litPrev tA prev || a.hlR.within lo hi 4
      | _ => true)
  | _ => true

/-- **What the segment from the row before leaves known** at an item, when it ends there: an ordinary
instruction; a jump or a return not taken; an item of no bytes (`pi`, `pr`, `pa`: the item, row,
what is known there). -/
def absAfter (la : List (String × Nat)) (pi : Item) (pr : Row) (pa : AS) : Option AS :=
  match pr.tag, pi with
  | .ord, .ins i =>
    match (Form.cands (argVal i))[pr.fi]? with
    | some f => if f.instr = i then some (absT la f pa) else none
    | none => none
  | .jump, .ins ⟨op, [cc, .imm (.sym _ 0)]⟩ =>
    if (op = .jp ∨ op = .jr) ∧ ccOK (some cc) then some (absJ cc pa) else none
  | .ret, .ins ⟨.ret, [cc]⟩ => if ccOK (some cc) then some (absJ cc pa) else none
  | .skipBoth, it | .skipA, it => if isZero it then some pa else none
  | _, _ => none

def isLabel : Item → Bool
  | .label _ => true
  | _ => false

/-- **The check at an item** (`prev`: the item, row and what is known before; `as`: what is known
from the next on): known only where the segment from the row before ends with it known, or at a
label after a `ret` (a function's entry; what is known there, the rows that go there
check); after `ldir`'s row, a round that goes on keeps it; at a meeting point, enough for it; the
rows the segments of `blkR`, `pack`, `copyR` end at, nothing known. -/
def absOK (la : List (String × Nat)) (tA : List (String × Nat × List Item)) (lo hi : Nat)
    (prev : Option (Item × Row × AS)) (it : Item) (r : Row) (a : AS) (as : List AS) : Bool :=
  (a.isNone ||
    match prev with
    | some (pi, pr, pa) =>
      (!isLabel it && match absAfter la pi pr pa with
        | some b => AS.le b a
        | none => false) || (isLabel it && decide (pi = .ins ⟨.ret, []⟩))
    | none => false) &&
  (r.tag != .ldir || AS.le (ldirIter a) a) &&
  (r.tag != .blkR || (as.drop 1).head?.join.isNone) &&
  ((r.tag != .pack && r.tag != .copyR) || (as.drop 3).head?.join.isNone) &&
  (r.tag == .none || needOK tA lo hi (prev.map (·.1)) it a)

/-- What is known at the labels where the runs meet (rows `skipBoth`), as `mkTbl` finds them. -/
def acTbl : List Item → List Row → List AS → List (String × AS)
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | it :: xs, r :: rs, a :: as =>
    let rest := acTbl xs rs as
    match it with
    | .label l => if r.tag = .skipBoth then (l, a) :: rest else rest
    | _ => rest

def acOf (lt : List (String × AS)) (l : String) : AS := (lt.lookup l).getD none

/-- **The rows that go to a label**: a call keeps what is known; the others leave nothing known
there. -/
def tgtOK (lt : List (String × AS)) (it : Item) (r : Row) (a : AS) : Bool :=
  match r.tag, it with
  | .call, .ins ⟨.call, [.imm (.sym l 0)]⟩ => AS.le a (acOf lt l)
  | .jump, .ins ⟨_, args⟩ | .condRet, .ins ⟨_, args⟩ | .djnz, .ins ⟨_, args⟩ | .tail, .ins ⟨_, args⟩ =>
    match args.getLast? with
    | some (.imm (.sym l 0)) => (acOf lt l).isNone
    | _ => false
  | _, _ => true

end Ember.Proof.PassSim
