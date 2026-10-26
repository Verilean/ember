import Ember.Proof.Z80PassCert
import Ember.Proof.Z80PassCheck

/-!
# Ember.Proof.Z80PassChk — the checker of the two images (plan M7.3)

A certificate gives, for each item of `A` (the image without the passes)
where the two runs meet, the index of `B`'s item there, whether `H` and
`L` may differ, the functions whose activation the run may be in, and
which segment of the two runs starts there (`Row`); and, for each
function, whether `H` and `L` may differ when it returns (`tr`).  It is
made by a computation outside the proofs; what is checked here, by one
walk over the items of both images (`check`), is that it is closed: every
segment starting at a row of it ends at rows of it, as the segment lemmas
say, with `H`, `L` free there only where the row lets them be.

The walk keeps each image's items from the current index on (no indexing
into the lists: the kernel runs it), and looks labels up in a table made
by an earlier walk (`mkTbl`).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Proof.PassCheck Ember.Proof.Z80Gen Ember.Proof.PassLocal

set_option linter.constructorNameAsVariable false

/-- Which segment of the two runs starts at an item. -/
inductive Tag where
  /-- Not a meeting point of the runs. -/
  | none
  /-- An item of no bytes in both (a label, an `equ`): both go on. -/
  | skipBoth
  /-- An item of no bytes in `A` that `B` has not. -/
  | skipA
  | ord | jump | djnz | call | ret | halt | ldsp | ldir | pack
  /-- A call of a routine of the runtime through `HL` (`rt_ld32`, …), the RAM kept equal. -/
  | blk
  /-- `ld hl,lit` and a call of such a routine: each image's literal. -/
  | blkR
  /-- `ld hl,lit; ld de,dst; ld bc,n; ldir`. -/
  | copyR
  /-- `jp l` (`jp cc,l`) to a `ret` in `A`, `ret` (`ret cc`) in `B`. -/
  | retThr
  /-- `jp cc,l` over a return in `A`, `ret` on the other condition in `B`. -/
  | condRet
  /-- A call before a return in `A`, a jump in `B`. -/
  | tail
  /-- The same, of a routine of the runtime through `HL`. -/
  | tailBlk
  deriving DecidableEq, Repr, Inhabited

/-- A row of the certificate. -/
structure Row where
  tag : Tag := .none
  kb : Nat := 0
  /-- For `ord`: the index of the instruction's form in `Form.cands`. -/
  fi : Nat := 0
  th : Bool := false
  tl : Bool := false
  act : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- The activation of no function: the start-up and the main loop. -/
def topE : Nat := 1000000

/-- What the table of labels has for a label where the runs meet: where it is in each image, the row
there, `A`'s items from there on. -/
structure LInfo where
  ia : Nat
  ib : Nat
  row : Row
  sufA : List Item

/-- The table of the labels where the runs meet (rows `skipBoth`): by a walk over `A`'s items and the
rows. -/
def mkTbl : List Item → List Row → Nat → List (String × LInfo)
  | [], _, _ => []
  | _, [], _ => []
  | it :: as, r :: rs, k =>
    let rest := mkTbl as rs (k + 1)
    match it with
    | .label l => if r.tag = .skipBoth then (l, ⟨k, r.kb, r, it :: as⟩) :: rest else rest
    | _ => rest

def lookupL (t : List (String × LInfo)) (l : String) : Option LInfo := t.lookup l

/-- Every label of an image: its index and the items from there on. -/
def labTbl : List Item → Nat → List (String × Nat × List Item)
  | [], _ => []
  | it :: r, k =>
    match it with
    | .label l => (l, k, it :: r) :: labTbl r (k + 1)
    | _ => labTbl r (k + 1)

/-- The items of an image from a label on. -/
def sufOf (t : List (String × Nat × List Item)) (l : String) : Option (List Item) := (t.lookup l).map (·.2)

/-! ## What the walk checks at a row -/

/-- A form that is not `halt`. -/
def Form.notHalt : Form → Bool
  | .halt => false
  | _ => true

/-- The return taint of a function: `H` and `L`. -/
def trOf (tr : List (Nat × Bool × Bool)) (e : Nat) : Bool × Bool := (tr.lookup e).getD (false, false)

/-- A row the segment may end at: a meeting point with `B`'s index `kb`, `H`, `L` free there where
they may be after the segment, the activations of the segment's start among its own. -/
def succOK (r : Row) (kb : Nat) (th tl : Bool) (act : List Nat) : Bool :=
  r.tag != .none && r.kb == kb && (!th || r.th) && (!tl || r.tl) && act.all (r.act.contains ·)

def isZero : Item → Bool
  | .label _ | .equ .. | .comment _ => true
  | _ => false

/-- A `ret` past labels (`RetAt`). -/
def retAtB : List Item → Bool
  | .label _ :: r => retAtB r
  | .ins ⟨.ret, []⟩ :: _ => true
  | _ => false

/-- A return of `A` past labels (`RetSeq`): a `ret`, or a `jp` to a label that is a `ret`. -/
def retSeqB (tA : List (String × Nat × List Item)) : List Item → Bool
  | .label _ :: r => retSeqB tA r
  | .ins ⟨.ret, []⟩ :: _ => true
  | .ins ⟨.jp, [.imm (.sym l 0)]⟩ :: _ =>
    match sufOf tA l with
    | some sa => retAtB sa
    | none => false
  | _ => false

/-- The conditions of `jp` / `jr` / `ret` this proof takes. -/
def ccOK : Option Arg → Bool
  | none => true
  | some .nz | some .z | some .nc | some .c => true
  | _ => false

/-- The routines of the runtime through `HL`, by the label of their call: the label at the start
of their items, and their items. -/
def ptrRoutine : String → Option (String × List Item)
  | "rt_ld32" => some ("rt_ld64", ldItems)
  | "rt_st32" => some ("rt_st64", stItems)
  | "rt_add32" => some ("rt_add64", bytewiseItems "add" [.ins ⟨.or, [.a]⟩] ⟨.adc, [.a, .mhl]⟩)
  | "rt_sub32" => some ("rt_sub64", bytewiseItems "sub" [.ins ⟨.or, [.a]⟩] ⟨.sbc, [.a, .mhl]⟩)
  | "rt_or32" => some ("rt_or64", bytewiseItems "or" [] ⟨.or, [.mhl]⟩)
  | "rt_cmp32" => some ("rt_cmp64", cmpItems)
  | _ => none

/-- The routine's items at its label in both images. -/
def routineOK (tA tB : List (String × Nat × List Item)) (f : String) : Bool :=
  match ptrRoutine f with
  | some (h, its) =>
    match sufOf tA h, sufOf tB h with
    | some sa, some sb => decide (its = sa.take its.length) && decide (its = sb.take its.length)
    | _, _ => false
  | none => false

/-- A literal: a label followed by `db` of numbers, the same in both images, its bytes `n` of them. -/
def litOK (tA tB : List (String × Nat × List Item)) (l : String) (n : Nat) : Bool :=
  match sufOf tA l, sufOf tB l with
  | some (_ :: .db vs :: _), some (_ :: .db vs' :: _) =>
    decide (vs = vs') && vs.length == n && vs.all fun v => match v with | .num m => decide (0 ≤ m ∧ m < 256) | _ => false
  | _, _ => false

/-- A symbol that is not a label of `A` (an `equ`, or nothing): `ld hl` of it is no literal. -/
def notLabel (tA : List (String × Nat × List Item)) (l : String) : Bool := (tA.lookup l).isNone

/-- The value of a symbol from an image's labels, latest first (`Assembled.labels.reverse`). -/
def symValL (la : List (String × Nat)) (s : String) : Option Int := (la.lookup s).map Int.ofNat

/-- An operand the same number in both images (`valSameB`), from their labels. -/
def valSameL (la lb : List (String × Nat)) : Val → Bool
  | .num _ => true
  | .sym s _ => decide (symValL la s = symValL lb s)

/-- The value of an operand in an image, when it is a number or a known symbol. -/
def valOf (la : List (String × Nat)) : Val → Option Int
  | .num n => some n
  | .sym s off => (symValL la s).map (· + off)

/-- An operand address and the byte after it in `[lo, hi)`. -/
def nnOK (la : List (String × Nat)) (lo hi : Nat) (v : Val) : Bool :=
  match valOf la v with
  | some n => decide (0 ≤ n ∧ lo ≤ n.toNat ∧ n.toNat + 1 < hi)
  | none => false

/-- What the checks at the rows look things up in: each image's labels (latest first, as `Assembled.env`
resolves them), the RAM kept equal `[lo, hi)`, the tables of labels, the return taints. -/
structure Ctx where
  la : List (String × Nat)
  lb : List (String × Nat)
  lo : Nat
  hi : Nat
  t : List (String × LInfo)
  tA : List (String × Nat × List Item)
  tB : List (String × Nat × List Item)
  tr : List (Nat × Bool × Bool)

/-- The row after (`rs`: the rows from the next on). -/
def nextRow (rs : List Row) : Row := (rs.head?).getD default

/-- The row `n` after. -/
def rowN (rs : List Row) (n : Nat) : Row := (rs.drop (n - 1)).head?.getD default

/-- A return there: not in the activation of no function; `H`, `L` free only where every function it
may be in may return them so. -/
def retOK (tr : List (Nat × Bool × Bool)) (r : Row) : Bool :=
  !(r.act.contains topE) && r.act.all fun e =>
    let t' := trOf tr e
    (!r.th || t'.1) && (!r.tl || t'.2)

def skipBothOK (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | a :: _, b :: _ => isZero a && decide (a = b) && succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act
  | _, _ => false

def skipAOK (as : List Item) (r : Row) (rs : List Row) : Bool :=
  match as with
  | a :: _ => isZero a && succOK (nextRow rs) r.kb r.th r.tl r.act
  | _ => false

def ordOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins i :: _, .ins j :: _ =>
    decide (i = j) &&
    match (Form.cands (argVal i))[r.fi]? with
    | some f =>
      decide (f.instr = i) && f.notHalt && valSameL c.la c.lb (argVal f.instr) && (!r.th || !f.readsH) &&
      (!r.tl || !f.readsL) && (!f.viaNN || nnOK c.la c.lo c.hi (argVal f.instr)) &&
      succOK (nextRow rs) (r.kb + 1) (r.th && !f.writesH) (r.tl && !f.writesL) r.act
    | none => false
  | _, _ => false

def jumpOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨opA, argsA⟩ :: _, .ins ⟨opB, argsB⟩ :: _ =>
    (decide (opA = .jp) || decide (opA = .jr)) && (decide (opB = .jp) || decide (opB = .jr)) &&
      decide (argsA = argsB) &&
    match argsA with
    | [.imm (.sym l 0)] =>
      match lookupL c.t l with
      | some li => succOK li.row li.ib r.th r.tl r.act
      | none => false
    | [cc, .imm (.sym l 0)] =>
      ccOK (some cc) &&
      match lookupL c.t l with
      | some li => succOK li.row li.ib r.th r.tl r.act && succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act
      | none => false
    | _ => false
  | _, _ => false

def djnzOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.djnz, [.imm (.sym l 0)]⟩ :: _, .ins ⟨.djnz, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' &&
    match lookupL c.t l with
    | some li => succOK li.row li.ib r.th r.tl r.act && succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act
    | none => false
  | _, _ => false

def callOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.call, [.imm (.sym l 0)]⟩ :: _, .ins ⟨.call, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' &&
    match lookupL c.t l with
    | some li =>
      succOK li.row li.ib r.th r.tl [li.ia] &&
        succOK (nextRow rs) (r.kb + 1) (trOf c.tr li.ia).1 (trOf c.tr li.ia).2 r.act
    | none => false
  | _, _ => false

def retRowOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.ret, cc⟩ :: _, .ins ⟨.ret, cc'⟩ :: _ =>
    decide (cc = cc') && retOK c.tr r &&
    match cc with
    | [] => true
    | [x] => ccOK (some x) && succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act
    | _ => false
  | _, _ => false

def haltOK (as bs : List Item) : Bool :=
  match as, bs with
  | .ins ⟨.halt, []⟩ :: _, .ins ⟨.halt, []⟩ :: _ => true
  | _, _ => false

def ldspOK (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: _, .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: _ =>
    succOK (nextRow rs) (r.kb + 1) r.th r.tl [topE]
  | _, _ => false

def ldirOK (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.ldir, []⟩ :: _, .ins ⟨.ldir, []⟩ :: _ => !r.th && !r.tl && succOK (nextRow rs) (r.kb + 1) false false r.act
  | _, _ => false

def packOK (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  decide (packHighFrom.map Item.ins = as.take 4) && decide (packHighTo.map Item.ins = bs.take 2) &&
    succOK (rowN rs 4) (r.kb + 2) false false r.act

def blkOK (c : Ctx) (prev : Option Item) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.call, [.imm (.sym f 0)]⟩ :: _, .ins ⟨.call, [.imm (.sym f' 0)]⟩ :: _ =>
    f == f' && !r.th && !r.tl && routineOK c.tA c.tB f &&
    (match prev with
      | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => notLabel c.tA l
      | _ => true) &&
    succOK (nextRow rs) (r.kb + 1) false false r.act
  | _, _ => false

def blkROK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.call, [.imm (.sym f 0)]⟩ :: _,
      .ins ⟨.ld, [.hl, .imm (.sym l' 0)]⟩ :: .ins ⟨.call, [.imm (.sym f' 0)]⟩ :: _ =>
    l == l' && f == f' && f != "rt_st32" && f != "rt_or32" && routineOK c.tA c.tB f && litOK c.tA c.tB l 4 &&
    succOK (rowN rs 2) (r.kb + 2) true true r.act
  | _, _ => false

def copyROK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as with
  | .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.ld, [.de, .imm (.sym g 0)]⟩ ::
        .ins ⟨.ld, [.bc, .imm (.num n)]⟩ :: .ins ⟨.ldir, []⟩ :: _ =>
    decide (as.take 4 = bs.take 4) &&
    decide (1 ≤ n ∧ n < 65536) && litOK c.tA c.tB l n.toNat && valSameL c.la c.lb (.sym g 0) &&
    (match valOf c.la (.sym g 0) with
      | some d => decide (0 ≤ d ∧ c.lo ≤ d.toNat ∧ d.toNat + n.toNat ≤ c.hi)
      | none => false) &&
    succOK (rowN rs 4) (r.kb + 4) true true r.act
  | _ => false

def retThrOK (c : Ctx) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match as, bs with
  | .ins ⟨.jp, argsA⟩ :: _, .ins ⟨.ret, cc⟩ :: _ =>
    retOK c.tr r &&
    match argsA, cc with
    | [.imm (.sym l 0)], [] =>
      match sufOf c.tA l with
      | some sa => retAtB sa
      | none => false
    | [x, .imm (.sym l 0)], [x'] =>
      decide (x = x') && ccOK (some x) &&
      match sufOf c.tA l with
      | some sa => retAtB sa && succOK (nextRow rs) (r.kb + 1) r.th r.tl r.act
      | none => false
    | _, _ => false
  | _, _ => false

def condRetOK (c : Ctx) (as bs : List Item) (r : Row) : Bool :=
  match as, bs with
  | .ins ⟨.jp, [x, .imm (.sym l 0)]⟩ :: as', .ins ⟨.ret, [x']⟩ :: _ =>
    retOK c.tr r && ccOK (some x) && decide (Codegen.invert x = some x') && retSeqB c.tA as' &&
    match lookupL c.t l with
    | some li => succOK li.row (r.kb + 1) r.th r.tl r.act
    | none => false
  | _, _ => false

def tailOK (c : Ctx) (as bs : List Item) (r : Row) : Bool :=
  match as, bs with
  | .ins ⟨.call, [.imm (.sym l 0)]⟩ :: as', .ins ⟨opB, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' && (decide (opB = .jp) || decide (opB = .jr)) && retSeqB c.tA as' && !(r.act.contains topE) &&
    match lookupL c.t l with
    | some li =>
      succOK li.row li.ib r.th r.tl [li.ia] &&
        r.act.all fun e =>
          (!(trOf c.tr li.ia).1 || (trOf c.tr e).1) && (!(trOf c.tr li.ia).2 || (trOf c.tr e).2)
    | none => false
  | _, _ => false

def tailBlkOK (c : Ctx) (prev : Option Item) (as bs : List Item) (r : Row) : Bool :=
  match as, bs with
  | .ins ⟨.call, [.imm (.sym f 0)]⟩ :: as', .ins ⟨.jp, [.imm (.sym f' 0)]⟩ :: _ =>
    f == f' && (f == "rt_st32" || f == "rt_or32") && !r.th && !r.tl && routineOK c.tA c.tB f &&
      (match prev with
        | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => notLabel c.tA l
        | _ => true) &&
      retSeqB c.tA as' && !(r.act.contains topE)
  | _, _ => false

/-- **The check at a row** (`as`, `bs`: the items of each image from the row on; `rs`: the rows after;
`prev`: `A`'s item before). -/
def rowOK (c : Ctx) (prev : Option Item) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  match r.tag with
  | .none => false
  | .skipBoth => skipBothOK as bs r rs
  | .skipA => skipAOK as r rs
  | .ord => ordOK c as bs r rs
  | .jump => jumpOK c as bs r rs
  | .djnz => djnzOK c as bs r rs
  | .call => callOK c as bs r rs
  | .ret => retRowOK c as bs r rs
  | .halt => haltOK as bs
  | .ldsp => ldspOK as bs r rs
  | .ldir => ldirOK as bs r rs
  | .pack => packOK as bs r rs
  | .blk => blkOK c prev as bs r rs
  | .blkR => blkROK c as bs r rs
  | .copyR => copyROK c as bs r rs
  | .retThr => retThrOK c as bs r rs
  | .condRet => condRetOK c as bs r
  | .tail => tailOK c as bs r
  | .tailBlk => tailBlkOK c prev as bs r

/-- **The walk**, over `n` items of `A`: every row of the certificate that is a meeting point checked,
`B`'s items kept in step (its indices going up). -/
def walk (c : Ctx) : Nat → Option Item → List Item → List Row → List Item → Nat → Bool
  | 0, _, _, _, _, _ => true
  | _ + 1, _, [], _, _, _ => true
  | _ + 1, _, _ :: _, [], _, _ => false
  | n + 1, prev, a :: as, r :: rs, bs, kb =>
    if r.tag = .none then walk c n (some a) as rs bs kb
    else
      decide (kb ≤ r.kb) && rowOK c prev (a :: as) (bs.drop (r.kb - kb)) r rs &&
      walk c n (some a) as rs (bs.drop (r.kb - kb)) r.kb

/-- The context of the check of a certificate for two images. -/
def mkCtx (xs ys : List Item) (a b : Assembled) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool)) :
    Ctx :=
  ⟨a.labels.reverse, b.labels.reverse, lo, hi, mkTbl xs cert 0, labTbl xs 0, labTbl ys 0, tr⟩

/-- **The check of a certificate** for the two images: the walk, and the start (`A`'s first item, `B`'s
first, the activation of no function). -/
def check (xs ys : List Item) (a b : Assembled) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool)) :
    Bool :=
  cert.length == xs.length &&
  (match cert with
    | r :: _ => r.tag != .none && r.kb == 0 && !r.th && !r.tl && r.act.contains topE
    | [] => false) &&
  walk (mkCtx xs ys a b lo hi cert tr) xs.length none xs cert ys 0

end Ember.Proof.PassSim
