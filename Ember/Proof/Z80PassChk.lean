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
    | some sa, some sb => its.isPrefixOf sa && its.isPrefixOf sb
    | _, _ => false
  | none => false

/-- A literal: a label followed by `db` of numbers, the same in both images, its bytes `n` of them. -/
def litOK (tA tB : List (String × Nat × List Item)) (l : String) (n : Nat) : Bool :=
  match sufOf tA l, sufOf tB l with
  | some (_ :: .db vs :: _), some (_ :: .db vs' :: _) =>
    vs == vs' && vs.length == n && vs.all fun v => match v with | .num m => decide (0 ≤ m ∧ m < 256) | _ => false
  | _, _ => false

/-- A symbol that is not a label of `A` (an `equ`, or nothing): `ld hl` of it is no literal. -/
def notLabel (tA : List (String × Nat × List Item)) (l : String) : Bool := (tA.lookup l).isNone

/-- The value of a symbol from an image's labels, latest first (`Assembled.labels.reverse`). -/
def symValL (la : List (String × Nat)) (s : String) : Option Int := (la.lookup s).map Int.ofNat

/-- An operand the same number in both images (`valSameB`), from their labels. -/
def valSameL (la lb : List (String × Nat)) : Val → Bool
  | .num _ => true
  | .sym s _ => symValL la s == symValL lb s

/-- The value of an operand in an image, when it is a number or a known symbol. -/
def valOf (la : List (String × Nat)) : Val → Option Int
  | .num n => some n
  | .sym s off => (symValL la s).map (· + off)

/-- An operand address and the byte after it in `[lo, hi)`. -/
def nnOK (la : List (String × Nat)) (lo hi : Nat) (v : Val) : Bool :=
  match valOf la v with
  | some n => decide (0 ≤ n ∧ lo ≤ n.toNat ∧ n.toNat + 1 < hi)
  | none => false

/-- **The check at a row** (`as`, `bs`: the items of each image from the row on; `rs`: the rows; `prev`:
`A`'s item before). -/
def rowOK (la lb : List (String × Nat)) (lo hi : Nat) (t : List (String × LInfo)) (tA tB : List (String × Nat × List Item))
    (tr : List (Nat × Bool × Bool)) (prev : Option Item) (as bs : List Item) (r : Row) (rs : List Row) : Bool :=
  let next := (rs.head?).getD default
  let rowAt (n : Nat) : Row := (rs.drop (n - 1)).head?.getD default
  let retOK : Bool := !(r.act.contains topE) && r.act.all fun e =>
    let t' := trOf tr e
    (!r.th || t'.1) && (!r.tl || t'.2)
  match r.tag, as, bs with
  | .skipBoth, a :: _, b :: _ => isZero a && a == b && succOK next (r.kb + 1) r.th r.tl r.act
  | .skipA, a :: _, _ => isZero a && succOK next r.kb r.th r.tl r.act
  | .ord, .ins i :: _, .ins j :: _ =>
    i == j &&
    match (Form.cands (argVal i))[r.fi]? with
    | some f =>
      decide (f.instr = i) && f != .halt && valSameL la lb (argVal f.instr) && (!r.th || !f.readsH) && (!r.tl || !f.readsL) &&
      (!f.viaNN || nnOK la lo hi (argVal f.instr)) &&
      succOK next (r.kb + 1) (r.th && !f.writesH) (r.tl && !f.writesL) r.act
    | none => false
  | .jump, .ins ⟨opA, argsA⟩ :: _, .ins ⟨opB, argsB⟩ :: _ =>
    (opA == .jp || opA == .jr) && (opB == .jp || opB == .jr) && argsA == argsB &&
    match argsA with
    | [.imm (.sym l 0)] =>
      match lookupL t l with
      | some li => succOK li.row li.ib r.th r.tl r.act
      | none => false
    | [c, .imm (.sym l 0)] =>
      ccOK (some c) && c != .imm (.sym l 0) &&
      match lookupL t l with
      | some li => succOK li.row li.ib r.th r.tl r.act && succOK next (r.kb + 1) r.th r.tl r.act
      | none => false
    | _ => false
  | .djnz, .ins ⟨.djnz, [.imm (.sym l 0)]⟩ :: _, .ins ⟨.djnz, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' &&
    match lookupL t l with
    | some li => succOK li.row li.ib r.th r.tl r.act && succOK next (r.kb + 1) r.th r.tl r.act
    | none => false
  | .call, .ins ⟨.call, [.imm (.sym l 0)]⟩ :: _, .ins ⟨.call, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' &&
    match lookupL t l with
    | some li =>
      let t' := trOf tr li.ia
      succOK li.row li.ib r.th r.tl [li.ia] && succOK next (r.kb + 1) t'.1 t'.2 r.act
    | none => false
  | .ret, .ins ⟨.ret, cc⟩ :: _, .ins ⟨.ret, cc'⟩ :: _ =>
    cc == cc' && retOK &&
    match cc with
    | [] => true
    | [c] => ccOK (some c) && succOK next (r.kb + 1) r.th r.tl r.act
    | _ => false
  | .halt, .ins ⟨.halt, []⟩ :: _, .ins ⟨.halt, []⟩ :: _ => true
  | .ldsp, .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: _, .ins ⟨.ld, [.sp, .imm (.num 0)]⟩ :: _ =>
    succOK next (r.kb + 1) r.th r.tl [topE]
  | .ldir, .ins ⟨.ldir, []⟩ :: _, .ins ⟨.ldir, []⟩ :: _ =>
    !r.th && !r.tl && succOK next (r.kb + 1) false false r.act
  | .pack, _, _ =>
    (packHighFrom.map Item.ins).isPrefixOf as && (packHighTo.map Item.ins).isPrefixOf bs &&
    succOK (rowAt 4) (r.kb + 2) false false r.act
  | .blk, .ins ⟨.call, [.imm (.sym f 0)]⟩ :: _, .ins ⟨.call, [.imm (.sym f' 0)]⟩ :: _ =>
    f == f' && !r.th && !r.tl && routineOK tA tB f &&
    (match prev with
      | some (.ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩) => notLabel tA l
      | _ => true) &&
    succOK next (r.kb + 1) false false r.act
  | .blkR, .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.call, [.imm (.sym f 0)]⟩ :: _,
      .ins ⟨.ld, [.hl, .imm (.sym l' 0)]⟩ :: .ins ⟨.call, [.imm (.sym f' 0)]⟩ :: _ =>
    l == l' && f == f' && f != "rt_st32" && f != "rt_or32" && routineOK tA tB f && litOK tA tB l 4 &&
    succOK (rowAt 2) (r.kb + 2) true true r.act
  | .copyR, .ins ⟨.ld, [.hl, .imm (.sym l 0)]⟩ :: .ins ⟨.ld, [.de, .imm (.sym g 0)]⟩ ::
        .ins ⟨.ld, [.bc, .imm (.num n)]⟩ :: .ins ⟨.ldir, []⟩ :: _, b0 :: b1 :: b2 :: b3 :: _ =>
    some b0 == as.head? && some b1 == (as.drop 1).head? && some b2 == (as.drop 2).head? &&
      some b3 == (as.drop 3).head? &&
    decide (1 ≤ n ∧ n < 65536) && litOK tA tB l n.toNat && valSameL la lb (.sym g 0) &&
    (match valOf la (.sym g 0) with
      | some d => decide (0 ≤ d ∧ lo ≤ d.toNat ∧ d.toNat + n.toNat ≤ hi)
      | none => false) &&
    succOK (rowAt 4) (r.kb + 4) true true r.act
  | .retThr, .ins ⟨.jp, argsA⟩ :: _, .ins ⟨.ret, cc⟩ :: _ =>
    retOK &&
    match argsA, cc with
    | [.imm (.sym l 0)], [] =>
      match sufOf tA l with
      | some sa => retAtB sa
      | none => false
    | [c, .imm (.sym l 0)], [c'] =>
      c == c' && ccOK (some c) &&
      match sufOf tA l with
      | some sa => retAtB sa && succOK next (r.kb + 1) r.th r.tl r.act
      | none => false
    | _, _ => false
  | .condRet, .ins ⟨.jp, [c, .imm (.sym l 0)]⟩ :: as', .ins ⟨.ret, [c']⟩ :: _ =>
    retOK && ccOK (some c) && Codegen.invert c == some c' && retSeqB tA as' &&
    match lookupL t l with
    | some li => succOK li.row (r.kb + 1) r.th r.tl r.act
    | none => false
  | .tail, .ins ⟨.call, [.imm (.sym l 0)]⟩ :: as', .ins ⟨opB, [.imm (.sym l' 0)]⟩ :: _ =>
    l == l' && (opB == .jp || opB == .jr) && retSeqB tA as' && !(r.act.contains topE) &&
    match lookupL t l with
    | some li =>
      let t' := trOf tr li.ia
      succOK li.row li.ib r.th r.tl [li.ia] &&
        r.act.all fun e => let te := trOf tr e; (!t'.1 || te.1) && (!t'.2 || te.2)
    | none => false
  | .tailBlk, .ins ⟨.call, [.imm (.sym f 0)]⟩ :: as', .ins ⟨.jp, [.imm (.sym f' 0)]⟩ :: _ =>
    f == f' && (f == "rt_st32" || f == "rt_or32") && !r.th && !r.tl && routineOK tA tB f && retSeqB tA as' &&
    !(r.act.contains topE)
  | _, _, _ => false

/-- **The walk**, over `n` items of `A`: every row of the certificate that is a meeting point checked,
`B`'s items kept in step (its indices going up). -/
def walk (la lb : List (String × Nat)) (lo hi : Nat) (t : List (String × LInfo)) (tA tB : List (String × Nat × List Item))
    (tr : List (Nat × Bool × Bool)) : Nat → Option Item → List Item → List Row → List Item → Nat → Bool
  | 0, _, _, _, _, _ => true
  | _ + 1, _, [], _, _, _ => true
  | _ + 1, _, _ :: _, [], _, _ => false
  | n + 1, prev, a :: as, r :: rs, bs, kb =>
    if r.tag = .none then walk la lb lo hi t tA tB tr n (some a) as rs bs kb
    else
      decide (kb ≤ r.kb) &&
      rowOK la lb lo hi t tA tB tr prev (a :: as) (bs.drop (r.kb - kb)) r rs &&
      walk la lb lo hi t tA tB tr n (some a) as rs (bs.drop (r.kb - kb)) r.kb

/-- **The check of a certificate** for the two images: the walk, and the start (`A`'s first item, `B`'s
first, the activation of no function). -/
def check (xs ys : List Item) (a b : Assembled) (lo hi : Nat) (cert : List Row) (tr : List (Nat × Bool × Bool)) :
    Bool :=
  let t := mkTbl xs cert 0
  cert.length == xs.length &&
  (match cert with
    | r :: _ => r.tag != .none && r.kb == 0 && !r.th && !r.tl && r.act.contains topE
    | [] => false) &&
  walk a.labels.reverse b.labels.reverse lo hi t (labTbl xs 0) (labTbl ys 0) tr xs.length none xs cert ys 0

end Ember.Proof.PassSim
