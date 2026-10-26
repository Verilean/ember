import Ember.Z80.Codegen

/-!
# Ember.Proof.Z80PassCheck — the items of the two images, matched (plan M7.3)

The image without the passes (`A`) and one with them (`B`) are run side
by side; the relation between the two machines is kept at the items of
`A` that have one of `B` (`align`).  This file computes the match, by
the kernel as well as at run time (total, structural recursion); what
it means is in the theorems that use it.

Each item of `A` gets a kind (`Kind`) and the index of its item in `B`:

| kind | `A` | `B` |
|---|---|---|
| `same` | an item | the same item |
| `relax` | `jp nn` / `jp cc,nn` | `jr` to the same target |
| `retThr` | `jp l` / `jp cc,l`, `l` a `ret` | `ret` / `ret cc` |
| `pack` | `ld l,a; ld h,0; ld h,l; ld l,0` (the first) | `ld h,a; ld l,0` |
| `condRet` | `jp cc,l` then a return, then `l:` | `ret !cc` |
| `tail` | `call f` before a return | `jp f` / `jr f` |
| `inner` | the other items of a rewrite above (the three after `pack`'s first, the return after `condRet`'s jump or `tail`'s call) | — |
| `drop` | an item `B` has not: a label nothing refers to, code not reached | — |

A return here is a `ret`, or a `jp l` where `l` is a `ret` (`retLabels`).
-/

namespace Ember.Proof.PassCheck
open Ember.Z80 Ember.Z80.Asm

inductive Kind where
  | same | relax | retThr | pack | condRet | tail | inner | drop
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The labels that are a `ret` (past further labels at the same place). -/
def retLabels : List Item → List String
  | [] => []
  | .label l :: rest =>
    let after := rest.dropWhile fun it => match it with | .label _ => true | _ => false
    let tl := retLabels rest
    match after with
    | .ins ⟨.ret, []⟩ :: _ => l :: tl
    | _ => tl
  | _ :: rest => retLabels rest

def isLabel : Item → Bool
  | .label _ => true
  | _ => false

/-- A return: `ret`, or a jump to a label that is a `ret`. -/
def isReturn (rl : List String) : Item → Bool
  | .ins ⟨.ret, []⟩ => true
  | .ins ⟨.jp, [.imm (.sym l 0)]⟩ => rl.contains l
  | _ => false

def nextNonLabel : List Item → Option Item
  | [] => none
  | it :: rest => if isLabel it then nextNonLabel rest else some it

/-- `n` items of a kind, none in `B`. -/
def many (k : Kind) (n : Nat) : List (Kind × Option Nat) := List.replicate n (k, none)

/-- **The match**: for each item of `A`, its kind and the index of its item in `B` (`kb`: the
index of the first of `ys`); `none` when they do not match.  `fuel`: at least the number of
items of `A`. -/
def align (rl : List String) : Nat → List Item → List Item → Nat → Option (List (Kind × Option Nat))
  | _, [], [], _ => some []
  | 0, _, _, _ => none
  | fuel + 1, xs, ys, kb =>
    match xs, ys with
    | [], [] => some []
    | [], _ :: _ => none
    | x :: xs', [] => (align rl fuel xs' [] kb).map ((.drop, none) :: ·)
    | .ins ⟨.ld, [.l, .a]⟩ :: .ins ⟨.ld, [.h, .imm (.num 0)]⟩ :: .ins ⟨.ld, [.h, .l]⟩ ::
        .ins ⟨.ld, [.l, .imm (.num 0)]⟩ :: xs',
      .ins ⟨.ld, [.h, .a]⟩ :: .ins ⟨.ld, [.l, .imm (.num 0)]⟩ :: ys' =>
      (align rl fuel xs' ys' (kb + 2)).map (((.pack, some kb) :: many .inner 3) ++ ·)
    | x :: xs', y :: ys' =>
      if x == y then (align rl fuel xs' ys' (kb + 1)).map ((.same, some kb) :: ·) else
      match x, y with
      | .ins ⟨.jp, [.imm v]⟩, .ins ⟨.jr, [.imm v']⟩ =>
        if v == v' then (align rl fuel xs' ys' (kb + 1)).map ((.relax, some kb) :: ·) else none
      | .ins ⟨.jp, [cc, .imm v]⟩, .ins ⟨.jr, [cc', .imm v']⟩ =>
        if v == v' && cc == cc' then (align rl fuel xs' ys' (kb + 1)).map ((.relax, some kb) :: ·) else none
      | .ins ⟨.jp, [.imm (.sym l 0)]⟩, .ins ⟨.ret, []⟩ =>
        if rl.contains l then (align rl fuel xs' ys' (kb + 1)).map ((.retThr, some kb) :: ·) else none
      | .ins ⟨.jp, [cc, .imm (.sym l 0)]⟩, .ins ⟨.ret, [cc']⟩ =>
        if cc == cc' && rl.contains l then (align rl fuel xs' ys' (kb + 1)).map ((.retThr, some kb) :: ·)
        else
          -- `jp cc,l` (labels dropped) a return, `l:` → `ret !cc`, `l:`
          let labs := (xs'.takeWhile isLabel).length
          match xs'.drop labs with
          | r :: .label m :: rest =>
            if isReturn rl r && m == l && Codegen.invert cc == some cc' then
              (align rl fuel (.label m :: rest) ys' (kb + 1)).map
                (((.condRet, some kb) :: many .drop labs) ++ (.inner, none) :: ·)
            else none
          | _ => none
      | .ins ⟨.call, [.imm v]⟩, .ins ⟨op, [.imm v']⟩ =>
        if (op == .jp || op == .jr) && v == v' && (nextNonLabel xs').any (isReturn rl) then
          match xs' with
          | r :: xs'' =>
            if isReturn rl r then (align rl fuel xs'' ys' (kb + 1)).map ([(.tail, some kb), (.inner, none)] ++ ·)
            else
              let labs := xs'.takeWhile isLabel
              -- the labels between kept (others jump to the return), or dropped with it
              if ys'.take labs.length == labs then (align rl fuel xs' ys' (kb + 1)).map ((.tail, some kb) :: ·)
              else
                match xs'.drop labs.length with
                | _ :: xs''' => (align rl fuel xs''' ys' (kb + 1)).map
                    (((.tail, some kb) :: many .drop labs.length) ++ (.inner, none) :: ·)
                | [] => none
          | [] => none
        else none
      | _, _ => (align rl fuel xs' ys kb).map ((.drop, none) :: ·)

/-- The match of two images' items. -/
def alignOf (a b : List Item) : Option (List (Kind × Option Nat)) :=
  align (retLabels a) (a.length + 1) a b 0

end Ember.Proof.PassCheck
