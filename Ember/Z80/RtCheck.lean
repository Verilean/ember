import Ember.Z80.Runtime
import Ember.Z80.Cpu
import Ember.Util.Rand

/-!
# Ember.Z80.RtCheck — the runtime routines against their specifications (plan M6.6)

Every routine of `Ember.Z80.Runtime.pieces` is called on the CPU model
with its inputs in the registers and memory its convention names, and
the result is compared with the specification — a line of arithmetic on
natural numbers here.  8-bit routines are checked on every pair of
operands; wider ones on edge values (0, 1, powers of two and their
neighbours, all ones) in every combination and on random values.
-/

namespace Ember.Z80.RtCheck
open Ember.Z80.Asm

structure Rig where
  cpu : Cpu
  labels : List (String × Nat)

def Rig.addr (r : Rig) (l : String) : Nat := (r.labels.lookup l).getD 0

/-- Second operand of the wide routines. -/
def opAddr : Nat := 0x9000

def build : Except String Rig := do
  let pieces ← Runtime.pieces.mapM fun p => do return (← Asm.parse p.src) ++ p.items
  let stubs ← Asm.parse "
t_stop: halt
rt_trap: ld a,0xEE
  ld (t_trapped),a
  halt
"
  let mut at_ := 0x8000
  let mut equs : List Item := [.equ "t_trapped" 0x8F00]
  for (n, sz) in Runtime.cells do
    equs := equs ++ [.equ n at_]
    at_ := at_ + sz
  let a ← Asm.assemble (equs ++ stubs ++ pieces.flatten)
  return { cpu := ({} : Cpu).load 0 a.bytes, labels := a.labels }

def poke (c : Cpu) (a n v : Nat) : Cpu := Id.run do
  let mut m := c.mem
  let mut c := { c with mem := ByteArray.empty }
  for k in [0:n] do m := m.set! (a + k) (UInt8.ofNat ((v >>> (8 * k)) % 256))
  c := { c with mem := m }
  return c

def peek (c : Cpu) (a n : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do v := v + (c.mem.get! (a + k)).toNat <<< (8 * k)
  return v

/-- Call the routine at `entry`; the CPU when it has returned (or trapped). -/
def call (r : Rig) (c : Cpu) (entry : String) : Except String Cpu := do
  let stop := r.addr "t_stop"
  let c := poke (poke c 0x8F00 1 0) 0xFFF0 2 stop
  let mut c := { c with sp := 0xFFF0, pc := UInt16.ofNat (r.addr entry), halted := false, iff1 := false }
  let mut n := 0
  while !c.halted do
    if n > 2000000 then throw s!"{entry} does not return"
    c := c.step fun _ => 0xFF
    n := n + 1
  return c

def flagZ (c : Cpu) : Bool := c.f &&& 0x40 != 0
def flagC (c : Cpu) : Bool := c.f &&& 0x01 != 0

def edges (bitsN : Nat) : List Nat :=
  let m := 2 ^ bitsN
  ([0, 1, 2, 3, 7, 8, 9, 15, 16, 255, 256, 257, m / 2 - 1, m / 2, m / 2 + 1, m - 2, m - 1] ++
   (List.range (bitsN / 8)).map fun k => 0xA5 <<< (8 * k)).filter (· < m) |>.eraseDups

structure Tally where
  cases : Nat := 0
  bad : Nat := 0
  first : Option String := none

def Tally.note (t : Tally) (ok : Bool) (what : Unit → String) : Tally :=
  if ok then { t with cases := t.cases + 1 }
  else { t with cases := t.cases + 1, bad := t.bad + 1, first := t.first <|> some (what ()) }

def setHL (c : Cpu) (v : Nat) : Cpu := { c with h := UInt8.ofNat (v / 256), l := UInt8.ofNat v }
def setDE (c : Cpu) (v : Nat) : Cpu := { c with d := UInt8.ofNat (v / 256), e := UInt8.ofNat v }
def hl (c : Cpu) : Nat := c.h.toNat * 256 + c.l.toNat

/-- All the checks; the number of cases run and the failures. -/
def run (seed : Nat := 1) (randoms : Nat := 300) : Except String Tally := do
  let r ← build
  let mut c := r.cpu
  let mut t : Tally := {}
  -- 8 bits: every pair
  for (name, spec) in [("rt_mul8", fun (a e : Nat) => a * e % 256), ("rt_div8", fun a e => if e == 0 then 0 else a / e),
                       ("rt_mod8", fun a e => if e == 0 then 0 else a % e)] do
    for a in [0:256] do
      for e in [0:256] do
        c ← call r { c with a := UInt8.ofNat a, e := UInt8.ofNat e } name
        t := t.note (c.a.toNat == spec a e) fun _ => s!"{name}({a}, {e}) = {c.a.toNat}, expected {spec a e}"
  for (name, left) in [("rt_shl8", true), ("rt_shr8", false)] do
    for a in [0:256] do
      for b in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 100, 255] do
        c ← call r { c with a := UInt8.ofNat a, b := UInt8.ofNat b } name
        let want := if b ≥ 8 then 0 else if left then (a <<< b) % 256 else a >>> b
        t := t.note (c.a.toNat == want) fun _ => s!"{name}({a}, {b}) = {c.a.toNat}, expected {want}"
  -- 16 bits
  let rng := Rng.ofSeed seed
  let (r16, rng) := Id.run do
    let mut g := rng
    let mut out := #[]
    for _ in [0:randoms] do
      let (v, g') := g.next
      g := g'
      out := out.push (v.toNat % 65536)
    return (out.toList, g)
  let vals16 := edges 16 ++ r16.take 40
  for (name, spec) in [("rt_mul16", fun (a b : Nat) => a * b % 65536), ("rt_div16", fun a b => if b == 0 then 0 else a / b),
                       ("rt_mod16", fun a b => if b == 0 then 0 else a % b), ("rt_and16", fun a b => a &&& b),
                       ("rt_or16", fun a b => a ||| b), ("rt_xor16", fun a b => a ^^^ b)] do
    for a in vals16 do
      for b in vals16 do
        c ← call r (setDE (setHL c a) b) name
        t := t.note (hl c == spec a b) fun _ => s!"{name}({a}, {b}) = {hl c}, expected {spec a b}"
  for a in vals16 do
    c ← call r (setHL c a) "rt_not16"
    t := t.note (hl c == 65535 - a) fun _ => s!"rt_not16({a}) = {hl c}"
    c ← call r (setHL c a) "rt_neg16"
    t := t.note (hl c == (65536 - a) % 65536) fun _ => s!"rt_neg16({a}) = {hl c}"
    c ← call r (setHL c a) "rt_sat16"
    t := t.note (c.a.toNat == (if a > 255 then 255 else a)) fun _ => s!"rt_sat16({a}) = {c.a.toNat}"
    for b in [0, 1, 7, 8, 9, 15, 16, 17, 255] do
      c ← call r { setHL c a with b := UInt8.ofNat b } "rt_shl16"
      t := t.note (hl c == (if b ≥ 16 then 0 else (a <<< b) % 65536)) fun _ => s!"rt_shl16({a}, {b}) = {hl c}"
      c ← call r { setHL c a with b := UInt8.ofNat b } "rt_shr16"
      t := t.note (hl c == (if b ≥ 16 then 0 else a >>> b)) fun _ => s!"rt_shr16({a}, {b}) = {hl c}"
    -- the index check: returns with HL when below, traps otherwise
    for b in vals16.take 12 do
      c ← call r { setHL c a with b := UInt8.ofNat (b / 256), c := UInt8.ofNat b } "rt_bound"
      let trapped := peek c 0x8F00 1 == 0xEE
      t := t.note (trapped == (a ≥ b) && (trapped || hl c == a)) fun _ => s!"rt_bound({a}, {b}): trapped = {trapped}, HL = {hl c}"
  -- 32 and 64 bits: accumulator and the operand HL points to
  let acc := r.addr "rt_acc"
  let mut g := rng
  for n in [4, 8] do
    let w := 8 * n
    let m := 2 ^ w
    let mut rs := #[]
    for _ in [0:randoms / 10] do
      let (v, g') := g.next
      g := g'
      rs := rs.push (v.toNat % m)
    let vals := edges w ++ rs.toList
    let two (name : String) (spec : Nat → Nat → Nat) (t : Tally) (c : Cpu) : Except String (Tally × Cpu) := do
      let mut t := t
      let mut c := c
      for a in vals do
        for b in vals do
          c ← call r (setHL (poke (poke c acc n a) opAddr n b) opAddr) s!"{name}{w}"
          let got := peek c acc n
          t := t.note (got == spec a b % m) fun _ => s!"{name}{w}({a}, {b}) = {got}, expected {spec a b % m}"
      return (t, c)
    (t, c) ← two "rt_add" (· + ·) t c
    (t, c) ← two "rt_sub" (fun a b => a + m - b) t c
    (t, c) ← two "rt_and" (· &&& ·) t c
    (t, c) ← two "rt_or" (· ||| ·) t c
    (t, c) ← two "rt_xor" (· ^^^ ·) t c
    (t, c) ← two "rt_mul" (· * ·) t c
    (t, c) ← two "rt_div" (fun a b => if b == 0 then 0 else a / b) t c
    (t, c) ← two "rt_mod" (fun a b => if b == 0 then 0 else a % b) t c
    for a in vals do
      for b in vals do
        c ← call r (setHL (poke (poke c acc n a) opAddr n b) opAddr) s!"rt_cmp{w}"
        t := t.note (flagZ c == (a == b) && flagC c == (a < b) && peek c acc n == a) fun _ =>
          s!"rt_cmp{w}({a}, {b}): Z = {flagZ c}, C = {flagC c}"
      c ← call r (poke c acc n a) s!"rt_not{w}"
      t := t.note (peek c acc n == m - 1 - a) fun _ => s!"rt_not{w}({a}) = {peek c acc n}"
      c ← call r (poke c acc n a) s!"rt_neg{w}"
      t := t.note (peek c acc n == (m - a) % m) fun _ => s!"rt_neg{w}({a}) = {peek c acc n}"
      c ← call r (poke c acc n a) s!"rt_sat{w}"
      t := t.note (c.a.toNat == (if a > 255 then 255 else a)) fun _ => s!"rt_sat{w}({a}) = {c.a.toNat}"
      for b in [0, 1, 7, 8, 9, 16, 31, 32, 33, 63, 64, 65, 255] do
        c ← call r { poke c acc n a with b := UInt8.ofNat b } s!"rt_shl{w}"
        t := t.note (peek c acc n == (if b ≥ w then 0 else (a <<< b) % m)) fun _ => s!"rt_shl{w}({a}, {b}) = {peek c acc n}"
        c ← call r { poke c acc n a with b := UInt8.ofNat b } s!"rt_shr{w}"
        t := t.note (peek c acc n == (if b ≥ w then 0 else a >>> b)) fun _ => s!"rt_shr{w}({a}, {b}) = {peek c acc n}"
      -- load and store
      c ← call r (setHL (poke (poke c acc n 0) opAddr n a) opAddr) s!"rt_ld{w}"
      t := t.note (peek c acc n == a) fun _ => s!"rt_ld{w}({a}) = {peek c acc n}"
      c ← call r (setHL (poke (poke c acc n a) opAddr n 0) opAddr) s!"rt_st{w}"
      t := t.note (peek c opAddr n == a) fun _ => s!"rt_st{w}({a}) = {peek c opAddr n}"
  -- widening
  for a in edges 16 do
    c ← call r { poke c acc 8 (2 ^ 64 - 1) with a := UInt8.ofNat a } "rt_acc_a"
    t := t.note (peek c acc 8 == a % 256) fun _ => s!"rt_acc_a({a % 256}) = {peek c acc 8}"
    c ← call r (setHL (poke c acc 8 (2 ^ 64 - 1)) a) "rt_acc_hl"
    t := t.note (peek c acc 8 == a) fun _ => s!"rt_acc_hl({a}) = {peek c acc 8}"
  c ← call r (poke c acc 8 (2 ^ 64 - 1)) "rt_zx32"
  t := t.note (peek c acc 8 == 2 ^ 32 - 1) fun _ => s!"rt_zx32 = {peek c acc 8}"
  -- clearing memory
  for n in [1, 2, 3, 255, 256, 257, 700] do
    c := poke (poke c (opAddr - 1) 1 0x55) (opAddr + n) 1 0x55
    for k in [0:n] do c := poke c (opAddr + k) 1 0xFF
    c ← call r { setHL c opAddr with b := UInt8.ofNat (n / 256), c := UInt8.ofNat n } "rt_zero"
    let clear := (List.range n).all fun k => peek c (opAddr + k) 1 == 0
    t := t.note (clear && peek c (opAddr - 1) 1 == 0x55 && peek c (opAddr + n) 1 == 0x55) fun _ => s!"rt_zero({n})"
  return t

end Ember.Z80.RtCheck
