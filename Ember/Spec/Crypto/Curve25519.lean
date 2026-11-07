import Ember.Spec.Crypto.ChaCha

/-!
# Ember.Spec.Crypto.Curve25519 — X25519 and Ed25519 (RFC 7748, RFC 8032; plan M8.5)

Reference implementations over `Nat`: the field is `ℕ mod p`, `p = 2^255 - 19`.
They are written as the RFCs state them, for clarity, not for speed
or constant time; the Ember versions are checked against them.
-/

namespace Ember.Spec.Crypto

def p25519 : Nat := 2 ^ 255 - 19

def fpow (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

def finv (x : Nat) : Nat := fpow x (p25519 - 2) p25519

/-! ## X25519 (RFC 7748 §5) -/

def decodeScalar25519 (k : ByteArray) : Nat :=
  let n := leNat (k.extract 0 32)
  (n &&& (2 ^ 255 - 8)) ||| 2 ^ 254

def decodeU (u : ByteArray) : Nat := (leNat (u.extract 0 32) &&& (2 ^ 255 - 1)) % p25519

def x25519 (k u : ByteArray) : ByteArray := Id.run do
  let p := p25519
  let kk := decodeScalar25519 k
  let x1 := decodeU u
  let mut x2 := 1; let mut z2 := 0; let mut x3 := x1; let mut z3 := 1
  let mut swap := 0
  for i in [0:255] do
    let t := 254 - i
    let kt := (kk >>> t) % 2
    swap := swap ^^^ kt
    if swap == 1 then
      (x2, x3) := (x3, x2); (z2, z3) := (z3, z2)
    swap := kt
    let a := (x2 + z2) % p
    let aa := a * a % p
    let b := (x2 + p - z2) % p
    let bb := b * b % p
    let e := (aa + p - bb) % p
    let c := (x3 + z3) % p
    let d := (x3 + p - z3) % p
    let da := d * a % p
    let cb := c * b % p
    x3 := (da + cb) % p; x3 := x3 * x3 % p
    z3 := (da + p - cb) % p; z3 := x1 * (z3 * z3 % p) % p
    x2 := aa * bb % p
    z2 := e * ((aa + 121665 * e) % p) % p
  if swap == 1 then
    (x2, x3) := (x3, x2); (z2, z3) := (z3, z2)
  return natLe (x2 * finv z2 % p) 32

def basepoint9 : ByteArray := natLe 9 32

/-! ## Ed25519 (RFC 8032 §5.1) -/

def edD : Nat := (p25519 - 121665) * finv 121666 % p25519
def edQ : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- Extended coordinates (X, Y, Z, T), x = X/Z, y = Y/Z, xy = T/Z. -/
structure EdPt where
  x : Nat
  y : Nat
  z : Nat
  t : Nat

def edAdd (P Q : EdPt) : EdPt :=
  let p := p25519
  let a := (P.y + p - P.x) * (Q.y + p - Q.x) % p
  let b := (P.y + P.x) * (Q.y + Q.x) % p
  let c := 2 * P.t * Q.t * edD % p
  let d := 2 * P.z * Q.z % p
  let e := (b + p - a) % p
  let f := (d + p - c) % p
  let g := (d + c) % p
  let h := (b + a) % p
  { x := e * f % p, y := g * h % p, t := e * h % p, z := f * g % p }

def edZero : EdPt := { x := 0, y := 1, z := 1, t := 0 }

def edMul (s : Nat) (P : EdPt) : EdPt := Id.run do
  let mut q := edZero
  let mut pp := P
  let mut s := s
  while s > 0 do
    if s % 2 == 1 then q := edAdd q pp
    pp := edAdd pp pp
    s := s / 2
  return q

/-- `P = Q` as projective points: `X₁ Z₂ ≡ X₂ Z₁` and `Y₁ Z₂ ≡ Y₂ Z₁` (mod p).
Each side is reduced on its own: a difference of `Nat`s would stop at 0
and call two different points equal. -/
def edEqual (P Q : EdPt) : Bool :=
  let p := p25519
  (P.x * Q.z) % p == (Q.x * P.z) % p && (P.y * Q.z) % p == (Q.y * P.z) % p

def sqrtM1 : Nat := fpow 2 ((p25519 - 1) / 4) p25519

def recoverX (y sign : Nat) : Option Nat :=
  let p := p25519
  if y ≥ p then none else
  let x2 := (y * y + p - 1) * finv (edD * y * y + 1) % p
  if x2 == 0 then (if sign == 1 then none else some 0) else
  let x := fpow x2 ((p + 3) / 8) p
  let x := if (x * x + p - x2) % p != 0 then x * sqrtM1 % p else x
  if (x * x + p - x2) % p != 0 then none
  else some (if x % 2 != sign then p - x else x)

def edBaseY : Nat := 4 * finv 5 % p25519
def edBase : EdPt :=
  let x := (recoverX edBaseY 0).getD 0
  { x, y := edBaseY, z := 1, t := x * edBaseY % p25519 }

def edCompress (P : EdPt) : ByteArray :=
  let zi := finv P.z
  let x := P.x * zi % p25519
  let y := P.y * zi % p25519
  natLe (y ||| ((x % 2) <<< 255)) 32

def edDecompress (b : ByteArray) : Option EdPt :=
  let n := leNat (b.extract 0 32)
  let y := n &&& (2 ^ 255 - 1)
  let sign := n >>> 255
  (recoverX y sign).map fun x => { x, y, z := 1, t := x * y % p25519 }

def edSecretExpand (sk : ByteArray) : Nat × ByteArray :=
  let h := sha512 (sk.extract 0 32)
  let a := (leNat (h.extract 0 32) &&& (2 ^ 254 - 8)) ||| 2 ^ 254
  (a, h.extract 32 64)

def edPublic (sk : ByteArray) : ByteArray := edCompress (edMul (edSecretExpand sk).1 edBase)

def edSign (sk msg : ByteArray) : ByteArray :=
  let (a, prefix_) := edSecretExpand sk
  let A := edCompress (edMul a edBase)
  let r := leNat (sha512 (prefix_ ++ msg)) % edQ
  let R := edCompress (edMul r edBase)
  let h := leNat (sha512 (R ++ A ++ msg)) % edQ
  let s := (r + h * a) % edQ
  R ++ natLe s 32

def edVerify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false else
  match edDecompress pk, edDecompress (sig.extract 0 32) with
  | some A, some R =>
    let s := leNat (sig.extract 32 64)
    if s ≥ edQ then false else
    let h := leNat (sha512 (sig.extract 0 32 ++ pk ++ msg)) % edQ
    edEqual (edMul s edBase) (edAdd R (edMul h A))
  | _, _ => false

end Ember.Spec.Crypto
