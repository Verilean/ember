import Ember.Spec.Crypto.Curve25519

/-!
# Ember.Spec.Crypto.P256 — ECDSA on P-256 with SHA-256 (FIPS 186-4, RFC 6979; plan M8.8)

The reference for the Ember version: the curve `y² = x³ - 3x + b` over
`p = 2^256 - 2^224 + 2^192 + 2^96 - 1`, affine points over `Nat`
(inverses by Fermat), the nonce made deterministic as RFC 6979 says
(HMAC-SHA256), and the signature in DER (`SEQUENCE { INTEGER r, INTEGER s }`)
as TLS 1.3 carries it (`ecdsa_secp256r1_sha256`).
-/

namespace Ember.Spec.Crypto

def p256 : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
def n256 : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def b256 : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def g256 : Nat × Nat :=
  (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
   0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)

/-- An affine point, or the point at infinity. -/
abbrev Pt := Option (Nat × Nat)

def pInv (x : Nat) : Nat := fpow x (p256 - 2) p256

def ptAdd (P Q : Pt) : Pt :=
  match P, Q with
  | none, q => q
  | p, none => p
  | some (x1, y1), some (x2, y2) =>
    let p := p256
    if x1 == x2 then
      if (y1 + y2) % p == 0 then none
      else
        -- doubling: λ = (3x² - 3) / 2y
        let l := (3 * x1 * x1 + p - 3) % p * pInv (2 * y1 % p) % p
        let x3 := (l * l + 2 * p - 2 * x1) % p
        some (x3, (l * ((x1 + p - x3) % p) + p - y1) % p)
    else
      let l := (y2 + p - y1) % p * pInv ((x2 + p - x1) % p) % p
      let x3 := (l * l + 2 * p - x1 - x2) % p
      some (x3, (l * ((x1 + p - x3) % p) + p - y1) % p)

def ptMul (k : Nat) (P : Pt) : Pt := Id.run do
  let mut r : Pt := none
  let mut q := P
  let mut k := k
  while k > 0 do
    if k % 2 == 1 then r := ptAdd r q
    q := ptAdd q q
    k := k / 2
  return r

def beNat (b : ByteArray) : Nat := b.toList.foldl (fun acc x => acc * 256 + x.toNat) 0
def natBe (n len : Nat) : ByteArray := (natLe n len).toList.reverse.toArray |> ByteArray.mk

/-- The public key of a private scalar, uncompressed: `04 || X || Y`. -/
def p256Public (d : Nat) : ByteArray :=
  match ptMul d (some g256) with
  | some (x, y) => ByteArray.mk #[4] ++ natBe x 32 ++ natBe y 32
  | none => .empty

/-- The nonces of RFC 6979 §3.2 for the private key `d` and the hash `h1`, in order. -/
def rfc6979 (d : Nat) (h1 : ByteArray) (count : Nat) : List Nat := Id.run do
  let x := natBe d 32
  let h := natBe (beNat h1 % n256) 32
  let mut v := ByteArray.mk (Array.replicate 32 1)
  let mut k := ByteArray.mk (Array.replicate 32 0)
  k := hmac256 k (v ++ ByteArray.mk #[0] ++ x ++ h)
  v := hmac256 k v
  k := hmac256 k (v ++ ByteArray.mk #[1] ++ x ++ h)
  v := hmac256 k v
  let mut out := []
  let mut tries := 0
  while out.length < count && tries < 64 do
    tries := tries + 1
    v := hmac256 k v
    let t := beNat v
    if 1 ≤ t && t < n256 then out := out ++ [t]
    k := hmac256 k (v ++ ByteArray.mk #[0])
    v := hmac256 k v
  return out

/-- ECDSA over the SHA-256 of `msg` with the private scalar `d`: `(r, s)`. -/
def p256SignRS (d : Nat) (msg : ByteArray) : Nat × Nat := Id.run do
  let h1 := sha256 msg
  let z := beNat h1
  for k in rfc6979 d h1 8 do
    match ptMul k (some g256) with
    | none => pure ()
    | some (x, _) =>
      let r := x % n256
      if r == 0 then continue
      let s := fpow k (n256 - 2) n256 * ((z + r * d) % n256) % n256
      if s == 0 then continue
      return (r, s)
  return (0, 0)

/-- A DER INTEGER: big-endian, no leading zeros, a zero byte before a high bit. -/
def derInt (v : Nat) : ByteArray :=
  let b := (natBe v 32).toList.dropWhile (· == 0)
  let b := if b.isEmpty then [0] else b
  let b := if b.head! ≥ 0x80 then 0 :: b else b
  ByteArray.mk #[2, UInt8.ofNat b.length] ++ ByteArray.mk b.toArray

def p256Sign (d : Nat) (msg : ByteArray) : ByteArray :=
  let (r, s) := p256SignRS d msg
  let body := derInt r ++ derInt s
  ByteArray.mk #[0x30, UInt8.ofNat body.size] ++ body

/-- Is `(x, y)` on the curve, with both coordinates below `p`? -/
def onCurve (x y : Nat) : Bool :=
  x < p256 && y < p256 && y * y % p256 == (x * x * x + 3 * (p256 - 1) * x + b256) % p256

/-- Verification on the hash `h` (32 bytes) with the public key `pub`
(`04 ‖ X ‖ Y`): `r`, `s` in [1, n), the key on the curve, `R = u1·G + u2·Q`
not the point at infinity and `x(R) mod n = r` (FIPS 186-4 §6.4). -/
def p256VerifyHash (pub h : ByteArray) (r s : Nat) : Bool :=
  if pub.size != 65 || r == 0 || s == 0 || r ≥ n256 || s ≥ n256 then false else
  let qx := beNat (pub.extract 1 33)
  let qy := beNat (pub.extract 33 65)
  if !onCurve qx qy then false else
  let z := beNat h % n256
  let w := fpow s (n256 - 2) n256
  match ptAdd (ptMul (z * w % n256) (some g256)) (ptMul (r * w % n256) (some (qx, qy))) with
  | some (x, _) => x % n256 == r
  | none => false

/-- Verification of a message (ECDSA P-256 with SHA-256). -/
def p256Verify (pub msg : ByteArray) (r s : Nat) : Bool :=
  p256VerifyHash pub (sha256 msg) r s

/-! ## Complete projective addition (Renes, Costello, Batina 2016, Algorithm 4; a = -3)

The form the Ember version computes: no case for the point at infinity
or for doubling, so a ladder over it branches on no bit of the scalar.
Checked against `ptMul` in the tests. -/

/-- Projective `(X : Y : Z)`; the point at infinity is `(0 : 1 : 0)`. -/
structure PPt where
  x : Nat
  y : Nat
  z : Nat

def ppAdd (P Q : PPt) : PPt := Id.run do
  let p := p256
  let mul (a b : Nat) := a * b % p
  let add (a b : Nat) := (a + b) % p
  let sub (a b : Nat) := (a + p - b) % p
  let mut t0 := mul P.x Q.x
  let mut t1 := mul P.y Q.y
  let mut t2 := mul P.z Q.z
  let mut t3 := add P.x P.y
  let mut t4 := add Q.x Q.y
  t3 := mul t3 t4
  t4 := add t0 t1
  t3 := sub t3 t4
  t4 := add P.y P.z
  let mut x3 := add Q.y Q.z
  t4 := mul t4 x3
  x3 := add t1 t2
  t4 := sub t4 x3
  x3 := add P.x P.z
  let mut y3 := add Q.x Q.z
  x3 := mul x3 y3
  y3 := add t0 t2
  y3 := sub x3 y3
  let mut z3 := mul b256 t2
  x3 := sub y3 z3
  z3 := add x3 x3
  x3 := add x3 z3
  z3 := sub t1 x3
  x3 := add t1 x3
  y3 := mul b256 y3
  t1 := add t2 t2
  t2 := add t1 t2
  y3 := sub y3 t2
  y3 := sub y3 t0
  t1 := add y3 y3
  y3 := add t1 y3
  t1 := add t0 t0
  t0 := add t1 t0
  t0 := sub t0 t2
  t1 := mul t4 y3
  t2 := mul t0 y3
  y3 := mul x3 z3
  y3 := add y3 t2
  x3 := mul t3 x3
  x3 := sub x3 t1
  z3 := mul t4 z3
  t1 := mul t3 t0
  z3 := add z3 t1
  return { x := x3, y := y3, z := z3 }

/-- `k·G` by a ladder over `ppAdd` (256 steps whatever `k`), in affine coordinates. -/
def ppMulG (k : Nat) : Pt := Id.run do
  let mut r0 : PPt := { x := 0, y := 1, z := 0 }
  let mut r1 : PPt := { x := g256.1, y := g256.2, z := 1 }
  for i in [0:256] do
    let bit := (k >>> (255 - i)) % 2
    if bit == 1 then (r0, r1) := (r1, r0)
    r1 := ppAdd r0 r1
    r0 := ppAdd r0 r0
    if bit == 1 then (r0, r1) := (r1, r0)
  if r0.z == 0 then return none
  let zi := pInv r0.z
  return some (r0.x * zi % p256, r0.y * zi % p256)

end Ember.Spec.Crypto
