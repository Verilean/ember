import Ember.Net.Crypto.X25519

/-!
# Ember.Net.Crypto.Sha512 — SHA-512 in Ember (plan M8.5b)

`Ember.Spec.Crypto.sha512` byte by byte, as `Sha256`: `s5_init`,
`s5_byte`, `s5_final` (the digest in `s5_out`).  For Ed25519, which hashes
at most a few hundred bytes, the length is counted in a `u32`.
-/

namespace Ember.Net.Crypto
open Ember.Lang

ember def rotr64 (x : u64) (n : u64) : u64 := do
  return (x >>> n) ||| (x <<< (64 - n))

ember def s5_init := do
  s5_h[0] := 0x6a09e667f3bcc908
  s5_h[1] := 0xbb67ae8584caa73b
  s5_h[2] := 0x3c6ef372fe94f82b
  s5_h[3] := 0xa54ff53a5f1d36f1
  s5_h[4] := 0x510e527fade682d1
  s5_h[5] := 0x9b05688c2b3e6c1f
  s5_h[6] := 0x1f83d9abfb41bd6b
  s5_h[7] := 0x5be0cd19137e2179
  s5_n := 0
  s5_len := 0

ember def s5_block := do
  for t : u16 in [0, 16) do
    let mut w : u64 := 0
    for b : u16 in [0, 8) do
      w := (w <<< 8) ||| (s5_blk[8 * t + b] : u64)
    s5_w[t] := w
  for t2 : u16 in [16, 80) do
    let x : u64 := s5_w[t2 - 15]
    let y : u64 := s5_w[t2 - 2]
    let r1 : u64 ← rotr64(x, 1)
    let r8 : u64 ← rotr64(x, 8)
    let r19 : u64 ← rotr64(y, 19)
    let r61 : u64 ← rotr64(y, 61)
    s5_w[t2] := s5_w[t2 - 16] + (r1 ^^^ r8 ^^^ (x >>> 7)) + s5_w[t2 - 7] + (r19 ^^^ r61 ^^^ (y >>> 6))
  let mut a : u64 := s5_h[0]
  let mut b2 : u64 := s5_h[1]
  let mut c : u64 := s5_h[2]
  let mut d : u64 := s5_h[3]
  let mut e : u64 := s5_h[4]
  let mut f : u64 := s5_h[5]
  let mut g : u64 := s5_h[6]
  let mut h : u64 := s5_h[7]
  for t3 : u16 in [0, 80) do
    let e14 : u64 ← rotr64(e, 14)
    let e18 : u64 ← rotr64(e, 18)
    let e41 : u64 ← rotr64(e, 41)
    let ch : u64 := (e &&& f) ^^^ (~~~e &&& g)
    let t1 : u64 := h + (e14 ^^^ e18 ^^^ e41) + ch + SHA5_K[t3] + s5_w[t3]
    let a28 : u64 ← rotr64(a, 28)
    let a34 : u64 ← rotr64(a, 34)
    let a39 : u64 ← rotr64(a, 39)
    let maj : u64 := (a &&& b2) ^^^ (a &&& c) ^^^ (b2 &&& c)
    let tb : u64 := (a28 ^^^ a34 ^^^ a39) + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b2
    b2 := a
    a := t1 + tb
  s5_h[0] := s5_h[0] + a
  s5_h[1] := s5_h[1] + b2
  s5_h[2] := s5_h[2] + c
  s5_h[3] := s5_h[3] + d
  s5_h[4] := s5_h[4] + e
  s5_h[5] := s5_h[5] + f
  s5_h[6] := s5_h[6] + g
  s5_h[7] := s5_h[7] + h

ember def s5_put (x : u8) := do
  s5_blk[s5_n] := x
  s5_n := s5_n + 1
  if s5_n == 128 then
    s5_block()
    s5_n := 0

ember def s5_byte (x : u8) := do
  s5_len := s5_len + 1
  s5_put(x)

ember def s5_final := do
  let bits : u32 := s5_len * 8
  let hi : u32 := s5_len >>> 29
  s5_put(0x80)
  loop (max := 128) do
    if s5_n == 112 then
      break
    s5_put(0)
  for z : u16 in [0, 11) do
    s5_put(0)
  s5_put((hi : u8))
  s5_put((bits >>> 24 : u8))
  s5_put((bits >>> 16 : u8))
  s5_put((bits >>> 8 : u8))
  s5_put((bits : u8))
  for i : u16 in [0, 8) do
    for j : u16 in [0, 8) do
      s5_out[8 * i + j] := (s5_h[i] >>> (56 - 8 * (j : u64)) : u8)

def k512 : List Nat := Spec.Crypto.k512.toList.map (·.toNat)

def sha512Globals : List Global :=
  [{ name := "SHA5_K", ty := .arr .u64 80, init := k512, const := true },
   { name := "s5_h", ty := .arr .u64 8 }, { name := "s5_w", ty := .arr .u64 80 },
   { name := "s5_blk", ty := .arr .u8 128 }, { name := "s5_n", ty := .u16 }, { name := "s5_len", ty := .u32 },
   { name := "s5_out", ty := .arr .u8 64 }]

def sha512Fns : List Fn := [rotr64, s5_init, s5_block, s5_put, s5_byte, s5_final]

end Ember.Net.Crypto
