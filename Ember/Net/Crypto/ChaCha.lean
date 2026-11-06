import Ember.Net.Crypto.Sha256
import Ember.Spec.Crypto.ChaCha

/-!
# Ember.Net.Crypto.ChaCha — ChaCha20, Poly1305 and their AEAD in Ember (plan M8.5b)

`Ember.Spec.Crypto.{chacha20, poly1305, aeadSeal}` written for small
machines:

* ChaCha20: the key in `cc_key`, the nonce in `cc_nonce`, the block
  counter `cc_ctr`; `chacha_block` puts 64 bytes of key stream in `cc_ks`.
* Poly1305: five 26-bit limbs, products in `u64`; `poly_init` (one-time
  key in `pk_key`), `poly_byte`, `poly_final` (the tag in `pk_tag`).  The
  final reduction selects with masks, not branches.
-/

namespace Ember.Net.Crypto
open Ember.Lang

ember def le32k (off : u16) : u32 := do
  return (cc_key[off] : u32) ||| ((cc_key[off + 1] : u32) <<< 8) ||| ((cc_key[off + 2] : u32) <<< 16) ||| ((cc_key[off + 3] : u32) <<< 24)

ember def rotl (x : u32) (n : u32) : u32 := do
  return (x <<< n) ||| (x >>> (32 - n))

ember def qr (a : u16) (b : u16) (c : u16) (d : u16) := do
  cc_x[a] := cc_x[a] + cc_x[b]
  let d1 : u32 ← rotl(cc_x[d] ^^^ cc_x[a], 16)
  cc_x[d] := d1
  cc_x[c] := cc_x[c] + cc_x[d]
  let b1 : u32 ← rotl(cc_x[b] ^^^ cc_x[c], 12)
  cc_x[b] := b1
  cc_x[a] := cc_x[a] + cc_x[b]
  let d2 : u32 ← rotl(cc_x[d] ^^^ cc_x[a], 8)
  cc_x[d] := d2
  cc_x[c] := cc_x[c] + cc_x[d]
  let b2 : u32 ← rotl(cc_x[b] ^^^ cc_x[c], 7)
  cc_x[b] := b2

ember def chacha_block := do
  cc_s[0] := 0x61707865
  cc_s[1] := 0x3320646e
  cc_s[2] := 0x79622d32
  cc_s[3] := 0x6b206574
  for i : u16 in [0, 8) do
    let w : u32 ← le32k(4 * i)
    cc_s[4 + i] := w
  cc_s[12] := cc_ctr
  for j : u16 in [0, 3) do
    cc_s[13 + j] := (cc_nonce[4 * j] : u32) ||| ((cc_nonce[4 * j + 1] : u32) <<< 8) ||| ((cc_nonce[4 * j + 2] : u32) <<< 16) ||| ((cc_nonce[4 * j + 3] : u32) <<< 24)
  for k : u16 in [0, 16) do
    cc_x[k] := cc_s[k]
  for r : u16 in [0, 10) do
    qr(0, 4, 8, 12)
    qr(1, 5, 9, 13)
    qr(2, 6, 10, 14)
    qr(3, 7, 11, 15)
    qr(0, 5, 10, 15)
    qr(1, 6, 11, 12)
    qr(2, 7, 8, 13)
    qr(3, 4, 9, 14)
  for m : u16 in [0, 16) do
    let v : u32 := cc_x[m] + cc_s[m]
    cc_ks[4 * m] := (v : u8)
    cc_ks[4 * m + 1] := (v >>> 8 : u8)
    cc_ks[4 * m + 2] := (v >>> 16 : u8)
    cc_ks[4 * m + 3] := (v >>> 24 : u8)

/-! ## Poly1305 -/

ember def pk32 (off : u16) : u32 := do
  return (pk_key[off] : u32) ||| ((pk_key[off + 1] : u32) <<< 8) ||| ((pk_key[off + 2] : u32) <<< 16) ||| ((pk_key[off + 3] : u32) <<< 24)

ember def pm32 (off : u16) : u32 := do
  return (pk_m[off] : u32) ||| ((pk_m[off + 1] : u32) <<< 8) ||| ((pk_m[off + 2] : u32) <<< 16) ||| ((pk_m[off + 3] : u32) <<< 24)

ember def poly_init := do
  let t0 : u32 ← pk32(0)
  let t1 : u32 ← pk32(3)
  let t2 : u32 ← pk32(6)
  let t3 : u32 ← pk32(9)
  let t4 : u32 ← pk32(12)
  pk_r[0] := t0 &&& 0x3ffffff
  pk_r[1] := (t1 >>> 2) &&& 0x3ffff03
  pk_r[2] := (t2 >>> 4) &&& 0x3ffc0ff
  pk_r[3] := (t3 >>> 6) &&& 0x3f03fff
  pk_r[4] := (t4 >>> 8) &&& 0x00fffff
  for i : u16 in [0, 5) do
    pk_h[i] := 0
  pk_n := 0

/-- One block of `pk_m`; `hibit` is `1 << 24` for a whole block, 0 for the last, padded one. -/
ember def poly_block (hibit : u32) := do
  let m0 : u32 ← pm32(0)
  let m1 : u32 ← pm32(3)
  let m2 : u32 ← pm32(6)
  let m3 : u32 ← pm32(9)
  let m4 : u32 ← pm32(12)
  let h0 : u64 := (pk_h[0] + (m0 &&& 0x3ffffff) : u64)
  let h1 : u64 := (pk_h[1] + ((m1 >>> 2) &&& 0x3ffffff) : u64)
  let h2 : u64 := (pk_h[2] + ((m2 >>> 4) &&& 0x3ffffff) : u64)
  let h3 : u64 := (pk_h[3] + ((m3 >>> 6) &&& 0x3ffffff) : u64)
  let h4 : u64 := (pk_h[4] + ((m4 >>> 8) ||| hibit) : u64)
  let r0 : u64 := (pk_r[0] : u64)
  let r1 : u64 := (pk_r[1] : u64)
  let r2 : u64 := (pk_r[2] : u64)
  let r3 : u64 := (pk_r[3] : u64)
  let r4 : u64 := (pk_r[4] : u64)
  let s1 : u64 := r1 * 5
  let s2 : u64 := r2 * 5
  let s3 : u64 := r3 * 5
  let s4 : u64 := r4 * 5
  let mut d0 : u64 := h0 * r0 + h1 * s4 + h2 * s3 + h3 * s2 + h4 * s1
  let mut d1 : u64 := h0 * r1 + h1 * r0 + h2 * s4 + h3 * s3 + h4 * s2
  let mut d2 : u64 := h0 * r2 + h1 * r1 + h2 * r0 + h3 * s4 + h4 * s3
  let mut d3 : u64 := h0 * r3 + h1 * r2 + h2 * r1 + h3 * r0 + h4 * s4
  let mut d4 : u64 := h0 * r4 + h1 * r3 + h2 * r2 + h3 * r1 + h4 * r0
  let mut c : u64 := d0 >>> 26
  pk_h[0] := (d0 &&& 0x3ffffff : u32)
  d1 := d1 + c
  c := d1 >>> 26
  pk_h[1] := (d1 &&& 0x3ffffff : u32)
  d2 := d2 + c
  c := d2 >>> 26
  pk_h[2] := (d2 &&& 0x3ffffff : u32)
  d3 := d3 + c
  c := d3 >>> 26
  pk_h[3] := (d3 &&& 0x3ffffff : u32)
  d4 := d4 + c
  c := d4 >>> 26
  pk_h[4] := (d4 &&& 0x3ffffff : u32)
  pk_h[0] := pk_h[0] + (c : u32) * 5
  let c2 : u32 := pk_h[0] >>> 26
  pk_h[0] := pk_h[0] &&& 0x3ffffff
  pk_h[1] := pk_h[1] + c2

ember def poly_byte (x : u8) := do
  pk_m[pk_n] := x
  pk_n := pk_n + 1
  if pk_n == 16 then
    poly_block(0x1000000)
    pk_n := 0

ember def poly_final := do
  if pk_n > 0 then
    pk_m[pk_n] := 1
    for i : u16 in [pk_n + 1, 16) do
      pk_m[i] := 0
    poly_block(0)
  let mut h0 : u32 := pk_h[0]
  let mut h1 : u32 := pk_h[1]
  let mut h2 : u32 := pk_h[2]
  let mut h3 : u32 := pk_h[3]
  let mut h4 : u32 := pk_h[4]
  let mut c : u32 := h1 >>> 26
  h1 := h1 &&& 0x3ffffff
  h2 := h2 + c
  c := h2 >>> 26
  h2 := h2 &&& 0x3ffffff
  h3 := h3 + c
  c := h3 >>> 26
  h3 := h3 &&& 0x3ffffff
  h4 := h4 + c
  c := h4 >>> 26
  h4 := h4 &&& 0x3ffffff
  h0 := h0 + c * 5
  c := h0 >>> 26
  h0 := h0 &&& 0x3ffffff
  h1 := h1 + c
  -- h - p, selected without a branch
  let mut g0 : u32 := h0 + 5
  c := g0 >>> 26
  g0 := g0 &&& 0x3ffffff
  let mut g1 : u32 := h1 + c
  c := g1 >>> 26
  g1 := g1 &&& 0x3ffffff
  let mut g2 : u32 := h2 + c
  c := g2 >>> 26
  g2 := g2 &&& 0x3ffffff
  let mut g3 : u32 := h3 + c
  c := g3 >>> 26
  g3 := g3 &&& 0x3ffffff
  let g4 : u32 := h4 + c - 0x4000000
  let mask : u32 := (g4 >>> 31) - 1
  let nmask : u32 := ~~~mask
  h0 := (h0 &&& nmask) ||| (g0 &&& mask)
  h1 := (h1 &&& nmask) ||| (g1 &&& mask)
  h2 := (h2 &&& nmask) ||| (g2 &&& mask)
  h3 := (h3 &&& nmask) ||| (g3 &&& mask)
  h4 := (h4 &&& nmask) ||| (g4 &&& mask)
  let w0 : u32 := h0 ||| (h1 <<< 26)
  let w1 : u32 := (h1 >>> 6) ||| (h2 <<< 20)
  let w2 : u32 := (h2 >>> 12) ||| (h3 <<< 14)
  let w3 : u32 := (h3 >>> 18) ||| (h4 <<< 8)
  let k0 : u32 ← pk32(16)
  let k1 : u32 ← pk32(20)
  let k2 : u32 ← pk32(24)
  let k3 : u32 ← pk32(28)
  let mut f : u64 := (w0 : u64) + (k0 : u64)
  let o0 : u32 := (f : u32)
  f := (w1 : u64) + (k1 : u64) + (f >>> 32)
  let o1 : u32 := (f : u32)
  f := (w2 : u64) + (k2 : u64) + (f >>> 32)
  let o2 : u32 := (f : u32)
  f := (w3 : u64) + (k3 : u64) + (f >>> 32)
  let o3 : u32 := (f : u32)
  for j : u16 in [0, 4) do
    pk_tag[j] := (o0 >>> (8 * (j : u32)) : u8)
    pk_tag[4 + j] := (o1 >>> (8 * (j : u32)) : u8)
    pk_tag[8 + j] := (o2 >>> (8 * (j : u32)) : u8)
    pk_tag[12 + j] := (o3 >>> (8 * (j : u32)) : u8)

/-! ## AEAD_CHACHA20_POLY1305: the one-time key, and the MAC's padding and lengths -/

/-- Poly1305's key from block 0 of the key stream (`cc_key`, `cc_nonce` set); `cc_ctr := 1`. -/
ember def aead_begin := do
  cc_ctr := 0
  chacha_block()
  for i : u16 in [0, 32) do
    pk_key[i] := cc_ks[i]
  poly_init()
  cc_ctr := 1

/-- Zeros to the next multiple of 16 in the MAC's input. -/
ember def poly_pad := do
  loop (max := 16) do
    if pk_n == 0 then
      break
    poly_byte(0)

ember def poly_len64 (n : u32) := do
  for i : u16 in [0, 8) do
    if i < 4 then
      poly_byte((n >>> (8 * (i : u32)) : u8))
    else
      poly_byte(0)

/-- AEAD opening: `ae_buf[0, n)` holds the cipher text and `ae_tag` the
received tag (`cc_key`, `cc_nonce` set, the AAD already through
`aead_begin`, `poly_byte`, `poly_pad`).  The plain text replaces the
cipher text in `ae_buf`; the result is whether the tag matches, compared
without a branch on any byte.  A caller must not use `ae_buf` when it is
`false`. -/
ember def aead_open (n : u16) (aadlen : u16) : bool := do
  let mut k : u16 := 64
  for i : u16 in [0, n) do
    if k == 64 then
      chacha_block()
      cc_ctr := cc_ctr + 1
      k := 0
    poly_byte(ae_buf[i])
    ae_buf[i] := ae_buf[i] ^^^ cc_ks[k]
    k := k + 1
  poly_pad()
  poly_len64((aadlen : u32))
  poly_len64((n : u32))
  poly_final()
  let mut diff : u8 := 0
  for j : u16 in [0, 16) do
    diff := diff ||| (pk_tag[j] ^^^ ae_tag[j])
  return diff == 0

def chachaGlobals : List Global :=
  [{ name := "cc_key", ty := .arr .u8 32 }, { name := "cc_nonce", ty := .arr .u8 12 },
   { name := "cc_ctr", ty := .u32 }, { name := "cc_s", ty := .arr .u32 16 }, { name := "cc_x", ty := .arr .u32 16 },
   { name := "cc_ks", ty := .arr .u8 64 },
   { name := "pk_key", ty := .arr .u8 32 }, { name := "pk_r", ty := .arr .u32 5 }, { name := "pk_h", ty := .arr .u32 5 },
   { name := "pk_m", ty := .arr .u8 16 }, { name := "pk_n", ty := .u16 }, { name := "pk_tag", ty := .arr .u8 16 },
   { name := "ae_buf", ty := .arr .u8 1024 }, { name := "ae_tag", ty := .arr .u8 16 }]

def chachaFns : List Fn :=
  [le32k, rotl, qr, chacha_block, pk32, pm32, poly_init, poly_block, poly_byte, poly_final, aead_begin, poly_pad, poly_len64,
   aead_open]

end Ember.Net.Crypto
