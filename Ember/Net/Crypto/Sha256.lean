import Ember.Lang.Surface
import Ember.Spec.Crypto.Sha2

/-!
# Ember.Net.Crypto.Sha256 — SHA-256 in Ember (plan M8.5b)

`Ember.Spec.Crypto.sha256` byte by byte: `sha_init`, `sha_byte b` for each
byte of the message, `sha_final` (the digest in `sh_out`).  One context
(`sh_*`); a computation that needs two at once (HMAC's inner and outer
hash, a transcript hash kept while another is computed) saves and
restores it (`sha_save`, `sha_load`, one spare context `sv_*`).  No branch
depends on the bytes hashed.
-/

namespace Ember.Net.Crypto
open Ember.Lang

ember def rotr (x : u32) (n : u32) : u32 := do
  return (x >>> n) ||| (x <<< (32 - n))

ember def sha_init := do
  sh_h[0] := 0x6a09e667
  sh_h[1] := 0xbb67ae85
  sh_h[2] := 0x3c6ef372
  sh_h[3] := 0xa54ff53a
  sh_h[4] := 0x510e527f
  sh_h[5] := 0x9b05688c
  sh_h[6] := 0x1f83d9ab
  sh_h[7] := 0x5be0cd19
  sh_n := 0
  sh_len := 0

ember def sha_block := do
  for t : u16 in [0, 16) do
    sh_w[t] := ((sh_blk[4 * t] : u32) <<< 24) ||| ((sh_blk[4 * t + 1] : u32) <<< 16) ||| ((sh_blk[4 * t + 2] : u32) <<< 8) ||| (sh_blk[4 * t + 3] : u32)
  for t2 : u16 in [16, 64) do
    let x : u32 := sh_w[t2 - 15]
    let y : u32 := sh_w[t2 - 2]
    let r7 : u32 ← rotr(x, 7)
    let r18 : u32 ← rotr(x, 18)
    let r17 : u32 ← rotr(y, 17)
    let r19 : u32 ← rotr(y, 19)
    let s0 : u32 := r7 ^^^ r18 ^^^ (x >>> 3)
    let s1 : u32 := r17 ^^^ r19 ^^^ (y >>> 10)
    sh_w[t2] := sh_w[t2 - 16] + s0 + sh_w[t2 - 7] + s1
  let mut a : u32 := sh_h[0]
  let mut b : u32 := sh_h[1]
  let mut c : u32 := sh_h[2]
  let mut d : u32 := sh_h[3]
  let mut e : u32 := sh_h[4]
  let mut f : u32 := sh_h[5]
  let mut g : u32 := sh_h[6]
  let mut h : u32 := sh_h[7]
  for t3 : u16 in [0, 64) do
    let e6 : u32 ← rotr(e, 6)
    let e11 : u32 ← rotr(e, 11)
    let e25 : u32 ← rotr(e, 25)
    let ch : u32 := (e &&& f) ^^^ (~~~e &&& g)
    let t1 : u32 := h + (e6 ^^^ e11 ^^^ e25) + ch + SHA_K[t3] + sh_w[t3]
    let a2 : u32 ← rotr(a, 2)
    let a13 : u32 ← rotr(a, 13)
    let a22 : u32 ← rotr(a, 22)
    let maj : u32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let tb : u32 := (a2 ^^^ a13 ^^^ a22) + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + tb
  sh_h[0] := sh_h[0] + a
  sh_h[1] := sh_h[1] + b
  sh_h[2] := sh_h[2] + c
  sh_h[3] := sh_h[3] + d
  sh_h[4] := sh_h[4] + e
  sh_h[5] := sh_h[5] + f
  sh_h[6] := sh_h[6] + g
  sh_h[7] := sh_h[7] + h

/-- A byte into the block, without counting it in the length (padding). -/
ember def sha_put (x : u8) := do
  sh_blk[sh_n] := x
  sh_n := sh_n + 1
  if sh_n == 64 then
    sha_block()
    sh_n := 0

ember def sha_byte (x : u8) := do
  sh_len := sh_len + 1
  sha_put(x)

ember def sha_final := do
  let bits : u32 := sh_len * 8
  let hi : u32 := sh_len >>> 29
  sha_put(0x80)
  loop (max := 64) do
    if sh_n == 56 then
      break
    sha_put(0)
  sha_put(0)
  sha_put(0)
  sha_put(0)
  sha_put((hi : u8))
  sha_put((bits >>> 24 : u8))
  sha_put((bits >>> 16 : u8))
  sha_put((bits >>> 8 : u8))
  sha_put((bits : u8))
  for i : u16 in [0, 8) do
    sh_out[4 * i] := (sh_h[i] >>> 24 : u8)
    sh_out[4 * i + 1] := (sh_h[i] >>> 16 : u8)
    sh_out[4 * i + 2] := (sh_h[i] >>> 8 : u8)
    sh_out[4 * i + 3] := (sh_h[i] : u8)

/-- Keep the context in `sv_*` / take it back. -/
ember def sha_save := do
  for i : u16 in [0, 8) do
    sv_h[i] := sh_h[i]
  for j : u16 in [0, 64) do
    sv_blk[j] := sh_blk[j]
  sv_n := sh_n
  sv_len := sh_len

ember def sha_load := do
  for i : u16 in [0, 8) do
    sh_h[i] := sv_h[i]
  for j : u16 in [0, 64) do
    sh_blk[j] := sv_blk[j]
  sh_n := sv_n
  sh_len := sv_len

/-! ## HMAC-SHA256 and HKDF (RFC 2104, RFC 5869)

The key is `hm_key[0, hm_klen)` (at most 64 bytes; zeros after it).
`hmac_begin`, the message by `sha_byte`, `hmac_end`: the MAC in `sh_out`.
`hkdf_expand n`: `n` bytes (at most 255) of `HKDF-Expand(PRK, info, n)` in
`hk_out`, with PRK in `hm_key` (32 bytes) and info `hk_info[0, hk_ilen)`. -/

ember def hmac_pad (p : u8) := do
  for i : u16 in [0, 64) do
    sha_byte(hm_key[i] ^^^ p)

ember def hmac_begin := do
  sha_init()
  hmac_pad(0x36)

ember def hmac_end := do
  sha_final()
  for i : u16 in [0, 32) do
    hm_in[i] := sh_out[i]
  sha_init()
  hmac_pad(0x5c)
  for j : u16 in [0, 32) do
    sha_byte(hm_in[j])
  sha_final()

/-- A key longer than a block is hashed first (the key is in `hk_out[0, n)`). -/
ember def hmac_key_long (n : u16) := do
  sha_init()
  for i : u16 in [0, n) do
    sha_byte(hk_out[i])
  sha_final()
  for j : u16 in [0, 64) do
    hm_key[j] := 0
  for k : u16 in [0, 32) do
    hm_key[k] := sh_out[k]

/-- HKDF-Extract (RFC 5869 §2.2) is HMAC with the salt as the key: put the
salt in `hm_key` (zeros for none; a salt longer than 64 bytes through
`hmac_key_long`, as any HMAC key), `hmac_begin`, the input keying material
by `sha_byte`, then `hkdf_extract_end` — the PRK in `sh_out`, and in
`hm_key` as the key of a following `hkdf_expand`. -/
ember def hkdf_extract_end := do
  hmac_end()
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  for j : u16 in [0, 32) do
    hm_key[j] := sh_out[j]

ember def hkdf_expand (n : u16) := do
  let mut done : u16 := 0
  let mut ctr : u8 := 1
  loop (max := 8) do
    if done >= n then
      break
    hmac_begin()
    if ctr > 1 then
      for i : u16 in [0, 32) do
        sha_byte(hk_t[i])
    for j : u16 in [0, hk_ilen) do
      sha_byte(hk_info[j])
    sha_byte(ctr)
    hmac_end()
    for k : u16 in [0, 32) do
      hk_t[k] := sh_out[k]
      if done + k < n then
        hk_out[done + k] := sh_out[k]
    done := done + 32
    ctr := ctr + 1

def k256 : List Nat := (Spec.Crypto.k256.toList.map (·.toNat))

def sha256Globals : List Global :=
  [{ name := "SHA_K", ty := .arr .u32 64, init := k256, const := true },
   { name := "sh_h", ty := .arr .u32 8 }, { name := "sh_w", ty := .arr .u32 64 },
   { name := "sh_blk", ty := .arr .u8 64 }, { name := "sh_n", ty := .u16 }, { name := "sh_len", ty := .u32 },
   { name := "sh_out", ty := .arr .u8 32 },
   { name := "sv_h", ty := .arr .u32 8 }, { name := "sv_blk", ty := .arr .u8 64 },
   { name := "sv_n", ty := .u16 }, { name := "sv_len", ty := .u32 },
   { name := "hm_key", ty := .arr .u8 64 }, { name := "hm_in", ty := .arr .u8 32 },
   { name := "hk_t", ty := .arr .u8 32 }, { name := "hk_info", ty := .arr .u8 255 },
   { name := "hk_ilen", ty := .u16 }, { name := "hk_out", ty := .arr .u8 288 }]

def sha256Fns : List Fn := [rotr, sha_init, sha_block, sha_put, sha_byte, sha_final, sha_save, sha_load,
  hmac_pad, hmac_begin, hmac_end, hmac_key_long, hkdf_extract_end, hkdf_expand]

end Ember.Net.Crypto
