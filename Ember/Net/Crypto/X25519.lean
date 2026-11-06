import Ember.Net.Crypto.ChaCha

/-!
# Ember.Net.Crypto.X25519 — the field of 2^255 - 19 and X25519 in Ember (plan M8.5b)

`Ember.Spec.Crypto.x25519` for small machines, after TweetNaCl: a field
element is 16 limbs of 16 bits, each in a `u64`, in the registers of
`fe` (register `r` is `fe[16 r, 16 r + 16)`).  Ember has no signed
integers, so a subtraction adds `4p` first and no limb goes below zero;
the products of `fe_mul` stay below 2^46.  The ladder swaps with masks
(`fe_cswap`), so which branch is taken never depends on the scalar.

Registers: 0–6 the ladder's `a b c d e f x`, 7 the constant 121665,
8–9 for `fe_mul`/`fe_inv`, 10–11 for packing; 12–33 are Ed25519's.
-/

namespace Ember.Net.Crypto
open Ember.Lang

ember def fe_carry (o : u16) := do
  let b : u16 := o * 16
  for i : u16 in [0, 16) do
    let c : u64 := fe[b + i] >>> 16
    fe[b + i] := fe[b + i] &&& 0xffff
    if i < 15 then
      fe[b + i + 1] := fe[b + i + 1] + c
    else
      fe[b] := fe[b] + 38 * c

ember def fe_copy (o : u16) (a : u16) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := fe[a * 16 + i]

ember def fe_set (o : u16) (v : u64) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := 0
  fe[o * 16] := v

ember def fe_add (o : u16) (a : u16) (b : u16) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := fe[a * 16 + i] + fe[b * 16 + i]

/-- `a - b + 4p`, limb by limb (every limb of `4p` is above any limb of a carried `b`). -/
ember def fe_sub (o : u16) (a : u16) (b : u16) := do
  for i : u16 in [0, 16) do
    let mut q : u64 := 0x3fffc
    if i == 0 then
      q := 0x3ffb4
    if i == 15 then
      q := 0x1fffc
    fe[o * 16 + i] := fe[a * 16 + i] + q - fe[b * 16 + i]
  fe_carry(o)

ember def fe_mul (o : u16) (a : u16) (b : u16) := do
  for i : u16 in [0, 31) do
    fe_t[i] := 0
  for i2 : u16 in [0, 16) do
    for j : u16 in [0, 16) do
      fe_t[i2 + j] := fe_t[i2 + j] + fe[a * 16 + i2] * fe[b * 16 + j]
  for k : u16 in [0, 15) do
    fe_t[k] := fe_t[k] + 38 * fe_t[k + 16]
  for m : u16 in [0, 16) do
    fe[o * 16 + m] := fe_t[m]
  fe_carry(o)
  fe_carry(o)

ember def fe_sq (o : u16) (a : u16) := do
  fe_mul(o, a, a)

/-- Swap registers `p` and `q` when `bit` is 1, with masks. -/
ember def fe_cswap (p : u16) (q : u16) (bit : u64) := do
  let mask : u64 := 0 - bit
  for i : u16 in [0, 16) do
    let dx : u64 := mask &&& (fe[p * 16 + i] ^^^ fe[q * 16 + i])
    fe[p * 16 + i] := fe[p * 16 + i] ^^^ dx
    fe[q * 16 + i] := fe[q * 16 + i] ^^^ dx

/-- `o := a^(p-2)` (the exponent is public: the branch is not on a secret). -/
ember def fe_inv (o : u16) (a : u16) := do
  fe_copy(9, a)
  for k : u16 in [0, 254) do
    let e : u16 := 253 - k
    fe_sq(9, 9)
    if e != 2 && e != 4 then
      fe_mul(9, 9, a)
  fe_copy(o, 9)

/-- 32 little-endian bytes into register `o` (bit 255 dropped). -/
ember def fe_unpack (o : u16) (src : u16) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := (fe_in[src + 2 * i] : u64) + ((fe_in[src + 2 * i + 1] : u64) <<< 8)
  fe[o * 16 + 15] := fe[o * 16 + 15] &&& 0x7fff

/-- Register `a`, reduced below p, as 32 little-endian bytes in `fe_bytes`. -/
ember def fe_pack (a : u16) := do
  let tb : u16 := 160
  let mb : u16 := 176
  fe_copy(10, a)
  fe_carry(10)
  fe_carry(10)
  fe_carry(10)
  for r : u16 in [0, 2) do
    fe[mb] := fe[tb] - 0xffed
    for i : u16 in [1, 15) do
      fe[mb + i] := fe[tb + i] - 0xffff - ((fe[mb + i - 1] >>> 16) &&& 1)
      fe[mb + i - 1] := fe[mb + i - 1] &&& 0xffff
    fe[mb + 15] := fe[tb + 15] - 0x7fff - ((fe[mb + 14] >>> 16) &&& 1)
    let borrow : u64 := (fe[mb + 15] >>> 16) &&& 1
    fe[mb + 14] := fe[mb + 14] &&& 0xffff
    fe_cswap(10, 11, 1 - borrow)
  for j : u16 in [0, 16) do
    fe_bytes[2 * j] := (fe[tb + j] : u8)
    fe_bytes[2 * j + 1] := (fe[tb + j] >>> 8 : u8)

/-- X25519 of the scalar `x_k` and the u-coordinate `fe_in[0, 32)`; the result in `fe_bytes`. -/
ember def x25519 := do
  for i : u16 in [0, 32) do
    x_z[i] := x_k[i]
  x_z[31] := (x_k[31] &&& 127) ||| 64
  x_z[0] := x_z[0] &&& 248
  fe_unpack(6, 0)
  fe_copy(1, 6)
  fe_set(0, 1)
  fe_set(2, 0)
  fe_set(3, 1)
  fe_set(7, 0xdb41)
  let kb : u16 := 112
  fe[kb + 1] := 1
  for k : u16 in [0, 255) do
    let n : u16 := 254 - k
    let bit : u64 := ((x_z[n >>> 3] >>> ((n &&& 7) : u8)) &&& 1 : u64)
    fe_cswap(0, 1, bit)
    fe_cswap(2, 3, bit)
    fe_add(4, 0, 2)
    fe_sub(0, 0, 2)
    fe_add(2, 1, 3)
    fe_sub(1, 1, 3)
    fe_sq(3, 4)
    fe_sq(5, 0)
    fe_mul(0, 2, 0)
    fe_mul(2, 1, 4)
    fe_add(4, 0, 2)
    fe_sub(0, 0, 2)
    fe_sq(1, 0)
    fe_sub(2, 3, 5)
    fe_mul(0, 2, 7)
    fe_add(0, 0, 3)
    fe_mul(2, 2, 0)
    fe_mul(0, 3, 5)
    fe_mul(3, 1, 6)
    fe_sq(1, 4)
    fe_cswap(0, 1, bit)
    fe_cswap(2, 3, bit)
  fe_inv(2, 2)
  fe_mul(0, 0, 2)
  fe_pack(0)

def x25519Globals : List Global :=
  [{ name := "fe", ty := .arr .u64 (16 * 34) }, { name := "fe_t", ty := .arr .u64 31 },
   { name := "fe_in", ty := .arr .u8 64 }, { name := "fe_bytes", ty := .arr .u8 32 },
   { name := "x_k", ty := .arr .u8 32 }, { name := "x_z", ty := .arr .u8 32 }]

def x25519Fns : List Fn :=
  [fe_carry, fe_copy, fe_set, fe_add, fe_sub, fe_mul, fe_sq, fe_cswap, fe_inv, fe_unpack, fe_pack, x25519]

end Ember.Net.Crypto
