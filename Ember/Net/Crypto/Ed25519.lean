import Ember.Net.Crypto.Sha512
import Ember.Spec.Crypto.Curve25519

/-!
# Ember.Net.Crypto.Ed25519 — Ed25519 signatures in Ember (plan M8.5b)

`Ember.Spec.Crypto.edSign` after TweetNaCl, on the field registers of
`X25519` (registers 12–33 are the points and the temporaries here):

* points in extended coordinates (X, Y, Z, T), 4 registers each:
  P = 12–15 (the result), Q = 16–19, the temporaries 20–28, 2d in 29;
* `ed_mul_base`: P := s·B with s in `ed_s`, a ladder that swaps with
  masks — the bits of the (secret) scalar choose no branch;
* scalars mod L: `sc_reduce` reduces the 64 bytes of `sc_in` bit by bit
  (2·rem + bit, then a subtraction of L kept or not by a mask);
  `sc_muladd` puts (r + k·a) mod L in `sc_out`.

`ed_sign` signs `ed_msg[0, ed_mlen)` with the secret seed `ed_sk`; the
signature in `ed_sig`.  The base point and 2d are constants computed
from `Ember.Spec.Crypto` when the program is built.
-/

namespace Ember.Net.Crypto
open Ember.Lang

/-- Register `r` of point `p` (its base register). -/
ember def ed_padd (p : u16) (q : u16) := do
  fe_sub(20, p + 1, p)
  fe_sub(24, q + 1, q)
  fe_mul(20, 20, 24)
  fe_add(21, p, p + 1)
  fe_add(24, q, q + 1)
  fe_mul(21, 21, 24)
  fe_mul(22, p + 3, q + 3)
  fe_mul(22, 22, 29)
  fe_mul(23, p + 2, q + 2)
  fe_add(23, 23, 23)
  fe_sub(25, 21, 20)
  fe_sub(26, 23, 22)
  fe_add(27, 23, 22)
  fe_add(28, 21, 20)
  fe_mul(p, 25, 26)
  fe_mul(p + 1, 28, 27)
  fe_mul(p + 2, 27, 26)
  fe_mul(p + 3, 25, 28)

ember def ed_pcswap (p : u16) (q : u16) (bit : u64) := do
  for i : u16 in [0, 4) do
    fe_cswap(p + i, q + i, bit)

ember def fe_load_const (o : u16) (which : u16) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := ED_C[which * 16 + i]

/-- P := s·B, s the 32 little-endian bytes of `ed_s`. -/
ember def ed_mul_base := do
  fe_load_const(29, 2)
  fe_set(12, 0)
  fe_set(13, 1)
  fe_set(14, 1)
  fe_set(15, 0)
  fe_load_const(16, 0)
  fe_load_const(17, 1)
  fe_set(18, 1)
  fe_mul(19, 16, 17)
  for k : u16 in [0, 256) do
    let n : u16 := 255 - k
    let bit : u64 := ((ed_s[n >>> 3] >>> ((n &&& 7) : u8)) &&& 1 : u64)
    ed_pcswap(12, 16, bit)
    ed_padd(16, 12)
    ed_padd(12, 12)
    ed_pcswap(12, 16, bit)

/-- The 32-byte encoding of P in `ed_enc`. -/
ember def ed_pack := do
  fe_inv(30, 14)
  fe_mul(31, 12, 30)
  fe_mul(32, 13, 30)
  fe_pack(31)
  let par : u8 := fe_bytes[0] &&& 1
  fe_pack(32)
  for i : u16 in [0, 32) do
    ed_enc[i] := fe_bytes[i]
  ed_enc[31] := ed_enc[31] ^^^ (par <<< 7)

/-! ## Scalars mod L -/

/-- `sc_out` := `sc_in` (64 bytes, little-endian) mod L. -/
ember def sc_reduce := do
  for i : u16 in [0, 9) do
    sc_rem[i] := 0
  for k : u16 in [0, 512) do
    let n : u16 := 511 - k
    let bit : u32 := ((sc_in[n >>> 3] >>> ((n &&& 7) : u8)) &&& 1 : u32)
    -- rem := 2 rem + bit
    let mut c : u32 := bit
    for j : u16 in [0, 9) do
      let v : u32 := sc_rem[j]
      sc_rem[j] := (v <<< 1) ||| c
      c := v >>> 31
    -- t := rem - L; keep it when there was no borrow
    let mut borrow : u64 := 0
    for j2 : u16 in [0, 9) do
      let d : u64 := (sc_rem[j2] : u64) - (SC_L[j2] : u64) - borrow
      sc_t[j2] := (d : u32)
      borrow := (d >>> 63) &&& 1
    let keep : u32 := (borrow : u32) - 1
    for j3 : u16 in [0, 9) do
      sc_rem[j3] := (sc_t[j3] &&& keep) ||| (sc_rem[j3] &&& ~~~keep)
  for m : u16 in [0, 8) do
    sc_out[4 * m] := (sc_rem[m] : u8)
    sc_out[4 * m + 1] := (sc_rem[m] >>> 8 : u8)
    sc_out[4 * m + 2] := (sc_rem[m] >>> 16 : u8)
    sc_out[4 * m + 3] := (sc_rem[m] >>> 24 : u8)

/-- `sc_out` := (`sc_r` + `sc_k` · `sc_a`) mod L (each 32 bytes). -/
ember def sc_muladd := do
  for i : u16 in [0, 64) do
    sc_acc[i] := 0
  for i2 : u16 in [0, 32) do
    for j : u16 in [0, 32) do
      sc_acc[i2 + j] := sc_acc[i2 + j] + (sc_k[i2] : u32) * (sc_a[j] : u32)
  for i3 : u16 in [0, 32) do
    sc_acc[i3] := sc_acc[i3] + (sc_r[i3] : u32)
  let mut c : u32 := 0
  for m : u16 in [0, 64) do
    let v : u32 := sc_acc[m] + c
    sc_in[m] := (v : u8)
    c := v >>> 8
  sc_reduce()

/-! ## Signing -/

ember def ed_sign := do
  -- the secret scalar a and the prefix
  s5_init()
  for i : u16 in [0, 32) do
    s5_byte(ed_sk[i])
  s5_final()
  for j : u16 in [0, 32) do
    sc_a[j] := s5_out[j]
    ed_prefix[j] := s5_out[32 + j]
  sc_a[0] := sc_a[0] &&& 248
  sc_a[31] := (sc_a[31] &&& 127) ||| 64
  -- A = a·B
  for j2 : u16 in [0, 32) do
    ed_s[j2] := sc_a[j2]
  ed_mul_base()
  ed_pack()
  for j3 : u16 in [0, 32) do
    ed_pub[j3] := ed_enc[j3]
  -- r = H(prefix || M) mod L, R = r·B
  s5_init()
  for j4 : u16 in [0, 32) do
    s5_byte(ed_prefix[j4])
  for k : u16 in [0, ed_mlen) do
    s5_byte(ed_msg[k])
  s5_final()
  for k2 : u16 in [0, 64) do
    sc_in[k2] := s5_out[k2]
  sc_reduce()
  for k3 : u16 in [0, 32) do
    sc_r[k3] := sc_out[k3]
    ed_s[k3] := sc_out[k3]
  ed_mul_base()
  ed_pack()
  for k4 : u16 in [0, 32) do
    ed_sig[k4] := ed_enc[k4]
  -- k = H(R || A || M) mod L, S = r + k·a
  s5_init()
  for m : u16 in [0, 32) do
    s5_byte(ed_sig[m])
  for m2 : u16 in [0, 32) do
    s5_byte(ed_pub[m2])
  for m3 : u16 in [0, ed_mlen) do
    s5_byte(ed_msg[m3])
  s5_final()
  for m4 : u16 in [0, 64) do
    sc_in[m4] := s5_out[m4]
  sc_reduce()
  for m5 : u16 in [0, 32) do
    sc_k[m5] := sc_out[m5]
  sc_muladd()
  for m6 : u16 in [0, 32) do
    ed_sig[32 + m6] := sc_out[m6]

/-! ## Constants and globals -/

open Ember.Spec.Crypto in
/-- Limbs of 16 bits of a field element. -/
def limbs16 (n : Nat) : List Nat := (List.range 16).map fun i => (n >>> (16 * i)) % 65536

open Ember.Spec.Crypto in
/-- B.x, B.y, 2d: the constants of `ed_mul_base` and `ed_padd`. -/
def edConsts : List Nat :=
  let b := edBase
  limbs16 (b.x % p25519) ++ limbs16 (b.y % p25519) ++ limbs16 (2 * edD % p25519)

open Ember.Spec.Crypto in
def scL : List Nat := (List.range 9).map fun i => (edQ >>> (32 * i)) % 2 ^ 32

def ed25519Globals : List Global :=
  [{ name := "ED_C", ty := .arr .u64 48, init := edConsts, const := true },
   { name := "SC_L", ty := .arr .u32 9, init := scL, const := true },
   { name := "ed_s", ty := .arr .u8 32 }, { name := "ed_enc", ty := .arr .u8 32 },
   { name := "ed_sk", ty := .arr .u8 32 }, { name := "ed_pub", ty := .arr .u8 32 },
   { name := "ed_prefix", ty := .arr .u8 32 }, { name := "ed_sig", ty := .arr .u8 64 },
   { name := "ed_msg", ty := .arr .u8 512 }, { name := "ed_mlen", ty := .u16 },
   { name := "sc_in", ty := .arr .u8 64 }, { name := "sc_out", ty := .arr .u8 32 },
   { name := "sc_rem", ty := .arr .u32 9 }, { name := "sc_t", ty := .arr .u32 9 },
   { name := "sc_acc", ty := .arr .u32 64 }, { name := "sc_a", ty := .arr .u8 32 },
   { name := "sc_r", ty := .arr .u8 32 }, { name := "sc_k", ty := .arr .u8 32 }]

def ed25519Fns : List Fn :=
  [ed_padd, ed_pcswap, fe_load_const, ed_mul_base, ed_pack, sc_reduce, sc_muladd, ed_sign]

end Ember.Net.Crypto
