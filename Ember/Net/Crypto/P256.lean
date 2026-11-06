import Ember.Net.Crypto.Ed25519
import Ember.Spec.Crypto.P256

/-!
# Ember.Net.Crypto.P256 — ECDSA on P-256 in Ember (plan M8.8)

`Ember.Spec.Crypto.p256Sign` for small machines:

* numbers mod `p` and mod `n` (the curve's field and its order) are eight
  32-bit limbs in the registers of `pr` (register `r` is `pr[8 r, 8 r + 8)`),
  in Montgomery form; `pm_mul` is the CIOS Montgomery product with `u64`
  partial products, for either modulus (`m` 0 is `p`, 1 is `n`); the final
  subtraction, the additions and the subtractions select with masks;
* points are projective, added by the complete formulas of Renes,
  Costello and Batina (2016, Algorithm 4, a = −3: `Spec.Crypto.ppAdd`),
  so the ladder of `p2_mul_g` swaps with masks and branches on no bit of
  the scalar;
* the nonce is RFC 6979's (HMAC-SHA256 of `Sha256`), the signature DER.

`p2_sign` signs `ed_msg[0, ed_mlen)` with the private scalar `p2_d`
(32 bytes, big-endian); the DER signature in `p2_sig[0, p2_siglen)`.

Registers: 0–5 temporaries of `pm_*`, 6–8 `t0 t1 t2` and 9–13 `t3 t4 x3
y3 z3` of the addition, 14–16 the point R0, 17–19 R1, 20 the curve's b,
21–24 for the signature.
-/

namespace Ember.Net.Crypto
open Ember.Lang

/-- Register `o` := register `a` · register `b` · R⁻¹ mod modulus `m`. -/
ember def pm_mul (o : u16) (a : u16) (b : u16) (m : u16) := do
  for i : u16 in [0, 10) do
    pm_t[i] := 0
  let np : u64 := (P2_NP[m] : u64)
  for i2 : u16 in [0, 8) do
    let bi : u64 := (pr[b * 8 + i2] : u64)
    let mut c : u64 := 0
    for j : u16 in [0, 8) do
      let s : u64 := (pm_t[j] : u64) + (pr[a * 8 + j] : u64) * bi + c
      pm_t[j] := (s : u32)
      c := s >>> 32
    let s2 : u64 := (pm_t[8] : u64) + c
    pm_t[8] := (s2 : u32)
    pm_t[9] := (s2 >>> 32 : u32)
    let mv : u64 := ((pm_t[0] : u64) * np) &&& 0xffffffff
    let s3 : u64 := (pm_t[0] : u64) + mv * (P2_MOD[m * 8] : u64)
    let mut c2 : u64 := s3 >>> 32
    for j2 : u16 in [1, 8) do
      let s4 : u64 := (pm_t[j2] : u64) + mv * (P2_MOD[m * 8 + j2] : u64) + c2
      pm_t[j2 - 1] := (s4 : u32)
      c2 := s4 >>> 32
    let s5 : u64 := (pm_t[8] : u64) + c2
    pm_t[7] := (s5 : u32)
    pm_t[8] := pm_t[9] + (s5 >>> 32 : u32)
  -- t - N, kept when there was no borrow (t ≥ N)
  let mut borrow : u64 := 0
  for k : u16 in [0, 8) do
    let d : u64 := (pm_t[k] : u64) - (P2_MOD[m * 8 + k] : u64) - borrow
    pm_u[k] := (d : u32)
    borrow := (d >>> 63) &&& 1
  let last : u64 := (pm_t[8] : u64) - borrow
  let keepT : u32 := (last >>> 63 : u32) * 0xffffffff
  for q : u16 in [0, 8) do
    pr[o * 8 + q] := (pm_t[q] &&& keepT) ||| (pm_u[q] &&& ~~~keepT)

/-- `o` := `a` + `b` mod `m` (both below the modulus). -/
ember def pm_add (o : u16) (a : u16) (b : u16) (m : u16) := do
  let mut c : u64 := 0
  for i : u16 in [0, 8) do
    let s : u64 := (pr[a * 8 + i] : u64) + (pr[b * 8 + i] : u64) + c
    pm_t[i] := (s : u32)
    c := s >>> 32
  let mut borrow : u64 := 0
  for k : u16 in [0, 8) do
    let d : u64 := (pm_t[k] : u64) - (P2_MOD[m * 8 + k] : u64) - borrow
    pm_u[k] := (d : u32)
    borrow := (d >>> 63) &&& 1
  -- the sum is below N when it did not carry and the subtraction borrowed
  let below : u64 := (1 - c) &&& borrow
  let keepT : u32 := (below : u32) * 0xffffffff
  for q : u16 in [0, 8) do
    pr[o * 8 + q] := (pm_t[q] &&& keepT) ||| (pm_u[q] &&& ~~~keepT)

/-- `o` := `a` − `b` mod `m`. -/
ember def pm_sub (o : u16) (a : u16) (b : u16) (m : u16) := do
  let mut borrow : u64 := 0
  for i : u16 in [0, 8) do
    let d : u64 := (pr[a * 8 + i] : u64) - (pr[b * 8 + i] : u64) - borrow
    pm_t[i] := (d : u32)
    borrow := (d >>> 63) &&& 1
  -- add N back when it borrowed
  let addN : u64 := 0 - borrow
  let mut c : u64 := 0
  for k : u16 in [0, 8) do
    let s : u64 := (pm_t[k] : u64) + ((P2_MOD[m * 8 + k] : u64) &&& addN) + c
    pr[o * 8 + k] := (s : u32)
    c := s >>> 32

ember def pm_copy (o : u16) (a : u16) := do
  for i : u16 in [0, 8) do
    pr[o * 8 + i] := pr[a * 8 + i]

/-- Register `o` := constant `which` (8 words of `P2_C`). -/
ember def pm_const (o : u16) (which : u16) := do
  for i : u16 in [0, 8) do
    pr[o * 8 + i] := P2_C[which * 8 + i]

/-- Into Montgomery form (`a · R² · R⁻¹`), and out of it (`a · 1 · R⁻¹`). -/
ember def pm_to (o : u16) (a : u16) (m : u16) := do
  pm_const(5, C_R2P + m)
  pm_mul(o, a, 5, m)

ember def pm_from (o : u16) (a : u16) (m : u16) := do
  pm_const(5, C_ONE)
  pm_mul(o, a, 5, m)

/-- `o` := `a`^(N − 2) mod `m` (Montgomery form in and out; the exponent is public). -/
ember def pm_inv (o : u16) (a : u16) (m : u16) := do
  pm_const(4, C_MONE_P + m)
  for k : u16 in [0, 256) do
    let nb : u16 := 255 - k
    pm_mul(4, 4, 4, m)
    let w : u32 := P2_EXP[m * 8 + (nb >>> 5)]
    if ((w >>> ((nb &&& 31) : u32)) &&& 1) == 1 then
      pm_mul(4, 4, a, m)
  pm_copy(o, 4)

/-- The complete addition: point at `p` += point at `q` (registers p, p+1, p+2). -/
ember def p2_add (pp : u16) (qq : u16) := do
  pm_mul(6, pp, qq, 0)
  pm_mul(7, pp + 1, qq + 1, 0)
  pm_mul(8, pp + 2, qq + 2, 0)
  pm_add(9, pp, pp + 1, 0)
  pm_add(10, qq, qq + 1, 0)
  pm_mul(9, 9, 10, 0)
  pm_add(10, 6, 7, 0)
  pm_sub(9, 9, 10, 0)
  pm_add(10, pp + 1, pp + 2, 0)
  pm_add(11, qq + 1, qq + 2, 0)
  pm_mul(10, 10, 11, 0)
  pm_add(11, 7, 8, 0)
  pm_sub(10, 10, 11, 0)
  pm_add(11, pp, pp + 2, 0)
  pm_add(12, qq, qq + 2, 0)
  pm_mul(11, 11, 12, 0)
  pm_add(12, 6, 8, 0)
  pm_sub(12, 11, 12, 0)
  pm_mul(13, 20, 8, 0)
  pm_sub(11, 12, 13, 0)
  pm_add(13, 11, 11, 0)
  pm_add(11, 11, 13, 0)
  pm_sub(13, 7, 11, 0)
  pm_add(11, 7, 11, 0)
  pm_mul(12, 20, 12, 0)
  pm_add(7, 8, 8, 0)
  pm_add(8, 7, 8, 0)
  pm_sub(12, 12, 8, 0)
  pm_sub(12, 12, 6, 0)
  pm_add(7, 12, 12, 0)
  pm_add(12, 7, 12, 0)
  pm_add(7, 6, 6, 0)
  pm_add(6, 7, 6, 0)
  pm_sub(6, 6, 8, 0)
  pm_mul(7, 10, 12, 0)
  pm_mul(8, 6, 12, 0)
  pm_mul(12, 11, 13, 0)
  pm_add(12, 12, 8, 0)
  pm_mul(11, 9, 11, 0)
  pm_sub(11, 11, 7, 0)
  pm_mul(13, 10, 13, 0)
  pm_mul(7, 9, 6, 0)
  pm_add(13, 13, 7, 0)
  pm_copy(pp, 11)
  pm_copy(pp + 1, 12)
  pm_copy(pp + 2, 13)

ember def p2_cswap (pp : u16) (qq : u16) (bit : u32) := do
  let mask : u32 := 0 - bit
  for i : u16 in [0, 24) do
    let dx : u32 := mask &&& (pr[pp * 8 + i] ^^^ pr[qq * 8 + i])
    pr[pp * 8 + i] := pr[pp * 8 + i] ^^^ dx
    pr[qq * 8 + i] := pr[qq * 8 + i] ^^^ dx

/-- Registers 14, 15 := the affine x, y of `k·G` (out of Montgomery form), `k`
the 32 big-endian bytes of `p2_k`; `p2_inf` when it is the point at infinity. -/
ember def p2_mul_g := do
  pm_const(20, C_B)
  -- R0 = (0 : 1 : 0), R1 = G, in Montgomery form
  pm_const(14, C_ZERO)
  pm_const(15, C_MONE_P)
  pm_const(16, C_ZERO)
  pm_const(17, C_GX)
  pm_const(18, C_GY)
  pm_const(19, C_MONE_P)
  for k : u16 in [0, 256) do
    let byte : u8 := p2_k[k >>> 3]
    let bit : u32 := ((byte >>> (7 - ((k &&& 7) : u8))) &&& 1 : u32)
    p2_cswap(14, 17, bit)
    p2_add(17, 14)
    p2_add(14, 14)
    p2_cswap(14, 17, bit)
  let mut z : u32 := 0
  for i : u16 in [0, 8) do
    z := z ||| pr[Z_BASE + i]
  p2_inf := z == 0
  pm_inv(21, 16, 0)
  pm_mul(14, 14, 21, 0)
  pm_mul(15, 15, 21, 0)
  pm_from(14, 14, 0)
  pm_from(15, 15, 0)

/-- Register `o` := 32 big-endian bytes of `src` at `off` (plain form). -/
ember def pm_load (o : u16) (src : u16) := do
  for i : u16 in [0, 8) do
    let b0 : u32 := (p2_in[src + 28 - 4 * i] : u32) <<< 24
    let b1 : u32 := (p2_in[src + 29 - 4 * i] : u32) <<< 16
    let b2 : u32 := (p2_in[src + 30 - 4 * i] : u32) <<< 8
    pr[o * 8 + i] := b0 ||| b1 ||| b2 ||| (p2_in[src + 31 - 4 * i] : u32)

/-- Register `a` (plain) as 32 big-endian bytes in `p2_out`. -/
ember def pm_store (a : u16) := do
  for i : u16 in [0, 8) do
    let w : u32 := pr[a * 8 + i]
    p2_out[28 - 4 * i] := (w >>> 24 : u8)
    p2_out[29 - 4 * i] := (w >>> 16 : u8)
    p2_out[30 - 4 * i] := (w >>> 8 : u8)
    p2_out[31 - 4 * i] := (w : u8)

/-- `a` (plain, below 2²⁵⁶) reduced once by `n`: below `n` since 2²⁵⁶ < 2n. -/
ember def pm_reduce_n (a : u16) := do
  pm_const(5, C_ZERO)
  pm_add(a, a, 5, 1)

/-! ## RFC 6979 and the signature -/

/-- `p2_v` := HMAC(`p2_kk`, `p2_v` || extra bytes `p2_in[64, 64 + nx)`); when `withKey`,
the private key and the reduced hash follow (as RFC 6979 §3.2 d and f). -/
ember def p2_hmac_v (into : bool) (sep : u8) (withSep : bool) (withKey : bool) := do
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  for j : u16 in [0, 32) do
    hm_key[j] := p2_kk[j]
  hmac_begin()
  for k : u16 in [0, 32) do
    sha_byte(p2_v[k])
  if withSep then
    sha_byte(sep)
  if withKey then
    for q : u16 in [0, 32) do
      sha_byte(p2_d[q])
    for q2 : u16 in [0, 32) do
      sha_byte(p2_h[q2])
  hmac_end()
  for m : u16 in [0, 32) do
    if into then
      p2_kk[m] := sh_out[m]
    else
      p2_v[m] := sh_out[m]

/-- Is the 32-byte big-endian `p2_v` in [1, n)? -/
ember def p2_v_ok : bool := do
  let mut nz : u8 := 0
  let mut lt : bool := false
  let mut eq : bool := true
  for i : u16 in [0, 32) do
    nz := nz ||| p2_v[i]
    let nb : u8 := P2_NBYTES[i]
    if eq then
      if p2_v[i] < nb then
        lt := true
        eq := false
      if p2_v[i] > nb then
        eq := false
  return nz != 0 && lt

/-- DER INTEGER of `p2_out[0, 32)` at `p2_sig[pos]`; the new position. -/
ember def p2_der_int (pos : u16) : u16 := do
  let mut first : u16 := 32
  for i : u16 in [0, 32) do
    if first == 32 && p2_out[i] != 0 then
      first := i
  if first == 32 then
    first := 31
  let pad : bool := p2_out[first] >= 0x80
  let mut ilen : u16 := 32 - first
  if pad then
    ilen := ilen + 1
  p2_sig[pos] := 2
  p2_sig[pos + 1] := (ilen : u8)
  let mut at2 : u16 := pos + 2
  if pad then
    p2_sig[at2] := 0
    at2 := at2 + 1
  for j : u16 in [first, 32) do
    p2_sig[at2] := p2_out[j]
    at2 := at2 + 1
  return at2

ember def p2_sign := do
  -- the hash, and the hash reduced mod n (RFC 6979 bits2octets)
  sha_init()
  for i : u16 in [0, ed_mlen) do
    sha_byte(ed_msg[i])
  sha_final()
  for j : u16 in [0, 32) do
    p2_in[j] := sh_out[j]
  pm_load(21, 0)
  pm_reduce_n(21)
  pm_store(21)
  for j2 : u16 in [0, 32) do
    p2_h[j2] := p2_out[j2]
  -- RFC 6979 §3.2 b–g
  for j3 : u16 in [0, 32) do
    p2_v[j3] := 1
    p2_kk[j3] := 0
  p2_hmac_v(true, 0, true, true)
  p2_hmac_v(false, 0, false, false)
  p2_hmac_v(true, 1, true, true)
  p2_hmac_v(false, 0, false, false)
  p2_siglen := 0
  loop (max := 64) do
    p2_hmac_v(false, 0, false, false)
    let ok : bool ← p2_v_ok()
    if ok then
      for j4 : u16 in [0, 32) do
        p2_k[j4] := p2_v[j4]
      p2_mul_g()
      -- r = x mod n
      pm_reduce_n(14)
      let mut rz : u32 := 0
      for j5 : u16 in [0, 8) do
        rz := rz ||| pr[X_BASE + j5]
      if rz != 0 && !p2_inf then
        -- s = k⁻¹ (z + r d) mod n, in Montgomery form for n
        for j6 : u16 in [0, 32) do
          p2_in[j6] := p2_k[j6]
          p2_in[32 + j6] := p2_d[j6]
        pm_load(22, 0)
        pm_to(22, 22, 1)
        pm_inv(22, 22, 1)
        pm_load(23, 32)
        pm_to(23, 23, 1)
        pm_to(24, 14, 1)
        pm_mul(23, 24, 23, 1)
        for j7 : u16 in [0, 32) do
          p2_in[j7] := p2_h[j7]
        pm_load(24, 0)
        pm_to(24, 24, 1)
        pm_add(23, 24, 23, 1)
        pm_mul(23, 22, 23, 1)
        pm_from(23, 23, 1)
        let mut sz : u32 := 0
        for j8 : u16 in [0, 8) do
          sz := sz ||| pr[S_BASE + j8]
        if sz != 0 then
          -- SEQUENCE { INTEGER r, INTEGER s }
          pm_store(14)
          let e1 : u16 ← p2_der_int(2)
          pm_store(23)
          let e2 : u16 ← p2_der_int(e1)
          p2_sig[0] := 0x30
          p2_sig[1] := (e2 - 2 : u8)
          p2_siglen := e2
          break
    -- the next candidate: K = HMAC(K, V || 0), V = HMAC(K, V)
    p2_hmac_v(true, 0, true, false)
    p2_hmac_v(false, 0, false, false)

/-! ## Constants -/

open Ember.Spec.Crypto in
def words8 (v : Nat) : List Nat := (List.range 8).map fun i => (v >>> (32 * i)) % 2 ^ 32

open Ember.Spec.Crypto in
/-- −m⁻¹ mod 2³². -/
def nprime (m : Nat) : Nat := (2 ^ 32 - fpow m (2 ^ 31 - 1) (2 ^ 32)) % 2 ^ 32

open Ember.Spec.Crypto in
def p256Consts : List (String × Nat) :=
  let R := 2 ^ 256
  [("C_ZERO", 0), ("C_ONE", 1), ("C_MONE_P", R % p256), ("C_MONE_N", R % n256),
   ("C_R2P", R * R % p256), ("C_R2N", R * R % n256),
   ("C_B", b256 * R % p256), ("C_GX", g256.1 * R % p256), ("C_GY", g256.2 * R % p256)]

open Ember.Spec.Crypto in
def p256Globals : List Global :=
  let cs := p256Consts
  [{ name := "P2_MOD", ty := .arr .u32 16, init := words8 p256 ++ words8 n256, const := true },
   { name := "P2_NP", ty := .arr .u32 2, init := [nprime p256, nprime n256], const := true },
   { name := "P2_EXP", ty := .arr .u32 16, init := words8 (p256 - 2) ++ words8 (n256 - 2), const := true },
   { name := "P2_NBYTES", ty := .arr .u8 32, init := (natBe n256 32).toList.map (·.toNat), const := true },
   { name := "P2_C", ty := .arr .u32 (8 * cs.length), init := cs.flatMap (fun (_, v) => words8 v), const := true }] ++
  (cs.zipIdx.map fun ((name, _), i) => { name, ty := .u16, init := [i], const := true }) ++
  -- the first word of the registers read word by word: R0's Z, R0's x, s
  [{ name := "Z_BASE", ty := .u16, init := [16 * 8], const := true },
   { name := "X_BASE", ty := .u16, init := [14 * 8], const := true },
   { name := "S_BASE", ty := .u16, init := [23 * 8], const := true }] ++
  [{ name := "pr", ty := .arr .u32 (8 * 25) }, { name := "pm_t", ty := .arr .u32 10 },
   { name := "pm_u", ty := .arr .u32 8 }, { name := "p2_in", ty := .arr .u8 64 },
   { name := "p2_out", ty := .arr .u8 32 }, { name := "p2_d", ty := .arr .u8 32 },
   { name := "p2_h", ty := .arr .u8 32 }, { name := "p2_k", ty := .arr .u8 32 },
   { name := "p2_v", ty := .arr .u8 32 }, { name := "p2_kk", ty := .arr .u8 32 },
   { name := "p2_inf", ty := .bool }, { name := "p2_sig", ty := .arr .u8 72 }, { name := "p2_siglen", ty := .u16 }]

def p256Fns : List Fn :=
  [pm_mul, pm_add, pm_sub, pm_copy, pm_const, pm_to, pm_from, pm_inv, p2_add, p2_cswap, p2_mul_g,
   pm_load, pm_store, pm_reduce_n, p2_hmac_v, p2_v_ok, p2_der_int, p2_sign]

end Ember.Net.Crypto
