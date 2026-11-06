import Ember.Net.Crypto.P256

/-!
# Ember.Net.Crypto.Test — a program that runs the Ember crypto on its input (plan M8.5b)

Each request is an operation byte, a 16-bit big-endian length and that
many bytes; the answer is one output frame.  `main` takes one input byte
per call into `rq` (as the stack does: on a target the bytes arrive while
it runs) and answers when a request is complete; the operations read the
request from `rq` (`rd`).  The same input runs on the
interpreter, as host C, and on the targets, and is compared with
`Ember.Spec.Crypto` (`Tests/Ember/CryptoTests.lean`).

| op | input | output |
|---|---|---|
| 1 | message | SHA-256 |
| 2 | key length (1 byte), key, message | HMAC-SHA256 |
| 3 | PRK (32), length L (1 byte), info | HKDF-Expand, L bytes |
| 4 | key (32), nonce (12), counter (4, little-endian), message | ChaCha20 |
| 5 | key (32), message | Poly1305 |
| 6 | key (32), nonce (12), AAD length (2), AAD, plain text | AEAD: cipher text and tag |
| 7 | scalar (32), u-coordinate (32) | X25519 |
| 8 | secret seed (32), message (at most 512) | Ed25519 signature |
| 9 | 64 bytes | their value mod L (32 bytes) |
| 10 | key (32), nonce (12), AAD length (2), AAD, cipher text and tag | AEAD opening: 1 and the plain text, or 0 alone |
| 11 | salt length (1 byte), salt, input keying material | HKDF-Extract |
| 12 | private scalar (32, big-endian), message (at most 512) | ECDSA P-256 / SHA-256, DER |
-/

namespace Ember.Net.Crypto
open Ember.Lang

/-- The next byte of the request in `rq`. -/
ember def rd : u16 := do
  let v : u16 := (rq[rq_pos] : u16)
  rq_pos := rq_pos + 1
  return v

ember def rd16 : u16 := do
  let h : u16 ← rd()
  let l : u16 ← rd()
  return (h <<< 8) ||| (l &&& 0xFF)

ember def op_sha256 (n : u16) := do
  sha_init()
  for i : u16 in [0, n) do
    let x : u16 ← rd()
    sha_byte((x : u8))
  sha_final()
  for j : u16 in [0, 32) do
    out.byte(sh_out[j])
  out.end()

ember def op_hmac (n : u16) := do
  let kl : u16 ← rd()
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  if kl > 64 then
    for j : u16 in [0, kl) do
      let x : u16 ← rd()
      hk_out[j] := (x : u8)
    hmac_key_long(kl)
  else
    for k : u16 in [0, kl) do
      let y : u16 ← rd()
      hm_key[k] := (y : u8)
  hmac_begin()
  for m : u16 in [0, n - 1 - kl) do
    let z : u16 ← rd()
    sha_byte((z : u8))
  hmac_end()
  for o : u16 in [0, 32) do
    out.byte(sh_out[o])
  out.end()

ember def op_hkdf (n : u16) := do
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  for j : u16 in [0, 32) do
    let x : u16 ← rd()
    hm_key[j] := (x : u8)
  let l : u16 ← rd()
  hk_ilen := n - 33
  for k : u16 in [0, hk_ilen) do
    let y : u16 ← rd()
    hk_info[k] := (y : u8)
  hkdf_expand(l)
  for o : u16 in [0, l) do
    out.byte(hk_out[o])
  out.end()

ember def rd_key_nonce := do
  for i : u16 in [0, 32) do
    let x : u16 ← rd()
    cc_key[i] := (x : u8)
  for j : u16 in [0, 12) do
    let y : u16 ← rd()
    cc_nonce[j] := (y : u8)

/-- XOR `n` bytes of input with the key stream from `cc_ctr` on, out. -/
ember def chacha_stream (n : u16) (mac : bool) := do
  let mut k : u16 := 64
  for i : u16 in [0, n) do
    if k == 64 then
      chacha_block()
      cc_ctr := cc_ctr + 1
      k := 0
    let x : u16 ← rd()
    let y : u8 := (x : u8) ^^^ cc_ks[k]
    if mac then
      poly_byte(y)
    out.byte(y)
    k := k + 1

ember def op_chacha (n : u16) := do
  rd_key_nonce()
  let mut ctr : u32 := 0
  for i : u16 in [0, 4) do
    let x : u16 ← rd()
    ctr := ctr ||| ((x : u32) <<< (8 * (i : u32)))
  cc_ctr := ctr
  chacha_stream(n - 48, false)
  out.end()

ember def op_poly (n : u16) := do
  for i : u16 in [0, 32) do
    let x : u16 ← rd()
    pk_key[i] := (x : u8)
  poly_init()
  for j : u16 in [0, n - 32) do
    let y : u16 ← rd()
    poly_byte((y : u8))
  poly_final()
  for k : u16 in [0, 16) do
    out.byte(pk_tag[k])
  out.end()

ember def op_seal (n : u16) := do
  rd_key_nonce()
  let al : u16 ← rd16()
  aead_begin()
  for i : u16 in [0, al) do
    let x : u16 ← rd()
    poly_byte((x : u8))
  poly_pad()
  let pl : u16 := n - 46 - al
  chacha_stream(pl, true)
  poly_pad()
  poly_len64((al : u32))
  poly_len64((pl : u32))
  poly_final()
  for k : u16 in [0, 16) do
    out.byte(pk_tag[k])
  out.end()

ember def op_x25519 := do
  for i : u16 in [0, 32) do
    let x : u16 ← rd()
    x_k[i] := (x : u8)
  for j : u16 in [0, 32) do
    let y : u16 ← rd()
    fe_in[j] := (y : u8)
  x25519()
  for k : u16 in [0, 32) do
    out.byte(fe_bytes[k])
  out.end()

ember def op_sign (n : u16) := do
  for i : u16 in [0, 32) do
    let x : u16 ← rd()
    ed_sk[i] := (x : u8)
  ed_mlen := n - 32
  for j : u16 in [0, ed_mlen) do
    let y : u16 ← rd()
    ed_msg[j] := (y : u8)
  ed_sign()
  for k : u16 in [0, 64) do
    out.byte(ed_sig[k])
  out.end()

ember def op_reduce := do
  for i : u16 in [0, 64) do
    let x : u16 ← rd()
    sc_in[i] := (x : u8)
  sc_reduce()
  for k : u16 in [0, 32) do
    out.byte(sc_out[k])
  out.end()

ember def op_open (n : u16) := do
  rd_key_nonce()
  let al : u16 ← rd16()
  aead_begin()
  for i : u16 in [0, al) do
    let x : u16 ← rd()
    poly_byte((x : u8))
  poly_pad()
  let cl : u16 := n - 46 - al - 16
  for j : u16 in [0, cl) do
    let y : u16 ← rd()
    ae_buf[j] := (y : u8)
  for k : u16 in [0, 16) do
    let z : u16 ← rd()
    ae_tag[k] := (z : u8)
  let ok : bool ← aead_open(cl, al)
  if ok then
    out.byte(1)
    for m : u16 in [0, cl) do
      out.byte(ae_buf[m])
  else
    out.byte(0)
  out.end()

ember def op_extract (n : u16) := do
  let sl : u16 ← rd()
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  -- a salt longer than a block is hashed first, as an HMAC key is (RFC 2104)
  if sl > 64 then
    for j : u16 in [0, sl) do
      let x : u16 ← rd()
      hk_out[j] := (x : u8)
    hmac_key_long(sl)
  else
    for j2 : u16 in [0, sl) do
      let x2 : u16 ← rd()
      hm_key[j2] := (x2 : u8)
  hmac_begin()
  for k : u16 in [0, n - 1 - sl) do
    let y : u16 ← rd()
    sha_byte((y : u8))
  hkdf_extract_end()
  for m : u16 in [0, 32) do
    out.byte(sh_out[m])
  out.end()

ember def op_p256 (n : u16) := do
  for i : u16 in [0, 32) do
    let x : u16 ← rd()
    p2_d[i] := (x : u8)
  ed_mlen := n - 32
  for j : u16 in [0, ed_mlen) do
    let y : u16 ← rd()
    ed_msg[j] := (y : u8)
  p2_sign()
  for k : u16 in [0, p2_siglen) do
    out.byte(p2_sig[k])
  out.end()

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF || k == 0x0100 then
    return
  rq[rq_len] := (k : u8)
  rq_len := rq_len + 1
  if rq_len < 3 then
    return
  let n : u16 := ((rq[1] : u16) <<< 8) ||| (rq[2] : u16)
  if rq_len < 3 + n then
    return
  let op : u8 := rq[0]
  rq_pos := 3
  rq_len := 0
  if op == 1 then
    op_sha256(n)
    return
  if op == 2 then
    op_hmac(n)
    return
  if op == 3 then
    op_hkdf(n)
    return
  if op == 4 then
    op_chacha(n)
    return
  if op == 5 then
    op_poly(n)
    return
  if op == 6 then
    op_seal(n)
    return
  if op == 7 then
    op_x25519()
    return
  if op == 8 then
    op_sign(n)
    return
  if op == 9 then
    op_reduce()
    return
  if op == 10 then
    op_open(n)
    return
  if op == 11 then
    op_extract(n)
    return
  if op == 12 then
    op_p256(n)
    return

def testProg : Prog :=
  { globals := sha256Globals ++ chachaGlobals ++ x25519Globals ++ sha512Globals ++ ed25519Globals ++ p256Globals ++
    [{ name := "rq", ty := .arr .u8 1024 }, { name := "rq_len", ty := .u16 }, { name := "rq_pos", ty := .u16 }],
    fns := sha256Fns ++ chachaFns ++ x25519Fns ++ sha512Fns ++ ed25519Fns ++ p256Fns ++ [rd, rd16, op_sha256, op_hmac, op_hkdf, rd_key_nonce, chacha_stream, op_chacha,
      op_poly, op_seal, op_x25519, op_sign, op_reduce, op_open, op_extract, op_p256, main] }

end Ember.Net.Crypto
