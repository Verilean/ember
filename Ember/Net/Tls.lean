import Ember.Net.Http
import Ember.Net.Crypto.P256
import Ember.Spec.Srv.Tls

/-!
# Ember.Net.Tls — the TLS 1.3 server in Ember (plan M8.7)

`Ember.Spec.Srv.Tls` on `Ember.Net.Srv`, record for record and alert for
alert, with the crypto of `Ember.Net.Crypto` and the HTTP of
`Ember.Net.Http` (its request parser `h_decide` and its response tables
`h_byte`; not its `app_*` functions).

Per connection (`cur`): the records received and not yet whole
(`t_inb`, `INB` bytes), the bytes to send from `snd.una` on (`t_out`,
`OUTB` bytes: the server's flight and the protected response are kept
as the Spec keeps them), the transcript hash (`t_tr_*`, a SHA-256 context
of its own), the traffic keys and sequence numbers (`t_r*` to receive,
`t_w*` to send), the client's Finished key, the application secrets and
the transcript hash the client's Finished covers.  Shared by all
connections: the crypto's registers and buffers (one connection is
worked on at a time).

Records are opened and sealed in place, in `t_inb` and `t_out`.
-/

namespace Ember.Net.Tls
open Ember.Lang

/-! ## Bytes of the connection -/

ember def ib (k : u16) : u16 := do
  return (t_inb[cur * INB + k] : u16)

ember def ib16 (k : u16) : u16 := do
  let h : u16 ← ib(k)
  let l : u16 ← ib(k + 1)
  return (h <<< 8) ||| l

ember def ob (x : u8) := do
  t_out[cur * OUTB + t_outl[cur]] := x
  t_outl[cur] := t_outl[cur] + 1

ember def ob16 (x : u16) := do
  ob((x >>> 8 : u8))
  ob((x : u8))

/-! ## The transcript hash: a SHA-256 context per connection -/

ember def tr_load := do
  for i : u16 in [0, 8) do
    sh_h[i] := t_tr_h[cur * 8 + i]
  for j : u16 in [0, 64) do
    sh_blk[j] := t_tr_blk[cur * 64 + j]
  sh_n := t_tr_n[cur]
  sh_len := t_tr_len[cur]

ember def tr_store := do
  for i : u16 in [0, 8) do
    t_tr_h[cur * 8 + i] := sh_h[i]
  for j : u16 in [0, 64) do
    t_tr_blk[cur * 64 + j] := sh_blk[j]
  t_tr_n[cur] := sh_n
  t_tr_len[cur] := sh_len

/-- The transcript hash so far in `tl_th` (the context is not changed). -/
ember def tr_hash := do
  tr_load()
  sha_final()
  for i : u16 in [0, 32) do
    tl_th[i] := sh_out[i]

/-- `t_out[from, to)` into the transcript. -/
ember def tr_out (frm : u16) (upto : u16) := do
  tr_load()
  for i : u16 in [frm, upto) do
    sha_byte(t_out[cur * OUTB + i])
  tr_store()

/-! ## The key schedule (RFC 8446 §7.1) -/

/-- `hk_out[0, n)` := HKDF-Expand-Label(`tl_sec`, label `lab`, context, `n`):
the context is `tl_th` when `withTh`, empty otherwise. -/
ember def expand_label (lab : u16) (withTh : bool) (n : u16) := do
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  for j : u16 in [0, 32) do
    hm_key[j] := tl_sec[j]
  let ll : u16 := TL_LLEN[lab]
  hk_info[0] := (n >>> 8 : u8)
  hk_info[1] := (n : u8)
  hk_info[2] := (6 + ll : u8)
  for k : u16 in [0, 6) do
    hk_info[3 + k] := TL_TLS13[k]
  for m : u16 in [0, ll) do
    hk_info[9 + m] := TL_LABELS[TL_LOFF[lab] + m]
  let c : u16 := 9 + ll
  if withTh then
    hk_info[c] := 32
    for q : u16 in [0, 32) do
      hk_info[c + 1 + q] := tl_th[q]
    hk_ilen := c + 33
  else
    hk_info[c] := 0
    hk_ilen := c + 1
  hkdf_expand(n)

/-- `tl_sec` := HKDF-Extract(salt `tl_salt`, IKM `tl_ikm`). -/
ember def extract := do
  for i : u16 in [0, 64) do
    hm_key[i] := 0
  for j : u16 in [0, 32) do
    hm_key[j] := tl_salt[j]
  hmac_begin()
  for k : u16 in [0, 32) do
    sha_byte(tl_ikm[k])
  hkdf_extract_end()
  for m : u16 in [0, 32) do
    tl_sec[m] := sh_out[m]

/-- `tl_sec` := Derive-Secret(`tl_sec`, label, `tl_th`). -/
ember def derive (lab : u16) := do
  expand_label(lab, true, 32)
  for i : u16 in [0, 32) do
    tl_sec[i] := hk_out[i]

/-- Keys of the traffic secret `tl_sec` to receive (`toRx`) or to send, sequence 0. -/
ember def set_keys (toRx : bool) := do
  expand_label(L_KEY, false, 32)
  for i : u16 in [0, 32) do
    if toRx then
      t_rk[cur * 32 + i] := hk_out[i]
    else
      t_wk[cur * 32 + i] := hk_out[i]
  expand_label(L_IV, false, 12)
  for j : u16 in [0, 12) do
    if toRx then
      t_riv[cur * 12 + j] := hk_out[j]
    else
      t_wiv[cur * 12 + j] := hk_out[j]
  if toRx then
    t_rseq[cur] := 0
  else
    t_wseq[cur] := 0
    t_wset[cur] := true

/-! ## Record protection, in place -/

/-- The ChaCha20 key and nonce of the receiving (`rx`) or sending keys. -/
ember def use_keys (rx : bool) := do
  let mut seq : u32 := t_wseq[cur]
  if rx then
    seq := t_rseq[cur]
  for i : u16 in [0, 32) do
    if rx then
      cc_key[i] := t_rk[cur * 32 + i]
    else
      cc_key[i] := t_wk[cur * 32 + i]
  for j : u16 in [0, 12) do
    let mut v : u8 := t_wiv[cur * 12 + j]
    if rx then
      v := t_riv[cur * 12 + j]
    let mut sb : u8 := 0
    if j >= 8 then
      sb := (seq >>> (8 * (11 - (j : u32))) : u8)
    cc_nonce[j] := v ^^^ sb

/-- Seal `t_out[pos + 5, pos + 5 + n)` (the content and its type byte) as one
record: the header at `pos`, the tag after; `t_outl` past the tag. -/
ember def rec_seal (pos : u16) (n : u16) := do
  let base : u16 := cur * OUTB
  t_out[base + pos] := 23
  t_out[base + pos + 1] := 3
  t_out[base + pos + 2] := 3
  t_out[base + pos + 3] := ((n + 16) >>> 8 : u8)
  t_out[base + pos + 4] := (n + 16 : u8)
  use_keys(false)
  aead_begin()
  for i : u16 in [0, 5) do
    poly_byte(t_out[base + pos + i])
  poly_pad()
  let mut k : u16 := 64
  for j : u16 in [0, n) do
    if k == 64 then
      chacha_block()
      cc_ctr := cc_ctr + 1
      k := 0
    let c : u8 := t_out[base + pos + 5 + j] ^^^ cc_ks[k]
    t_out[base + pos + 5 + j] := c
    poly_byte(c)
    k := k + 1
  poly_pad()
  poly_len64(5)
  poly_len64((n : u32))
  poly_final()
  for m : u16 in [0, 16) do
    t_out[base + pos + 5 + n + m] := pk_tag[m]
  t_outl[cur] := pos + 5 + n + 16
  t_wseq[cur] := t_wseq[cur] + 1

/-- A record of `content` (`tl_msg[0, n)`) of type `ty`, protected. -/
ember def seal_msg (ty : u8) (n : u16) := do
  let pos : u16 := t_outl[cur]
  t_outl[cur] := pos + 5
  for i : u16 in [0, n) do
    ob(tl_msg[i])
  ob(ty)
  rec_seal(pos, n + 1)

/-- Open the record whose header is pos `t_inb[0, 5)` and body `[5, 5 + bl)`
in place with the receiving keys: whether the tag matches; the content
type in `tl_ity` and the content's length in `tl_ilen` (zero padding
dropped); a record with no type (all zeros) is a failure too. -/
ember def open_rec (bl : u16) : bool := do
  if bl < 17 then
    return false
  let base : u16 := cur * INB
  let n : u16 := bl - 16
  use_keys(true)
  aead_begin()
  for i : u16 in [0, 5) do
    poly_byte(t_inb[base + i])
  poly_pad()
  let mut k : u16 := 64
  for j : u16 in [0, n) do
    if k == 64 then
      chacha_block()
      cc_ctr := cc_ctr + 1
      k := 0
    poly_byte(t_inb[base + 5 + j])
    t_inb[base + 5 + j] := t_inb[base + 5 + j] ^^^ cc_ks[k]
    k := k + 1
  poly_pad()
  poly_len64(5)
  poly_len64((n : u32))
  poly_final()
  let mut diff : u8 := 0
  for m : u16 in [0, 16) do
    diff := diff ||| (pk_tag[m] ^^^ t_inb[base + 5 + n + m])
  if diff != 0 then
    return false
  -- the last byte that is not zero is the type
  let mut l : u16 := n
  loop (max := 2048) do
    if l == 0 then
      break
    if t_inb[base + 5 + l - 1] != 0 then
      break
    l := l - 1
  if l == 0 then
    return false
  tl_ity := t_inb[base + 5 + l - 1]
  tl_ilen := l - 1
  t_rseq[cur] := t_rseq[cur] + 1
  return true

/-! ## Endings -/

/-- A fatal alert — protected once there are sending keys — and the end. -/
ember def fail (desc : u8) := do
  if t_phase[cur] == PH_HELLO || !t_wset[cur] then
    ob(21)
    ob(3)
    ob(3)
    ob(0)
    ob(2)
    ob(2)
    ob(desc)
  else
    tl_msg[0] := 2
    tl_msg[1] := desc
    seal_msg(21, 2)
  t_phase[cur] := PH_CLOSED
  t_done[cur] := true

/-- The HTTP response for the request in `h_req` (`h_dec`, `h_kind`,
`h_head` set; nothing when `withResp` is false) in records of pos most
`CHUNK` bytes, then `close_notify`, and the end. -/
ember def respond (withResp : bool) := do
  if withResp then
    h_pos[cur] := 0
    let total : u16 ← h_total()
    let mut off : u16 := 0
    loop (max := 64) do
      if off >= total then
        break
      let mut n : u16 := total - off
      if n > CHUNK then
        n := CHUNK
      let pos : u16 := t_outl[cur]
      t_outl[cur] := pos + 5
      for i : u16 in [0, n) do
        let x : u8 ← h_byte(off + i)
        ob(x)
      ob(23)
      rec_seal(pos, n + 1)
      off := off + n
  tl_msg[0] := 1
  tl_msg[1] := 0
  seal_msg(21, 2)
  t_phase[cur] := PH_CLOSED
  t_done[cur] := true

/-! ## The ClientHello (as `Spec.Srv.Tls.parseHello`) -/

/-- Parse the ClientHello in the record body `t_inb[5, 5 + size)`: `true`
and its random, session id and key share in `tl_crand`, `tl_sid`
(`tl_sidl`), `tl_share`, or `false`. -/
ember def parse_hello (size : u16) : bool := do
  let b : u16 := 5
  if size < 4 then
    return false
  let t0 : u16 ← ib(b)
  let l1 : u16 ← ib(b + 1)
  let l2 : u16 ← ib16(b + 2)
  if t0 != 1 || l1 != 0 || l2 + 4 != size then
    return false
  let mut i : u16 := 6
  if i + 32 > size then
    return false
  for k : u16 in [0, 32) do
    tl_crand[k] := t_inb[cur * INB + b + i + k]
  i := i + 32
  if i + 1 > size then
    return false
  let sl : u16 ← ib(b + i)
  if sl > 32 || i + 1 + sl > size then
    return false
  tl_sidl := sl
  for k2 : u16 in [0, sl) do
    tl_sid[k2] := t_inb[cur * INB + b + i + 1 + k2]
  i := i + 1 + sl
  if i + 2 > size then
    return false
  let cl : u16 ← ib16(b + i)
  if (cl &&& 1) != 0 || i + 2 + cl > size then
    return false
  let mut suite : bool := false
  for k3 : u16 in [0, cl / 2) do
    let s : u16 ← ib16(b + i + 2 + 2 * k3)
    if s == 0x1303 then
      suite := true
  if !suite then
    return false
  i := i + 2 + cl
  if i + 1 > size then
    return false
  let ml : u16 ← ib(b + i)
  if i + 1 + ml > size then
    return false
  i := i + 1 + ml
  if i + 2 > size then
    return false
  let el : u16 ← ib16(b + i)
  i := i + 2
  let stop : u16 := i + el
  if stop != size then
    return false
  let mut versions : bool := false
  let mut sigok : bool := false
  tl_sig_ed := false
  tl_sig_p := false
  let mut share : bool := false
  loop (max := 1024) do
    if i + 4 > stop then
      break
    let ty : u16 ← ib16(b + i)
    let el2 : u16 ← ib16(b + i + 2)
    if i + 4 + el2 > stop then
      return false
    let d : u16 := b + i + 4
    if ty == 43 then
      -- the length of the list is read only inside the extension
      if el2 < 1 then
        return false
      let vl : u16 ← ib(d)
      if vl + 1 != el2 || (vl &&& 1) != 0 || vl < 2 then
        return false
      versions := false
      for k4 : u16 in [0, vl / 2) do
        let v : u16 ← ib16(d + 1 + 2 * k4)
        if v == 0x0304 then
          versions := true
    if ty == 13 then
      if el2 < 2 then
        return false
      let al : u16 ← ib16(d)
      if al + 2 != el2 || (al &&& 1) != 0 || al < 2 then
        return false
      sigok := true
      tl_sig_ed := false
      tl_sig_p := false
      for k5 : u16 in [0, al / 2) do
        let a : u16 ← ib16(d + 2 + 2 * k5)
        if a == 0x0807 then
          tl_sig_ed := true
        if a == 0x0403 then
          tl_sig_p := true
    if ty == 51 then
      if el2 < 2 then
        return false
      let sl2 : u16 ← ib16(d)
      if sl2 + 2 != el2 then
        return false
      let mut j : u16 := 2
      loop (max := 1024) do
        if j + 4 > el2 then
          break
        let g : u16 ← ib16(d + j)
        let kl : u16 ← ib16(d + j + 2)
        if j + 4 + kl > el2 then
          return false
        if g == 0x001d && kl == 32 then
          share := true
          for k6 : u16 in [0, 32) do
            tl_share[k6] := t_inb[cur * INB + d + j + 4 + k6]
        j := j + 4 + kl
      if j != el2 then
        return false
    i := i + 4 + el2
  return i == stop && versions && sigok && share

/-! ## The server's flight (as `Spec.Srv.Tls.serverFlight`) -/

/-- SHA-256 of the seed, a label (`TL_LABELS[off, off + n)`) and the client's random, in `sh_out`. -/
ember def seeded (off : u16) (n : u16) := do
  sha_init()
  for i : u16 in [0, TL_SEEDLEN) do
    sha_byte(TL_SEED[i])
  if TL_HWRNG then
    for e : u16 in [0, 32) do
      sha_byte(tl_ent[e])
  for j : u16 in [0, n) do
    sha_byte(TL_LABELS[off + j])
  for k : u16 in [0, 32) do
    sha_byte(tl_crand[k])
  sha_final()

/-- A handshake message header, into `t_out` and the transcript later. -/
ember def hs_head (ty : u8) (n : u16) := do
  ob(ty)
  ob(0)
  ob16(n)

ember def flight (size : u16) := do
  -- Ed25519 when offered, else P-256 when offered and there is such a
  -- certificate; neither is handshake_failure, before anything else
  tl_usep := !tl_sig_ed && tl_sig_p && CERT2_LEN > 0
  if !tl_sig_ed && !tl_usep then
    fail(40)
    return
  -- the transcript starts with the ClientHello
  sha_init()
  for i : u16 in [0, size) do
    sha_byte(t_inb[cur * INB + 5 + i])
  tr_store()
  -- the RNG's bytes for this handshake (plan M9.4)
  if TL_HWRNG then
    for w : u16 in [0, 8) do
      let v : u32 ← mmio.read32(RNG_DATA)
      tl_ent[4 * w] := (v : u8)
      tl_ent[4 * w + 1] := (v >>> 8 : u8)
      tl_ent[4 * w + 2] := (v >>> 16 : u8)
      tl_ent[4 * w + 3] := (v >>> 24 : u8)
    -- eight equal reads: a dead generator, internal_error (decision 9)
    let mut moved : bool := false
    for qe : u16 in [4, 32) do
      if tl_ent[qe] != tl_ent[qe - 4] then
        moved := true
    if !moved then
      fail(80)
      return
  -- server random, ephemeral key, its public key, the shared secret
  seeded(TL_L_RANDOM, 13)
  for j : u16 in [0, 32) do
    tl_srand[j] := sh_out[j]
  seeded(TL_L_ECDHE, 5)
  for k : u16 in [0, 32) do
    x_k[k] := sh_out[k]
    fe_in[k] := 0
  fe_in[0] := 9
  x25519()
  for m : u16 in [0, 32) do
    tl_pub[m] := fe_bytes[m]
    fe_in[m] := tl_share[m]
  x25519()
  let mut z : u8 := 0
  for q : u16 in [0, 32) do
    tl_ikm[q] := fe_bytes[q]
    z := z ||| fe_bytes[q]
  if z == 0 then
    fail(47)
    return
  -- ServerHello, in a record of its own
  let sl : u16 := tl_sidl
  ob(22)
  ob(3)
  ob(3)
  ob16(4 + 86 + sl)
  let shAt : u16 := t_outl[cur]
  hs_head(2, 86 + sl)
  ob16(0x0303)
  for r : u16 in [0, 32) do
    ob(tl_srand[r])
  ob((sl : u8))
  for r2 : u16 in [0, sl) do
    ob(tl_sid[r2])
  ob16(0x1303)
  ob(0)
  ob16(46)
  ob16(43)
  ob16(2)
  ob16(0x0304)
  ob16(51)
  ob16(36)
  ob16(0x001d)
  ob16(32)
  for r3 : u16 in [0, 32) do
    ob(tl_pub[r3])
  tr_out(shAt, t_outl[cur])
  -- the handshake secret and the handshake traffic secrets
  tr_hash()
  for a : u16 in [0, 32) do
    tl_salt[a] := TL_DERIVED1[a]
  extract()
  for a2 : u16 in [0, 32) do
    tl_hs[a2] := tl_sec[a2]
  derive(L_C_HS)
  for a3 : u16 in [0, 32) do
    tl_chs[a3] := tl_sec[a3]
    tl_sec[a3] := tl_hs[a3]
  derive(L_S_HS)
  for a4 : u16 in [0, 32) do
    tl_shs[a4] := tl_sec[a4]
  -- the master secret: Derive-Secret(hs, "derived", "") as salt, zeros as IKM
  for a5 : u16 in [0, 32) do
    tl_sec[a5] := tl_hs[a5]
    tl_th[a5] := TL_EMPTYH[a5]
  derive(L_DERIVED)
  for a6 : u16 in [0, 32) do
    tl_salt[a6] := tl_sec[a6]
    tl_ikm[a6] := 0
  extract()
  for a7 : u16 in [0, 32) do
    tl_ms[a7] := tl_sec[a7]
  -- ChangeCipherSpec
  ob(20)
  ob(3)
  ob(3)
  ob(0)
  ob(1)
  ob(1)
  -- EncryptedExtensions, Certificate, CertificateVerify, Finished in one protected record
  for a8 : u16 in [0, 32) do
    tl_sec[a8] := tl_shs[a8]
  set_keys(false)
  let pos : u16 := t_outl[cur]
  t_outl[cur] := pos + 5
  let p0 : u16 := t_outl[cur]
  hs_head(8, 2)
  ob16(0)
  let mut cl : u16 := CERT_LEN
  if tl_usep then
    cl := CERT2_LEN
  hs_head(11, cl + 9)
  ob(0)
  ob(0)
  ob16(cl + 5)
  ob(0)
  ob16(cl)
  for c : u16 in [0, cl) do
    if tl_usep then
      ob(TL_CERT2[c])
    else
      ob(TL_CERT[c])
  ob16(0)
  tr_out(p0, t_outl[cur])
  tr_hash()
  -- CertificateVerify: Ed25519 over 64 spaces, the context string, 0, the hash
  for e : u16 in [0, 64) do
    ed_msg[e] := 0x20
  for e2 : u16 in [0, 33) do
    ed_msg[64 + e2] := TL_CVCTX[e2]
  ed_msg[97] := 0
  for e3 : u16 in [0, 32) do
    ed_msg[98 + e3] := tl_th[e3]
  ed_mlen := 130
  let p1 : u16 := t_outl[cur]
  if tl_usep then
    for e4 : u16 in [0, 32) do
      p2_d[e4] := TL_KEY2[e4]
    p2_sign()
    hs_head(15, 4 + p2_siglen)
    ob16(0x0403)
    ob16(p2_siglen)
    for e6 : u16 in [0, p2_siglen) do
      ob(p2_sig[e6])
  else
    for e7 : u16 in [0, 32) do
      ed_sk[e7] := TL_KEY[e7]
    ed_sign()
    hs_head(15, 68)
    ob16(0x0807)
    ob16(64)
    for e5 : u16 in [0, 64) do
      ob(ed_sig[e5])
  tr_out(p1, t_outl[cur])
  tr_hash()
  -- the server's Finished
  for f : u16 in [0, 32) do
    tl_sec[f] := tl_shs[f]
  expand_label(L_FINISHED, false, 32)
  for f2 : u16 in [0, 64) do
    hm_key[f2] := 0
  for f3 : u16 in [0, 32) do
    hm_key[f3] := hk_out[f3]
  hmac_begin()
  for f4 : u16 in [0, 32) do
    sha_byte(tl_th[f4])
  hmac_end()
  let p2 : u16 := t_outl[cur]
  hs_head(20, 32)
  for f5 : u16 in [0, 32) do
    ob(sh_out[f5])
  tr_out(p2, t_outl[cur])
  ob(22)
  rec_seal(pos, t_outl[cur] - pos - 5)
  -- the transcript to the server's Finished: the client's Finished and the application secrets
  tr_hash()
  for g : u16 in [0, 32) do
    t_th[cur * 32 + g] := tl_th[g]
    tl_sec[g] := tl_ms[g]
  derive(L_C_AP)
  for g2 : u16 in [0, 32) do
    t_cap[cur * 32 + g2] := tl_sec[g2]
    tl_sec[g2] := tl_ms[g2]
  derive(L_S_AP)
  for g3 : u16 in [0, 32) do
    t_sap[cur * 32 + g3] := tl_sec[g3]
    tl_sec[g3] := tl_chs[g3]
  -- to receive: the client's handshake keys; its Finished key; nothing to send with yet
  set_keys(true)
  expand_label(L_FINISHED, false, 32)
  for g4 : u16 in [0, 32) do
    t_cfin[cur * 32 + g4] := hk_out[g4]
  t_wset[cur] := false
  t_phase[cur] := PH_FINISHED

/-! ## Records (as `Spec.Srv.Tls.onRecord`) -/

ember def on_record (bl : u16) := do
  let ty : u16 ← ib(0)
  let ph : u8 := t_phase[cur]
  if ph == PH_CLOSED then
    return
  if ph == PH_HELLO then
    if ty != 22 then
      fail(10)
      return
    let ok : bool ← parse_hello(bl)
    if ok then
      flight(bl)
    else
      fail(40)
    return
  if ph == PH_FINISHED then
    if ty == 20 then
      let b0 : u16 ← ib(5)
      if bl != 1 || b0 != 1 then
        fail(10)
      return
    if ty != 23 then
      fail(10)
      return
    let ok2 : bool ← open_rec(bl)
    if !ok2 then
      fail(20)
      return
    -- the client's Finished: HMAC(its Finished key, the transcript to the server's)
    for i : u16 in [0, 64) do
      hm_key[i] := 0
    for j : u16 in [0, 32) do
      hm_key[j] := t_cfin[cur * 32 + j]
    hmac_begin()
    for k : u16 in [0, 32) do
      sha_byte(t_th[cur * 32 + k])
    hmac_end()
    let mut same : bool := tl_ity == 22 && tl_ilen == 36
    if same then
      let h0 : u16 ← ib(5)
      let h1 : u16 ← ib(6)
      let h2 : u16 ← ib16(7)
      same := h0 == 20 && h1 == 0 && h2 == 32
      let mut diff : u8 := 0
      for m : u16 in [0, 32) do
        diff := diff ||| (sh_out[m] ^^^ t_inb[cur * INB + 9 + m])
      same := same && diff == 0
    if !same then
      fail(51)
      return
    for q : u16 in [0, 32) do
      tl_sec[q] := t_cap[cur * 32 + q]
    set_keys(true)
    for q2 : u16 in [0, 32) do
      tl_sec[q2] := t_sap[cur * 32 + q2]
    set_keys(false)
    t_phase[cur] := PH_APP
    return
  -- the application phase
  if ty != 23 then
    fail(10)
    return
  let ok3 : bool ← open_rec(bl)
  if !ok3 then
    fail(20)
    return
  if tl_ity == 21 then
    respond(false)
    return
  if tl_ity != 23 then
    fail(10)
    return
  -- the request, byte by byte, as `Net.Http` takes it
  for r : u16 in [0, tl_ilen) do
    if !h_dec[cur] then
      h_feed(t_inb[cur * INB + 5 + r])
  if h_dec[cur] then
    respond(true)

/-- Take every whole record from `t_inb` (as `Spec.Srv.Tls.drain`). -/
ember def drain := do
  loop (max := 64) do
    if t_inl[cur] < 5 || t_phase[cur] == PH_CLOSED then
      break
    let bl : u16 ← ib16(3)
    if bl > REC_MAX then
      t_inl[cur] := 0
      fail(22)
      break
    if t_inl[cur] < 5 + bl then
      break
    on_record(bl)
    -- drop the record: the rest moves to the front
    let rest : u16 := t_inl[cur] - 5 - bl
    for i : u16 in [0, rest) do
      t_inb[cur * INB + i] := t_inb[cur * INB + 5 + bl + i]
    t_inl[cur] := rest

/-! ## The application interface of `Net.Srv` -/

ember def app_reset := do
  t_phase[cur] := PH_HELLO
  t_done[cur] := false
  t_inl[cur] := 0
  t_outl[cur] := 0
  t_wset[cur] := false
  t_rseq[cur] := 0
  t_wseq[cur] := 0
  h_rlen[cur] := 0
  h_crlf[cur] := 0
  h_seen[cur] := 0
  h_dec[cur] := false
  h_kind[cur] := 0
  h_head[cur] := false
  h_pos[cur] := 0

ember def app_room (c : u16) : u16 := do
  if t_phase[cur] == PH_CLOSED then
    return c
  let r : u16 := REC_MAX + 5 - t_inl[cur]
  if r < c then
    return r
  return c

ember def app_recv (off : u16) (n : u16) := do
  if t_phase[cur] == PH_CLOSED then
    return
  for i : u16 in [0, n) do
    t_inb[cur * INB + t_inl[cur] + i] := buf[off + i]
  t_inl[cur] := t_inl[cur] + n
  drain()

ember def app_avail : u16 := do
  return t_outl[cur]

ember def app_fill (src : u16) (n : u16) (dst : u16) := do
  for i : u16 in [0, n) do
    buf[dst + i] := t_out[cur * OUTB + src + i]

ember def app_acked (n : u16) := do
  for i : u16 in [0, t_outl[cur] - n) do
    t_out[cur * OUTB + i] := t_out[cur * OUTB + n + i]
  t_outl[cur] := t_outl[cur] - n

ember def app_close : bool := do
  return t_done[cur]

/-! ## Constants and the program -/

def labels : List String :=
  ["derived", "c hs traffic", "s hs traffic", "c ap traffic", "s ap traffic", "key", "iv", "finished",
   "server random", "ecdhe"]

def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

def scalar (name : String) (ty : Ty) (v : Nat) : Global := { name, ty, init := [v], const := true }
def table (name : String) (ty : Ty) (xs : List Nat) : Global :=
  { name, ty := .arr ty (max 1 xs.length), init := xs, const := true }

open Ember.Spec.Crypto Ember.Spec.Srv in
/-- The TLS application of `site` for `n` connections. -/
def app (n : Nat) (site : Tls.Site) (outb : Nat := 4096) : Net.Srv.App :=
  let h := Net.Http.app n site.http (crypto := false)
  let prot := Net.Auth.protected? site.http || site.http.ctl
  let labs := labels.map bytesOf
  let loff := (labs.foldl (fun (acc, o) l => (acc ++ [o], o + l.length)) (([] : List Nat), 0)).1
  let early := hkdfExtract (Tls.zeros 32) (Tls.zeros 32)
  let derived1 := Tls.deriveSecret early "derived" .empty
  let idx (s : String) : Nat := (labels.findIdx? (· == s)).getD 0
  let inb := site.recMax + 5
  let hglobals := h.globals.filter fun g => !["APP_PORT", "APP_IDLE_CLOSE", "APP_REUSE_TW"].contains g.name
  { globals := hglobals ++
      [scalar "APP_PORT" .u16 site.port.toNat,
       { name := "APP_IDLE_CLOSE", ty := .bool, init := [1] }, { name := "APP_REUSE_TW", ty := .bool, init := [1] },
       scalar "INB" .u16 inb, scalar "OUTB" .u16 outb, scalar "REC_MAX" .u16 site.recMax,
       scalar "CHUNK" .u16 site.chunk, scalar "CERT_LEN" .u16 site.cert.size,
       scalar "PH_HELLO" .u8 0, scalar "PH_FINISHED" .u8 1, scalar "PH_APP" .u8 2, scalar "PH_CLOSED" .u8 3,
       scalar "L_DERIVED" .u16 (idx "derived"), scalar "L_C_HS" .u16 (idx "c hs traffic"),
       scalar "L_S_HS" .u16 (idx "s hs traffic"), scalar "L_C_AP" .u16 (idx "c ap traffic"),
       scalar "L_S_AP" .u16 (idx "s ap traffic"), scalar "L_KEY" .u16 (idx "key"), scalar "L_IV" .u16 (idx "iv"),
       scalar "L_FINISHED" .u16 (idx "finished"),
       scalar "TL_L_RANDOM" .u16 (loff.getD (idx "server random") 0), scalar "TL_L_ECDHE" .u16 (loff.getD (idx "ecdhe") 0),
       table "TL_LABELS" .u8 labs.flatten, table "TL_LOFF" .u16 loff, table "TL_LLEN" .u16 (labs.map (·.length)),
       table "TL_TLS13" .u8 (bytesOf "tls13 "), table "TL_CVCTX" .u8 (bytesOf "TLS 1.3, server CertificateVerify"),
       table "TL_CERT" .u8 (site.cert.toList.map (·.toNat)), table "TL_KEY" .u8 (site.key.toList.map (·.toNat)),
       table "TL_CERT2" .u8 (site.certP256.toList.map (·.toNat)), scalar "CERT2_LEN" .u16 site.certP256.size,
       table "TL_KEY2" .u8 ((natBe site.keyP256 32).toList.map (·.toNat)),
       { name := "tl_sig_ed", ty := .bool }, { name := "tl_sig_p", ty := .bool }, { name := "tl_usep", ty := .bool },
       table "TL_SEED" .u8 (site.seed.toList.map (·.toNat)), scalar "TL_SEEDLEN" .u16 site.seed.size,
       { name := "TL_HWRNG", ty := .bool, init := [if site.entropy.isSome then 1 else 0], const := true },
       -- the ESP32-C3's RNG data register (plan M9.4), and the bytes read from it
       scalar "RNG_DATA" .u32 0x600260B0, { name := "tl_ent", ty := .arr .u8 32 },
       table "TL_DERIVED1" .u8 (derived1.toList.map (·.toNat)),
       table "TL_EMPTYH" .u8 ((sha256 .empty).toList.map (·.toNat)),
       { name := "t_phase", ty := .arr .u8 n }, { name := "t_done", ty := .arr .bool n },
       { name := "t_inb", ty := .arr .u8 (n * inb) }, { name := "t_inl", ty := .arr .u16 n },
       { name := "t_out", ty := .arr .u8 (n * outb) }, { name := "t_outl", ty := .arr .u16 n },
       { name := "t_tr_h", ty := .arr .u32 (8 * n) }, { name := "t_tr_blk", ty := .arr .u8 (64 * n) },
       { name := "t_tr_n", ty := .arr .u16 n }, { name := "t_tr_len", ty := .arr .u32 n },
       { name := "t_rk", ty := .arr .u8 (32 * n) }, { name := "t_riv", ty := .arr .u8 (12 * n) },
       { name := "t_rseq", ty := .arr .u32 n },
       { name := "t_wk", ty := .arr .u8 (32 * n) }, { name := "t_wiv", ty := .arr .u8 (12 * n) },
       { name := "t_wseq", ty := .arr .u32 n }, { name := "t_wset", ty := .arr .bool n },
       { name := "t_cfin", ty := .arr .u8 (32 * n) }, { name := "t_cap", ty := .arr .u8 (32 * n) },
       { name := "t_sap", ty := .arr .u8 (32 * n) }, { name := "t_th", ty := .arr .u8 (32 * n) },
       { name := "tl_th", ty := .arr .u8 32 }, { name := "tl_sec", ty := .arr .u8 32 },
       { name := "tl_salt", ty := .arr .u8 32 }, { name := "tl_ikm", ty := .arr .u8 32 },
       { name := "tl_hs", ty := .arr .u8 32 }, { name := "tl_chs", ty := .arr .u8 32 },
       { name := "tl_shs", ty := .arr .u8 32 }, { name := "tl_ms", ty := .arr .u8 32 },
       { name := "tl_crand", ty := .arr .u8 32 }, { name := "tl_srand", ty := .arr .u8 32 },
       { name := "tl_sid", ty := .arr .u8 32 }, { name := "tl_sidl", ty := .u16 },
       { name := "tl_share", ty := .arr .u8 32 }, { name := "tl_pub", ty := .arr .u8 32 },
       { name := "tl_msg", ty := .arr .u8 8 }, { name := "tl_ity", ty := .u8 }, { name := "tl_ilen", ty := .u16 }] ++
      Net.Crypto.sha256Globals ++ Net.Crypto.chachaGlobals ++ Net.Crypto.x25519Globals ++
      Net.Crypto.sha512Globals ++ Net.Crypto.ed25519Globals ++ Net.Crypto.p256Globals (verify := prot)
    fns := (if site.http.ctl then [Net.Ctl.Tls.h_kept] else [Net.Http.h_byte, Net.Http.h_total]) ++ Net.Http.feedFns site.http ++
      Net.Crypto.sha256Fns ++ Net.Crypto.chachaFns ++ Net.Crypto.x25519Fns ++ Net.Crypto.sha512Fns ++
      Net.Crypto.ed25519Fns ++ Net.Crypto.p256Fns ++ (if prot then Net.Crypto.p256VerifyFns else []) ++
      [ib, ib16, ob, ob16, tr_load, tr_store, tr_hash, tr_out, expand_label, extract, derive, set_keys,
       use_keys, rec_seal, seal_msg, open_rec, fail, respond, parse_hello, seeded, hs_head, flight, on_record,
       drain, app_reset, app_room, app_recv, app_avail, app_fill, app_acked, app_close] }

/-- The HTTPS server for `site` on `n` connections (SLIP, MTU 296). -/
def prog (n : Nat) (site : Spec.Srv.Tls.Site) : Prog := Net.Srv.prog n (app n site)

end Ember.Net.Tls
