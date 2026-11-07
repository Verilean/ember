import Ember.Net.Crypto.P256
import Ember.Spec.Srv.Http

/-!
# Ember.Net.Auth — OIDC access tokens, read as they arrive (plan M9.3)

`Spec.Srv.Auth.check` and the protected routes of `Spec.Srv.Http`, for
`Net.Http` (and so for HTTPS, whose records feed the same `h_feed`).
Nothing of the token is kept but what the check needs:

* the header's lines are followed byte by byte (`ha_line`): the field
  name `authorization` (any case) and a colon start the first such
  field's value; the number of such fields is counted (two or more: 400);
* the value (`ha_vbyte`): white space, the scheme `bearer` (any case), the
  spaces, the token, white space at the end; a CR right before the LF
  ends the line, any other CR is a byte of the value;
* the token (`j_char`): base64url, strict, by segment; the signing input
  (`header.payload` as ASCII) goes into a SHA-256 context of the
  connection (`a_h`, `a_blk`); the two decoded JSON texts into one
  scanner (`js_byte`), which keeps a depth and a bit per level (array or
  object) and looks at the top level only; the signature into `j_sig`;
* the claims are compared with the configuration as they are decoded:
  `alg` with `ES256`, `kid` with each key's id, `iss`, `aud` (a string or
  an array of strings), `exp`, `nbf` and `iat` as numbers, `scope`'s words with
  every scope a route of the site needs (a bit each, `j_grant`);
* when the header is complete and the route is protected (`ha_decide`),
  the answer is chosen as `Spec.Srv.Http.guard` chooses it; only then is
  the hash finished and the signature verified (`p2_verify`).

The state of a connection is reset with its first byte of a request
(`h_seen` is 0), so `Net.Http` and `Net.Tls` need no change: a program
with protected routes takes this module's `h_feed` in place of
`Net.Http.h_feed`.
-/

namespace Ember.Net.Auth
open Ember.Lang

/-! ## SHA-256 of the signing input, a context per connection -/

ember def a_hash_byte (x : u8) := do
  a_blk[cur * 64 + a_bn[cur]] := x
  a_bn[cur] := a_bn[cur] + 1
  a_len[cur] := a_len[cur] + 1
  if a_bn[cur] == 64 then
    for i : u16 in [0, 8) do
      sh_h[i] := a_h[cur * 8 + i]
    for j : u16 in [0, 64) do
      sh_blk[j] := a_blk[cur * 64 + j]
    sha_block()
    for k : u16 in [0, 8) do
      a_h[cur * 8 + k] := sh_h[k]
    a_bn[cur] := 0

/-- The hash of the signing input, into `p2_h`. -/
ember def a_hash_final := do
  for i : u16 in [0, 8) do
    sh_h[i] := a_h[cur * 8 + i]
  for j : u16 in [0, 64) do
    sh_blk[j] := a_blk[cur * 64 + j]
  sh_n := a_bn[cur]
  sh_len := a_len[cur]
  sha_final()
  for k : u16 in [0, 32) do
    p2_h[k] := sh_out[k]

/-! ## The JSON scanner -/

ember def js_bad := do
  j_bad[cur] := true

/-- Is the container at the current depth an array? -/
ember def js_isarr : bool := do
  let d : u16 := (j_dep[cur] : u16)
  return ((j_arr[cur] >>> (d - 1)) &&& 1) == 1

/-- A value is complete; `kind`: 0 a string, 1 a short non-negative integer, 2 anything else. -/
ember def js_vdone (kind : u8) := do
  let d : u8 := j_dep[cur]
  let u : bool := j_u[cur]
  let sp : u16 := j_spos[cur]
  if d == 2 && j_inaud[cur] && kind == 0 then
    if !u && j_vok[cur] && sp == A_AUD_LEN then
      j_audhit[cur] := true
  if d != 1 then
    return
  let key : u8 := j_key[cur]
  if key == 1 then
    j_algok[cur] := kind == 0 && !u && j_vok[cur] && sp == 5
  if key == 2 then
    if kind != 0 || u then
      js_bad()
    else
      let mut m : u8 := 0
      for i : u16 in [0, N_KEYS) do
        if ((j_vmask[cur] >>> (i : u8)) &&& 1) == 1 && A_KLEN[i] == sp then
          m := m ||| ((1 : u8) <<< (i : u8))
      j_kid[cur] := m
  if key == 3 then
    js_bad()
  if key == 4 then
    j_issok[cur] := kind == 0 && !u && j_vok[cur] && sp == A_ISS_LEN
  if key == 5 then
    if j_inaud[cur] then
      j_audok[cur] := j_audhit[cur] && !j_audbad[cur]
      j_inaud[cur] := false
    else
      j_audok[cur] := kind == 0 && !u && j_vok[cur] && sp == A_AUD_LEN
  if key == 6 then
    if kind == 1 then
      j_exp[cur] := j_num[cur]
      j_expok[cur] := true
    else
      js_bad()
  if key == 7 then
    if kind == 1 then
      j_nbf[cur] := j_num[cur]
      j_nbfok[cur] := true
    else
      js_bad()
  if key == 9 then
    if kind == 1 then
      j_iat[cur] := j_num[cur]
      j_iatok[cur] := true
    else
      js_bad()
  if key == 8 then
    if kind != 0 || u then
      js_bad()
    else
      -- the last word
      if j_wpos[cur] > 0 then
        for i2 : u16 in [0, N_SC) do
          if ((j_walive[cur] >>> (i2 : u8)) &&& 1) == 1 && A_SCLEN[i2] == j_wpos[cur] then
            j_grant[cur] := j_grant[cur] ||| ((1 : u8) <<< (i2 : u8))

/-- One decoded byte of a string. -/
ember def js_sbyte (b : u8) := do
  let sp : u16 := j_spos[cur]
  if j_isk[cur] && j_dep[cur] == 1 then
      for i : u16 in [0, 9) do
        if ((j_kmask[cur] >>> (i : u8)) &&& 1) == 1 then
          let mut same : bool := false
          if sp < JK_LEN[i] then
            same := JK[JK_OFF[i] + sp] == b
          if !same then
            j_kmask[cur] := j_kmask[cur] &&& (~~~((1 : u16) <<< (i : u8)))
  if !j_isk[cur] then
    let key : u8 := j_key[cur]
    let d : u8 := j_dep[cur]
    if d == 1 && key == 1 then
      let mut same1 : bool := false
      if sp < 5 then
        same1 := A_ALG[sp] == b
      if !same1 then
        j_vok[cur] := false
    if d == 1 && key == 4 then
      let mut same2 : bool := false
      if sp < A_ISS_LEN then
        same2 := A_ISS[sp] == b
      if !same2 then
        j_vok[cur] := false
    if (d == 1 && key == 5) || (d == 2 && j_inaud[cur]) then
      let mut same3 : bool := false
      if sp < A_AUD_LEN then
        same3 := A_AUD[sp] == b
      if !same3 then
        j_vok[cur] := false
    if d == 1 && key == 2 then
      for k : u16 in [0, N_KEYS) do
        if ((j_vmask[cur] >>> (k : u8)) &&& 1) == 1 then
          let mut same4 : bool := false
          if sp < A_KLEN[k] then
            same4 := A_KIDS[A_KOFF[k] + sp] == b
          if !same4 then
            j_vmask[cur] := j_vmask[cur] &&& (~~~((1 : u8) <<< (k : u8)))
    if d == 1 && key == 8 then
      let wp : u16 := j_wpos[cur]
      if b == 32 then
        if wp > 0 then
          for i2 : u16 in [0, N_SC) do
            if ((j_walive[cur] >>> (i2 : u8)) &&& 1) == 1 && A_SCLEN[i2] == wp then
              j_grant[cur] := j_grant[cur] ||| ((1 : u8) <<< (i2 : u8))
        j_wpos[cur] := 0
        j_walive[cur] := 0xFF
      else
        for i3 : u16 in [0, N_SC) do
          if ((j_walive[cur] >>> (i3 : u8)) &&& 1) == 1 then
            let mut same5 : bool := false
            if wp < A_SCLEN[i3] then
              same5 := A_SC[A_SCOFF[i3] + wp] == b
            if !same5 then
              j_walive[cur] := j_walive[cur] &&& (~~~((1 : u8) <<< (i3 : u8)))
        if wp < 1000 then
          j_wpos[cur] := wp + 1
  if sp < 1000 then
    j_spos[cur] := sp + 1

ember def js_sstart (isKey : bool) := do
  j_isk[cur] := isKey
  j_st[cur] := J_STR
  j_spos[cur] := 0
  j_esc[cur] := 0
  j_u[cur] := false
  j_vok[cur] := true
  j_vmask[cur] := 0xFF
  j_wpos[cur] := 0
  j_walive[cur] := 0xFF
  if isKey then
    if j_seg[cur] == 0 then
      j_kmask[cur] := 0x07
    else
      j_kmask[cur] := 0x1F8

/-- A key's closing quote: at the top level, which key it is (and was it there before). -/
ember def js_kend := do
  j_st[cur] := J_COLON
  if j_dep[cur] != 1 then
    return
  let mut key : u8 := 0
  for i : u16 in [0, 9) do
    if ((j_kmask[cur] >>> (i : u8)) &&& 1) == 1 && JK_LEN[i] == j_spos[cur] then
      key := (i : u8) + 1
  j_key[cur] := key
  if key != 0 then
    let bit : u16 := (1 : u16) <<< (key - 1)
    if (j_seen[cur] &&& bit) != 0 then
      js_bad()
    j_seen[cur] := j_seen[cur] ||| bit

/-- A string's byte (inside the quotes, escapes as they come). -/
ember def js_str (x : u8) := do
  let e : u8 := j_esc[cur]
  if e == 0 then
    if x == 34 then
      if j_isk[cur] then
        js_kend()
        return
      j_st[cur] := J_AFTER
      js_vdone(0)
      return
    if x < 32 then
      js_bad()
      return
    if x == 92 then
      if j_isk[cur] && j_dep[cur] == 1 then
        js_bad()
        return
      j_esc[cur] := 1
      return
    js_sbyte(x)
    return
  if e == 1 then
    j_esc[cur] := 0
    if x == 34 || x == 92 || x == 47 then
      js_sbyte(x)
      return
    if x == 98 then
      js_sbyte(8)
      return
    if x == 102 then
      js_sbyte(12)
      return
    if x == 110 then
      js_sbyte(10)
      return
    if x == 114 then
      js_sbyte(13)
      return
    if x == 116 then
      js_sbyte(9)
      return
    if x == 117 then
      j_u[cur] := true
      j_esc[cur] := 2
      return
    js_bad()
    return
  -- four hex digits of `\u`
  let hex : bool := (x >= 48 && x <= 57) || (x >= 97 && x <= 102) || (x >= 65 && x <= 70)
  if !hex then
    js_bad()
    return
  if e == 5 then
    j_esc[cur] := 0
  else
    j_esc[cur] := e + 1

ember def js_close := do
  j_dep[cur] := j_dep[cur] - 1
  if j_dep[cur] == 0 then
    j_st[cur] := J_DONE
    return
  j_st[cur] := J_AFTER
  js_vdone(2)

/-- The first byte of a value (white space skipped). -/
ember def js_vstart (x : u8) := do
  let d : u8 := j_dep[cur]
  if x == 34 then
    js_sstart(false)
    return
  if d == 2 && j_inaud[cur] then
    j_audbad[cur] := true
  if x == 123 || x == 91 then
    if d + 1 > 16 then
      js_bad()
      return
    if d == 1 && x == 91 && j_key[cur] == 5 then
      j_inaud[cur] := true
      j_audhit[cur] := false
      j_audbad[cur] := false
    j_dep[cur] := d + 1
    let bit : u16 := (1 : u16) <<< (d : u16)
    if x == 91 then
      j_arr[cur] := j_arr[cur] ||| bit
      j_st[cur] := J_VOE
    else
      j_arr[cur] := j_arr[cur] &&& (~~~bit)
      j_st[cur] := J_KOE
    return
  if x == 45 || (x >= 48 && x <= 57) then
    j_st[cur] := J_NUM
    j_num[cur] := 0
    j_ndig[cur] := 0
    j_nplain[cur] := x != 45
    if x == 45 then
      j_sub[cur] := N_MINUS
    else
      j_ndig[cur] := 1
      j_num[cur] := (x - 48 : u64)
      if x == 48 then
        j_sub[cur] := N_ZERO
      else
        j_sub[cur] := N_INT
    return
  let mut lid : u8 := 3
  if x == 116 then
    lid := 0
  if x == 102 then
    lid := 1
  if x == 110 then
    lid := 2
  if lid == 3 then
    js_bad()
    return
  j_st[cur] := J_LIT
  j_lid[cur] := lid
  j_sub[cur] := 1

ember def js_lit (x : u8) := do
  let lid : u16 := (j_lid[cur] : u16)
  let lp : u16 := (j_sub[cur] : u16)
  if LITS[LIT_OFF[lid] + lp] != x then
    js_bad()
    return
  if lp + 1 == LIT_LEN[lid] then
    j_st[cur] := J_AFTER
    js_vdone(2)
    return
  j_sub[cur] := (lp + 1 : u8)

/-- The number ends before `x`: its value is complete. -/
ember def js_nend := do
  j_st[cur] := J_AFTER
  if j_nplain[cur] && j_ndig[cur] <= 12 then
    js_vdone(1)
  else
    js_vdone(2)

/-- A byte while in a number; true when the number ended before it. -/
ember def js_num (x : u8) : bool := do
  let s : u8 := j_sub[cur]
  let dig : bool := x >= 48 && x <= 57
  if s == N_MINUS then
    if dig then
      if x == 48 then
        j_sub[cur] := N_ZERO
      else
        j_sub[cur] := N_INT
    else
      js_bad()
    return false
  if s == N_INT && dig then
    if j_ndig[cur] < 13 then
      j_num[cur] := j_num[cur] * 10 + (x - 48 : u64)
      j_ndig[cur] := j_ndig[cur] + 1
    return false
  if s == N_INT || s == N_ZERO then
    if x == 46 then
      j_nplain[cur] := false
      j_sub[cur] := N_DOT
      return false
    if x == 101 || x == 69 then
      j_nplain[cur] := false
      j_sub[cur] := N_E
      return false
    js_nend()
    return true
  if s == N_DOT then
    if dig then
      j_sub[cur] := N_FRAC
    else
      js_bad()
    return false
  if s == N_FRAC then
    if dig then
      return false
    if x == 101 || x == 69 then
      j_sub[cur] := N_E
      return false
    js_nend()
    return true
  if s == N_E then
    if x == 43 || x == 45 then
      j_sub[cur] := N_ESIGN
    else
      if dig then
        j_sub[cur] := N_EXP
      else
        js_bad()
    return false
  if s == N_ESIGN then
    if dig then
      j_sub[cur] := N_EXP
    else
      js_bad()
    return false
  -- N_EXP
  if dig then
    return false
  js_nend()
  return true

/-- One byte of a decoded JSON text. -/
ember def js_byte (x : u8) := do
  if j_bad[cur] then
    return
  if j_st[cur] == J_NUM then
    let ended : bool ← js_num(x)
    if !ended || j_bad[cur] then
      return
  let st : u8 := j_st[cur]
  if st == J_STR then
    js_str(x)
    return
  if st == J_LIT then
    js_lit(x)
    return
  if x == 32 || x == 9 || x == 10 || x == 13 then
    return
  if st == J_BEGIN then
    if x == 123 then
      j_dep[cur] := 1
      j_arr[cur] := 0
      j_st[cur] := J_KOE
    else
      js_bad()
    return
  if st == J_KOE then
    if x == 125 then
      js_close()
      return
    if x == 34 then
      js_sstart(true)
      return
    js_bad()
    return
  if st == J_KEY then
    if x == 34 then
      js_sstart(true)
      return
    js_bad()
    return
  if st == J_COLON then
    if x == 58 then
      j_st[cur] := J_VAL
    else
      js_bad()
    return
  if st == J_VOE then
    if x == 93 then
      js_close()
      return
    js_vstart(x)
    return
  if st == J_VAL then
    js_vstart(x)
    return
  if st == J_AFTER then
    let arr : bool ← js_isarr()
    if x == 44 then
      if arr then
        j_st[cur] := J_VAL
      else
        j_st[cur] := J_KEY
      return
    if (x == 125 && !arr) || (x == 93 && arr) then
      js_close()
      return
    js_bad()
    return
  -- J_DONE: only white space
  js_bad()

/-! ## The token: base64url by segment -/

ember def j_reset_json := do
  j_st[cur] := J_BEGIN
  j_dep[cur] := 0
  j_arr[cur] := 0
  j_inaud[cur] := false
  j_key[cur] := 0

/-- The end of a segment: the base64url's tail, and what the segment holds. -/
ember def j_segend := do
  if j_cnt[cur] == 1 || j_acc[cur] != 0 then
    js_bad()
  let sgi : u8 := j_seg[cur]
  if sgi <= 1 && j_st[cur] != J_DONE then
    js_bad()
  if sgi == 2 && j_slen[cur] != 64 then
    js_bad()

ember def j_out (b : u8) := do
  let sgi : u8 := j_seg[cur]
  if sgi <= 1 then
    js_byte(b)
    return
  if j_slen[cur] < 64 then
    j_sig[cur * 64 + (j_slen[cur] : u16)] := b
  if j_slen[cur] < 65 then
    j_slen[cur] := j_slen[cur] + 1

ember def j_char (x : u8) := do
  if j_bad[cur] then
    return
  if x == 46 then
    j_segend()
    if j_seg[cur] == 2 then
      js_bad()
    if j_bad[cur] then
      return
    if j_seg[cur] == 0 then
      a_hash_byte(46)
    j_seg[cur] := j_seg[cur] + 1
    j_cnt[cur] := 0
    j_acc[cur] := 0
    j_nb[cur] := 0
    j_reset_json()
    return
  let mut v : u16 := 64
  if x >= 65 && x <= 90 then
    v := (x - 65 : u16)
  if x >= 97 && x <= 122 then
    v := (x - 71 : u16)
  if x >= 48 && x <= 57 then
    v := (x : u16) + 4
  if x == 45 then
    v := 62
  if x == 95 then
    v := 63
  if v == 64 then
    js_bad()
    return
  if j_seg[cur] <= 1 then
    a_hash_byte(x)
  j_cnt[cur] := (j_cnt[cur] + 1) &&& 3
  let acc : u16 := (j_acc[cur] <<< 6) ||| v
  let nb : u8 := j_nb[cur] + 6
  if nb >= 8 then
    let rest : u8 := nb - 8
    j_nb[cur] := rest
    j_acc[cur] := acc &&& (((1 : u16) <<< (rest : u16)) - 1)
    j_out((acc >>> (rest : u16) : u8))
  else
    j_nb[cur] := nb
    j_acc[cur] := acc

/-- The token is complete (its line ended). -/
ember def j_fin := do
  if j_bad[cur] then
    return
  if j_seg[cur] != 2 then
    js_bad()
    return
  j_segend()

/-! ## The `Authorization` field -/

ember def ha_reset := do
  a_ln[cur] := L_REQ
  a_cnt[cur] := 0
  a_vs[cur] := 0
  a_cr[cur] := false
  a_res[cur] := RES_CHAL

ember def j_start := do
  j_bad[cur] := false
  j_seg[cur] := 0
  j_cnt[cur] := 0
  j_acc[cur] := 0
  j_nb[cur] := 0
  j_slen[cur] := 0
  j_reset_json()
  j_seen[cur] := 0
  j_algok[cur] := false
  j_kid[cur] := 0
  j_issok[cur] := false
  j_audok[cur] := false
  j_expok[cur] := false
  j_nbfok[cur] := false
  j_iatok[cur] := false
  j_grant[cur] := 0
  for i : u16 in [0, 8) do
    a_h[cur * 8 + i] := A_IV[i]
  a_bn[cur] := 0
  a_len[cur] := 0

/-- A byte of the field's value (not the CR that ends it). -/
ember def ha_vbyte (x : u8) := do
  let mut vs : u8 := a_vs[cur]
  let ows : bool := x == 32 || x == 9
  let mut lx : u8 := x
  if x >= 65 && x <= 90 then
    lx := x + 32
  if vs == V_LEAD then
    if ows then
      return
    vs := V_SCH
  if vs >= V_SCH && vs < V_SCH + 6 then
    if lx == BEARER[(vs - V_SCH : u16)] then
      a_vs[cur] := vs + 1
    else
      a_vs[cur] := V_SCHBAD
    return
  if vs == V_SCH + 6 then
    if x == 32 then
      a_vs[cur] := V_SP
      j_start()
      return
    if x == 9 then
      a_vs[cur] := V_SCHHT
      return
    a_vs[cur] := V_SCHBAD
    return
  if vs == V_SCHHT then
    if !ows then
      a_vs[cur] := V_SCHBAD
    return
  if vs == V_SP then
    if x == 32 then
      return
    if x == 9 then
      a_vs[cur] := V_TOKBAD
      return
    a_vs[cur] := V_TOK
    j_char(x)
    return
  if vs == V_TOK then
    if ows then
      a_vs[cur] := V_TRAIL
      return
    j_char(x)
    return
  if vs == V_TRAIL then
    if !ows then
      a_vs[cur] := V_TOKBAD

/-- The field's line ended: what its value is. -/
ember def ha_vend := do
  let vs : u8 := a_vs[cur]
  a_ln[cur] := 0
  if vs == V_TOK || vs == V_TRAIL then
    j_fin()
    a_res[cur] := RES_TOK
    return
  if vs == V_SCH + 6 || vs == V_SCHHT || vs == V_SP || vs == V_TOKBAD then
    a_res[cur] := RES_INV
    return
  a_res[cur] := RES_CHAL

/-- One byte of the request header, for the `Authorization` fields. -/
ember def ha_line (x : u8) := do
  let st : u8 := a_ln[cur]
  if st == L_VAL then
    if a_cr[cur] then
      a_cr[cur] := false
      if x == 10 then
        ha_vend()
        return
      ha_vbyte(13)
    if x == 13 then
      a_cr[cur] := true
      return
    if x == 10 then
      ha_vend()
      return
    ha_vbyte(x)
    return
  if x == 10 then
    a_ln[cur] := 0
    return
  if st == L_REQ || st == L_SKIP then
    return
  if st < 13 then
    let mut lx : u8 := x
    if x >= 65 && x <= 90 then
      lx := x + 32
    if lx == AUTHZ[(st : u16)] then
      a_ln[cur] := st + 1
    else
      a_ln[cur] := L_SKIP
    return
  -- `authorization` read: a colon makes it the field
  if x != 58 then
    a_ln[cur] := L_SKIP
    return
  if a_cnt[cur] < 2 then
    a_cnt[cur] := a_cnt[cur] + 1
  if a_cnt[cur] == 1 then
    a_ln[cur] := L_VAL
    a_vs[cur] := V_LEAD
    a_cr[cur] := false
  else
    a_ln[cur] := L_SKIP

/-! ## The answer on a protected route -/

/-- The time: `h_now` when it was set, plus the seconds since (the board's
runtime answers reads of `UPTIME` with the seconds since the start; 0 off
the board, where the time stays as set, as in the Spec). -/
ember def clock : u64 := do
  let up : u32 ← mmio.read32(UPTIME)
  let d : u32 := up - h_up_at
  return h_now + (d : u64)

/-- Is the token of the connection accepted (`Spec.Srv.Auth.check`)? -/
ember def ha_valid : bool := do
  if j_bad[cur] || !j_algok[cur] || !j_issok[cur] || !j_audok[cur] || !j_expok[cur] then
    return false
  let now : u64 ← clock()
  if now >= j_exp[cur] + A_SKEW then
    return false
  if j_nbfok[cur] && j_nbf[cur] > now + A_SKEW then
    return false
  -- the key: by `kid`, or the only one
  let mut key : u16 := 0xFFFF
  let byKid : bool := (j_seen[cur] &&& 2) != 0
  if byKid then
    for i : u16 in [0, N_KEYS) do
      if key == 0xFFFF && ((j_kid[cur] >>> (i : u8)) &&& 1) == 1 then
        key := i
  if !byKid && N_KEYS == 1 then
    key := 0
  if key == 0xFFFF then
    return false
  a_hash_final()
  for j : u16 in [0, 64) do
    p2_rs[j] := j_sig[cur * 64 + j]
    p2_q[j] := A_PUB[key * 64 + j]
  let ok : bool ← p2_verify()
  return ok

/-- The route `h_kind` is protected: the answer (`Spec.Srv.Http.guard`). -/
ember def ha_guard := do
  let route : u16 := (h_kind[cur] : u16)
  if a_cnt[cur] == 0 then
    h_kind[cur] := K_401C
    return
  if a_cnt[cur] >= 2 then
    h_kind[cur] := KB_400
    h_head[cur] := false
    return
  if a_res[cur] == RES_CHAL then
    h_kind[cur] := K_401C
    return
  if !A_HAVE || !h_now_ok then
    h_kind[cur] := K_503
    return
  if a_res[cur] == RES_INV then
    h_kind[cur] := K_401I
    return
  let ok : bool ← ha_valid()
  if !ok then
    h_kind[cur] := K_401I
    return
  let need : u8 := R_SCOPE[route]
  if need >= 2 && ((j_grant[cur] >>> (need - 2)) &&& 1) == 0 then
    h_kind[cur] := K_403 + (need - 2)

ember def ha_decide := do
  h_decide()
  let k : u16 := (h_kind[cur] : u16)
  if k < N_ROUTES then
    if R_SCOPE[k] != 0 then
      ha_guard()

/-- `Net.Http.h_feed` with the `Authorization` fields followed; it takes its
place in a program with protected routes. -/
ember def h_feed (x : u8) := do
  if h_seen[cur] == 0 then
    ha_reset()
  ha_line(x)
  let base : u16 := cur * REQ_MAX
  let rl : u16 := h_rlen[cur]
  if rl < REQ_MAX then
    h_req[base + rl] := x
    h_rlen[cur] := rl + 1
  let st : u8 := h_crlf[cur]
  let mut ns : u8 := 0
  if (st == 0 || st == 2) && x == 13 then
    ns := st + 1
  else
    if (st == 1 || st == 3) && x == 10 then
      ns := st + 1
    else
      if x == 13 then
        ns := 1
  h_crlf[cur] := ns
  h_seen[cur] := h_seen[cur] + 1
  if ns == 4 then
    let mut cr : bool := false
    for i : u16 in [0, h_rlen[cur]) do
      if h_req[base + i] == 13 then
        cr := true
    if cr then
      ha_decide()
    else
      h_kind[cur] := KB_400
      h_head[cur] := false
    h_dec[cur] := true
    return
  if h_seen[cur] >= HDR_MAX then
    h_kind[cur] := KB_400
    h_head[cur] := false
    h_dec[cur] := true

def fns : List Fn :=
  [a_hash_byte, a_hash_final, js_bad, js_isarr, js_vdone, js_sbyte, js_sstart, js_kend, js_str, js_close, js_vstart,
   js_lit, js_nend, js_num, js_byte, j_reset_json, j_segend, j_out, j_char, j_fin, ha_reset, j_start,
   ha_vbyte, ha_vend, ha_line, clock, ha_valid, ha_guard, ha_decide, h_feed]

/-- `fns` without `h_feed` (the control requests of M9.5 have their own). -/
def coreFns : List Fn := fns.filter (·.name != "h_feed")

def u8s (name : String) (xs : List Nat) : Global :=
  { name, ty := .arr .u8 (max 1 xs.length), init := xs, const := true }
def u16s (name : String) (xs : List Nat) : Global :=
  { name, ty := .arr .u16 (max 1 xs.length), init := xs, const := true }
def scalar (name : String) (ty : Ty) (v : Nat) : Global := { name, ty, init := [v], const := true }
def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)
def offsets (xs : List (List Nat)) : List Nat :=
  (xs.foldl (fun (acc, o) l => (acc ++ [o], o + l.length)) (([] : List Nat), 0)).1

/-- The scopes the routes of a site need, in order, each once. -/
def scopes (site : Spec.Srv.Http.Site) : List String :=
  site.routes.foldl (fun acc r => match r.scope with
    | some s => if s == "" || acc.contains s then acc else acc ++ [s]
    | none => acc) []

/-- Does a site have a protected route? -/
def protected? (site : Spec.Srv.Http.Site) : Bool := site.routes.any (·.scope.isSome)

open Ember.Spec.Srv in
/-- The globals of the token check for `site` on `n` connections; `nr`: its
number of routes (the kinds of the answers follow those of `Net.Http`). -/
def globals (n : Nat) (site : Http.Site) : List Global :=
  let nr := site.routes.length
  let cfg := site.auth.getD { keys := [], iss := "", aud := "" }
  let scs := scopes site
  let kids := cfg.keys.map (bytesOf ·.kid)
  let scb := scs.map bytesOf
  let jk := ["alg", "kid", "crit", "iss", "aud", "exp", "nbf", "scope", "iat"].map bytesOf
  let lits := ["true", "false", "null"].map bytesOf
  let rscope := site.routes.map fun r => match r.scope with
    | none => 0
    | some "" => 1
    | some s => 2 + (scs.findIdx? (· == s)).getD 0
  [scalar "K_401C" .u8 (nr + 3), scalar "K_401I" .u8 (nr + 4), scalar "K_503" .u8 (nr + 5), scalar "K_403" .u8 (nr + 6),
   u8s "R_SCOPE" rscope,
   u8s "AUTHZ" (bytesOf "authorization"), u8s "BEARER" (bytesOf "bearer"),
   u8s "JK" jk.flatten, u16s "JK_OFF" (offsets jk), u16s "JK_LEN" (jk.map (·.length)),
   u8s "LITS" lits.flatten, u16s "LIT_OFF" (offsets lits), u16s "LIT_LEN" (lits.map (·.length)),
   u8s "A_ALG" (bytesOf "ES256"),
   u8s "A_ISS" (bytesOf cfg.iss), scalar "A_ISS_LEN" .u16 cfg.iss.utf8ByteSize,
   u8s "A_AUD" (bytesOf cfg.aud), scalar "A_AUD_LEN" .u16 cfg.aud.utf8ByteSize,
   { name := "N_KEYS", ty := .u16, init := [cfg.keys.length] },
   u8s "A_KIDS" kids.flatten, u16s "A_KOFF" (offsets kids), u16s "A_KLEN" (kids.map (·.length)),
   u8s "A_PUB" (cfg.keys.flatMap fun k => (k.pub.extract 1 65).toList.map (·.toNat)),
   { name := "N_SC", ty := .u16, init := [scs.length] },
   u8s "A_SC" scb.flatten, u16s "A_SCOFF" (offsets scb), u16s "A_SCLEN" (scb.map (·.length)),
   scalar "A_SKEW" .u64 cfg.skew, { name := "A_HAVE", ty := .bool, init := [if site.auth.isSome then 1 else 0], const := true },
   { name := "A_IV", ty := .arr .u32 8, const := true,
     init := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19] },
   -- the time (plan M9.4: set by `Net.Ctl.time_in` while running): its value
   -- when set, the board's uptime then, the time of the start
   { name := "h_now", ty := .u64, init := [site.now.getD 0] },
   { name := "h_now_ok", ty := .bool, init := [if site.now.isSome then 1 else 0] },
   { name := "h_up_at", ty := .u32 }, { name := "h_boot", ty := .u64, init := [site.now.getD 0] },
   -- read by the ESP32-C3's runtime as the seconds since the start (SYSTIMER)
   scalar "UPTIME" .u32 0x60023040,
   scalar "L_REQ" .u8 16, scalar "L_SKIP" .u8 15, scalar "L_VAL" .u8 14,
   scalar "V_LEAD" .u8 0, scalar "V_SCH" .u8 10, scalar "V_SCHBAD" .u8 20, scalar "V_SCHHT" .u8 21,
   scalar "V_SP" .u8 22, scalar "V_TOK" .u8 23, scalar "V_TRAIL" .u8 24, scalar "V_TOKBAD" .u8 25,
   scalar "RES_CHAL" .u8 0, scalar "RES_INV" .u8 1, scalar "RES_TOK" .u8 2,
   scalar "J_BEGIN" .u8 0, scalar "J_KOE" .u8 1, scalar "J_KEY" .u8 2, scalar "J_STR" .u8 3, scalar "J_COLON" .u8 4,
   scalar "J_VAL" .u8 5, scalar "J_VOE" .u8 6, scalar "J_AFTER" .u8 7, scalar "J_NUM" .u8 8, scalar "J_LIT" .u8 9,
   scalar "J_DONE" .u8 10,
   scalar "N_MINUS" .u8 0, scalar "N_ZERO" .u8 1, scalar "N_INT" .u8 2, scalar "N_DOT" .u8 3, scalar "N_FRAC" .u8 4,
   scalar "N_E" .u8 5, scalar "N_ESIGN" .u8 6, scalar "N_EXP" .u8 7,
   -- per connection
   { name := "a_ln", ty := .arr .u8 n }, { name := "a_cnt", ty := .arr .u8 n }, { name := "a_vs", ty := .arr .u8 n },
   { name := "a_cr", ty := .arr .bool n }, { name := "a_res", ty := .arr .u8 n },
   { name := "a_h", ty := .arr .u32 (8 * n) }, { name := "a_blk", ty := .arr .u8 (64 * n) },
   { name := "a_bn", ty := .arr .u16 n }, { name := "a_len", ty := .arr .u32 n },
   { name := "j_bad", ty := .arr .bool n }, { name := "j_seg", ty := .arr .u8 n }, { name := "j_cnt", ty := .arr .u8 n },
   { name := "j_acc", ty := .arr .u16 n }, { name := "j_nb", ty := .arr .u8 n },
   { name := "j_sig", ty := .arr .u8 (64 * n) }, { name := "j_slen", ty := .arr .u8 n },
   { name := "j_st", ty := .arr .u8 n }, { name := "j_dep", ty := .arr .u8 n }, { name := "j_arr", ty := .arr .u16 n },
   { name := "j_sub", ty := .arr .u8 n }, { name := "j_lid", ty := .arr .u8 n }, { name := "j_esc", ty := .arr .u8 n },
   { name := "j_isk", ty := .arr .bool n }, { name := "j_u", ty := .arr .bool n }, { name := "j_spos", ty := .arr .u16 n },
   { name := "j_kmask", ty := .arr .u16 n }, { name := "j_key", ty := .arr .u8 n }, { name := "j_seen", ty := .arr .u16 n },
   { name := "j_vok", ty := .arr .bool n }, { name := "j_vmask", ty := .arr .u8 n },
   { name := "j_wpos", ty := .arr .u16 n }, { name := "j_walive", ty := .arr .u8 n }, { name := "j_grant", ty := .arr .u8 n },
   { name := "j_inaud", ty := .arr .bool n }, { name := "j_audhit", ty := .arr .bool n }, { name := "j_audbad", ty := .arr .bool n },
   { name := "j_algok", ty := .arr .bool n }, { name := "j_kid", ty := .arr .u8 n }, { name := "j_issok", ty := .arr .bool n },
   { name := "j_audok", ty := .arr .bool n }, { name := "j_expok", ty := .arr .bool n }, { name := "j_nbfok", ty := .arr .bool n },
   { name := "j_exp", ty := .arr .u64 n }, { name := "j_nbf", ty := .arr .u64 n }, { name := "j_num", ty := .arr .u64 n },
   { name := "j_iat", ty := .arr .u64 n }, { name := "j_iatok", ty := .arr .bool n },
   { name := "j_ndig", ty := .arr .u8 n }, { name := "j_nplain", ty := .arr .bool n }]

end Ember.Net.Auth
