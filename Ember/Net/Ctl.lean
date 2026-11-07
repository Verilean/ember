import Ember.Net.Auth

/-!
# Ember.Net.Ctl — control requests and kept connections (plan M9.5)

`Spec.Srv.Http.stepCtl` (and the TLS of `Spec.Srv.Tls.appData`) for a site
with control routes or `keepAlive`.  It takes the place of `Net.Http`'s
`h_feed`, `h_byte`, `h_total` and of `Net.Auth`'s `h_feed` in such a
program:

* the header's lines are read for five names at once (`hc_line`):
  `authorization` (whose value goes to `Net.Auth`'s reader), and the
  values of `content-length` and `x-ember-seq` (canonical decimals),
  `transfer-encoding` (counted) and `connection` (`close` among its
  comma-separated tokens?);
* once the header is complete (`hc_decide`) the answer or the body to
  read is chosen as `Spec.Srv.Http.answerCtl` chooses it;
* the body goes into a buffer of the connection and into the SHA-256
  context of `Net.Auth`; when it is complete, the shared state
  (`ctl_last`, `ctl_hash`, the device's command `ctl_cmd`) decides
  (`hc_exec`), and `200 ok N` is written into the connection's buffer
  `h_dyn` (the one response not in ROM);
* a kept response calls `h_kept`: the TLS program seals it and takes the
  next request at once (`Spec.Srv.Tls.appData`); the HTTP program does
  nothing, and takes the next request once the response is acknowledged
  (`app_acked`), refusing data meanwhile (`app_room` 0).
-/

namespace Ember.Net.Ctl
open Ember.Lang

/-! ## Values of the header's fields -/

/-- One byte of a decimal field's value (`c_val`, `c_dig`, `c_first0`, `c_bad`, `c_trail`). -/
ember def hc_dec_byte (x : u8) := do
  let ows : bool := x == 32 || x == 9
  if ows then
    if c_dig[cur] > 0 then
      c_trail[cur] := true
    return
  if x < 48 || x > 57 || c_trail[cur] then
    c_bad[cur] := true
    return
  if c_dig[cur] == 0 then
    c_first0[cur] := x == 48
  if c_dig[cur] < 11 then
    c_val[cur] := c_val[cur] * 10 + (x - 48 : u64)
    c_dig[cur] := c_dig[cur] + 1

/-- A canonical decimal of at most `maxd` digits? -/
ember def hc_dec_ok (maxd : u8) : bool := do
  return !c_bad[cur] && c_dig[cur] > 0 && c_dig[cur] <= maxd && !(c_dig[cur] > 1 && c_first0[cur])

/-- The end of a token of a `connection` value: was it `close`? -/
ember def hc_conn_tok := do
  if !c_bad[cur] && c_cpos[cur] == 5 then
    c_close[cur] := true
  c_cpos[cur] := 0
  c_trail[cur] := false
  c_bad[cur] := false

/-- One byte of a `connection` value: comma-separated tokens, each `close`
(any case, white space around) or not (`Spec.Srv.Http.wantsClose`). -/
ember def hc_conn_byte (x : u8) := do
  if x == 44 then
    hc_conn_tok()
    return
  let ows : bool := x == 32 || x == 9
  if ows then
    if c_cpos[cur] > 0 then
      c_trail[cur] := true
    return
  let mut lx : u8 := x
  if x >= 65 && x <= 90 then
    lx := x + 32
  let p : u16 := (c_cpos[cur] : u16)
  let mut same : bool := false
  if p < 5 && !c_trail[cur] then
    same := CLOSEW[p] == lx
  if !same then
    c_bad[cur] := true
  if c_cpos[cur] < 6 then
    c_cpos[cur] := c_cpos[cur] + 1

/-- The value of field `f` ended. -/
ember def hc_vend := do
  let f : u8 := c_fid[cur]
  if f == F_CL then
    if c_clcnt[cur] < 2 then
      c_clcnt[cur] := c_clcnt[cur] + 1
    let ok : bool ← hc_dec_ok(9)
    c_clok[cur] := ok
    c_cl[cur] := c_val[cur]
  if f == F_SEQ then
    if c_sqcnt[cur] < 2 then
      c_sqcnt[cur] := c_sqcnt[cur] + 1
    let ok2 : bool ← hc_dec_ok(10)
    c_sqok[cur] := ok2 && c_val[cur] < 4294967296
    c_seq[cur] := c_val[cur]
  if f == F_CONN then
    hc_conn_tok()
  c_lst[cur] := 0
  c_lpos[cur] := 0
  c_lmask[cur] := 0xFF

ember def hc_vbyte (x : u8) := do
  let f : u8 := c_fid[cur]
  if f == F_CL || f == F_SEQ then
    hc_dec_byte(x)
  if f == F_CONN then
    hc_conn_byte(x)

/-- One byte of the request header, for the five fields. -/
ember def hc_line (x : u8) := do
  let st : u8 := c_lst[cur]
  -- the `authorization` field's value: `Net.Auth` reads it to its line's end
  if st == LS_AUTH then
    ha_line(x)
    if a_ln[cur] == 0 then
      c_lst[cur] := 0
      c_lpos[cur] := 0
      c_lmask[cur] := 0xFF
    return
  if st == LS_VAL then
    if c_cr[cur] then
      c_cr[cur] := false
      if x == 10 then
        hc_vend()
        return
      hc_vbyte(13)
    if x == 13 then
      c_cr[cur] := true
      return
    if x == 10 then
      hc_vend()
      return
    hc_vbyte(x)
    return
  if x == 10 then
    c_lst[cur] := 0
    c_lpos[cur] := 0
    c_lmask[cur] := 0xFF
    return
  if st == LS_REQ || st == LS_SKIP then
    return
  let p : u16 := (c_lpos[cur] : u16)
  if x == 58 then
    -- the name ends: which one, if any
    let mut fid : u8 := 0
    for i : u16 in [0, 5) do
      if ((c_lmask[cur] >>> (i : u8)) &&& 1) == 1 && FN_LEN[i] == p then
        fid := (i : u8) + 1
    if fid == F_AUTH then
      if a_cnt[cur] < 2 then
        a_cnt[cur] := a_cnt[cur] + 1
      if a_cnt[cur] == 1 then
        a_ln[cur] := L_VAL
        a_vs[cur] := V_LEAD
        a_cr[cur] := false
        c_lst[cur] := LS_AUTH
      else
        c_lst[cur] := LS_SKIP
      return
    if fid == F_TE then
      if c_te[cur] < 2 then
        c_te[cur] := c_te[cur] + 1
      c_lst[cur] := LS_SKIP
      return
    if fid == 0 then
      c_lst[cur] := LS_SKIP
      return
    c_fid[cur] := fid
    c_lst[cur] := LS_VAL
    c_cr[cur] := false
    c_val[cur] := 0
    c_dig[cur] := 0
    c_first0[cur] := false
    c_bad[cur] := false
    c_trail[cur] := false
    c_cpos[cur] := 0
    return
  let mut lx : u8 := x
  if x >= 65 && x <= 90 then
    lx := x + 32
  for k : u16 in [0, 5) do
    if ((c_lmask[cur] >>> (k : u8)) &&& 1) == 1 then
      let mut same : bool := false
      if p < FN_LEN[k] then
        same := FN[FN_OFF[k] + p] == lx
      if !same then
        c_lmask[cur] := c_lmask[cur] &&& (~~~((1 : u8) <<< (k : u8)))
  if c_lpos[cur] < 200 then
    c_lpos[cur] := c_lpos[cur] + 1

ember def hc_reset := do
  c_lst[cur] := LS_REQ
  c_lpos[cur] := 0
  c_lmask[cur] := 0xFF
  c_cr[cur] := false
  c_clcnt[cur] := 0
  c_sqcnt[cur] := 0
  c_te[cur] := 0
  c_close[cur] := false
  c_body[cur] := false
  c_bpos[cur] := 0
  h_close[cur] := true

/-! ## Responses: ROM, and `200 ok N` in `h_dyn` -/

/-- Byte `off` of the response of the connection `cur`. -/
ember def h_byte (off : u16) : u8 := do
  let k : u16 := (h_kind[cur] : u16)
  if k == K_DYN then
    return h_dyn[cur * DYN_MAX + off]
  if off < h_hlen[k] then
    return h_rom[h_hoff[k] + off]
  return h_rom[h_boff[k] + off - h_hlen[k]]

ember def h_total : u16 := do
  let k : u16 := (h_kind[cur] : u16)
  if k == K_DYN then
    return h_dlen[cur]
  let mut n : u16 := h_hlen[k]
  if !h_head[cur] then
    n := n + h_blen[k]
  return n

ember def dyn_put (x : u8) := do
  h_dyn[cur * DYN_MAX + h_dlen[cur]] := x
  h_dlen[cur] := h_dlen[cur] + 1

/-- `v` in decimal into `h_dyn` (32-bit arithmetic: no 64-bit division on the targets). -/
ember def dyn_num (v : u32) := do
  let mut d : u32 := 1
  loop (max := 20) do
    if d > v / 10 then
      break
    d := d * 10
  loop (max := 20) do
    dyn_put(((v / d) % 10 + 48 : u8))
    if d == 1 then
      break
    d := d / 10

/-- `200 ok <seq>` for the connection (with `Connection: close` unless kept). -/
ember def dyn_ok (seq : u32) := do
  h_dlen[cur] := 0
  for i : u16 in [0, DYN_HEAD_LEN) do
    dyn_put(DYN_HEAD[i])
  -- the body is `ok <seq>\n`: 4 bytes and the digits
  let mut nd : u32 := 1
  let mut d : u32 := 1
  loop (max := 20) do
    if seq / d < 10 then
      break
    d := d * 10
    nd := nd + 1
  dyn_num(nd + 4)
  dyn_put(13)
  dyn_put(10)
  if h_close[cur] then
    for j : u16 in [0, 19) do
      dyn_put(CONN_CLOSE[j])
  dyn_put(13)
  dyn_put(10)
  dyn_put(111)
  dyn_put(107)
  dyn_put(32)
  dyn_num(seq)
  dyn_put(10)
  h_kind[cur] := (K_DYN : u8)
  h_head[cur] := false

/-! ## The decision -/

/-- A control request's body is complete: the shared state decides (`Spec.Srv.Http.control`). -/
ember def hc_exec := do
  a_hash_final()
  let seq : u32 := (c_seq[cur] : u32)
  let n : u16 := c_bpos[cur]
  -- a number above the last: executed
  if seq > ctl_last then
    ctl_last := seq
    ctl_has := true
    for j : u16 in [0, 32) do
      ctl_hash[j] := p2_h[j]
    for k : u16 in [0, n) do
      ctl_cmd[k] := c_buf[cur * BODY_MAX + k]
    ctl_len := n
    ctl_cmds := ctl_cmds + 1
    ctl_new := true
    dyn_ok(seq)
    return
  -- the last one again with the same body: the same answer, not executed
  let mut same : bool := ctl_has
  for i : u16 in [0, 32) do
    if p2_h[i] != ctl_hash[i] then
      same := false
  if seq == ctl_last && same then
    dyn_ok(seq)
    return
  if h_close[cur] then
    h_kind[cur] := K_409
  else
    h_kind[cur] := K_409K
  h_head[cur] := false

/-- The answer once the header is complete, or the body to read (`Spec.Srv.Http.answerCtl`). -/
ember def hc_decide := do
  let base : u16 := cur * REQ_MAX
  let rlen : u16 := h_rlen[cur]
  let mut l : u16 := rlen
  for j1 in [0, rlen) do
    if l == rlen && h_req[base + j1] == 13 then
      l := j1
  let mut ns : u16 := 0
  let mut s1 : u16 := 0
  let mut s2 : u16 := 0
  for j2 in [0, l) do
    if h_req[base + j2] == 32 then
      if ns == 0 then
        s1 := j2
      if ns == 1 then
        s2 := j2
      ns := ns + 1
  h_head[cur] := false
  h_close[cur] := true
  if ns != 2 then
    h_kind[cur] := KB_400
    return
  let v : u16 := s2 + 1
  if l - v != 8 || s2 - s1 < 2 then
    h_kind[cur] := KB_400
    return
  if h_req[base + v] != 72 || h_req[base + v + 1] != 84 || h_req[base + v + 2] != 84 || h_req[base + v + 3] != 80 || h_req[base + v + 4] != 47 || h_req[base + v + 5] != 49 || h_req[base + v + 6] != 46 || h_req[base + v + 7] < 48 || h_req[base + v + 7] > 57 then
    h_kind[cur] := KB_400
    return
  let keep : bool := KEEP_ALIVE && h_req[base + v + 7] == 49 && !c_close[cur]
  let get : bool := s1 == 3 && h_req[base] == 71 && h_req[base + 1] == 69 && h_req[base + 2] == 84
  let head : bool := s1 == 4 && h_req[base] == 72 && h_req[base + 1] == 69 && h_req[base + 2] == 65 && h_req[base + 3] == 68
  let post : bool := s1 == 4 && h_req[base] == 80 && h_req[base + 1] == 79 && h_req[base + 2] == 83 && h_req[base + 3] == 84
  if !get && !head && !post then
    h_kind[cur] := KB_501
    return
  -- the route: the target up to `?`
  let t0 : u16 := s1 + 1
  let mut plen : u16 := s2 - t0
  for j3 in [0, s2 - t0) do
    if plen == s2 - t0 && h_req[base + t0 + j3] == 63 then
      plen := j3
  let mut kind : u16 := K_404
  for k in [0, N_ROUTES) do
    if kind == K_404 && h_plen[k] == plen then
      let mut same : bool := true
      for j4 in [0, plen) do
        if h_paths[h_poff[k] + j4] != h_req[base + t0 + j4] then
          same := false
      if same then
        kind := k
  if get || head then
    h_head[cur] := head
    h_close[cur] := !keep
    if kind == K_404 then
      if keep then
        h_kind[cur] := K_404K
      else
        h_kind[cur] := (K_404 : u8)
      return
    if R_POST[kind] then
      if keep then
        h_kind[cur] := K_405GK
      else
        h_kind[cur] := K_405G
      return
    h_kind[cur] := (kind : u8)
    if R_SCOPE[kind] != 0 then
      ha_guard()
      if (h_kind[cur] : u16) != kind then
        h_close[cur] := true
        return
    if keep then
      h_kind[cur] := (K_KEEP + kind : u8)
    return
  -- POST
  if kind == K_404 then
    h_kind[cur] := (K_404 : u8)
    return
  if !R_POST[kind] then
    h_kind[cur] := K_405P
    return
  if c_te[cur] > 0 then
    h_kind[cur] := KB_501
    return
  if c_clcnt[cur] == 0 then
    h_kind[cur] := K_411
    return
  if c_clcnt[cur] > 1 || !c_clok[cur] then
    h_kind[cur] := KB_400
    return
  if c_cl[cur] > (BODY_MAX : u64) then
    h_kind[cur] := K_413
    return
  if c_sqcnt[cur] != 1 || !c_sqok[cur] then
    h_kind[cur] := KB_400
    return
  if R_SCOPE[kind] != 0 then
    h_kind[cur] := (kind : u8)
    ha_guard()
    if (h_kind[cur] : u16) != kind then
      return
    -- no token issued before the device started (decision 8-4)
    if !j_iatok[cur] || j_iat[cur] < h_boot then
      h_kind[cur] := K_401I
      return
  -- read the body
  h_close[cur] := !keep
  c_body[cur] := true
  c_bpos[cur] := 0
  c_blen[cur] := (c_cl[cur] : u16)
  for i : u16 in [0, 8) do
    a_h[cur * 8 + i] := A_IV[i]
  a_bn[cur] := 0
  a_len[cur] := 0
  if c_blen[cur] == 0 then
    c_body[cur] := false
    hc_exec()

/-- A response is decided: a kept one goes to `h_kept`. -/
ember def hc_decided := do
  h_dec[cur] := true
  if !h_close[cur] then
    h_kept()

/-- One byte of a request (`Spec.Srv.Http.stepCtl`). -/
ember def h_feed (x : u8) := do
  if c_body[cur] then
    a_hash_byte(x)
    c_buf[cur * BODY_MAX + c_bpos[cur]] := x
    c_bpos[cur] := c_bpos[cur] + 1
    if c_bpos[cur] == c_blen[cur] then
      c_body[cur] := false
      hc_exec()
      hc_decided()
    return
  if h_seen[cur] == 0 then
    ha_reset()
    hc_reset()
  hc_line(x)
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
      hc_decide()
    else
      h_kind[cur] := KB_400
      h_head[cur] := false
      h_close[cur] := true
    if !c_body[cur] then
      hc_decided()
    return
  if h_seen[cur] >= HDR_MAX then
    h_kind[cur] := KB_400
    h_head[cur] := false
    h_close[cur] := true
    hc_decided()

/-- The request state of the connection, for the next request on it. -/
ember def hc_next := do
  h_rlen[cur] := 0
  h_crlf[cur] := 0
  h_seen[cur] := 0
  h_dec[cur] := false
  h_kind[cur] := 0
  h_head[cur] := false
  h_pos[cur] := 0

/-! ## The HTTP program's application interface (kept connections) -/

ember def h_kept := do
  return

ember def app_room (c : u16) : u16 := do
  if h_dec[cur] then
    return 0
  return c

ember def app_acked (n : u16) := do
  h_pos[cur] := h_pos[cur] + n
  if h_dec[cur] && !h_close[cur] then
    let tot : u16 ← h_total()
    if h_pos[cur] == tot then
      hc_next()

ember def app_close : bool := do
  return h_dec[cur] && h_close[cur]

end Ember.Net.Ctl

namespace Ember.Net.Ctl.Tls
open Ember.Lang

/-- The TLS program's `h_kept` (`Spec.Srv.Tls.respondKeep`): the response in
records, no `close_notify`, and the next request at once. -/
ember def h_kept := do
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
  hc_next()

end Ember.Net.Ctl.Tls

namespace Ember.Net.Ctl
open Ember.Lang

/-! ## The time (plan M9.4, decision 7) -/

/-- A datagram of 8 bytes on the time port (`buf[28, 36)`, seconds since
1970, big-endian): `Spec.Srv.Http.timeIn`.  The first one sets the time
and the start (the time less the board's uptime); later ones only move
the time forward. -/
ember def time_in := do
  let mut v : u64 := 0
  for ti : u16 in [28, 36) do
    v := (v <<< 8) ||| (buf[ti] : u64)
  let up : u32 ← mmio.read32(UPTIME)
  if !h_now_ok then
    h_now := v
    h_up_at := up
    if v >= (up : u64) then
      h_boot := v - (up : u64)
    else
      h_boot := 0
    h_now_ok := true
    return
  let tnow : u64 ← clock()
  if v >= tnow then
    h_now := v
    h_up_at := up

/-- `Net.udp_input` with the time port: a datagram to it goes to `time_in`
when it holds 8 bytes, and is dropped silently otherwise; nothing is sent
back (`Spec.Srv.Stack.udpInput` with the application's `udpPort`). -/
ember def udp_input (src : u32) (dst : u32) (n : u16) := do
  if n < 8 then
    trace.drop(D_SHORT_UDP)
    return
  let ul : u16 ← get16(24)
  if ul < 8 || ul > n then
    trace.drop(D_BAD_UDP_LENGTH)
    return
  let cs : u16 ← get16(26)
  if cs != 0 then
    let p : u16 ← pseudo(src, dst, 17, ul)
    let s : u16 ← csum(20, ul, p)
    let ok : bool ← verifies(s)
    if !ok then
      trace.drop(D_BAD_UDP_CHECKSUM)
      return
  let sport : u16 ← get16(20)
  let dport : u16 ← get16(22)
  if dport == TIME_PORT then
    if ul == 16 then
      time_in()
    return
  if dport != ECHO_PORT then
    trace.drop(D_UDP_PORT_CLOSED)
    return
  set16(20, dport)
  set16(22, sport)
  set16(26, 0)
  let p2 : u16 ← pseudo(OUR_IP, src, 17, ul)
  let s2 : u16 ← csum(20, ul, p2)
  let c : u16 := ~~~s2
  if c == 0 then
    set16(26, 0xFFFF)
  else
    set16(26, c)
  ip_send(17, src, ul)

def fns : List Fn :=
  [hc_dec_byte, hc_dec_ok, hc_conn_tok, hc_conn_byte, hc_vend, hc_vbyte, hc_line, hc_reset, h_byte, h_total, dyn_put, dyn_num,
   dyn_ok, hc_exec, hc_decide, hc_decided, h_feed, hc_next, time_in, udp_input]

/-- The functions the HTTP program takes in place of `Net.Http`'s (kept connections). -/
def httpFns : List Fn := [h_kept, app_room, app_acked, app_close]

def u8s (name : String) (xs : List Nat) : Global :=
  { name, ty := .arr .u8 (max 1 xs.length), init := xs, const := true }
def u16s (name : String) (xs : List Nat) : Global :=
  { name, ty := .arr .u16 (max 1 xs.length), init := xs, const := true }
def scalar (name : String) (ty : Ty) (v : Nat) : Global := { name, ty, init := [v], const := true }
def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- The globals for `site` on `n` connections; `base`: the first kind after
those of `Net.Http` and `Net.Auth` (see `Net.Http.responses`). -/
def globals (n : Nat) (site : Spec.Srv.Http.Site) (base : Nat) : List Global :=
  let nr := site.routes.length
  let names := ["authorization", "content-length", "transfer-encoding", "x-ember-seq", "connection"].map bytesOf
  let dynMax := 128
  [u8s "FN" names.flatten, u16s "FN_OFF" (Auth.offsets names), u16s "FN_LEN" (names.map (·.length)),
   scalar "F_AUTH" .u8 1, scalar "F_CL" .u8 2, scalar "F_TE" .u8 3, scalar "F_SEQ" .u8 4, scalar "F_CONN" .u8 5,
   scalar "LS_VAL" .u8 1, scalar "LS_AUTH" .u8 2, scalar "LS_SKIP" .u8 3, scalar "LS_REQ" .u8 4,
   u8s "CLOSEW" (bytesOf "close"),
   { name := "KEEP_ALIVE", ty := .bool, init := [if site.keepAlive then 1 else 0], const := true },
   { name := "R_POST", ty := .arr .bool (max 1 nr), init := site.routes.map (fun r => if r.post then 1 else 0), const := true },
   scalar "BODY_MAX" .u16 site.bodyMax, scalar "TIME_PORT" .u16 Spec.Srv.Http.timePort.toNat,
   scalar "K_KEEP" .u16 base, scalar "K_404K" .u8 (base + nr), scalar "K_405GK" .u8 (base + nr + 1),
   scalar "K_405G" .u8 (base + nr + 2), scalar "K_405P" .u8 (base + nr + 3), scalar "K_411" .u8 (base + nr + 4),
   scalar "K_413" .u8 (base + nr + 5), scalar "K_409K" .u8 (base + nr + 6), scalar "K_409" .u8 (base + nr + 7),
   scalar "K_DYN" .u16 (base + nr + 8),
   u8s "DYN_HEAD" (bytesOf "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: "),
   scalar "DYN_HEAD_LEN" .u16 (bytesOf "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: ").length,
   u8s "CONN_CLOSE" (bytesOf "Connection: close\r\n"),
   scalar "DYN_MAX" .u16 dynMax,
   -- the shared state and the device's command
   { name := "ctl_last", ty := .u32 }, { name := "ctl_has", ty := .bool }, { name := "ctl_hash", ty := .arr .u8 32 },
   { name := "ctl_cmd", ty := .arr .u8 (max 1 site.bodyMax) }, { name := "ctl_len", ty := .u16 },
   { name := "ctl_cmds", ty := .u32 }, { name := "ctl_new", ty := .bool },
   -- per connection
   { name := "c_lst", ty := .arr .u8 n }, { name := "c_lpos", ty := .arr .u8 n }, { name := "c_lmask", ty := .arr .u8 n },
   { name := "c_cr", ty := .arr .bool n }, { name := "c_fid", ty := .arr .u8 n },
   { name := "c_val", ty := .arr .u64 n }, { name := "c_dig", ty := .arr .u8 n }, { name := "c_first0", ty := .arr .bool n },
   { name := "c_bad", ty := .arr .bool n }, { name := "c_trail", ty := .arr .bool n }, { name := "c_cpos", ty := .arr .u8 n },
   { name := "c_clcnt", ty := .arr .u8 n }, { name := "c_clok", ty := .arr .bool n }, { name := "c_cl", ty := .arr .u64 n },
   { name := "c_sqcnt", ty := .arr .u8 n }, { name := "c_sqok", ty := .arr .bool n }, { name := "c_seq", ty := .arr .u64 n },
   { name := "c_te", ty := .arr .u8 n }, { name := "c_close", ty := .arr .bool n },
   { name := "c_body", ty := .arr .bool n }, { name := "c_bpos", ty := .arr .u16 n }, { name := "c_blen", ty := .arr .u16 n },
   { name := "c_buf", ty := .arr .u8 (n * max 1 site.bodyMax) },
   { name := "h_close", ty := .arr .bool n },
   { name := "h_dyn", ty := .arr .u8 (n * dynMax) }, { name := "h_dlen", ty := .arr .u16 n }]

end Ember.Net.Ctl
