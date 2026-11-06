import Ember.Net.Srv
import Ember.Net.Ctl
import Ember.Spec.Srv.Http

/-!
# Ember.Net.Http — the HTTP application in Ember (plan M8.2)

`Ember.Spec.Srv.Http` for `Ember.Net.Srv`.  The site is fixed when the
program is built, so every response is known then up to the `HEAD`
flag: its header (`Http.response … (head := true)`) and its body.  Both
are put in one constant array `h_rom`, with tables of where each
response's header and body are; the routes' paths are in `h_paths`.
Response `k` is route `k`, or `404`, `400`, `501` after the routes.

Per connection (index `cur`): the first `REQ_MAX` bytes of the request
(`h_req`, their number `h_rlen`), how much of `CRLF CRLF` was just seen
(`h_crlf`) and how many bytes the header has so far (`h_seen`), whether it is answered
(`h_dec`), with which response (`h_kind`) and whether for `HEAD`
(`h_head`), and how much of the response is acknowledged (`h_pos`).
A segment's bytes are computed from the tables (`h_byte`): nothing of
the response is kept in RAM, a retransmission computes them again.
-/

namespace Ember.Net.Http
open Ember.Lang

/-- Byte `off` of the response of the connection `cur`. -/
ember def h_byte (off : u16) : u8 := do
  let k : u16 := (h_kind[cur] : u16)
  if off < h_hlen[k] then
    return h_rom[h_hoff[k] + off]
  return h_rom[h_boff[k] + off - h_hlen[k]]

ember def h_total : u16 := do
  let k : u16 := (h_kind[cur] : u16)
  let mut n : u16 := h_hlen[k]
  if !h_head[cur] then
    n := n + h_blen[k]
  return n

ember def app_reset := do
  h_rlen[cur] := 0
  h_crlf[cur] := 0
  h_seen[cur] := 0
  h_dec[cur] := false
  h_kind[cur] := 0
  h_head[cur] := false
  h_pos[cur] := 0

ember def app_room (c : u16) : u16 := do
  return c

/-- Answer the request in `h_req` (its header is complete). -/
ember def h_decide := do
  let base : u16 := cur * REQ_MAX
  let rlen : u16 := h_rlen[cur]
  -- the request line: up to the first CR
  let mut l : u16 := rlen
  for j1 in [0, rlen) do
    if l == rlen && h_req[base + j1] == 13 then
      l := j1
  -- exactly two spaces in it
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
  let get : bool := s1 == 3 && h_req[base] == 71 && h_req[base + 1] == 69 && h_req[base + 2] == 84
  let head : bool := s1 == 4 && h_req[base] == 72 && h_req[base + 1] == 69 && h_req[base + 2] == 65 && h_req[base + 3] == 68
  if !get && !head then
    h_kind[cur] := KB_501
    return
  h_head[cur] := head
  -- the path: the target up to `?`
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
  h_kind[cur] := (kind : u8)

/-- One byte of the request (`Spec.Srv.Http.step`): its first `REQ_MAX`
bytes kept, the end of the header found by a four-state matcher
(`h_crlf`), the bytes counted (`h_seen`, at most `HDR_MAX`). -/
ember def h_feed (x : u8) := do
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
    -- the request line must end within the bytes kept
    let mut cr : bool := false
    for i : u16 in [0, h_rlen[cur]) do
      if h_req[base + i] == 13 then
        cr := true
    if cr then
      h_decide()
    else
      h_kind[cur] := KB_400
      h_head[cur] := false
    h_dec[cur] := true
    return
  if h_seen[cur] >= HDR_MAX then
    h_kind[cur] := KB_400
    h_head[cur] := false
    h_dec[cur] := true

ember def app_recv (off : u16) (n : u16) := do
  for i : u16 in [0, n) do
    if !h_dec[cur] then
      h_feed(buf[off + i])

ember def app_avail : u16 := do
  if !h_dec[cur] then
    return 0
  let tot : u16 ← h_total()
  return tot - h_pos[cur]

ember def app_fill (src : u16) (n : u16) (dst : u16) := do
  let p : u16 := h_pos[cur] + src
  for i in [0, n) do
    buf[dst + i] ← h_byte(p + i)

ember def app_acked (n : u16) := do
  h_pos[cur] := h_pos[cur] + n

ember def app_close : bool := do
  return h_dec[cur]

open Ember.Spec.Srv.Http in
/-- The responses of a site, in order: the routes, then 404, 400, 501 —
headers (as for `HEAD`) and bodies; with protected routes (M9.3) then 401
(no token), 401 (`invalid_token`), 503 and a 403 for each scope a route
needs (`Net.Auth.scopes`). -/
def responses (site : Site) : List (ByteArray × ByteArray) :=
  site.routes.map (fun r => (response 200 "OK" r.ctype r.body true, r.body)) ++
  [(errorText 404 "Not Found" true, str "Not Found\n"),
   (errorText 400 "Bad Request" true, str "Bad Request\n"),
   (errorText 501 "Not Implemented" true, str "Not Implemented\n")] ++
  (if Net.Auth.protected? site || site.ctl then
    [(errorText 401 "Unauthorized" true challenge, str "Unauthorized\n"),
     (errorText 401 "Unauthorized" true invalidToken, str "Unauthorized\n"),
     (errorText 503 "Service Unavailable" true, str "Service Unavailable\n")] ++
    (Net.Auth.scopes site).map fun sc => (errorText 403 "Forbidden" true (insufficientScope sc), str "Forbidden\n")
   else []) ++
  -- M9.5 (`Net.Ctl`): the routes and 404 on a kept connection, 405 (kept
  -- and not), 411, 413, 409 (kept and not), and a place for `200 ok N`
  (if site.ctl then
    site.routes.map (fun r => (response 200 "OK" r.ctype r.body true "" false, r.body)) ++
    [(errorText 404 "Not Found" true "" false, str "Not Found\n"),
     (errorText 405 "Method Not Allowed" true "Allow: POST\r\n" false, str "Method Not Allowed\n"),
     (errorText 405 "Method Not Allowed" true "Allow: POST\r\n", str "Method Not Allowed\n"),
     (errorText 405 "Method Not Allowed" true "Allow: GET, HEAD\r\n", str "Method Not Allowed\n"),
     (errorText 411 "Length Required" true, str "Length Required\n"),
     (errorText 413 "Content Too Large" true, str "Content Too Large\n"),
     (errorText 409 "Conflict" true "" false, str "Conflict\n"),
     (errorText 409 "Conflict" true, str "Conflict\n"),
     (.empty, .empty)]
   else [])

def u16s (name : String) (xs : List Nat) : Global :=
  { name, ty := .arr .u16 (max 1 xs.length), init := xs, const := true }

def bytesG (name : String) (b : List Nat) : Global :=
  { name, ty := .arr .u8 (max 1 b.length), init := b, const := true }

def scalar (name : String) (ty : Ty) (v : Nat) : Global := { name, ty, init := [v], const := true }

/-- The functions that take the request: `Net.Auth`'s `h_feed` (and the
token check) for a site with protected routes, this module's otherwise. -/
def feedFns (site : Spec.Srv.Http.Site) : List Fn :=
  if site.ctl then [h_decide] ++ Net.Auth.coreFns ++ Net.Ctl.fns
  else if Net.Auth.protected? site then [h_decide] ++ Net.Auth.fns else [h_decide, h_feed]

/-- The first kind of `Net.Ctl`'s responses (after the routes, 404, 400,
501, and the 401, 401, 503 and 403s of `Net.Auth`). -/
def ctlBase (site : Spec.Srv.Http.Site) : Nat :=
  site.routes.length + 6 + (Net.Auth.scopes site).length

/-- The HTTP application of `site` for `n` connections; `crypto`: with the
globals and functions of SHA-256 and P-256 that the token check needs
(`Net.Tls` has its own). -/
def app (n : Nat) (site : Spec.Srv.Http.Site) (crypto : Bool := true) : Net.Srv.App :=
  let prot := Net.Auth.protected? site || site.ctl
  let rs := responses site
  -- h_rom: header 0, body 0, header 1, body 1, …
  let (rom, hoff, boff) := rs.foldl (fun (rom, ho, bo) (h, b) =>
    (rom ++ h.toList.map (·.toNat) ++ b.toList.map (·.toNat), ho ++ [rom.length], bo ++ [rom.length + h.size]))
    (([] : List Nat), ([] : List Nat), ([] : List Nat))
  let paths := site.routes.map fun r => r.path.toUTF8.toList.map (·.toNat)
  let poff := (paths.foldl (fun (acc, o) p => (acc ++ [o], o + p.length)) (([] : List Nat), 0)).1
  let nr := site.routes.length
  { globals :=
      [scalar "APP_PORT" .u16 site.port.toNat, { name := "APP_IDLE_CLOSE", ty := .bool, init := [1] }, { name := "APP_REUSE_TW", ty := .bool, init := [1] },
       scalar "REQ_MAX" .u16 site.reqMax,
       -- a variable, not a constant: with a constant bound SDCC sees the
       -- index checks of the route loop never fail and stops on "unreachable code"
       { name := "N_ROUTES", ty := .u16, init := [nr] },
       scalar "K_404" .u16 nr,
       -- the kinds stored in `h_kind` as bytes: the own Z80 back end does not cast a constant
       scalar "KB_400" .u8 (nr + 1), scalar "KB_501" .u8 (nr + 2),
       bytesG "h_rom" rom, u16s "h_hoff" hoff, u16s "h_hlen" (rs.map (·.1.size)),
       u16s "h_boff" boff, u16s "h_blen" (rs.map (·.2.size)),
       bytesG "h_paths" paths.flatten, u16s "h_poff" poff, u16s "h_plen" (paths.map (·.length)),
       { name := "h_req", ty := .arr .u8 (n * site.reqMax) },
       { name := "h_rlen", ty := .arr .u16 n }, { name := "h_dec", ty := .arr .bool n },
       { name := "h_crlf", ty := .arr .u8 n }, { name := "h_seen", ty := .arr .u16 n },
       scalar "HDR_MAX" .u16 site.hdrMax,
       { name := "h_kind", ty := .arr .u8 n }, { name := "h_head", ty := .arr .bool n },
       { name := "h_pos", ty := .arr .u16 n }] ++
      (if prot then Net.Auth.globals n site else []) ++
      (if site.ctl then Net.Ctl.globals n site (ctlBase site) else []) ++
      (if prot && crypto then Net.Crypto.sha256Globals ++ Net.Crypto.p256Globals (verify := true) else [])
    fns := (if prot && crypto then Net.Crypto.sha256Fns ++ Net.Crypto.p256CoreFns ++ Net.Crypto.p256VerifyFns else []) ++
      (if site.ctl then [app_reset] ++ feedFns site ++ [app_recv, app_avail, app_fill] ++ Net.Ctl.httpFns
       else [h_byte, h_total, app_reset, app_room] ++ feedFns site ++ [app_recv, app_avail, app_fill,
            app_acked, app_close]) }

/-- The HTTP server for `site` on `n` connections (SLIP, MTU 296). -/
def prog (n : Nat) (site : Spec.Srv.Http.Site) : Prog := Net.Srv.prog n (app n site)

end Ember.Net.Http
