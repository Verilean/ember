import Ember.Spec.Srv.Tcp
import Ember.Spec.Srv.Auth

/-!
# Ember.Spec.Srv.Http — an HTTP/1.1 server as an `App` (plan M8.2)

The reference for `Ember.Net.Srv.Http`.  One request per connection:

* the request header is taken until it ends (`CRLF CRLF`), at most
  `hdrMax` bytes, and its first `reqMax` bytes are kept for the request
  line; a body is not read (nothing here takes one);
* the request line is `METHOD SP target SP HTTP/1.d`, `d` a digit; `GET` and `HEAD`
  are served, another method gets `501 Not Implemented`, a line that is
  not of that form or does not end within `reqMax` bytes, or a header
  longer than `hdrMax`, `400 Bad Request`;
* the target's path (the query is ignored) is looked up in the site's
  routes, exactly; a path that is not there gets `404 Not Found`;
* the response is the status line, `Content-Type`, `Content-Length`,
  `Connection: close`, an empty line and the body (not for `HEAD`); the
  server closes the connection once all of it is sent (FIN with its last
  byte);
* what arrives after the request's header is read and dropped.

The site is static: routes and their bodies are fixed when the program
is built (on the targets, constants in ROM).

A route may be protected (plan M9.1): it then needs an OAuth 2.0 bearer
token (RFC 6750), an OIDC access token that `Auth.check` accepts.  On such
a route only:

* more than one `Authorization` field: `400 Bad Request`;
* no `Authorization` field, or one whose scheme is not `Bearer` (any
  case): `401` with `WWW-Authenticate: Bearer realm="ember"`;
* the time not known, or no keys configured: `503 Service Unavailable`;
* a credential that is not one token (`Bearer`, spaces, then no white
  space), or a token `Auth.check` refuses: `401` with
  `error="invalid_token"`;
* a token without the route's scope: `403` with
  `error="insufficient_scope"`.

A field's name is compared without case; its value is what follows the
colon without the white space (SP, HT) around it.  A public route ignores
`Authorization` altogether.
-/

namespace Ember.Spec.Srv.Http
open Ember

structure Route where
  path  : String
  ctype : String := "text/html; charset=utf-8"
  body  : ByteArray
  /-- `none`: public; `some ""`: any accepted token; `some s`: a token with scope `s`. -/
  scope : Option String := none
  /-- A control route (plan M9.5): it takes `POST` with a body and a
  sequence number, not `GET`. -/
  post  : Bool := false
  deriving Inhabited

structure Site where
  routes : List Route
  /-- Most bytes of a request header kept (the request line must end within them). -/
  reqMax : Nat := 512
  /-- Most bytes of a request header taken. -/
  hdrMax : Nat := 8192
  port   : UInt16 := 80
  /-- The tokens accepted on protected routes. -/
  auth   : Option Auth.Cfg := none
  /-- The time, in seconds since 1970, if known. -/
  now    : Option Nat := none
  /-- Keep the connection for further requests (plan M9.5). -/
  keepAlive : Bool := false
  /-- Most bytes of a control request's body. -/
  bodyMax : Nat := 256
  deriving Inhabited

/-- Does the site use the control requests or keep-alive of M9.5?  A site
that does not is served exactly as in M8. -/
def Site.ctl (site : Site) : Bool := site.keepAlive || site.routes.any (·.post)

structure Conn where
  /-- The request so far (until it is answered). -/
  req     : ByteArray := .empty
  /-- The response, once decided: the part from `snd.una` on. -/
  resp    : ByteArray := .empty
  decided : Bool := false
  /-- How much of `CRLF CRLF` the last bytes are; the bytes of the header so far. -/
  crlf    : Nat := 0
  seen    : Nat := 0
  /-- The whole header so far (at most `hdrMax` bytes). -/
  hdr     : ByteArray := .empty
  /-- M9.5: the body still to read of a control request (its route and
  sequence number), and what of it has come. -/
  body    : Option (Nat × Nat × Nat) := none
  bodyBuf : ByteArray := .empty
  /-- M9.5: close once the response is sent (else take the next request). -/
  closeAfter : Bool := true
  deriving Inhabited

/-- The state shared by the connections of a site with control routes
(plan M9.5): the last sequence number executed, the SHA-256 of its body,
the commands handed to the device (the last one, and how many). -/
structure Ctl where
  last     : Nat := 0
  lastHash : ByteArray := .empty
  cmd      : ByteArray := .empty
  cmds     : Nat := 0
  /-- Plan M9.4: the time (seconds since 1970) once known, and the time the
  device started at, for the control routes (decision 8-4). -/
  now      : Option Nat := none
  boot     : Option Nat := none
  deriving Inhabited

/-- The shared state at the start: the site's time, if it has one (the tests). -/
def ctlInit (site : Site) : Ctl := { now := site.now, boot := site.now }

/-- The UDP port of the time (plan M9.4, decision 7). -/
def timePort : UInt16 := 37

/-- A datagram on the time port: 8 bytes, seconds since 1970, big-endian.
The time only moves forward; the first one also fixes the start (the
uptime of the reference is 0).  Anything else changes nothing. -/
def timeIn (g : Ctl) (d : ByteArray) : Ctl :=
  if d.size != 8 then g else
  let v := d.foldl (fun a b => a * 256 + b.toNat) 0
  match g.now with
  | none => { g with now := some v, boot := some v }
  | some t => if v ≥ t then { g with now := some v } else g

def crlf2 : List UInt8 := [13, 10, 13, 10]

/-- Does `b` contain `CRLF CRLF`? -/
def headerEnds (b : ByteArray) : Bool :=
  (List.range (b.size + 1 - 4)).any fun i => (Bytes.slice b i 4).toList == crlf2

def str (s : String) : ByteArray := s.toUTF8

/-- `extra`: more fields, each ending with CRLF; `close`: with
`Connection: close` (every response but those of a kept connection, M9.5). -/
def response (code : Nat) (reason ctype : String) (body : ByteArray) (head : Bool) (extra : String := "")
    (close : Bool := true) : ByteArray :=
  str s!"HTTP/1.1 {code} {reason}\r\nContent-Type: {ctype}\r\nContent-Length: {body.size}\r\n{extra}{if close then "Connection: close\r\n" else ""}\r\n"
    ++ (if head then .empty else body)

def errorText (code : Nat) (reason : String) (head : Bool) (extra : String := "") (close : Bool := true) : ByteArray :=
  response code reason "text/plain" (str (reason ++ "\n")) head extra close

def challenge : String := "WWW-Authenticate: Bearer realm=\"ember\"\r\n"
def invalidToken : String := "WWW-Authenticate: Bearer realm=\"ember\", error=\"invalid_token\"\r\n"
def insufficientScope (s : String) : String :=
  s!"WWW-Authenticate: Bearer realm=\"ember\", error=\"insufficient_scope\", scope=\"{s}\"\r\n"

def lower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c
def isOws (c : UInt8) : Bool := c == 32 || c == 9

/-- The values of the `Authorization` fields of a header (request line,
fields, each ending with CRLF), without the white space around them. -/
def authFields (hdr : ByteArray) : List (List UInt8) :=
  let lines := (Auth.splitOn 10 hdr.toList).map fun l => if l.getLast? == some 13 then l.dropLast else l
  (lines.drop 1).filterMap fun l =>
    let (name, rest) := l.span (· != 58)
    if rest.isEmpty || name.map lower != (str "authorization").toList then none
    else some (((rest.drop 1).dropWhile isOws).reverse.dropWhile isOws).reverse

/-- The answer on a protected route that needs `need`, when the route itself is `ok`. -/
def guard (site : Site) (need : String) (hdr : ByteArray) (head : Bool) (ok : ByteArray)
    (minIat : Option Nat := none) : ByteArray :=
  match authFields hdr with
  | [] => errorText 401 "Unauthorized" head challenge
  | [v] =>
    let (sch, rest) := v.span (· != 32)
    if sch.map lower != (str "bearer").toList then errorText 401 "Unauthorized" head challenge else
    match site.auth, site.now with
    | some cfg, some now =>
      let tok := rest.dropWhile (· == 32)
      if tok.isEmpty || tok.any isOws then errorText 401 "Unauthorized" head invalidToken else
      match Auth.checkIat cfg now (ByteArray.mk tok.toArray) with
      | none => errorText 401 "Unauthorized" head invalidToken
      | some (scopes, iat) =>
        if need != "" && !scopes.contains (str need) then errorText 403 "Forbidden" head (insufficientScope need)
        -- a control route: no token issued before the device started (decision 8-4)
        else if minIat.any (fun b => !iat.any (· ≥ b)) then errorText 401 "Unauthorized" head invalidToken
        else ok
    | _, _ => errorText 503 "Service Unavailable" head
  | _ => errorText 400 "Bad Request" false

/-- The request line: bytes up to the first CR (or the end). -/
def requestLine (b : ByteArray) : List UInt8 :=
  b.toList.takeWhile (· != 13)

def spaceSplit (l : List UInt8) : List (List UInt8) :=
  let (cur, acc) := l.foldl (fun (cur, acc) b =>
    if b == 32 then ([], acc ++ [cur]) else (cur ++ [b], acc)) (([] : List UInt8), ([] : List (List UInt8)))
  acc ++ [cur]

/-- The answer to a complete request header. -/
def answer (site : Site) (req : ByteArray) (hdr : ByteArray := .empty) : ByteArray :=
  match spaceSplit (requestLine req) with
  | [m, target, v] =>
    if (v.take 7) != (str "HTTP/1.").toList || v.length != 8 || !(v.getLast?.any fun c => 48 ≤ c && c ≤ 57) ||
        target.isEmpty then
      errorText 400 "Bad Request" false
    else if m == (str "GET").toList || m == (str "HEAD").toList then
      let head := m == (str "HEAD").toList
      let path := target.takeWhile (· != 63)
      match site.routes.find? (fun r => (str r.path).toList == path) with
      | some r =>
        let ok := response 200 "OK" r.ctype r.body head
        match r.scope with
        | none => ok
        | some need => guard site need hdr head ok
      | none => errorText 404 "Not Found" head
    else errorText 501 "Not Implemented" false
  | _ => errorText 400 "Bad Request" false

/-- One byte of the request.  The header ends at `CRLF CRLF`, found by a
four-state matcher (`crlf`: how much of it the last bytes are), over
however many bytes the header has; only its first `reqMax` bytes are
kept, for the request line.  A request line that does not end within
them, or a header longer than `hdrMax`, is answered with 400. -/
def step (site : Site) (c : Conn) (b : UInt8) : Conn :=
  if c.decided then c else
  let req := if c.req.size < site.reqMax then c.req.push b else c.req
  let want : List UInt8 := [13, 10, 13, 10]
  let crlf := if b == want.getD c.crlf 0 then c.crlf + 1 else if b == 13 then 1 else 0
  let seen := c.seen + 1
  let hdr := c.hdr.push b
  if crlf == 4 then
    { req := .empty, decided := true,
      resp := if req.toList.contains 13 then answer site req hdr else errorText 400 "Bad Request" false }
  else if seen ≥ site.hdrMax then { req := .empty, decided := true, resp := errorText 400 "Bad Request" false }
  else { c with req, crlf, seen, hdr }

def recv (site : Site) (c : Conn) (d : ByteArray) : Conn :=
  d.foldl (step site) c

/-! ## Control requests and kept connections (plan M9.5)

On a site with control routes or `keepAlive` (`Site.ctl`) a request is
taken as in M8 up to the end of its header; then:

* the connection is kept after the response when the site keeps
  connections, the request is `HTTP/1.1` and no `Connection` field lists
  `close` among its comma-separated tokens (`wantsClose`);
  a kept connection's responses have no `Connection` field;
* `GET`/`HEAD` of a control route, or `POST` of another route: 405;
* `POST` of a control route: a `Transfer-Encoding` field gives 501, no
  `Content-Length` 411, two of them or one that is not a canonical decimal
  (digits, no leading zero but `0` itself) 400, more than `bodyMax` 413;
  `X-Ember-Seq` must be there once, a canonical decimal below 2^32, else
  400; a protected route answers as `guard` does when the token is
  refused; each of these closes the connection (the body is not read);
* otherwise the body is read (`Content-Length` bytes), and with the
  shared state `Ctl`: a sequence number above the last one is executed
  (the body becomes the device's command; 200 `ok N`), the last one again
  with the same body (its SHA-256) is answered the same without executing,
  anything else gets 409.
-/

/-- The header's fields (after the request line): names in lower case,
values without the white space around them. -/
def fields (hdr : ByteArray) : List (List UInt8 × List UInt8) :=
  let lines := (Auth.splitOn 10 hdr.toList).map fun l => if l.getLast? == some 13 then l.dropLast else l
  (lines.drop 1).filterMap fun l =>
    let (name, rest) := l.span (· != 58)
    if rest.isEmpty then none
    else some (name.map lower, (((rest.drop 1).dropWhile isOws).reverse.dropWhile isOws).reverse)

def fieldVals (hdr : ByteArray) (name : String) : List (List UInt8) :=
  (fields hdr).filterMap fun (n, v) => if n == (str name).toList then some v else none

/-- A canonical decimal (digits, no leading zero but `0`) of at most `maxDigits` digits. -/
def decimal (v : List UInt8) (maxDigits : Nat) : Option Nat :=
  if v.isEmpty || v.length > maxDigits || !v.all (fun c => 48 ≤ c && c ≤ 57) || (v.length > 1 && v.head! == 48) then none
  else some (v.foldl (fun a c => a * 10 + (c.toNat - 48)) 0)

/-- Does a `Connection` field ask to close?  Its values are lists of
tokens separated by commas (RFC 9110 §7.6.1); `close` (any case, white
space around) among them asks to (RFC 9112 §9.6). -/
def wantsClose (hdr : ByteArray) : Bool :=
  (fieldVals hdr "connection").any fun v =>
    (Auth.splitOn 44 v).any fun t =>
      ((t.dropWhile isOws).reverse.dropWhile isOws).reverse.map lower == (str "close").toList

/-- What to do once a request's header is complete. -/
inductive Next where
  /-- Answer, then close or not. -/
  | respond (resp : ByteArray) (close : Bool)
  /-- Read a control request's body: its length and sequence number. -/
  | body (n seq : Nat)

def answerCtl (site : Site) (req hdr : ByteArray) (boot : Option Nat := none) : Next :=
  match spaceSplit (requestLine req) with
  | [m, target, v] =>
    if (v.take 7) != (str "HTTP/1.").toList || v.length != 8 || !(v.getLast?.any fun c => 48 ≤ c && c ≤ 57) ||
        target.isEmpty then
      .respond (errorText 400 "Bad Request" false) true
    else
    let keep := site.keepAlive && v.getLast? == some 49 && !wantsClose hdr
    let path := target.takeWhile (· != 63)
    let route := site.routes.find? (fun r => (str r.path).toList == path)
    let isGet := m == (str "GET").toList || m == (str "HEAD").toList
    let head := m == (str "HEAD").toList
    if isGet then
      match route with
      | none => .respond (errorText 404 "Not Found" head "" !keep) !keep
      | some r =>
        if r.post then .respond (errorText 405 "Method Not Allowed" head "Allow: POST\r\n" !keep) !keep else
        let ok := response 200 "OK" r.ctype r.body head "" !keep
        match r.scope with
        | none => .respond ok !keep
        | some need =>
          let a := guard site need hdr head ok
          -- a refusal closes as before; `guard`'s 400 never keeps the connection
          if a == ok then .respond ok !keep else .respond (guard site need hdr head (response 200 "OK" r.ctype r.body head)) true
    else if m == (str "POST").toList then
      match route with
      | none => .respond (errorText 404 "Not Found" false) true
      | some r =>
        if !r.post then .respond (errorText 405 "Method Not Allowed" false "Allow: GET, HEAD\r\n") true
        else if !(fieldVals hdr "transfer-encoding").isEmpty then .respond (errorText 501 "Not Implemented" false) true
        else match fieldVals hdr "content-length" with
        | [] => .respond (errorText 411 "Length Required" false) true
        | [cl] =>
          match decimal cl 9 with
          | none => .respond (errorText 400 "Bad Request" false) true
          | some n =>
            if n > site.bodyMax then .respond (errorText 413 "Content Too Large" false) true else
            match fieldVals hdr "x-ember-seq" with
            | [sq] =>
              match decimal sq 10 with
              | some seq =>
                if seq ≥ 2 ^ 32 then .respond (errorText 400 "Bad Request" false) true else
                let ok := response 200 "OK" r.ctype r.body false
                let allowed := match r.scope with
                  | none => none
                  | some need => let a := guard site need hdr false ok boot; if a == ok then none else some a
                match allowed with
                | some refusal => .respond refusal true
                | none => .body n seq
              | none => .respond (errorText 400 "Bad Request" false) true
            | _ => .respond (errorText 400 "Bad Request" false) true
        | _ => .respond (errorText 400 "Bad Request" false) true
    else .respond (errorText 501 "Not Implemented" false) true
  | _ => .respond (errorText 400 "Bad Request" false) true

/-- The answer to a complete control request with the shared state. -/
def control (g : Ctl) (body : ByteArray) (seq : Nat) (keep : Bool) : Ctl × ByteArray :=
  let h := Spec.Crypto.sha256 body
  let ok := response 200 "OK" "text/plain" (str s!"ok {seq}\n") false "" !keep
  if seq > g.last then ({ g with last := seq, lastHash := h, cmd := body, cmds := g.cmds + 1 }, ok)
  else if seq == g.last && h == g.lastHash then (g, ok)
  else (g, errorText 409 "Conflict" false "" !keep)

/-- One byte of a request on a `ctl` site. -/
def stepCtl (site : Site) (gc : Ctl × Conn) (b : UInt8) : Ctl × Conn :=
  let (g, c) := gc
  if c.decided then (g, c) else
  match c.body with
  | some (n, seq, _) =>
    let buf := c.bodyBuf.push b
    if buf.size < n then (g, { c with bodyBuf := buf }) else
    let (g, r) := control g buf seq !c.closeAfter
    (g, { c with body := none, bodyBuf := .empty, decided := true, resp := r })
  | none =>
  let req := if c.req.size < site.reqMax then c.req.push b else c.req
  let want : List UInt8 := [13, 10, 13, 10]
  let crlf := if b == want.getD c.crlf 0 then c.crlf + 1 else if b == 13 then 1 else 0
  let seen := c.seen + 1
  let hdr := c.hdr.push b
  if crlf == 4 then
    if !req.toList.contains 13 then (g, { decided := true, resp := errorText 400 "Bad Request" false }) else
    match answerCtl { site with now := g.now } req hdr g.boot with
    | .respond r close => (g, { decided := true, resp := r, closeAfter := close })
    | .body n seq =>
      -- the connection is kept unless the request says otherwise (as for GET)
      let keep := match spaceSplit (requestLine req) with
        | [_, _, v] => site.keepAlive && v.getLast? == some 49 && !wantsClose hdr
        | _ => false
      let c' : Conn := { closeAfter := !keep, body := some (n, seq, 0) }
      if n == 0 then
        let (g, r) := control g .empty seq keep
        (g, { c' with body := none, decided := true, resp := r })
      else (g, c')
  else if seen ≥ site.hdrMax then (g, { decided := true, resp := errorText 400 "Bad Request" false })
  else (g, { c with req, crlf, seen, hdr })

def recvCtl (site : Site) (g : Ctl) (c : Conn) (d : ByteArray) : Ctl × Conn :=
  d.foldl (stepCtl site) (g, c)

/-- A kept connection whose response is all acknowledged takes the next request. -/
def ackedCtl (c : Conn) (n : Nat) : Conn :=
  let c := { c with resp := c.resp.extract n c.resp.size }
  if c.decided && !c.closeAfter && c.resp.size == 0 then {} else c

/-- The HTTP application of a site with control routes or kept connections. -/
def appCtl (site : Site) : App where
  σ := Conn
  port := site.port
  init := {}
  -- nothing more is taken while a response is out (no pipelining)
  room c cap := if c.decided then 0 else cap
  recv c d := (recvCtl site (ctlInit site) c d).2
  avail c := c.resp.size
  bytes c off n := Bytes.slice c.resp off n
  acked := ackedCtl
  close c := c.decided && c.closeAfter
  idleClose := true
  reuseTimeWait := true
  G := Ctl
  ginit := ctlInit site
  recvG g c d := recvCtl site g c d
  udpPort := some timePort
  udpG := timeIn

/-- The HTTP application of a site as in M8 (no control routes, one request per connection). -/
def appM8 (site : Site) : App where
  σ := Conn
  port := site.port
  init := {}
  room _ cap := cap
  recv := recv site
  avail c := c.resp.size
  bytes c off n := Bytes.slice c.resp off n
  acked c n := { c with resp := c.resp.extract n c.resp.size }
  close c := c.decided
  idleClose := true
  reuseTimeWait := true

/-- The HTTP application of `site`: as in M8, or with control routes and
kept connections (M9.5). -/
def app (site : Site) : App := if site.ctl then appCtl site else appM8 site

/-- A small site for the tests. -/
def demo : Site where
  routes :=
    [{ path := "/", body := str "<!doctype html><title>Ember</title><h1>Hello from Ember</h1>\n" },
     { path := "/hello.txt", ctype := "text/plain", body := str "hello\n" },
     { path := "/big.txt", ctype := "text/plain",
       body := str (String.join ((List.range 40).map fun i => s!"line {i}: the quick brown fox jumps over the lazy dog\n")) }]

/-- The demo site with protected routes (plan M9.3): `/status` for any
token of the demo provider, `/control` with `drone:control`, `/camera`
with `camera:read`; the time fixed at `Auth.demoNow`. -/
def demoAuth : Site :=
  { demo with
    routes := demo.routes ++
      [{ path := "/status", ctype := "application/json", body := str "{\"battery\":87,\"armed\":false}\n", scope := some "" },
       { path := "/control", ctype := "text/plain", body := str "ok\n", scope := some "drone:control" },
       { path := "/camera", ctype := "text/plain", body := str "frame 0\n", scope := some "camera:read" }]
    auth := some Auth.demoCfg, now := some Auth.demoNow }

/-- `demoAuth` with a control route and kept connections (plan M9.5):
`POST /cmd` with `drone:control` hands the body to the device. -/
def demoCtl : Site :=
  { demoAuth with
    routes := demoAuth.routes ++ [{ path := "/cmd", ctype := "text/plain", body := .empty, scope := some "drone:control", post := true }]
    keepAlive := true }

end Ember.Spec.Srv.Http
