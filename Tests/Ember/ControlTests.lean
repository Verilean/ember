import Tests.Ember.AuthTests

/-!
# Control requests and kept connections in the reference (plan M9.5)

`Spec.Srv.Http.recvCtl` on the demo site with a control route: the
answers, whether the connection is kept, and the shared state (the last
sequence number, the device's command), request after request.
-/

namespace Ember.Tests.ControlTests
open Ember Ember.Spec.Srv

def str (s : String) : ByteArray := s.toUTF8

def site : Http.Site := Http.demoCtl
def ctl := Auth.demoToken "drone:control camera:read"
def cam := Auth.demoToken "camera:read"
def bearer (t : ByteArray) : String := s!"Authorization: Bearer {String.fromUTF8! t}\r\n"

def post (seq : String) (body : String) (extra : String := "") (tok : ByteArray := ctl) : ByteArray :=
  str s!"POST /cmd HTTP/1.1\r\nHost: ember\r\n{bearer tok}X-Ember-Seq: {seq}\r\nContent-Length: {body.utf8ByteSize}\r\n{extra}\r\n{body}"

def statusLine (b : ByteArray) : String :=
  String.fromUTF8! (ByteArray.mk (b.toList.takeWhile (· != 13)).toArray)

/-- A request on a fresh connection with the shared state `g`: status line,
whether the connection is closed after, the shared state after. -/
def one (g : Http.Ctl) (req : ByteArray) : String × Bool × Http.Ctl :=
  let (g, c) := Http.recvCtl site g {} req
  (statusLine c.resp, c.closeAfter, g)

/-- Each case: a name, the request, the status line, closed after. -/
def single : List (String × ByteArray × String × Bool) := [
  ("GET with a token, kept", str s!"GET /status HTTP/1.1\r\n{bearer ctl}\r\n", "HTTP/1.1 200 OK", false),
  ("GET, HTTP/1.0, closed", str s!"GET /status HTTP/1.0\r\n{bearer ctl}\r\n", "HTTP/1.1 200 OK", true),
  ("GET, Connection: close", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: Close\r\n\r\n", "HTTP/1.1 200 OK", true),
  ("Connection: keep-alive, close", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: keep-alive, close\r\n\r\n", "HTTP/1.1 200 OK", true),
  ("Connection: close, keep-alive", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: close, keep-alive\r\n\r\n", "HTTP/1.1 200 OK", true),
  ("Connection with white space and cases", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: \t Keep-Alive ,  CLOSE  \r\n\r\n", "HTTP/1.1 200 OK", true),
  ("Connection: ,close,", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: ,close,\r\n\r\n", "HTTP/1.1 200 OK", true),
  ("two Connection fields, the second close", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: keep-alive\r\nconnection: close\r\n\r\n", "HTTP/1.1 200 OK", true),
  ("Connection: keep-alive", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: keep-alive\r\n\r\n", "HTTP/1.1 200 OK", false),
  ("Connection: closed", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: closed\r\n\r\n", "HTTP/1.1 200 OK", false),
  ("Connection: clo se", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: clo se\r\n\r\n", "HTTP/1.1 200 OK", false),
  ("Connection: keep-alive;close", str s!"GET /status HTTP/1.1\r\n{bearer ctl}Connection: keep-alive;close\r\n\r\n", "HTTP/1.1 200 OK", false),
  ("POST with Connection: keep-alive, close", post "1" "go" "Connection: keep-alive, close\r\n", "HTTP/1.1 200 OK", true),
  ("GET of the control route", str s!"GET /cmd HTTP/1.1\r\n{bearer ctl}\r\n", "HTTP/1.1 405 Method Not Allowed", false),
  ("POST of a page", str s!"POST /status HTTP/1.1\r\n{bearer ctl}Content-Length: 0\r\n\r\n", "HTTP/1.1 405 Method Not Allowed", true),
  ("POST of no route", str "POST /nowhere HTTP/1.1\r\nContent-Length: 0\r\n\r\n", "HTTP/1.1 404 Not Found", true),
  ("no Content-Length", str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\n\r\n", "HTTP/1.1 411 Length Required", true),
  ("Transfer-Encoding", post "1" "go" "Transfer-Encoding: chunked\r\n", "HTTP/1.1 501 Not Implemented", true),
  ("Content-Length 01", str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\nContent-Length: 01\r\n\r\nx", "HTTP/1.1 400 Bad Request", true),
  ("Content-Length twice", post "1" "go" "Content-Length: 2\r\n", "HTTP/1.1 400 Bad Request", true),
  ("Content-Length above bodyMax", str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\nContent-Length: 257\r\n\r\n", "HTTP/1.1 413 Content Too Large", true),
  ("Content-Length of ten digits", str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\nContent-Length: 1000000000\r\n\r\n", "HTTP/1.1 400 Bad Request", true),
  ("no X-Ember-Seq", str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}Content-Length: 2\r\n\r\ngo", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq twice", post "1" "go" "X-Ember-Seq: 1\r\n", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq +1", post "+1" "go", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq 1,2", post "1,2" "go", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq empty", post "" "go", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq 007", post "007" "go", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq 2^32", post "4294967296" "go", "HTTP/1.1 400 Bad Request", true),
  ("X-Ember-Seq 2^32 - 1", post "4294967295" "go", "HTTP/1.1 200 OK", false),
  ("no token", str "POST /cmd HTTP/1.1\r\nX-Ember-Seq: 1\r\nContent-Length: 2\r\n\r\ngo", "HTTP/1.1 401 Unauthorized", true),
  ("a token without the scope", post "1" "go" "" cam, "HTTP/1.1 403 Forbidden", true),
  ("an empty body", post "1" "", "HTTP/1.1 200 OK", false)
]

/-- The shared state at the start: the demo site's time. -/
def g0 : Http.Ctl := Http.ctlInit site

def be8 (v : Nat) : ByteArray := ByteArray.mk ((List.range 8).reverse.map fun i => (v / 256 ^ i % 256).toUInt8).toArray

/-- A token of the demo provider with a payload of our own. -/
def tokenWith (payload : String) : ByteArray :=
  Auth.sign Auth.demoIdpKey "{\"alg\":\"ES256\",\"kid\":\"demo\"}" payload

def claims (rest : String) (now : Nat := Auth.demoNow) : String :=
  s!"\{\"iss\":\"https://idp.ember.local\",\"aud\":\"ember-drone\",\"exp\":{now + 3600},\"scope\":\"drone:control camera:read\"{rest}}"

/-- Plan M9.4: the time from datagrams (forward only), 503 without it,
and `iat` on the control routes (decision 8-4). -/
def time : IO Nat := do
  let mut bad := 0
  let t := Auth.demoNow
  -- timeIn
  let g := Http.timeIn {} (be8 t)
  if g.now != some t || g.boot != some t then
    IO.println s!"  FAIL time: first datagram {g.now} {g.boot}"; bad := bad + 1
  let g2 := Http.timeIn g (be8 (t - 1))
  let g3 := Http.timeIn g (be8 (t + 10))
  let g4 := Http.timeIn g ((be8 (t + 10)).push 0)
  let g5 := Http.timeIn {} (ByteArray.mk #[1, 2, 3])
  if g2.now != some t || g3.now != some (t + 10) || g3.boot != some t || g4.now != some t || g5.now.isSome then
    IO.println "  FAIL time: forward only, 8 bytes only"; bad := bad + 1
  -- no time: 503 on protected routes, a page without scope as ever
  let none0 : Http.Site := { site with now := none }
  let n0 := Http.ctlInit none0
  let st (gs : Http.Ctl) (s : Http.Site) (req : ByteArray) := statusLine (Http.recvCtl s gs {} req).2.resp
  if st n0 none0 (post "1" "go") != "HTTP/1.1 503 Service Unavailable" ||
     st n0 none0 (str s!"GET /status HTTP/1.1\r\n{bearer ctl}\r\n") != "HTTP/1.1 503 Service Unavailable" ||
     st n0 none0 (str "GET /hello.txt HTTP/1.1\r\n\r\n") != "HTTP/1.1 200 OK" then
    IO.println "  FAIL time: no time"; bad := bad + 1
  let n1 := Http.timeIn n0 (be8 t)
  if st n1 none0 (post "1" "go") != "HTTP/1.1 200 OK" then
    IO.println "  FAIL time: after the datagram"; bad := bad + 1
  -- the time moved past the token's exp
  if st (Http.timeIn n1 (be8 (t + 3600 + 60))) none0 (post "1" "go") != "HTTP/1.1 401 Unauthorized" then
    IO.println "  FAIL time: expired after a later datagram"; bad := bad + 1
  -- iat: control needs one at or after the start; other routes do not
  let early := tokenWith (claims ",\"iat\":1799999999")
  let atBoot := tokenWith (claims s!",\"iat\":{t}")
  let noIat := tokenWith (claims "")
  let strIat := tokenWith (claims ",\"iat\":\"1800000000\"")
  let twoIat := tokenWith (claims s!",\"iat\":{t},\"iat\":{t}")
  let earlyCam := tokenWith ((claims ",\"iat\":1").replace "drone:control camera:read" "camera:read")
  let cases : List (String × ByteArray × String) := [
    ("POST, iat before the start", post "1" "go" "" early, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat at the start", post "1" "go" "" atBoot, "HTTP/1.1 200 OK"),
    ("POST, no iat", post "1" "go" "" noIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat a string", post "1" "go" "" strIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat twice", post "1" "go" "" twoIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, no scope and an early iat: 403 first", post "1" "go" "" earlyCam, "HTTP/1.1 403 Forbidden"),
    ("GET, iat before the start", str s!"GET /control HTTP/1.1\r\n{bearer early}\r\n", "HTTP/1.1 200 OK"),
    ("GET, no iat", str s!"GET /control HTTP/1.1\r\n{bearer noIat}\r\n", "HTTP/1.1 200 OK"),
    ("GET, iat a string", str s!"GET /control HTTP/1.1\r\n{bearer strIat}\r\n", "HTTP/1.1 401 Unauthorized")]
  for (name, req, want) in cases do
    let got := st g0 site req
    if got != want then
      IO.println s!"  FAIL time {name}: {got}"; bad := bad + 1
  IO.println s!"time: datagrams, 503 without the time, {cases.length} iat cases, {bad} failures"
  return bad

def run : IO Nat := do
  let mut bad := 0
  for (name, req, line, close) in single do
    let (l, c, _) := one g0 req
    if l != line || c != close then
      IO.println s!"  FAIL control {name}: {l} closed={c}"; bad := bad + 1
  -- a sequence on the shared state, each request on a fresh connection
  let steps : List (String × ByteArray × String × Nat × String) := [
    ("seq 1 takeoff", post "1" "takeoff", "HTTP/1.1 200 OK", 1, "takeoff"),
    ("seq 1 again, same body: answered, not executed", post "1" "takeoff", "HTTP/1.1 200 OK", 1, "takeoff"),
    ("seq 1 again, another body", post "1" "land", "HTTP/1.1 409 Conflict", 1, "takeoff"),
    ("seq 0", post "0" "land", "HTTP/1.1 409 Conflict", 1, "takeoff"),
    ("seq 2 land", post "2" "land", "HTTP/1.1 200 OK", 2, "land"),
    ("seq 5", post "5" "hover", "HTTP/1.1 200 OK", 3, "hover"),
    ("seq 3 after 5", post "3" "x", "HTTP/1.1 409 Conflict", 3, "hover")]
  let mut g : Http.Ctl := g0
  for (name, req, line, cmds, cmd) in steps do
    let (l, _, g') := one g req
    g := g'
    if l != line || g.cmds != cmds || g.cmd != str cmd then
      IO.println s!"  FAIL control {name}: {l}, {g.cmds} commands, last {String.fromUTF8! g.cmd}"; bad := bad + 1
  -- byte by byte = whole; the answer carries the number
  let (g1, c1) := Http.recvCtl site g0 {} (post "7" "takeoff")
  let (g2, c2) := (post "7" "takeoff").foldl (fun (g, c) b => Http.recvCtl site g c (ByteArray.mk #[b])) (g0, ({} : Http.Conn))
  if c1.resp != c2.resp || g1.last != g2.last || !(String.fromUTF8! c1.resp).endsWith "ok 7\n" then
    IO.println "  FAIL control: byte by byte"; bad := bad + 1
  -- a kept connection: once the response is acknowledged, the next request
  let (k1, c) := Http.recvCtl site g0 {} (str s!"GET /status HTTP/1.1\r\n{bearer ctl}\r\n")
  let c := Http.ackedCtl c c.resp.size
  let (k2, c) := Http.recvCtl site k1 c (post "1" "takeoff")
  if statusLine c.resp != "HTTP/1.1 200 OK" || k2.last != 1 then
    IO.println s!"  FAIL control: kept connection {statusLine c.resp}"; bad := bad + 1
  -- M8's sites are served as before
  if Http.demoAuth.ctl || Http.demo.ctl || !site.ctl then
    IO.println "  FAIL control: Site.ctl"; bad := bad + 1
  IO.println s!"control: {single.length} requests, {steps.length} steps on the shared state, byte by byte, a kept connection, {bad} failures"
  return bad + (← time)

end Ember.Tests.ControlTests
