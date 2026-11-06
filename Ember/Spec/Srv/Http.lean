import Ember.Spec.Srv.Tcp

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
-/

namespace Ember.Spec.Srv.Http
open Ember

structure Route where
  path  : String
  ctype : String := "text/html; charset=utf-8"
  body  : ByteArray
  deriving Inhabited

structure Site where
  routes : List Route
  /-- Most bytes of a request header kept (the request line must end within them). -/
  reqMax : Nat := 512
  /-- Most bytes of a request header taken. -/
  hdrMax : Nat := 8192
  port   : UInt16 := 80
  deriving Inhabited

structure Conn where
  /-- The request so far (until it is answered). -/
  req     : ByteArray := .empty
  /-- The response, once decided: the part from `snd.una` on. -/
  resp    : ByteArray := .empty
  decided : Bool := false
  /-- How much of `CRLF CRLF` the last bytes are; the bytes of the header so far. -/
  crlf    : Nat := 0
  seen    : Nat := 0
  deriving Inhabited

def crlf2 : List UInt8 := [13, 10, 13, 10]

/-- Does `b` contain `CRLF CRLF`? -/
def headerEnds (b : ByteArray) : Bool :=
  (List.range (b.size + 1 - 4)).any fun i => (Bytes.slice b i 4).toList == crlf2

def str (s : String) : ByteArray := s.toUTF8

def response (code : Nat) (reason ctype : String) (body : ByteArray) (head : Bool) : ByteArray :=
  str s!"HTTP/1.1 {code} {reason}\r\nContent-Type: {ctype}\r\nContent-Length: {body.size}\r\nConnection: close\r\n\r\n"
    ++ (if head then .empty else body)

def errorText (code : Nat) (reason : String) (head : Bool) : ByteArray :=
  response code reason "text/plain" (str (reason ++ "\n")) head

/-- The request line: bytes up to the first CR (or the end). -/
def requestLine (b : ByteArray) : List UInt8 :=
  b.toList.takeWhile (· != 13)

def spaceSplit (l : List UInt8) : List (List UInt8) :=
  let (cur, acc) := l.foldl (fun (cur, acc) b =>
    if b == 32 then ([], acc ++ [cur]) else (cur ++ [b], acc)) (([] : List UInt8), ([] : List (List UInt8)))
  acc ++ [cur]

/-- The answer to a complete request header. -/
def answer (site : Site) (req : ByteArray) : ByteArray :=
  match spaceSplit (requestLine req) with
  | [m, target, v] =>
    if (v.take 7) != (str "HTTP/1.").toList || v.length != 8 || !(v.getLast?.any fun c => 48 ≤ c && c ≤ 57) ||
        target.isEmpty then
      errorText 400 "Bad Request" false
    else if m == (str "GET").toList || m == (str "HEAD").toList then
      let head := m == (str "HEAD").toList
      let path := target.takeWhile (· != 63)
      match site.routes.find? (fun r => (str r.path).toList == path) with
      | some r => response 200 "OK" r.ctype r.body head
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
  if crlf == 4 then
    { req := .empty, decided := true,
      resp := if req.toList.contains 13 then answer site req else errorText 400 "Bad Request" false }
  else if seen ≥ site.hdrMax then { req := .empty, decided := true, resp := errorText 400 "Bad Request" false }
  else { c with req, crlf, seen }

def recv (site : Site) (c : Conn) (d : ByteArray) : Conn :=
  d.foldl (step site) c

def app (site : Site) : App where
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

/-- A small site for the tests. -/
def demo : Site where
  routes :=
    [{ path := "/", body := str "<!doctype html><title>Ember</title><h1>Hello from Ember</h1>\n" },
     { path := "/hello.txt", ctype := "text/plain", body := str "hello\n" },
     { path := "/big.txt", ctype := "text/plain",
       body := str (String.join ((List.range 40).map fun i => s!"line {i}: the quick brown fox jumps over the lazy dog\n")) }]

end Ember.Spec.Srv.Http
