import Ember.Spec.Srv.Tcp

/-!
# Ember.Spec.Srv.Http — an HTTP/1.1 server as an `App` (plan M8.2)

The reference for `Ember.Net.Srv.Http`.  One request per connection:

* the request is kept until its header ends (`CRLF CRLF`), at most
  `reqMax` bytes; a body is not read (nothing here takes one);
* the request line is `METHOD SP target SP HTTP/1.d`, `d` a digit; `GET` and `HEAD`
  are served, another method gets `501 Not Implemented`, a line that is
  not of that form, or a header longer than `reqMax`, `400 Bad Request`;
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
  /-- Most bytes of a request header kept. -/
  reqMax : Nat := 512
  port   : UInt16 := 80
  deriving Inhabited

structure Conn where
  /-- The request so far (until it is answered). -/
  req     : ByteArray := .empty
  /-- The response, once decided: the part from `snd.una` on. -/
  resp    : ByteArray := .empty
  decided : Bool := false
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

def recv (site : Site) (c : Conn) (d : ByteArray) : Conn :=
  if c.decided then c
  else
    let req := c.req ++ d
    if headerEnds req then { req := .empty, resp := answer site req, decided := true }
    else if req.size ≥ site.reqMax then
      { req := .empty, resp := errorText 400 "Bad Request" false, decided := true }
    else { c with req }

def app (site : Site) : App where
  σ := Conn
  port := site.port
  init := {}
  room c cap := if c.decided then cap else min cap (site.reqMax - c.req.size)
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
