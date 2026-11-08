# 6 · Tutorial: an HTTP app

The echo stack of the earlier chapters has its application welded in:
the echo buffer *is* the TCP send buffer. Plan M8 took the application
out and gave it an interface, and then wrote an HTTP/1.1 server on that
interface — twice, as everything in Ember is written: once in the Spec
(plain Lean, the reference) and once in Ember (the DSL that becomes C for
the ESP32-C3 and the Z80). This chapter walks through both, shows how a
route is added, how the two are checked equal, and how to point `curl`
at the result on the host and in QEMU.

```
            curl (Linux, 10.0.0.2, in a user namespace)
                 │  SLIP over a TUN device (record-linux.py)
                 ▼
  ember-host --http          or      qemu-bridge.py stack-http.bin
  Spec.Srv  +  Spec.Srv.Http.app           Net.Srv.prog 2 (Net.Http.app 2 site)
  (Lean, the reference)                     (Ember → C → ESP32-C3 in QEMU)
                 ▲                                   ▲
                 └────── same Site value, same bytes on the wire ─┘
```

The site — routes and bodies — is a Lean value of type
`Spec.Srv.Http.Site`. The Spec interprets it; the Ember program is
*generated* from it. Adding a route is one edit, and both sides follow.

## 1 · The application boundary

The connection logic is `Ember.Spec.Tcp`'s, statement for statement; the
application is asked uIP-style what it can take and what it has to send.
In the Spec it is a structure,
[`Ember/Spec/Srv/Tcp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Tcp.lean):

```lean
/-- An application on one listening port; `σ` is its state per connection. -/
structure App where
  σ : Type
  port : UInt16
  /-- The state of a connection that has just been opened. -/
  init : σ
  /-- The receive window, given `cap = min ourMss peerMss`. -/
  room : σ → Nat → Nat
  /-- In-order data in ESTABLISHED, already cut to `room`. -/
  recv : σ → ByteArray → σ
  /-- Bytes of the outgoing stream from `snd.una` on (sent or not). -/
  avail : σ → Nat
  /-- `bytes s off n`: bytes `[off, off + n)` of the stream from `snd.una`. -/
  bytes : σ → Nat → Nat → ByteArray
  /-- The first `n` bytes from `snd.una` were acknowledged. -/
  acked : σ → Nat → σ
  /-- The application is done: FIN once everything it has is sent. -/
  close : σ → Bool
  /-- Close after `idleTicks` ticks with nothing in flight (echo does). -/
  idleClose : Bool
  /-- A SYN that finds no connection in LISTEN takes one in TIME-WAIT
  (a server that closes first, as HTTP does, would otherwise refuse
  clients for `timeWaitTicks` after each one). -/
  reuseTimeWait : Bool := false
  ...
```

(The fields after `reuseTimeWait` — a state `G` shared by all
connections and a UDP port — came with plan M9; Chapter 9 uses them.)

The stack keeps no copy of what it sent: on a retransmission it asks
`bytes` again. Echo itself is just one `App`:

```lean
def echo : App where
  σ := ByteArray
  port := echoPort
  init := .empty
  room p cap := cap - p.size
  recv p d := p ++ d
  avail p := p.size
  bytes p off n := Bytes.slice p off n
  acked p n := p.extract n p.size
  close _ := false
  idleClose := true
```

[`Ember/Spec/Srv/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Stack.lean) holds `n`
connections of it (`Srv.Config.conns`): a segment goes to the connection
whose tuple it carries, otherwise to the first in LISTEN (or in
TIME-WAIT, when `reuseTimeWait`), otherwise it is answered with RST.

In Ember there are no function values, so the same interface is a set of
functions with fixed names, written by the application and called by
the stack, [`Ember/Net/Srv.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Srv.lean):

| function | `Ember.Spec.Srv.App` |
|---|---|
| `app_reset()` | `init` (the connection is new, or closed) |
| `app_room(cap : u16) : u16` | `room` |
| `app_recv(off : u16, n : u16)` | `recv`: the data is `buf[off, off + n)` |
| `app_avail() : u16` | `avail` |
| `app_fill(from : u16, n : u16, dst : u16)` | `bytes`: write bytes `[from, from + n)` of the stream from `snd.una` to `buf[dst, …)` |
| `app_acked(n : u16)` | `acked` |
| `app_close() : bool` | `close` |

plus a constant `APP_PORT` and two settings `APP_IDLE_CLOSE` and
`APP_REUSE_TW`. An application is its globals and its functions, and a
program is the stack plus one application on `n` connections:

```lean
/-- An application: its globals and its functions. -/
structure App where
  globals : List Global
  fns : List Fn
```

```lean
/-- The SLIP build with `n` connections and the application `app`. -/
def prog (n : Nat) (app : App) : Prog :=
```

The application works on the connection `cur`; since Ember has no arrays
of records, its per-connection state is one array per field, indexed by
`cur` (the TCB is stored the same way, `c_<field> : [_; n]`).

The test that closes M8.1: with echo and one connection, `Spec.Srv`
gives the trace of the old `Spec.Stack` line for line, on the corpus and
on generated sessions; and the Ember program `Net.Srv` (interpreted, and
as host C) gives `Spec.Srv`'s trace with 1 and 2 connections
([`Tests/Ember/SrvTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/SrvTests.lean)).

## 2 · HTTP in the Spec

[`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean) is an
HTTP/1.1 server as an `App`. Its doc comment is the specification; the
part that matters for M8:

* one request per connection; the header is taken until `CRLF CRLF`, at
  most `hdrMax` bytes, and only its first `reqMax` bytes are kept (for
  the request line); a body is not read;
* the request line is `METHOD SP target SP HTTP/1.d`; `GET` and `HEAD`
  are served, any other method gets `501`, a malformed line or an
  over-long header `400`;
* the target's path (the query is ignored) is looked up in the routes,
  exactly; a miss is `404`;
* the response is the status line, `Content-Type`, `Content-Length`,
  `Connection: close`, an empty line and the body (not for `HEAD`), and
  the server closes once it is all sent.

### The site

A site is data:

```lean
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
  ...
```

(`scope` and `post` are the protected and control routes of Chapters 8
and 9; leave them at their defaults for a public page.)

The demo site that every test, image and `ember-host` uses is at the end
of the file:

```lean
/-- A small site for the tests. -/
def demo : Site where
  routes :=
    [{ path := "/", body := str "<!doctype html><title>Ember</title><h1>Hello from Ember</h1>\n" },
     { path := "/hello.txt", ctype := "text/plain", body := str "hello\n" },
     { path := "/big.txt", ctype := "text/plain",
       body := str (String.join ((List.range 40).map fun i => s!"line {i}: the quick brown fox jumps over the lazy dog\n")) }]
```

`/big.txt` is 2 110 bytes: more than one TCP segment on SLIP (MSS 256),
so it exercises the window, the acknowledgements and retransmission from
`bytes`.

### The answer

The answer to a complete request header is a pure function. The
response bytes come from one builder:

```lean
def response (code : Nat) (reason ctype : String) (body : ByteArray) (head : Bool) (extra : String := "")
    (close : Bool := true) : ByteArray :=
  str s!"HTTP/1.1 {code} {reason}\r\nContent-Type: {ctype}\r\nContent-Length: {body.size}\r\n{extra}{if close then "Connection: close\r\n" else ""}\r\n"
    ++ (if head then .empty else body)

def errorText (code : Nat) (reason : String) (head : Bool) (extra : String := "") (close : Bool := true) : ByteArray :=
  response code reason "text/plain" (str (reason ++ "\n")) head extra close
```

and `answer` parses the request line and looks the path up:

```lean
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
```

(`63` is `?`: the path is the target up to the query.)

### Byte by byte

The request arrives in segments cut anywhere, so the Spec takes it one
byte at a time with a four-state matcher for `CRLF CRLF` — the same
shape the Ember program must have, which is why the Spec is written this
way and not with a string search:

```lean
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
```

and the M8 `App` is a few lines over it:

```lean
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
```

`close c := c.decided` is the whole closing policy: once the response is
decided the server sends it and its FIN. `reuseTimeWait := true` lets the
next client take the connection that is still in TIME-WAIT — without
it, a one-connection server would refuse clients for the TIME-WAIT
period after each request.

## 3 · HTTP in Ember

[`Ember/Net/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Http.lean) is the same server
for small machines. The key design point: the site is fixed when the
program is built, so **every response is known at build time**. All of
them — headers (as for `HEAD`) and bodies — go into one constant array
`h_rom`, with tables of where each starts. Response `k` is route `k`,
then `404`, `400`, `501`:

```lean
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
  ...
```

Note that this calls the Spec's own `response` and `errorText`: the bytes
in ROM are made by the reference, not retyped.

Per connection the program keeps only the first `REQ_MAX` bytes of the
request, a few counters, and which response was chosen (`h_kind`). A
segment's bytes are computed from the tables, so nothing of the response
is in RAM and a retransmission simply computes them again:

```lean
/-- Byte `off` of the response of the connection `cur`. -/
ember def h_byte (off : u16) : u8 := do
  let k : u16 := (h_kind[cur] : u16)
  if off < h_hlen[k] then
    return h_rom[h_hoff[k] + off]
  return h_rom[h_boff[k] + off - h_hlen[k]]
```

```lean
ember def app_fill (src : u16) (n : u16) (dst : u16) := do
  let p : u16 := h_pos[cur] + src
  for i in [0, n) do
    buf[dst + i] ← h_byte(p + i)
```

The end-of-header matcher is the Spec's `step` written for a `u8` state:

```lean
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
  ...
```

and `h_decide` is `answer`: it finds the request line, checks for exactly
two spaces and `HTTP/1.d`, recognises `GET`/`HEAD`, cuts the path at `?`
and compares it with each route's path in `h_paths`:

```lean
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
```

Finally `Net.Http.app` turns a `Site` into the globals — the tables,
built in Lean from `responses site` — and the functions:

```lean
def app (n : Nat) (site : Spec.Srv.Http.Site) (crypto : Bool := true) : Net.Srv.App :=
  let prot := Net.Auth.protected? site || site.ctl
  let rs := responses site
  -- h_rom: header 0, body 0, header 1, body 1, …
  let (rom, hoff, boff) := rs.foldl (fun (rom, ho, bo) (h, b) =>
    (rom ++ h.toList.map (·.toNat) ++ b.toList.map (·.toNat), ho ++ [rom.length], bo ++ [rom.length + h.size]))
    (([] : List Nat), ([] : List Nat), ([] : List Nat))
  let paths := site.routes.map fun r => r.path.toUTF8.toList.map (·.toNat)
  ...

/-- The HTTP server for `site` on `n` connections (SLIP, MTU 296). -/
def prog (n : Nat) (site : Spec.Srv.Http.Site) : Prog := Net.Srv.prog n (app n site)
```

The image the ESP32-C3 and the Z80 run is registered by name in
[`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean):

```lean
def extra : List (String × Prog) :=
  [("trapnote", Examples.TrapNote.prog), ("http", Net.Http.prog 2 Spec.Srv.Http.demo),
```

so `lake exe ember-emit http --profile rv32` prints its C.

## 4 · Adding a route

Because both sides read the same `Site`, adding a page is one edit in
[`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean). Say you
want `/version.txt`:

```lean
def demo : Site where
  routes :=
    [{ path := "/", body := str "<!doctype html><title>Ember</title><h1>Hello from Ember</h1>\n" },
     { path := "/hello.txt", ctype := "text/plain", body := str "hello\n" },
     { path := "/version.txt", ctype := "text/plain", body := str "ember m8\n" },
     ...
```

What follows from that edit, with nothing else changed:

* **the Spec** serves it — `answer` looks it up in `site.routes`;
* **the Ember program** serves it — `Net.Http.app` puts its header and
  body into `h_rom` and its path into `h_paths`, and `N_ROUTES`, `K_404`
  and the error kinds after it move by one;
* **`ember-host --http`** serves it — it runs `Srv.Http.app Srv.Http.demo`;
* **the images** `stack-http` and `stack-https` carry it the next time
  `tools/ember/qemu-test.sh build` runs, since `http` and `https` in
  `Emit.extra` are built from `Spec.Srv.Http.demo` (`Spec.Srv.Tls.demo`
  has `http := Http.demo`).

For a site of your own rather than the demo, define another `Site` value
and register a program for it next to `http` in `Emit.extra`, for
example `("mysite", Net.Http.prog 2 MyApp.site)`; `ember-emit mysite`
then prints its C, and the Makefile line for `stack-http` in
[`tools/ember/qemu-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-test.sh) shows how to
build an image from it:

```sh
mk NAME=stack-http      PROG=$out/http.c
```

Three things to keep in mind:

* **The site is static.** A body is a `ByteArray` fixed at build time
  and kept in ROM. There is no handler function to run per request; the
  one response computed at run time is the `200 ok N` of a control
  request (Chapter 9).
* **Changing an existing body changes recorded traces.** The recorded
  sessions under `Tests/Ember/http/` and `Tests/Ember/https/` hold the
  server's bytes as they were sent; they are compared with what the Spec
  sends now. Adding a route leaves the old responses as they are;
  editing `/` or `/big.txt` means recording those sessions again
  (§6).
* **Size is gated.** The routes are constants in the image, and
  `tools/ember/size-report.py` checks code and RAM per image within
  ±3 % of `bench/ember-size.baseline` (rows `esp32c3.http.*`,
  `z80.http.*`, `z80own.http.*`, `esp32c3.https.*`). A large body moves
  `rodata`; `size-report.py --update` records a deliberate change.

## 5 · How the two are checked equal

Nothing here is proved (the plan's M8 decision: the echo stack keeps its
proofs, M8 is checked by tests). The checks are differential, and they
run in `lake test` (`EMBER_ONLY=srv .lake/build/bin/test` runs just this
suite).

**The Spec against itself.**
[`Tests/Ember/HttpTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/HttpTests.lean) has a
small TCP client that drives `Spec.Srv` with the HTTP application:
handshake, the request (whole or cut), an ACK for every segment until
the server's FIN. The requests and what they must get:

```lean
/-- Requests and what each must be answered with. -/
def cases : List (String × ByteArray) :=
  let get (p : String) := str s!"GET {p} HTTP/1.1\r\nHost: 10.0.0.1\r\nUser-Agent: curl/8\r\nAccept: */*\r\n\r\n"
  [("GET /", get "/"),
   ("GET /hello.txt", get "/hello.txt"),
   ("GET /big.txt", get "/big.txt"),
   ("GET /hello.txt?x=1", get "/hello.txt?x=1"),
   ("GET /missing", get "/missing"),
   ("HEAD /", str "HEAD / HTTP/1.1\r\nHost: x\r\n\r\n"),
   ("POST /", str "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\n\r\n"),
   ("HTTP/1.0", str "GET / HTTP/1.0\r\n\r\n"),
   ("garbage", str "hello there\r\n\r\n"),
   ("bad version", str "GET / HTTP/2.0\r\n\r\n"),
   ("version not a digit", str "GET / HTTP/1.A\r\n\r\n"),
   ("too long", str ("GET /" ++ String.mk (List.replicate 600 'a') ++ " HTTP/1.1\r\n\r\n")),
   ...
```

Each is sent in 1, 3 and 7 segments; the bytes the client receives must
be `Http.answer`'s and the server must close. A second table checks the
status line independently of `answer` (so a bug in `answer` cannot
excuse itself):

```lean
  let status : List (String × String) :=
    [("GET /", "200"), ("GET /hello.txt", "200"), ("GET /big.txt", "200"), ("GET /hello.txt?x=1", "200"),
     ("GET /missing", "404"), ("HEAD /", "200"), ("POST /", "501"), ("HTTP/1.0", "200"),
     ("garbage", "400"), ("bad version", "400"), ("version not a digit", "400"), ("too long", "400"), ("long header", "200")]
```

Three clients in a row on one connection check the TIME-WAIT reuse.

When you add a route, add a line to `cases` and to `status` for it; that
is what puts it into every check below.

**The Ember program against the Spec.** In
[`Tests/Ember/SrvTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/SrvTests.lean) the inputs
of every exchange above become a session, and each session is also
mutated, re-chunked and given ticks in the middle of frames:

```lean
/-- The exchanges of `HttpTests`, each also mutated and re-chunked. -/
def httpStreams (seed : Nat) : Array (String × Array Input) := Id.run do
  ...
    out := out ++ #[(name, ins), (name ++ " mutated", m.inputs), (name ++ " re-chunked", c.inputs),
                    (name ++ " ticks", t.inputs)]
  out := out.push ("three clients in a row", (HttpTests.series httpApp HttpTests.seriesReqs).2)
```

Every stream runs through `Spec.Srv`, through the Ember interpreter
(`httpNet`) and through the emitted C compiled for the host with `-O2`
and UBSan/ASan (`httpHostC`), with 1 and 2 connections; the traces must
be equal. The Z80 suite does the same on the Z80 model, through SDCC and
the own back end (M8.3), and `qemu-test.sh` on the ESP32-C3 image (§7).

**Recorded sessions.** `Tests/Ember/http/curl-session.trace` was recorded
from a real Linux `curl` against `ember-host --http`:

```
# ember-trace v1  impl=spec  build=dev  profile=host64  link=slip
# recorded from Linux: curl (GET /, GET /big.txt, GET /missing, POST /, HEAD /hello.txt) against ember-host --http
# (Spec.Srv with Spec.Srv.Http.demo, one connection; tools/ember/record-linux.py client)
```

`httpFixtures` replays its inputs through `Spec.Srv` and requires the
recorded output; the Ember program then runs on the same inputs.

## 6 · Try it on the host

`ember-host` is the Spec stack on stdin/stdout, speaking SLIP. Its flags
are documented at the top of
[`Ember/Tools/Host.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Host.lean):

> `--http` runs `Ember.Spec.Srv` with the HTTP application and its demo
> site (`Spec.Srv.Http.demo`, port 80) instead of the echo stack (plan
> M8.2); `--https` the TLS 1.3 server of plan M8.6 with the same site on
> port 443 […]; `--conns N` gives either N connections (default 1).

`--trace FILE` writes the trace; `--tick-ms N` sets the tick (500 ms by
default).

To give it a real Linux client without root,
[`tools/ember/record-linux.py`](https://github.com/Verilean/ember/blob/main/tools/ember/record-linux.py)
`client` makes a user and network namespace with a TUN device, bridges
it over SLIP to the `--host` command (Ember is 10.0.0.1, Linux 10.0.0.2),
and runs a command inside:

```sh
lake build ember-host
python3 tools/ember/record-linux.py client --name curl --out /tmp \
    --host ".lake/build/bin/ember-host --http" \
    -- sh -c 'curl -sS http://10.0.0.1/ && curl -sS -I http://10.0.0.1/hello.txt'
```

The first `curl` prints the demo page,
`<!doctype html><title>Ember</title><h1>Hello from Ember</h1>`; the
second prints the `HEAD` response's header:

```
HTTP/1.1 200 OK
Content-Type: text/plain
Content-Length: 6
Connection: close
```

The session is written to `/tmp` as a trace (`--name` names it); that is
how `curl-session.trace` was made. `lake exe ember-pcap X.trace > X.pcap`
turns it into a capture for Wireshark. Try the error paths too:
`curl -sS http://10.0.0.1/missing` gives `Not Found`, and
`curl -sS -X POST http://10.0.0.1/` gives `Not Implemented`.

## 7 · Try it in QEMU

The same program in Ember, compiled for the ESP32-C3, runs in Espressif's
QEMU (inside `nix-shell`). `tools/ember/qemu-test.sh build` emits the C
and builds the images; for HTTP there are two:

```sh
# the HTTP server of plan M8 (Net.Http, two connections): as shipped, and
# for replay; tools/ember/qemu-bridge.py puts the first on stdin/stdout
mk NAME=stack-http      PROG=$out/http.c
mk NAME=stack-http-test PROG=$out/http.c DEFS="-DEMBER_TICK_HOST=1"
```

[`tools/ember/qemu-bridge.py`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-bridge.py) runs an
image and puts its UART0 on stdin/stdout, as `ember-host` is, so it can
be `record-linux.py`'s `--host`:

```sh
tools/ember/qemu-test.sh build
python3 tools/ember/record-linux.py client --name curl-qemu --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-http.bin" \
    -- sh -c 'sleep 2; curl -sS http://10.0.0.1/big.txt'
```

(`sleep 2` lets QEMU boot.) You get the 40 lines of `/big.txt`, served by
the C that `Net.Http` became, over a SLIP link at the UART.

The full QEMU run, `tools/ember/qemu-test.sh` with no argument, also
replays the HTTP sessions on `stack-http-test` (the image that takes its
ticks from the host, so that traces are reproducible):

```sh
EMBER_HTTP_DUMP=$out/http-sessions .lake/build/bin/test
python3 tools/ember/esp32.py corpus --image stack-http-test Tests/Ember/http $out/http-sessions
```

`EMBER_HTTP_DUMP` writes every stream of `httpStreams` with `Spec.Srv`'s
trace as the expected output; `esp32.py corpus` feeds the inputs to the
image and compares. So the recorded curl session and every exchange of
`HttpTests.lean`, cut and mutated, give the same bytes on the ESP32-C3 as
in the Spec.

## Sizes

From the plan (M8, measured): `stack-http` on the ESP32-C3 with two
connections is 15 688 B of text (the site's constants about 2.6 KB) and
5 884 B of bss, of which 4 KB is the stack and 2 × 512 B the request
buffers. On the Z80 it is 15 094 B of code with SDCC and 12 224 B with
the own back end.

Next: [Chapter 7](07-https.md) puts TLS 1.3 under the same site.
