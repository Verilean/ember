# 9 · Control, status and time

Chapter 8 protected routes that *read* the device. This chapter covers
what the rest of plan M9 added to the server so that the device can be
*controlled*:

* **control requests** — `POST` with a bounded body and a sequence
  number, executed at most once (M9.5);
* **kept connections** — one TCP (and TLS) connection carries many
  requests (M9.5);
* **the time** as an input on UDP port 37, forward only, and the rule
  that control needs a token issued after the device started (M9.4);
* **entropy** for TLS from the board's RNG (M9.4; the mechanics are in
  [Chapter 7 §5](07-https.md#5--randomness)).

What this tree does **not** have, so you are not left looking for it:
there is no `/healthz` route, and `/status` in the demo site is a
constant body like any other route (`{"battery":87,"armed":false}`),
not a report generated from the device's state. The command a control
request delivers is left in globals for a device application to pick up
(§3); no such application is in the tree yet.

## 1 · Control routes in the Spec

A route becomes a control route with `post := true`, and a site uses the
M9.5 behaviour when it has one or keeps connections:

```lean
  /-- A control route (plan M9.5): it takes `POST` with a body and a
  sequence number, not `GET`. -/
  post  : Bool := false
```

```lean
  /-- Keep the connection for further requests (plan M9.5). -/
  keepAlive : Bool := false
  /-- Most bytes of a control request's body. -/
  bodyMax : Nat := 256
  deriving Inhabited

/-- Does the site use the control requests or keep-alive of M9.5?  A site
that does not is served exactly as in M8. -/
def Site.ctl (site : Site) : Bool := site.keepAlive || site.routes.any (·.post)
```

The demo control site adds one route to `demoAuth` (Chapter 8):

```lean
/-- `demoAuth` with a control route and kept connections (plan M9.5):
`POST /cmd` with `drone:control` hands the body to the device. -/
def demoCtl : Site :=
  { demoAuth with
    routes := demoAuth.routes ++ [{ path := "/cmd", ctype := "text/plain", body := .empty, scope := some "drone:control", post := true }]
    keepAlive := true }
```

The rules, from the doc comment of the M9.5 section of
[`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean):

* the connection is kept after the response when the site keeps
  connections, the request is `HTTP/1.1`, and no `Connection` field
  lists `close` among its comma-separated tokens; a kept connection's
  responses have no `Connection` field;
* `GET`/`HEAD` of a control route, or `POST` of another route: `405`
  (with `Allow`);
* `POST` of a control route: a `Transfer-Encoding` field gives `501`, no
  `Content-Length` `411`, two of them or one that is not a canonical
  decimal `400`, more than `bodyMax` `413`; `X-Ember-Seq` must be there
  once, a canonical decimal below 2^32, else `400`; a protected route
  answers as `guard` does when the token is refused; each of these
  closes the connection;
* otherwise the body is read (`Content-Length` bytes) and the shared
  state decides.

### Executed at most once

The decision (plan M9, "Replay of commands"): every control request
carries `X-Ember-Seq`; a number above the last executed one is executed;
the same number with a body of the same SHA-256 gets the same answer
again without executing; anything else is `409`. One number for the
whole device — so it lives in state shared by all connections, the
`G` of the `App` interface (Chapter 6):

```lean
/-- The state shared by the connections of a site with control routes
(plan M9.5): the last sequence number executed, the SHA-256 of its body,
the commands handed to the device (the last one, and how many). -/
structure Ctl where
  last     : Nat := 0
  lastHash : ByteArray := .empty
  cmd      : ByteArray := .empty
  cmds     : Nat := 0
  ...
```

```lean
/-- The answer to a complete control request with the shared state. -/
def control (g : Ctl) (body : ByteArray) (seq : Nat) (keep : Bool) : Ctl × ByteArray :=
  let h := Spec.Crypto.sha256 body
  let ok := response 200 "OK" "text/plain" (str s!"ok {seq}\n") false "" !keep
  if seq > g.last then ({ g with last := seq, lastHash := h, cmd := body, cmds := g.cmds + 1 }, ok)
  else if seq == g.last && h == g.lastHash then (g, ok)
  else (g, errorText 409 "Conflict" false "" !keep)
```

So a client that lost the answer to `seq 7` can send the same request
again and gets `200 ok 7` without the drone taking off twice. `200`
means the command was accepted into the device's buffer, not that it was
carried out.

The `App` for such a site takes no data while a response is out (no
pipelining) and puts the connection back to a fresh request once its
response is acknowledged:

```lean
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
```

Over TLS, `Spec.Srv.Tls.appData` feeds decrypted bytes one at a time,
so a second request in the same record after a kept response is the next
request; a kept response is sent without `close_notify`.

## 2 · The time

Tokens expire, so the device needs the time; it has no battery-backed
clock and no SNTP. The plan's decisions: the time is an input on UDP port
37 — 8 bytes, Unix seconds, big-endian — from the ground station or the
bridge; it only moves forward; the ESP32-C3's SYSTIMER advances it in
between. Someone on the link can move it forward (a denial of service),
not back.

```lean
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
```

Until the time is known every protected route answers `503`. The first
datagram also fixes the start (`boot`), which closes a gap the sequence
number would otherwise leave: the number is not kept across a restart,
so instead **a control request needs a token whose `iat` is at or after
the start** (decision 8-4). That is the `minIat` argument of `guard`
(Chapter 8), passed only for control routes; a token without `iat` is
refused there.

In Ember, [`Ember/Net/Ctl.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Ctl.lean) replaces the
stack's `udp_input` with one that sends datagrams for port 37 to
`time_in`:

```lean
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
```

and the token check reads the time through `clock`, which adds the
board's uptime since the last datagram:

```lean
/-- The time: `h_now` when it was set, plus the seconds since (the board's
runtime answers reads of `UPTIME` with the seconds since the start; 0 off
the board, where the time stays as set, as in the Spec). -/
ember def clock : u64 := do
  let up : u32 ← mmio.read32(UPTIME)
  let d : u32 := up - h_up_at
  return h_now + (d : u64)
```

On the ESP32-C3 the runtime answers reads of `UPTIME` with whole seconds
from SYSTIMER ([`runtime/esp32c3/rt.c`](https://github.com/Verilean/ember/blob/main/runtime/esp32c3/rt.c)); in
the interpreter and the host C it reads 0, so the time stays as set —
exactly the Spec, which has no uptime.

## 3 · Control in Ember

`Net.Ctl` is `Spec.Srv.Http.stepCtl` for small machines. It takes the
place of `Net.Http`'s `h_feed`, `h_byte`, `h_total` and of `Net.Auth`'s
`h_feed` in a program whose site is `ctl`:

* the header's lines are read for five names at once (`hc_line`):
  `authorization` (whose value goes to `Net.Auth`'s token reader),
  `content-length` and `x-ember-seq` (canonical decimals),
  `transfer-encoding` (counted) and `connection` (`close` among its
  tokens?);
* once the header is complete, `hc_decide` chooses the answer or the body
  to read, as `answerCtl` does;
* the body goes into a buffer of the connection (`c_buf`, `bodyMax`
  bytes each) and into the SHA-256 context that `Net.Auth` already has;
* when it is complete, `hc_exec` decides with the shared state:

```lean
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
  ...
```

`ctl_cmd[0, ctl_len)` holds the command and `ctl_new` says a new one has
arrived: that is the hand-off to the device. `200 ok N` is the one
response not in ROM: `dyn_ok` writes it into the connection's `h_dyn`
buffer. Every other answer — the `405`s, `411`, `413`, the two `409`s
(kept and not) — is another constant in `Net.Http.responses`.

## 4 · The images

[`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean) registers three
programs for M9, all HTTPS on two connections:

```lean
/-- The site of the shipped `https-ctl` image: the demo control site, the
RNG's bytes mixed in, no time until a datagram gives it. -/
def shippedCtl : Spec.Srv.Tls.Site :=
  let d := Spec.Srv.Tls.demoCtl
  let h : Spec.Srv.Http.Site := { d.http with now := none }
  { d with http := h, entropy := some (ByteArray.mk (Array.replicate 32 0)) }
```

```lean
   ("https-ctl", Net.Tls.prog 2 shippedCtl),
   ("https-ctl-test", Net.Tls.prog 2 Spec.Srv.Tls.demoCtl),
   ("https-auth-test", Net.Tls.prog 2 Spec.Srv.Tls.demoAuth)]
```

(The 32 zero bytes in `shippedCtl` only switch the RNG on, `TL_HWRNG`;
the Ember program reads the register, not those bytes.)

and [`tools/ember/qemu-test.sh`](https://github.com/Verilean/ember/blob/main/tools/ember/qemu-test.sh) builds
them:

```sh
mk NAME=stack-https-ctl       PROG=$out/https-ctl.c DEFS="-DEMBER_ENTROPY=1"
mk NAME=stack-https-ctl-test  PROG=$out/https-ctl-test.c DEFS="-DEMBER_TICK_HOST=1"
mk NAME=stack-https-auth-test PROG=$out/https-auth-test.c DEFS="-DEMBER_TICK_HOST=1"
```

`stack-https-ctl` is the one meant to ship: protected routes, control
requests, kept connections, the RNG's bytes in every handshake, and no
time until a datagram gives it. The two `-test` images have the demo
sites' fixed time and no RNG, so the recorded sessions replay on them.
Control over plain HTTP exists on the host (`ember-host --http --ctl`)
and in the tests, but no ESP32-C3 image is built for it.

## 5 · How it is checked

`EMBER_ONLY=control .lake/build/bin/test` runs both parts.

**The reference** ([`Tests/Ember/ControlTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/ControlTests.lean)):
33 requests on the demo control site — `405`, `404`, `411`, `413`,
`501`, `Content-Length` and `X-Ember-Seq` in and out of canonical form,
`401`/`403`, HTTP/1.0 and `Connection` lists (`close` among tokens, in
any case, with white space, in a second field; `closed`, `clo se`,
`keep-alive;close` keep), 2^32 − 1 and 2^32 — and seven steps of the
shared state (executed, answered again, `409` with another body or an
older number), byte by byte and on a kept connection. The time and
`iat` rules have their own cases:

```lean
  let cases : List (String × ByteArray × String) := [
    ("POST, iat before the start", post "1" "go" "" early, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat at the start", post "1" "go" "" atBoot, "HTTP/1.1 200 OK"),
    ("POST, no iat", post "1" "go" "" noIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat a string", post "1" "go" "" strIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, iat twice", post "1" "go" "" twoIat, "HTTP/1.1 401 Unauthorized"),
    ("POST, no scope and an early iat: 403 first", post "1" "go" "" earlyCam, "HTTP/1.1 403 Forbidden"),
    ("GET, iat before the start", str s!"GET /control HTTP/1.1\r\n{bearer early}\r\n", "HTTP/1.1 200 OK"),
    ...
```

along with: the first datagram sets the time and the start, an earlier
one is ignored, a datagram that is not 8 bytes changes nothing, `503`
before any time, and a later datagram that moves past the token's `exp`
turns `200` into `401`.

**Ember against the reference**
([`Tests/Ember/ControlNetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/ControlNetTests.lean)):
sixteen lists of requests on one kept connection (whole and in seven
pieces), and the recorded sessions; the interpreter and host C must give
`Spec.Srv`'s trace. The recorded sessions:

| fixture | recorded against | requests on one kept connection |
|---|---|---|
| `http-ctl/keep-post-conflict.trace` | `ember-host --http --ctl` | `POST /cmd` seq 2 `takeoff` (200 ok 2), seq 2 `land` (409), seq 3 `land` (200 ok 3) |
| `https-ctl/keep-get-post-retry.trace` | `ember-host --https --ctl` | `GET /status`, `POST /cmd` seq 1 `takeoff`, the same `POST` again (200, 200 ok 1, 200 ok 1) |

`qemu-test.sh` replays the HTTPS sessions on `stack-https-ctl-test` and
`stack-https-auth-test`. For the RNG, `AuthNetTests` checks that
entropy changes the handshake and that the Ember program reading the RNG
register gives `Spec.Srv.Tls`'s trace.

## 6 · Try it

### On the host

`ember-host --ctl` serves `Spec.Srv.Http.demoCtl` (over `--http`, or
under TLS with `--https`), at the time `--now` (default `Auth.demoNow`),
which is also the start. A token from `--token` is issued at that same
time, so its `iat` is at the start and control accepts it:

```sh
lake build ember-host
T=$(.lake/build/bin/ember-host --token "drone:control camera:read")
python3 tools/ember/record-linux.py client --name ctl --out /tmp \
    --host ".lake/build/bin/ember-host --http --ctl" \
    -- sh -c "curl -sS -H 'Authorization: Bearer $T' -H 'X-Ember-Seq: 1' --data-binary takeoff http://10.0.0.1/cmd \
              --next -sS -H 'Authorization: Bearer $T' -H 'X-Ember-Seq: 1' --data-binary takeoff http://10.0.0.1/cmd \
              --next -sS -H 'Authorization: Bearer $T' -H 'X-Ember-Seq: 1' --data-binary land http://10.0.0.1/cmd"
```

`--next` makes curl send the requests one after another on the same
connection. You see

```
ok 1
ok 1
Conflict
```

— executed, answered again without executing, refused because the same
number came with another body. Add `-v` to see that curl reused the
connection. A token without `drone:control` gets `403`; a `GET /cmd`
gets `405` with `Allow: POST`.

### In QEMU, with the time from the network

The shipped image has no time until it gets a datagram on port 37, so
before that `/status` and `/cmd` answer `503`. From the README of the
tests ([`Tests/Ember/README.md`](https://github.com/Verilean/ember/blob/main/Tests/Ember/README.md)), inside
`nix-shell` after `tools/ember/qemu-test.sh build`, with `T` a token from
`ember-host --token "drone:control"` (issued at `Auth.demoNow`, so that
is the time sent):

```sh
python3 tools/ember/record-linux.py client --name ctl-qemu --out /tmp --settle 3 \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-https-ctl.bin" \
    -- sh -c 'sleep 2; python3 -c "import socket, struct; socket.socket(socket.AF_INET, socket.SOCK_DGRAM).sendto(struct.pack(\">Q\", 1800000000), (\"10.0.0.1\", 37))"; sleep 1
       curl -sk -H "Authorization: Bearer $T" https://10.0.0.1/status \
       --next -sk -H "Authorization: Bearer $T" -H "X-Ember-Seq: 1" --data-binary takeoff https://10.0.0.1/cmd'
```

The one-line Python sends the 8-byte big-endian time; then curl reads
`/status` and posts a command on one TLS connection, and prints the
status JSON followed by `ok 1`. Here `$T` is expanded inside the
namespace, so export it first (`export T=…`).

On the board the time then advances by itself (SYSTIMER); the RNG feeds
every handshake; QEMU's RNG says nothing about the entropy's quality,
which the plan leaves to a test on a board.

That completes the server side of M9. For how these pieces are argued
about rather than tested, see [Chapter 10](10-proofs.md); for where
they sit in the whole, [Chapter 11](11-architecture.md).
