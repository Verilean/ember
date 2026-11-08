# 8 · Protected routes (OIDC / JWT)

Plan M9's goal is a device on the stack — a drone, say — that is read
and controlled over HTTPS, and only by those an identity provider
allows. This chapter covers the first half: **protected routes** that
take an OIDC access token (`Authorization: Bearer …`, a JWT signed with
ES256) and check it on the device itself. Chapter 9 covers the second
half: control commands, kept connections, and the time.

The decisions behind it are the table "Decided (the user, 2026-11-07)"
in the M9 section of [`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md); the
essentials:

* **The device is a resource server.** It verifies JWTs signed with
  ES256 against the identity provider's public keys, which are in the
  image (a list with their `kid`). It never talks to the provider (there
  is no TLS client, so no fetching of JWKS); a new key means a new image.
* **The time is an input.** While it is unknown, every protected route
  answers `503`.
* **Tokens are not revoked**; a short `exp` is the remedy.

## 1 · What a token must be

The reference is
[`Ember/Spec/Srv/Auth.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Auth.lean). Its doc
comment is the acceptance condition. The token is the JWS compact form
`B64(header) . B64(payload) . B64(signature)`, base64url without padding
(strict), and it is accepted when:

* `alg` is `"ES256"` (so `none`, `HS256`, `RS256` are refused) and there is
  no `crit`;
* `kid` names one of the configured keys, or there is no `kid` and there
  is exactly one key;
* the signature (`r ‖ s`, 64 bytes) verifies over the ASCII of
  `B64(header) . B64(payload)` with that key (ECDSA P-256, SHA-256);
* `iss` equals the configured issuer; `aud` equals the configured
  audience, or is an array of strings that contains it;
* `exp` is there and `now < exp + skew`; `nbf`, if there, has
  `nbf ≤ now + skew`; `iat`, if there, is a number;
* `scope`, if there, is a string; its words (split at spaces) are the
  scopes the token grants.

The JSON is parsed strictly and only the top level is looked at; a key
that the check reads and that appears twice refuses the token, and so
does a top-level key with an escape in it (so that `"nbf"` cannot
hide `nbf`).

The configuration is the issuer, the audience, the keys and a skew:

```lean
structure Key where
  kid : String
  /-- The public key, uncompressed: `04 ‖ X ‖ Y`. -/
  pub : ByteArray
  deriving Inhabited

structure Cfg where
  keys : List Key
  iss  : String
  aud  : String
  /-- Seconds of clock skew allowed on `exp` and `nbf`. -/
  skew : Nat := 60
  deriving Inhabited
```

and the check reads like the list above:

```lean
/-- The scopes a token grants and its `iat`, if it is accepted at time `now`. -/
def checkIat (cfg : Cfg) (now : Nat) (tok : ByteArray) : Option (List ByteArray × Option Nat) := do
  let [h, p, s] := splitOn 46 tok.toList | none
  let hb ← b64urlDecode h
  let pb ← b64urlDecode p
  let sb ← b64urlDecode s
  if sb.size != 64 then none
  let hj ← parseObj hb
  let pj ← parseObj pb
  -- the header
  let alg ← field hj "alg"
  if !isStr alg "ES256" then none
  let crit ← field hj "crit"
  if crit.isSome then none
  let kid ← field hj "kid"
  let key ← match kid with
    | none => if cfg.keys.length == 1 then cfg.keys.head? else none
    | some (.str (some k)) => cfg.keys.find? (·.kid.toUTF8 == k)
    | some _ => none
  let input := ByteArray.mk (h ++ [46] ++ p).toArray
  if !p256Verify key.pub input (beNat (sb.extract 0 32)) (beNat (sb.extract 32 64)) then none
  -- the claims
  let iss ← field pj "iss"
  if !isStr iss cfg.iss then none
  ...
```

### Your provider's key

A provider publishes its keys as a JWKS: for an EC key, `kid`, and the
coordinates `x` and `y` in base64url. `Key.pub` is `04 ‖ X ‖ Y`. The test
of RFC 7515 A.3 in
[`Tests/Ember/AuthTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/AuthTests.lean) builds
one from a JWK exactly so:

```lean
def a3Pub : ByteArray :=
  ByteArray.mk #[4] ++ ((Auth.b64urlDecode (bs "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU")).getD .empty)
    ++ ((Auth.b64urlDecode (bs "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0")).getD .empty)
```

```lean
def a3Cfg (aud : String) : Auth.Cfg := { keys := [{ kid := "a3", pub := a3Pub }], iss := "joe", aud }
```

### The demo provider

For `ember-host` and the recorded sessions there is a demo identity
provider whose private key is in the source (a demo key, never for a
real provider):

```lean
def demoCfg : Cfg :=
  { keys := [{ kid := "demo", pub := p256Public demoIdpKey }], iss := "https://idp.ember.local", aud := "ember-drone" }

/-- The time the recorded sessions were made at (2027-01-15). -/
def demoNow : Nat := 1_800_000_000

/-- A token of the demo provider with `scope`, valid for an hour from `now`. -/
def demoToken (scope : String) (now : Nat := demoNow) : ByteArray :=
  sign demoIdpKey "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"demo\"}"
    s!"\{\"iss\":\"https://idp.ember.local\",\"aud\":\"ember-drone\",\"sub\":\"pilot\",\"iat\":{now},\"exp\":{now + 3600},\"scope\":\"{scope}\"}"
```

`sign` makes the signature with an RFC 6979 nonce, so the same call
gives the same token every time.

## 2 · Protecting a route

A route is protected by its `scope` field (Chapter 6):

```lean
  /-- `none`: public; `some ""`: any accepted token; `some s`: a token with scope `s`. -/
  scope : Option String := none
```

and the site carries the configuration and the time:

```lean
  /-- The tokens accepted on protected routes. -/
  auth   : Option Auth.Cfg := none
  /-- The time, in seconds since 1970, if known. -/
  now    : Option Nat := none
```

The demo site with protected routes, in
[`Ember/Spec/Srv/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Http.lean):

```lean
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
```

So protecting a page is: give its route a `scope`, and give the site an
`auth` and a time. As in Chapter 6, Ember follows from the same value.

### The answers (RFC 6750)

`guard` decides the answer on a protected route; `answer` calls it with
the route's `ok` response when the route has a scope:

```lean
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
```

with the three `WWW-Authenticate` fields:

```lean
def challenge : String := "WWW-Authenticate: Bearer realm=\"ember\"\r\n"
def invalidToken : String := "WWW-Authenticate: Bearer realm=\"ember\", error=\"invalid_token\"\r\n"
def insufficientScope (s : String) : String :=
  s!"WWW-Authenticate: Bearer realm=\"ember\", error=\"insufficient_scope\", scope=\"{s}\"\r\n"
```

In a table:

| request on a protected route | answer |
|---|---|
| no `Authorization` field, or a scheme other than `Bearer` | `401`, `WWW-Authenticate: Bearer realm="ember"` |
| two or more `Authorization` fields | `400` |
| the time not known, or no keys configured | `503` |
| a credential that is not one token, or a token the check refuses | `401`, `error="invalid_token"` |
| an accepted token without the route's scope | `403`, `error="insufficient_scope", scope="…"` |
| an accepted token with the scope | `200` and the route's body |

A public route ignores `Authorization` altogether.

## 3 · The check in Ember, as the bytes arrive

A small machine cannot keep a token of arbitrary length and parse it
afterwards. [`Ember/Net/Auth.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Auth.lean) checks it
while the header arrives, keeping only what the check needs:

* the header's lines are followed byte by byte (`ha_line`), looking for
  the field name `authorization` in any case;
* the value (`ha_vbyte`): white space, the scheme `bearer`, the spaces,
  the token;
* the token (`j_char`): base64url decoded segment by segment; the signing
  input goes into a SHA-256 context of the connection; the two decoded
  JSON texts go through one scanner (`js_byte`) that keeps a depth and a
  bit per level and looks at the top level only; the signature into
  `j_sig`;
* the claims are compared with the configuration as they are decoded —
  `alg` with `ES256`, `kid` with each key's id, `iss`, `aud`, `exp`,
  `nbf`, `iat` as numbers, and `scope`'s words against every scope a
  route of the site needs (a bit each, `j_grant`);
* only when the header is complete and the route is protected is the
  hash finished and the signature verified (`p2_verify`, ECDSA P-256
  verification added for M9.2).

About 250 bytes per connection, whatever the token's length. The final
decision mirrors `guard` branch for branch:

```lean
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
```

The answers are still constants in ROM: `Net.Http.responses` adds, for a
site with protected routes, the two `401`s, the `503`, and one `403` per
scope that some route needs (`Net.Auth.scopes`). Its `h_feed` takes the
place of `Net.Http`'s in such a program (`Net.Http.feedFns`), in HTTP and
in HTTPS alike, since TLS feeds decrypted bytes to the same `h_feed`. A
site without protected routes gets the M8 functions, unchanged.

## 4 · How it is checked

`EMBER_ONLY=auth .lake/build/bin/test` runs both parts.

**The reference** (`Tests/Ember/AuthTests.lean`, M9.1): strict base64url;
RFC 7515 A.3 (an ES256 example token, its key, its claims); 74 tokens
signed by `Auth.sign`, each with the scopes it must grant or `none` for
a refusal. A few of them:

```lean
  ("alg none", cfg, Auth.sign d1 "{\"alg\":\"none\",\"kid\":\"k1\"}" (claims), none),
  ("alg HS256", cfg, Auth.sign d1 "{\"alg\":\"HS256\",\"kid\":\"k1\"}" (claims), none),
  ("alg RS256", cfg, Auth.sign d1 "{\"alg\":\"RS256\",\"kid\":\"k1\"}" (claims), none),
  ("alg es256", cfg, Auth.sign d1 "{\"alg\":\"es256\",\"kid\":\"k1\"}" (claims), none),
  ("alg missing", cfg, Auth.sign d1 "{\"kid\":\"k1\"}" (claims), none),
  ("alg twice", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"alg\":\"none\",\"kid\":\"k1\"}" (claims), none),
```

— and `exp`/`nbf` at the skew's bounds and as strings, `aud` arrays,
escapes, nesting depth 16 and 17, trailing commas, and so on. Then the
answers of a site with public and protected routes, for example:

```lean
  ("no token", site, get "/status" [], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\""),
  ("good token", site, get "/status" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 200 OK", "Connection: close"),
  ("two Authorization fields", site, get "/status" [s!"Authorization: Bearer {tok good}", s!"Authorization: Bearer {tok good}"], "HTTP/1.1 400 Bad Request", "Connection: close"),
  ("control without its scope", site, get "/control" [s!"Authorization: Bearer {withScope "camera:read"}"], "HTTP/1.1 403 Forbidden",
    "WWW-Authenticate: Bearer realm=\"ember\", error=\"insufficient_scope\", scope=\"drone:control\""),
  ("a scope's prefix is not the scope", site, get "/control" [s!"Authorization: Bearer {withScope "drone:control2 drone"}"], "HTTP/1.1 403 Forbidden", "Connection: close"),
```

With `openssl` present, a token signed by OpenSSL is accepted (and
refused once altered), and the signatures made by `Auth.sign` verify
with `openssl dgst -verify`.

**Ember against the reference** (`Tests/Ember/AuthNetTests.lean`,
M9.3): 119 requests — every token above on `/status`, the route cases,
and 28 edges of the `Authorization` field that a streaming reader could
get wrong (tabs and spaces around `Bearer`, a CR inside the value, a
bare LF, white space before the colon) — on five sites (two keys, one
key, no clock, no keys, a later clock), whole and in seven pieces. The
interpreter and the host C (1 and 2 connections, UBSan/ASan) must give
`Spec.Srv`'s trace.

**Recorded sessions** with `curl` and tokens of the demo provider:

| fixture | request | answer |
|---|---|---|
| `http-auth/status-token.trace` | token with `drone:control camera:read`, `GET /status` | 200 |
| `http-auth/control-scope.trace` | token with `camera:read`, `GET /control` | 403 |
| `https-auth/status-token.trace` | as above, over HTTPS | 200 |
| `https-auth/status-none.trace` | no token, `GET /status` | 401 |
| `https-auth/status-altered.trace` | token with its last character changed | 401, `invalid_token` |
| `https-auth/control-scope.trace` | token with `camera:read`, `GET /control` | 403 |

Each is replayed through `Spec.Srv` (must equal the recording), then
through the interpreter and host C, as recorded, re-chunked and with
ticks. `qemu-test.sh` replays the HTTPS ones on the ESP32-C3 image
`stack-https-auth-test` (`Net.Tls.prog 2 Spec.Srv.Tls.demoAuth`).

## 5 · Try it with curl

`ember-host` has three flags for this (doc comment of
[`Ember/Tools/Host.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Host.lean)):

* `--auth` serves the demo sites with protected routes
  (`Spec.Srv.Http.demoAuth` over `--http`, `Spec.Srv.Tls.demoAuth` over
  `--https`);
* `--now T` sets their time in seconds since 1970 (default
  `Auth.demoNow`, the time of the recorded sessions);
* `--token SCOPE` prints a token of the demo provider with that scope,
  valid for an hour from that time, and exits.

```sh
lake build ember-host
.lake/build/bin/ember-host --token "drone:control camera:read"
```

prints a three-part token beginning with `eyJ`. Put it in a variable and
use it against the host over HTTP:

```sh
T=$(.lake/build/bin/ember-host --token "drone:control camera:read")
C=$(.lake/build/bin/ember-host --token "camera:read")
python3 tools/ember/record-linux.py client --name auth --out /tmp \
    --host ".lake/build/bin/ember-host --http --auth" \
    -- sh -c "curl -sS -i http://10.0.0.1/status;
              curl -sS -i -H 'Authorization: Bearer $T' http://10.0.0.1/status;
              curl -sS -i -H 'Authorization: Bearer $C' http://10.0.0.1/control"
```

What you see, in order:

```
HTTP/1.1 401 Unauthorized
Content-Type: text/plain
Content-Length: 13
WWW-Authenticate: Bearer realm="ember"
Connection: close

Unauthorized
```

then `200 OK` with `{"battery":87,"armed":false}`, then `403 Forbidden`
with `WWW-Authenticate: Bearer realm="ember", error="insufficient_scope",
scope="drone:control"`. Over HTTPS it is the same with
`ember-host --https --auth` and `curl -k https://10.0.0.1/…`.

Two things about the host's time. It is fixed: `--auth` serves the site
with `now := some o.now`, and nothing in the M8 HTTP application moves
it, so a token from `--token` (issued at the same `--now`) stays valid
for as long as the host runs. And it is the token's time, not the
wall clock's: `ember-host --http --auth --now 1800003700` with the token
above answers `401 invalid_token`, since its `exp` (+ 60 s skew) has
passed. Chapter 9 shows the time as an input that moves.

Next: [Chapter 9](09-control.md) adds `POST` commands, kept connections
and the time.
