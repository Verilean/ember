# 7 · HTTPS and TLS 1.3

Chapter 6 served a site over plain HTTP. This chapter puts TLS 1.3 under
the same site: a server written as one more `App` in the Spec
([`Ember/Spec/Srv/Tls.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Tls.lean)), the same
server in Ember for the ESP32-C3
([`Ember/Net/Tls.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Tls.lean)), the crypto under both,
and the ways it is checked: RFC test vectors, OpenSSL, and sessions
recorded from `curl`, `openssl s_client` and a browser.

HTTPS runs on the host and on the ESP32-C3, not on the Z80: the plan's
M8 decision notes that SDCC miscompiles `u64` and that X25519 would take
minutes on a Z80.

## 1 · What the server does, and what it does not

The doc comment of `Spec.Srv.Tls` states the scope — RFC 8446, reduced:

* server only, full handshake only (no resumption, no 0-RTT, no
  HelloRetryRequest, no client certificate);
* **one suite**, `TLS_CHACHA20_POLY1305_SHA256`; **key exchange X25519**;
* **signatures**: the certificate's key and the `CertificateVerify`
  signature are **Ed25519** when the client offers it, otherwise **ECDSA
  P-256 with SHA-256** when the site has such a certificate (browsers;
  plan M8.8);
* the ClientHello must come in one record, every length in it inside
  what contains it; records up to `recMax` bytes are accepted;
* after the handshake, the application data is one HTTP request
  (`Spec.Srv.Http`); the response goes out in records of at most `chunk`
  bytes, then `close_notify`, then the TCP FIN;
* a key share whose shared secret is all zeros (a point of small order)
  ends the connection with `illegal_parameter` (RFC 8446 §7.4.2);
* anything else ends the connection with a fatal alert.

So a client that offers no ChaCha20 (an `openssl s_client
-ciphersuites TLS_AES_128_GCM_SHA256`, recorded in
`Tests/Ember/https/no-chacha.trace`) gets a `handshake_failure` alert.
Most clients offer ChaCha20 and X25519 by default; `curl`,
`openssl s_client` and Chromium all connect.

The parts of a ClientHello the server needs are what `parseHello`
returns:

```lean
structure Hello where
  random : ByteArray
  sid    : ByteArray
  share  : ByteArray
  /-- The signature algorithms offered: ed25519 (0x0807), ecdsa_secp256r1_sha256 (0x0403). -/
  ed     : Bool
  p256   : Bool
```

`parseHello` requires suite `0x1303` among the suites, `0x0304` among
`supported_versions`, a `signature_algorithms` extension, and an X25519
(`0x001d`) share of 32 bytes in `key_share`; every length is checked
against its container, so the Ember program reads the same bytes and
nothing beyond.

### The alerts

The alert numbers in the code are RFC 8446's:

| alert | when (in `Spec.Srv.Tls`) |
|---|---|
| 40 `handshake_failure` | a ClientHello that `parseHello` refuses, or neither Ed25519 nor (with a P-256 certificate) P-256 offered |
| 47 `illegal_parameter` | the shared secret is all zeros |
| 80 `internal_error` | no fresh entropy for this handshake, or a stuck RNG (§5) |
| 10 `unexpected_message` | a record of the wrong type for the phase |
| 20 `bad_record_mac` | a protected record that does not open |
| 51 `decrypt_error` | the client's Finished is wrong |
| 22 `record_overflow` | a record longer than `recMax` |

## 2 · The handshake in the Spec

The server keeps, per connection, the bytes received and not yet a whole
record (`inb`), what it has to send (`out`), the transcript, and the
traffic keys:

```lean
inductive Phase where
  | hello | finished | app | closed
  deriving Inhabited, BEq, Repr
```

`onRecord` moves through the phases. In `hello` a handshake record is
parsed and answered with the server's whole flight; in `finished` the
client's Finished is checked; in `app` the decrypted bytes go to the
HTTP application of Chapter 6:

```lean
  | .app =>
    if ty != 23 then (g, fail c 10) else
    match unprotect c.rx hdr body with
    | none => (g, fail c 20)
    | some (ity, m, rx) =>
      let c := { c with rx }
      -- a close_notify from the client: ours, and the end
      if ity == 21 then (g, respond site c .empty)
      else if ity != 23 then (g, fail c 10)
      else if site.http.ctl then appData site g c m
      else
        let hc := Http.recv site.http c.http m
        if hc.decided then (g, respond site c hc.resp) else (g, { c with http := hc })
```

That `Http.recv site.http` is the same function `ember-host --http`
runs: HTTPS is HTTP inside records, nothing more.

The key schedule is RFC 8446 §7.1 written out:

```lean
def expandLabel (secret : ByteArray) (label : String) (ctx : ByteArray) (len : Nat) : ByteArray :=
  let l := str ("tls13 " ++ label)
  hkdfExpand secret (b2 len ++ b1 l.size ++ l ++ b1 ctx.size ++ ctx) len

def deriveSecret (secret : ByteArray) (label : String) (msgs : ByteArray) : ByteArray :=
  expandLabel secret label (sha256 msgs) 32

def trafficKeys (secret : ByteArray) : Keys :=
  { key := expandLabel secret "key" .empty 32, iv := expandLabel secret "iv" .empty 12 }
```

and `serverFlight` builds ServerHello, a `change_cipher_spec` record, and
one protected record with EncryptedExtensions, Certificate,
CertificateVerify and Finished. The choice of signature is made there:

```lean
  -- Ed25519 when offered, else P-256 when offered and there is such a
  -- certificate; neither is handshake_failure, before anything else
  let useP := !h.ed && h.p256 && site.certP256.size > 0
  if !h.ed && !useP then fail c 40 else
  ...
  let certBytes := if useP then site.certP256 else site.cert
  ...
  let sig := if useP then p256Sign site.keyP256 (certVerifyContent (sha256 t2))
    else edSign site.key (certVerifyContent (sha256 t2))
  let cv := handshake 15 (b2 (if useP then 0x0403 else 0x0807) ++ b2 sig.size ++ sig)
```

## 3 · The site: certificates and keys

A TLS site is an HTTP site plus the certificates, the keys and the seed:

```lean
structure Site where
  http   : Http.Site
  /-- The certificate (DER) and the Ed25519 seed of its key. -/
  cert   : ByteArray
  key    : ByteArray
  /-- A second certificate with a P-256 key (its private scalar), for
  clients that do not offer Ed25519 — browsers (plan M8.8); none when empty. -/
  certP256 : ByteArray := .empty
  keyP256  : Nat := 0
  seed   : ByteArray
  ...
  recMax : Nat := 2048
  chunk  : Nat := 1024
  port   : UInt16 := 443
```

The demo site:

```lean
def demo : Site where
  http := Http.demo
  cert := demoCert
  key := demoKey
  certP256 := demoCertP256
  keyP256 := demoKeyP256
  seed := str "ember demo seed: not for production"
```

`demoCert` is a self-signed certificate for `ember.local` with an Ed25519
key; `demoCertP256` is one for `ember.local` and `10.0.0.1` with a P-256
key. Both were made once with `openssl req -x509` and are in the source
as hex DER, **with their private keys** (`demoKey`, the 32-byte Ed25519
seed; `demoKeyP256`, the P-256 scalar). They are demo keys, published —
so clients need `curl -k` or an exception in the browser.

The key and certificate are in the image (a plan M8 decision). To serve
your own, build a `Site` with your DER certificate and key in the same
form and register a program for it, as Chapter 6 §4 does for an HTTP
site; `Net.Tls.app` puts them into constant tables:

```lean
       table "TL_CERT" .u8 (site.cert.toList.map (·.toNat)), table "TL_KEY" .u8 (site.key.toList.map (·.toNat)),
       table "TL_CERT2" .u8 (site.certP256.toList.map (·.toNat)), scalar "CERT2_LEN" .u16 site.certP256.size,
       table "TL_KEY2" .u8 ((natBe site.keyP256 32).toList.map (·.toNat)),
```

A private key in ROM is readable by anyone who has the image; that is the
deal of this design, not something the code hides.

## 4 · TLS in Ember

`Net.Tls` is `Spec.Srv.Tls` "record for record and alert for alert",
with the crypto of `Ember/Net/Crypto` and the HTTP of `Net.Http` inside
(its request parser `h_decide` and its response tables `h_byte`).

The big difference from HTTP is memory. Plain HTTP regenerates every
response byte from ROM; TLS cannot, because a protected record depends
on the keys of the connection. So per connection there is a buffer of
records received (`t_inb`, `recMax + 5` = 2 053 bytes) and one of what is
sent from `snd.una` on (`t_out`, 4 096 bytes: the server's flight and the
protected response, kept as the Spec keeps them), and records are opened
and sealed in place. The transcript is a SHA-256 context per connection
(`t_tr_*`), saved and restored around the one shared SHA-256 engine:

```lean
ember def tr_load := do
  for i : u16 in [0, 8) do
    sh_h[i] := t_tr_h[cur * 8 + i]
  for j : u16 in [0, 64) do
    sh_blk[j] := t_tr_blk[cur * 64 + j]
  sh_n := t_tr_n[cur]
  sh_len := t_tr_len[cur]
```

The signature choice reads the same as the Spec's:

```lean
ember def flight (size : u16) := do
  -- Ed25519 when offered, else P-256 when offered and there is such a
  -- certificate; neither is handshake_failure, before anything else
  tl_usep := !tl_sig_ed && tl_sig_p && CERT2_LEN > 0
  if !tl_sig_ed && !tl_usep then
    fail(40)
    return
```

The program for a site is

```lean
/-- The HTTPS server for `site` on `n` connections (SLIP, MTU 296). -/
def prog (n : Nat) (site : Spec.Srv.Tls.Site) : Prog := Net.Srv.prog n (app n site)
```

and the shipped M8 image is `("https", Net.Tls.prog 2 Spec.Srv.Tls.demo)`
in [`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean). Measured (plan
M8): code 34 076 B, rodata 14 576 B (two certificates, the site, the
crypto's tables), RAM 28 860 B with two connections, against budgets of
64 KB and 32 KB.

## 5 · Randomness

TLS needs a fresh server random and a fresh ephemeral key per handshake.
The Spec must also be a function of its inputs, so it can be replayed.
Both are met by deriving them from three things:

```lean
  let entropy := if site.fresh then fresh else site.entropy
  let ent := entropy.getD .empty
  let srand := sha256 (site.seed ++ ent ++ str "server random" ++ h.random)
  let eph := sha256 (site.seed ++ ent ++ str "ecdhe" ++ h.random)
```

* `seed` — fixed in the site;
* `ent` — 32 bytes of entropy for this handshake (plan M9.4);
* the client's random.

With no entropy (`entropy := none`, the M8 sites) a ClientHello replayed
byte for byte gets the same key share: **a test configuration, not a
secure one**. The images `stack-https` and `stack-https-test`, built from
`Spec.Srv.Tls.demo`, are of this kind. Where the entropy comes from in
the configurations that have it:

* **`ember-host --https`** takes 32 bytes from the operating system's
  generator (`IO.getRandomBytes`) before each input, and the handshake
  uses them once (`Site.fresh`); see
  [`Ember/Tools/HostEntropy.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/HostEntropy.lean).
  If the system gives none, the host does not start (exit 3) or stops.
  A handshake that finds no fresh bytes ends with `internal_error`.
* **The ESP32-C3** reads its RNG data register eight times per handshake
  when the site has `entropy` (`TL_HWRNG`):

  ```lean
    -- the RNG's bytes for this handshake (plan M9.4)
    if TL_HWRNG then
      for w : u16 in [0, 8) do
        let v : u32 ← mmio.read32(RNG_DATA)
        tl_ent[4 * w] := (v : u8)
        tl_ent[4 * w + 1] := (v >>> 8 : u8)
        tl_ent[4 * w + 2] := (v >>> 16 : u8)
        tl_ent[4 * w + 3] := (v >>> 24 : u8)
      -- eight equal reads: a dead generator, internal_error (decision 9)
      let mut moved : bool := false
      for qe : u16 in [4, 32) do
        if tl_ent[qe] != tl_ent[qe - 4] then
          moved := true
      if !moved then
        fail(80)
        return
  ```

  The Spec takes the same 32 bytes as a value of the site, so a test can
  set the register and expect the Spec's trace. Built with
  `-DEMBER_ENTROPY=1`, the runtime
  ([`runtime/esp32c3/rt.c`](https://github.com/Verilean/ember/blob/main/runtime/esp32c3/rt.c)) turns on the SAR
  ADC noise source as ESP-IDF's `bootloader_random_enable` does and paces
  the reads as `esp_random` does. The image built this way is
  `stack-https-ctl` (Chapter 9). QEMU says nothing about the quality of
  the entropy; that needs a board.

For the tests, `ember-host` has two switches (said on stderr when used):
`--entropy HEX` gives 64 hex digits as fixed entropy for every handshake,
and `--no-entropy` keeps the fixed seed alone — the configuration the
recorded HTTPS fixtures were made with.

## 6 · The crypto

All of it is written twice, as everything else: a reference in plain
Lean over `Nat` and `ByteArray`, written as the RFCs state it, and an
Ember version for small machines.

| | Spec ([`Ember/Spec/Crypto`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Crypto)) | Ember ([`Ember/Net/Crypto`](https://github.com/Verilean/ember/tree/main/Ember/Net/Crypto)) |
|---|---|---|
| SHA-256, HMAC, HKDF | `Sha2.lean`: `sha256`, `hmac256`, `hkdfExtract`, `hkdfExpand` | `Sha256.lean`: `sha_init`/`sha_byte`/`sha_final`, `hmac_*`, `hkdf_*` |
| SHA-512 | `Sha2.lean` | `Sha512.lean` (for Ed25519) |
| ChaCha20, Poly1305, AEAD | `ChaCha.lean`: `aeadSeal`, `aeadOpen` | `ChaCha.lean`: Poly1305 in five 26-bit limbs |
| X25519, Ed25519 | `Curve25519.lean`: `x25519`, `edSign` | `X25519.lean`, `Ed25519.lean` (after TweetNaCl, 16 limbs of 16 bits) |
| ECDSA P-256 | `P256.lean`: `p256Sign`, `p256Verify` (RFC 6979 nonces) | `P256.lean`: Montgomery form, complete projective addition |

The Ember versions are written without branches on secret data: the
X25519 and P-256 ladders swap with masks, the Poly1305 final reduction
selects with masks, and the AEAD compares the tag without a branch. The
plan is explicit that this is a coding discipline, not a guarantee —
neither Ember nor the C compiler promises constant time, and no claim is
made about side channels. The crypto is not audited.

`Net.Crypto.testProg` ([`Ember/Net/Crypto/Test.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Crypto/Test.lean))
is a small request/answer program that runs one operation per request,
so the same requests can be run on the interpreter, as host C, and on
the ESP32-C3 (image `crypto-test`).

## 7 · How it is checked

All of these run in `lake test`; `EMBER_ONLY=crypto` and `EMBER_ONLY=srv`
select the two suites that hold them.

**The crypto against the RFCs and OpenSSL**
([`Tests/Ember/CryptoTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/CryptoTests.lean)).
The references against the standards' vectors: SHA-256 and SHA-512
(FIPS 180-2, a million `a`), HMAC (RFC 4231), HKDF (RFC 5869), ChaCha20,
Poly1305 and the AEAD (RFC 8439), X25519 (RFC 7748), Ed25519 (RFC 8032),
ECDSA P-256 (RFC 6979 A.2.5). Then against OpenSSL on 30 random inputs
each (skipped without `openssl`), and random P-256 signatures verified
by `openssl dgst -verify`. Then the Ember versions against the references
on about 460 requests — the vectors, edge values (Poly1305 near p, X25519
`u` at and above p, scalars at L − 1, L, L + 1), tampered tags, random
inputs — interpreted and as host C with UBSan/ASan.

**The key schedule against RFC 8448**
([`Tests/Ember/TlsTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/TlsTests.lean)). RFC
8448 §3 is a full trace of a TLS 1.3 handshake. Its suite is AES-GCM and
its certificate RSA, so its records and signature are not this server's,
but its key schedule is SHA-256 and HKDF as here. The test feeds the
trace's ClientHello, ServerHello and shared secret through the Spec's
functions and compares every secret:

```lean
  [("transcript hash CH..SH", sha256 (ch ++ sh), "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"),
   ("early secret", early, "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"),
   ("derived", derived, "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"),
   ("handshake secret", hs, "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"),
   ...
   ("server finished key", expandLabel sHs "finished" .empty 32, "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8")]
```

The same file sends hand-built ClientHellos: key shares of small order
(u = 0, u = 1, a point of order 8) must get only `illegal_parameter`;
15 malformed ClientHellos (a length past or short of what contains it)
only `handshake_failure`; a ClientHello offering only
`ecdsa_secp256r1_sha256` a ServerHello (the P-256 path).

**Real clients, recorded.** `Tests/Ember/https/` holds sessions recorded
from Linux against `ember-host --https --no-entropy`:

| fixture | client |
|---|---|
| `curl-get.trace` | `curl -k https://10.0.0.1/` |
| `session.trace` | `curl -k`: GET /big.txt, GET /nope, HEAD /hello.txt; `openssl s_client`: GET /hello.txt |
| `no-chacha.trace` | `openssl s_client -ciphersuites TLS_AES_128_GCM_SHA256` (answered with `handshake_failure`) |

That `curl` and OpenSSL completed these handshakes and read the pages is
the interoperability check: their own TLS stacks accepted every
signature, key share, Finished and record the Spec produced. The test
replays each through `Spec.Srv.Tls` and requires the recorded bytes, line
for line.

**Ember against the Spec** (`SrvTests.lean`, M8.7). The recorded and the
made sessions, as they are, re-chunked and with ticks, run through
`Spec.Srv.Tls`, through the Ember interpreter and through host C (`-O2`,
UBSan/ASan, 1 and 2 connections); the traces must be equal. The
interpreter is slow on a handshake (two X25519 and a signature,
instruction by instruction), so it takes the sessions as made and
recorded and the host C takes the variants. `qemu-test.sh` replays them
on the ESP32-C3 image `stack-https-test`:

```sh
EMBER_HTTPS_DUMP=$out/https-sessions .lake/build/bin/test
python3 tools/ember/esp32.py corpus --image stack-https-test $out/https-sessions
```

## 8 · Try it

### curl and openssl on the host

```sh
lake build ember-host
nix-shell --run 'python3 tools/ember/record-linux.py client --name tls --out /tmp \
    --host ".lake/build/bin/ember-host --https" \
    -- sh -c "curl -sS -k -v https://10.0.0.1/"'
```

`-v` shows the handshake from curl's side — TLS 1.3 with
`TLS_CHACHA20_POLY1305_SHA256`, and the self-signed certificate for
`CN=ember.local` that `-k` lets through — then the page.

That is the secure configuration: fresh entropy per handshake. The
fixtures were recorded the same way with `--no-entropy` added, so that
their traces are reproducible.

`openssl s_client` works as the `--host` command does for curl; in
`session.trace` it fetched `/hello.txt`. To exercise the P-256
certificate without a browser, restrict the client's signature
algorithms to ECDSA P-256, and the server answers with `demoCertP256`:

```sh
nix-shell --run 'python3 tools/ember/record-linux.py client --name p256 --out /tmp \
    --host ".lake/build/bin/ember-host --https" \
    -- sh -c "echo Q | openssl s_client -connect 10.0.0.1:443 -tls1_3 -sigalgs ecdsa_secp256r1_sha256"'
```

Among its lines:

```
   a:PKEY: EC, (prime256v1); sigalg: ecdsa-with-SHA256
subject=CN=ember.local
Peer signature type: ecdsa_secp256r1_sha256
New, TLSv1.3, Cipher is TLS_CHACHA20_POLY1305_SHA256
Verify return code: 18 (self-signed certificate)
```

### QEMU

```sh
tools/ember/qemu-test.sh build
python3 tools/ember/record-linux.py client --name tls-qemu --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-https.bin" \
    -- sh -c 'sleep 2; curl -sS -k https://10.0.0.1/'
```

The bridge drops the ROM boot loader's banner on UART0 (everything
before the first SLIP END). Remember that `stack-https` has no entropy
(§5).

### A browser (M8.8)

Browsers do not offer Ed25519 for certificates, so this is the P-256
path. Headless Chromium against the ESP32-C3 in QEMU, inside
`nix-shell` (`$CHROMIUM` from `nix-shell -p chromium --run 'command -v chromium'`):

```sh
python3 tools/ember/record-linux.py client --name browser --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-https.bin" \
    -- sh -c 'sleep 2; $CHROMIUM --headless=new --no-sandbox --ignore-certificate-errors \
                --user-data-dir=/tmp/profile --dump-dom https://10.0.0.1/'
```

`--dump-dom` prints the page Chromium loaded. A browser's request header
is longer than `reqMax` (512): the header is taken up to `hdrMax`
(8 KB) and only the first `reqMax` bytes — the request line — are kept;
`HttpTests.lean` has a "long header" case for exactly this.

Next: [Chapter 8](08-auth.md) protects some of these routes with
OIDC access tokens.
