# Ember tests

`lake test` runs everything below; tests that need a tool (gcc, sdcc,
tshark) say "skipped" when it is missing.  The full set of tools comes
with `nix-shell` (see `shell.nix`):

```
nix-shell --run 'lake test'          # ≈ 6 minutes; EMBER_ONLY=spec|srv|crypto|auth|lang|net|esp32|z80 .lake/build/bin/test runs one suite
```

## What `lake test` checks

| Suite | Milestone | Contents |
|---|---|---|
| `Tests/Ember/SpecTests.lean` | M1 | checksum (RFC 1071/1624), SLIP, headers, trace format and `ember-diff`; **corpus replay** (`corpus/`, `regress/`); hand-written **scenarios** with their expectations; **1 000 generated sessions** per protocol, each also mutated and re-chunked, against the properties of `Ember.Spec.Gen`; the corpus through the `ember-host` binary; pcaps decoded by `tshark` |
| `Tests/Ember/SrvTests.lean`, `HttpTests.lean` | M8.1, M8.2, M8.6 | the stack with an application interface: `Spec.Srv` with echo and one connection = `Spec.Stack`, every trace line, on the corpus and on generated sessions (ICMP, UDP, TCP, DHCP; mutated, re-chunked, ticks mid-frame, Ethernet); the Ember program `Net.Srv` (interpreted, and as host C with `-O2` and UBSan/ASan) = `Spec.Srv` with 1 and 2 connections; a second client served with 2 connections, reset with 1. HTTP: a TCP client drives `Spec.Srv` with `Spec.Srv.Http.demo` (11 requests: routes, query, 404, HEAD, 501, HTTP/1.0, bad lines, a header longer than `reqMax`; in 1, 3 and 7 segments; three clients in a row on one connection, taking the one in TIME-WAIT) — the bytes received are `Http.answer`'s and the server closes; the recorded curl session `http/` replays; the Ember program `Net.Http` (interpreted and host C) = `Spec.Srv` on all of these, mutated, re-chunked and with ticks; HTTPS: the sessions recorded from Linux clients (`https/`: curl and `openssl s_client` against `ember-host --https`, and a ClientHello without ChaCha20, answered with `handshake_failure`) replay through `Spec.Srv.Tls` line for line; `TlsTests.lean`: the key schedule against RFC 8448 §3 (early, handshake and master secrets, the handshake traffic secrets, the server's handshake key — 16 bytes there — and IV, its finished key; that trace's AES-GCM records and RSA signature are not this server's and are not checked), and key shares of small order (u = 0, 1, a point of order 8) answered with `illegal_parameter` only (RFC 8446 §7.4.2), and 15 malformed ClientHellos (a length past or short of what contains it) with `handshake_failure` only; **the HTTPS server in Ember** (`Net.Tls`, M8.7): the interpreter on the recorded and made sessions, the host C (`-O2`, UBSan/ASan, 1 and 2 connections) on those and on their re-chunked and ticked forms = `Spec.Srv.Tls`; `qemu-test.sh` replays them on the ESP32-C3 image `stack-https-test` (`EMBER_HTTPS_DUMP=DIR`) |
| `Tests/Ember/CryptoTests.lean` | M8.5a, M8.5b | the crypto reference (`Ember/Spec/Crypto`) against the RFCs' test vectors: SHA-256 and SHA-512 (FIPS 180-2, a million `a`), HMAC-SHA256 (RFC 4231), HKDF (RFC 5869), ChaCha20, Poly1305 and the AEAD (RFC 8439), X25519 (RFC 7748), Ed25519 (RFC 8032), verification and rejection, ECDSA P-256 (RFC 6979 A.2.5: the public key, the nonce, the signatures of `sample` and `test`; random signatures verified by `openssl dgst -verify`; the complete projective ladder the Ember version uses = the affine reference); and against OpenSSL on 30 random inputs each (SHA-256, SHA-512, HMAC, Poly1305, ChaCha20 from a random counter, X25519, Ed25519 signatures; skipped without `openssl`); **the crypto in Ember** (`Ember/Net/Crypto`: SHA-256, HMAC, HKDF-Extract and -Expand, ChaCha20, Poly1305, the AEAD — sealing, and opening with the tag compared without a branch —, X25519, SHA-512, Ed25519 signing, reduction mod L, ECDSA P-256 signing and, M9.2, verification on a hash — good signatures for nine keys (among them 1, 2, n − 1, n − 2), the hash, `r`, `s` altered, `n − s`, another key, a key off the curve, `x = p`, (0, 0), `r`/`s` at 0 and n, RFC 7515 A.3, and a key and signature made once by OpenSSL 3.5.9 — accepted, refused with the message, `r` or `s` changed) behind a request/answer program (`Net.Crypto.testProg`), interpreted and as host C with `-O2` and UBSan/ASan: about 460 requests (the RFC vectors, edge values, cipher texts and tags with a changed byte — padding lengths, Poly1305 near p, X25519 u at and above p, scalars at L − 1, L, L + 1, 2^512 − 1 — and random inputs) = the reference; `qemu-test.sh` replays the same requests on the ESP32-C3 image `crypto-test` (`EMBER_CRYPTO_DUMP=DIR` writes them) |
| `Tests/Ember/AuthTests.lean` | M9.1 | OIDC access tokens in the reference (`Ember/Spec/Srv/Auth.lean`, protected routes of `Spec/Srv/Http.lean`): strict base64url (11 cases, both ways); RFC 7515 A.3 (the ES256 signature, the key from `d`, the payload's members); 74 tokens signed by `Auth.sign` (RFC 6979) and the scopes each must grant or its refusal — `alg` none/HS256/RS256/twice, `crit`, `kid` (unknown, absent with one and with two keys), altered or missing signature, `iss`/`aud` (arrays, escapes, `\u`, twice), every key the check reads given twice (`crit`, `kid`, `nbf`, `exp`, `aud`, `scope`), `exp`/`nbf` at the skew's bounds and as strings, fractions, 13 digits, leading zeros, a key hidden behind an escape, nested values skipped, depth 16 and 17, trailing bytes, trailing commas in arrays and objects (an `aud` array with ours and a comma after it), `[,]`, two commas; 18 requests on a site with public and protected routes (401 with and without `error`, 403 with the scope, 400 for two fields, 503 without a clock or keys), whole and byte by byte; with `openssl`, a token signed by OpenSSL accepted (refused when altered) and ours verified by `openssl dgst -verify` |
| `Tests/Ember/AuthNetTests.lean`, `Tests/Ember/http-auth/`, `Tests/Ember/https-auth/` | M9.3 | the token check in Ember (`Ember/Net/Auth.lean`) against the reference: 119 requests (every token of `AuthTests` on `/status`, six on `/control`, the requests of `AuthTests.routes`, 28 edges of the `Authorization` field: tabs and spaces around `Bearer`, CRs inside the value, a bare LF, white space before the colon, longer and shorter names, HEAD, POST, a query) on five sites (two keys, one key, no clock, no keys, a later clock), whole and in seven pieces: answers = `Http.answer`, the interpreter (first site) and host C (every site, 1 and 2 connections; UBSan/ASan) = `Spec.Srv`; sessions recorded with curl and tokens of the demo provider (`ember-host --auth`, `--token`) over HTTP (200, 403) and HTTPS (200, 401 without a token, 403, 401 for an altered token): `Spec.Srv` = recorded, the interpreter and host C (as recorded, re-chunked, with ticks) = `Spec.Srv` |
| `Tests/Ember/LangTests.lean` | M2, M5.4, M5.7 | **the total semantics** `Lang.Sem` (what the proofs unfold) = interpreter, on random programs, the examples and every build of the stack on the corpus; **the emitted C under the C semantics** `Ember.C.Sem` = `Lang.Sem`, same programs, three profiles, never undefined, and a planted emitter bug noticed; type checker (one negative test per rule, with spans), interpreter (every construct, traps, fuel), surface syntax = hand-built AST, profiles, **golden C** (`golden/`), examples vs Lean references, **interpreter = host C** (−O0/−O2, UBSan/ASan, strict warnings), **SDCC** `--Werror`, **1 000 random programs** (`ember-fuzz`) |
| `Tests/Ember/NetTests.lean` | M3 | `Ember.Net` functions vs `Ember.Spec` on 10 000 random inputs; the corpus (SLIP and Ethernet fixtures) and **1 000 generated sessions** per protocol × 3 variants, plus 1 000 Ethernet and 1 000 DHCP sessions: Spec = Ember interpreter (**lockstep**) = host C |
| `Tests/Ember/TargetTests.lean` | M4 | `tools/ember/qemu-test.sh`: the bare-metal ESP32-C3 images in Espressif's QEMU — boot, trap handler, UART, interrupt-driven echo of 10 000 bytes, SLIP loopback, the SLIP corpus and **100 generated sessions** per protocol × 3 variants (target trace = Spec trace), SYSTIMER tick |
| `Tests/Ember/Z80Tests.lean` | M4z, M6.1 | the Z80 CPU model (interrupt modes, `EI` delay, `HALT`, `R`; random instruction streams against `z88dk-ticks`); SDCC's code on the model of the machine: the examples (interpreter = Z80), echo, SLIP loopback, the corpus and generated sessions (target trace = Spec trace) on the SLIP build's image and on its image without bounds checks (M5.9), random programs; the **own back end** (M6): assembler vs `z88dk-z80asm`, runtime routines vs their specifications, random programs through the IR and through generated code, index-check programs that must still trap, the corpus and sessions on the image it builds (`tools/ember/z80-test.sh`); **HTTP on the Z80** (plan M8.3): `Net.Http` (two connections) through SDCC and through the own back end, the recorded curl session and the HTTP exchanges replayed on the model = `Spec.Srv` |
| `Tests/Ember/Z80RegressW.lean` | M7.3 | `#guard`s when built (`tools/ember/ci.sh`; not imported by `lake test`): the lowering of `regress_wide_store` is the IR written out in `Ember/Proof/Z80RegressWIR.lean`, and what is computable of the checked program holds (entry, `progOkB`, `irOkB` of the layout of `Z80RegressWHItems`, no drop reasons or notes: the parts of `RegressSrc`), and, for two inputs, calls that end and a call that traps in `Lang.Sem` — evaluation, not a theorem; the theorems on its image, which take `RegressSrc`, are in `Ember/Proof/Z80RegressWH*.lean` |
| `Tests/Ember/Z80Cover.lean` | M7.3 | `#guard` when built (`tools/ember/ci.sh`; not imported by `lake test`): the instruction theorems cover all 30 instructions of `regress_wide_store` (`Ember.Proof.Z80Gen.coverage`) — evaluation, not a theorem, and nothing about its image |
| `lake build` | M5 | `Ember/Proof` is part of the library: the proofs are checked by building — properties of the Spec (M5.1–M5.3), refinement of the stack in Ember against it (M5.4–M5.6), the emitted C against the Ember semantics (M5.8), the IR of the Z80 back end against it (M7.1, M7.2), and the Z80 encoder against the CPU model (M7.4); the build also evaluates the `#guard`s that tie the theorems to the programs (the checked stack is the program the theorems are about; the checkers accept every build of the stack: `progOkB` for every profile of the C, `progOkB` and `irOkB` for the IR).  `Ember/Proof/README.md` lists the theorems and which links to the running code are tests, not theorems |

The target suites are skipped, with a line saying so, when their tools
are missing; inside `nix-shell` everything runs.

## Tools

| Command | Purpose |
|---|---|
| `lake exe ember-diff A B [--observable] [--context N] [--first-only] [--all]` | first difference of two traces, packets decoded field by field |
| `lake exe ember-pcap X.trace > X.pcap` | a trace's packets for Wireshark |
| `lake exe ember-replay [--write] F.trace…` | replay fixtures through `Ember.Spec` |
| `lake exe ember-host [--eth] [--dhcp] [--mtu N] [--tick-ms N] [--trace F]` | the Spec stack on stdin/stdout (SLIP, or length-prefixed Ethernet frames) |
| `lake exe ember-fixtures [--check]` | run the hand-written scenarios, (re)write their fixtures |
| `lake exe ember-gen [icmp\|udp\|tcp\|all] [N] [--seed S]` | generated sessions against the Spec's properties; failures shrunk into `regress/` |
| `lake exe ember-emit NAME [--profile P] [--ember] [--dropped] \| --golden` | emitted C of a registered program; `--dropped`: without its bounds checks, the SLIP build (`net`) only (M5.9); `--golden` rewrites `golden/` |
| `lake exe ember-fuzz [N] [--seed S] [--opt O0\|O2\|both] [--plant]` | random programs: interpreter vs C; `--plant` checks the fuzzer finds a planted emitter bug |
| `lake exe ember-lockstep FILES… \| --gen [P] [N] [--c]` | Spec = Ember interpreter (lockstep) [= host C]; `P`: `icmp udp tcp` (SLIP), `eth`, `dhcp` (the Ethernet builds), `slip`, `all`; a fixture runs on the build its header names; `--dropped`: the SLIP build's C without its bounds checks |
| `tools/ember/record-corpus.sh` | re-record the Linux fixtures (user namespace + TUN/TAP, no root) |
| `tools/ember/size-report.py [--update]` | code/RAM per function, ±3 % gate against `bench/ember-size.baseline` |
| `lake exe ember-z80 asm-check\|rt-check\|ir-fuzz\|ir-replay\|own-fuzz\|own-build\|own-size …` | the own Z80 back end: its checks; `own-build net` writes the image (`.ihx`), a listing with the IR between the instructions (`.lst`) and symbols; `own-size` the bytes per function; `--plain`: without the passes on the assembly (the image the proofs of M7.3 speak of) |
| `lake exe ember-z80 profile\|stack IMAGE …` | T-states per function for one ping; deepest stack over fixtures |
| `lake exe ember-z80 check\|replay\|echo\|slip\|ping\|fuzz\|run …` | the Z80 model: against `z88dk-ticks`; fixtures, echo and SLIP on an SDCC image; T-states per ping; random programs (interpreter vs SDCC's code, `--u64` to see SDCC's 64-bit bugs); instruction trace with symbols |
| `tools/ember/qemu-run.sh IMAGE [--gdb] [--log]`, `tools/ember/esp32.py TEST` | one ESP32-C3 image in QEMU; one test against it |
| `tools/ember/ci.sh [JOB]` | what CI runs (the plan's `ember-spec`, `ember-lang`, `ember-net`, `ember-esp32`, `ember-z80`, `ember-proofs` jobs) |

## Exit-criteria runs (not part of `lake test`)

```
nix-shell --run 'lake exe ember-gen all 10000 --seed 7'          # M1: 30 000 sessions per protocol
nix-shell --run 'lake exe ember-fuzz 10000 --seed 42 --all'      # M2: 10 000 programs, −O0 and −O2
nix-shell --run 'lake exe ember-fuzz 1000 --plant --opt O0'      # M2: planted bug found and shrunk
nix-shell --run 'lake exe ember-lockstep --gen all 10000 --c'    # M3: Spec = interpreter = C
```

## Manual demo: ping and TCP echo from Linux (M1 exit criterion)

`ember-host` is the reference stack speaking SLIP on stdin/stdout.
Attach it to a pseudo-terminal and let Linux's SLIP driver use it (needs
root for `slattach` and `ip`, so this variant is not exercised by the
tests; the user-namespace variant below is):

```
lake build ember-host
socat -d -d pty,raw,echo=0,link=/tmp/ember-pty \
      exec:'.lake/build/bin/ember-host --trace /tmp/ember.trace',pty,raw,echo=0 &
sudo slattach -s 115200 -p slip /tmp/ember-pty &
sudo ip addr add 10.0.0.2 peer 10.0.0.1 dev sl0
sudo ip link set sl0 up mtu 296
ping -c 3 10.0.0.1
printf 'hello\n' | nc -N 10.0.0.1 7
lake exe ember-pcap /tmp/ember.trace > /tmp/ember.pcap    # open in Wireshark
```

Without root the same exchange runs in a user namespace with a TUN
device bridged to `ember-host` — that is how the `linux-*` fixtures of
the corpus were recorded:

```
python3 tools/ember/record-linux.py client --name demo --out /tmp \
    --host .lake/build/bin/ember-host -- sh -c 'ping -c 3 10.0.0.1; printf "hello\n" | nc -N 10.0.0.1 7'
```

(Recorded here: `ping` 0 % loss, `nc` echoed the line, Linux 6.18.)

## Manual demo: HTTP from Linux (M8.2)

`ember-host --http` runs `Spec.Srv` with the HTTP application and its demo
site on port 80 (`--conns N` for N connections).  Without root, in a user
namespace with a TUN device:

```
lake build ember-host
python3 tools/ember/record-linux.py client --name curl --out /tmp \
    --host ".lake/build/bin/ember-host --http" \
    -- sh -c 'curl -sS http://10.0.0.1/ && curl -sS -I http://10.0.0.1/hello.txt'
```

The same on the ESP32-C3 in QEMU (inside `nix-shell`, after
`tools/ember/qemu-test.sh build`): `tools/ember/qemu-bridge.py` runs an
image and puts its UART0 on stdin/stdout, as `ember-host` is:

```
python3 tools/ember/record-linux.py client --name curl-qemu --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-http.bin" \
    -- sh -c 'sleep 2; curl -sS http://10.0.0.1/big.txt'
```

`qemu-test.sh` replays the HTTP sessions on the image `stack-http-test`
(`esp32.py corpus --image stack-http-test`): the recorded curl session
and the exchanges of `HttpTests.lean`, mutated, re-chunked and with ticks,
whose expected traces are `Spec.Srv`'s (`EMBER_HTTP_DUMP=DIR` writes them).

`Tests/Ember/http/curl-session.trace` was recorded so (GET of the page and
of a 2 110-byte file over several segments, a missing path, POST, HEAD;
one connection, each client taking the previous one's TIME-WAIT).

## Manual demo: HTTPS from Linux (M8.6)

`ember-host --https` runs `Spec.Srv.Tls` (TLS 1.3 with
`TLS_CHACHA20_POLY1305_SHA256`, X25519 and an Ed25519 certificate) with
the same demo site on port 443.  The certificate is a self-signed demo
(`Spec.Srv.Tls.demoCert`, its key in the source): use `curl -k` or
`openssl s_client`.  The server's random and ephemeral key come from a
fixed seed and the client's random, so traces are reproducible; this is
a test configuration, not a secure one.

```
nix-shell --run 'python3 tools/ember/record-linux.py client --name tls --out /tmp \
    --host ".lake/build/bin/ember-host --https" \
    -- sh -c "curl -sS -k -v https://10.0.0.1/"'
```

`Tests/Ember/https/` holds sessions recorded so.

The same on the ESP32-C3 in QEMU: `tools/ember/qemu-bridge.py
.lake/build/esp32c3/stack-https.bin` as `--host` (inside `nix-shell`, after
`tools/ember/qemu-test.sh build`), then `curl -sS -k https://10.0.0.1/`.
The bridge drops the ROM boot loader's banner on UART0 (before the first
SLIP END); `record-linux.py` keeps the bytes after the last END undecoded
between reads (a data byte 0xC0, sent escaped, split a frame when the
decoded rest was read again).

### A browser (M8.8)

A browser does not offer Ed25519: `Spec.Srv.Tls` and `Net.Tls` answer a
client that offers only `ecdsa_secp256r1_sha256` with the P-256 demo
certificate (`Spec.Srv.Tls.demoCertP256`, `ember.local` and `10.0.0.1`).
Headless Chromium against the ESP32-C3 in QEMU, inside `nix-shell`
(Chromium's path from `nix-shell -p chromium --run 'command -v chromium'`):

```
python3 tools/ember/record-linux.py client --name browser --out /tmp \
    --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-https.bin" \
    -- sh -c 'sleep 2; $CHROMIUM --headless=new --no-sandbox --ignore-certificate-errors \
                --user-data-dir=/tmp/profile --dump-dom https://10.0.0.1/'
```

A browser's request header is longer than `reqMax`: the header is taken
up to `hdrMax` (8 KB) and only its first `reqMax` bytes, the request line,
are kept.
