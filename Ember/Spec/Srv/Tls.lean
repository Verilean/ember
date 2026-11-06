import Ember.Spec.Srv.Http
import Ember.Spec.Crypto.Curve25519
import Ember.Spec.Crypto.P256

/-!
# Ember.Spec.Srv.Tls — a TLS 1.3 server as an `App`, HTTP inside (plan M8.6)

The reference for the HTTPS server of plan M8.  RFC 8446, reduced:

* server only, full handshake only (no resumption, no 0-RTT, no
  HelloRetryRequest, no client certificate);
* one suite, `TLS_CHACHA20_POLY1305_SHA256`; key exchange X25519; the
  certificate's key and the `CertificateVerify` signature Ed25519 when
  the client offers it, otherwise ECDSA P-256 with SHA-256 when the site
  has such a certificate (browsers; plan M8.8);
* the ClientHello must come in one record, every length in it inside
  what contains it; records up to `recMax` bytes are accepted;
* after the handshake, the application data is one HTTP request
  (`Spec.Srv.Http`); the response goes out in records of at most `chunk`
  bytes, then `close_notify`, then the TCP FIN;
* a key share whose shared secret is all zeros (a point of small order)
  ends the connection with `illegal_parameter` (RFC 8446 §7.4.2);
* anything else ends the connection with a fatal alert.

**Randomness.**  The trace must be a function of the inputs, so the
server's random and its ephemeral X25519 key are derived from the site's
`seed` and the ClientHello's random (SHA-256 of both).  With a fixed seed
alone a ClientHello replayed byte for byte gets the same key share — a
test configuration, not a secure one.  With `entropy` (plan M9.4) 32 bytes
read from the board's random number generator for each handshake go in
between the seed and the label: the Spec takes them as a value of the
site (what eight reads of the RNG register give), the target reads the
register, so the tests can set it and the board gets fresh bytes.

The bytes to send are kept as they are made (`out`): the Spec states what
is sent; how a small machine regenerates them for a retransmission is
the Ember program's business.
-/

namespace Ember.Spec.Srv.Tls
open Ember Ember.Spec.Crypto

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
  /-- The 32 bytes of the board's RNG for a handshake (eight 32-bit reads of
  its data register, little-endian), mixed into the server random and the
  ephemeral key (plan M9.4); none: the seed alone (the tests of M8). -/
  entropy : Option ByteArray := none
  recMax : Nat := 2048
  chunk  : Nat := 1024
  port   : UInt16 := 443

inductive Phase where
  | hello | finished | app | closed
  deriving Inhabited, BEq, Repr

structure Keys where
  key : ByteArray := .empty
  iv  : ByteArray := .empty
  seq : Nat := 0
  deriving Inhabited

structure Conn where
  inb    : ByteArray := .empty
  phase  : Phase := .hello
  out    : ByteArray := .empty
  /-- The handshake messages so far (for the transcript hash). -/
  hs     : ByteArray := .empty
  rx     : Keys := {}
  tx     : Keys := {}
  /-- The client's Finished key and the application traffic secrets, once known. -/
  cFin   : ByteArray := .empty
  cAp    : ByteArray := .empty
  sAp    : ByteArray := .empty
  /-- The HTTP request inside, as `Spec.Srv.Http` takes it. -/
  http   : Http.Conn := {}
  done   : Bool := false
  deriving Inhabited

/-! ## Bytes -/

def b1 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat n]
def b2 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]
def b3 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]
def str (s : String) : ByteArray := s.toUTF8
def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)
def get8 (b : ByteArray) (i : Nat) : Nat := (b[i]?.getD 0).toNat
def get16 (b : ByteArray) (i : Nat) : Nat := get8 b i * 256 + get8 b (i + 1)
def get24 (b : ByteArray) (i : Nat) : Nat := get8 b i * 65536 + get16 b (i + 1)

def handshake (ty : Nat) (body : ByteArray) : ByteArray := b1 ty ++ b3 body.size ++ body
def record (ty : Nat) (body : ByteArray) : ByteArray := b1 ty ++ b2 0x0303 ++ b2 body.size ++ body

/-! ## The key schedule (RFC 8446 §7.1) -/

def expandLabel (secret : ByteArray) (label : String) (ctx : ByteArray) (len : Nat) : ByteArray :=
  let l := str ("tls13 " ++ label)
  hkdfExpand secret (b2 len ++ b1 l.size ++ l ++ b1 ctx.size ++ ctx) len

def deriveSecret (secret : ByteArray) (label : String) (msgs : ByteArray) : ByteArray :=
  expandLabel secret label (sha256 msgs) 32

def trafficKeys (secret : ByteArray) : Keys :=
  { key := expandLabel secret "key" .empty 32, iv := expandLabel secret "iv" .empty 12 }

def nonce (k : Keys) : ByteArray :=
  ByteArray.mk ((List.range 12).toArray.map fun i =>
    k.iv[i]! ^^^ (if i < 4 then 0 else UInt8.ofNat (k.seq >>> (8 * (11 - i)))))

/-- A protected record: `content || type`, sealed; the outer type is 23. -/
def protect (k : Keys) (ty : Nat) (content : ByteArray) : ByteArray × Keys :=
  let inner := content.push (UInt8.ofNat ty)
  let hdr := b1 23 ++ b2 0x0303 ++ b2 (inner.size + 16)
  (hdr ++ aeadSeal k.key (nonce k) hdr inner, { k with seq := k.seq + 1 })

/-- Open a protected record (its header and body): the content type and the content. -/
def unprotect (k : Keys) (hdr body : ByteArray) : Option (Nat × ByteArray × Keys) := do
  let inner ← aeadOpen k.key (nonce k) hdr body
  -- strip the zero padding; the last nonzero byte is the type
  let l := inner.toList.reverse.dropWhile (· == 0)
  match l with
  | [] => none
  | ty :: rest => some (ty.toNat, ByteArray.mk rest.reverse.toArray, { k with seq := k.seq + 1 })

/-! ## The ClientHello -/

structure Hello where
  random : ByteArray
  sid    : ByteArray
  share  : ByteArray
  /-- The signature algorithms offered: ed25519 (0x0807), ecdsa_secp256r1_sha256 (0x0403). -/
  ed     : Bool
  p256   : Bool

/-- The parts of a ClientHello this server needs, or `none` when it cannot be
served.  Every length is checked against what contains it (a field that
runs past its container, a session id over 32 bytes, a list of 2-byte
items — suites, versions, signature algorithms — of odd or zero length,
extensions that do not end where the message does): the Ember
program reads the same bytes this reads, and nothing beyond. -/
def parseHello (m : ByteArray) : Option Hello := do
  let size := m.size
  guard (size ≥ 4 && get8 m 0 == 1 && get24 m 1 + 4 == size)
  let mut i := 4 + 2
  guard (i + 32 ≤ size)
  let random := m.extract i (i + 32)
  i := i + 32
  guard (i + 1 ≤ size)
  let sl := get8 m i
  guard (sl ≤ 32 && i + 1 + sl ≤ size)
  let sid := m.extract (i + 1) (i + 1 + sl)
  i := i + 1 + sl
  guard (i + 2 ≤ size)
  let cl := get16 m i
  guard (cl % 2 == 0 && i + 2 + cl ≤ size)
  let suites := (List.range (cl / 2)).map fun k => get16 m (i + 2 + 2 * k)
  guard (suites.contains 0x1303)
  i := i + 2 + cl
  guard (i + 1 ≤ size)
  let ml := get8 m i
  guard (i + 1 + ml ≤ size)
  i := i + 1 + ml
  guard (i + 2 ≤ size)
  let el := get16 m i
  i := i + 2
  let stop := i + el
  guard (stop == size)
  let mut versions := false
  let mut sigOk := false
  let mut sigEd := false
  let mut sigP := false
  let mut share : Option ByteArray := none
  while i + 4 ≤ stop do
    let ty := get16 m i
    let len := get16 m (i + 2)
    guard (i + 4 + len ≤ stop)
    let d := m.extract (i + 4) (i + 4 + len)
    if ty == 43 then
      -- a list of 2-byte versions: its length even, at least one
      guard (len ≥ 1 && get8 d 0 + 1 == len && get8 d 0 % 2 == 0 && get8 d 0 ≥ 2)
      versions := (List.range (get8 d 0 / 2)).any fun k => get16 d (1 + 2 * k) == 0x0304
    if ty == 13 then
      -- a list of 2-byte algorithms: its length even, at least one
      guard (len ≥ 2 && get16 d 0 + 2 == len && get16 d 0 % 2 == 0 && get16 d 0 ≥ 2)
      sigOk := true
      sigEd := (List.range (get16 d 0 / 2)).any fun k => get16 d (2 + 2 * k) == 0x0807
      sigP := (List.range (get16 d 0 / 2)).any fun k => get16 d (2 + 2 * k) == 0x0403
    if ty == 51 then
      guard (len ≥ 2 && get16 d 0 + 2 == len)
      let mut j := 2
      while j + 4 ≤ len do
        let g := get16 d j
        let kl := get16 d (j + 2)
        guard (j + 4 + kl ≤ len)
        if g == 0x001d && kl == 32 then share := some (d.extract (j + 4) (j + 36))
        j := j + 4 + kl
      guard (j == len)
    i := i + 4 + len
  guard (i == stop && versions && sigOk)
  let s ← share
  return { random, sid, share := s, ed := sigEd, p256 := sigP }

/-! ## The server's flight -/

def certVerifyContent (th : ByteArray) : ByteArray :=
  ByteArray.mk (Array.replicate 64 0x20) ++ str "TLS 1.3, server CertificateVerify" ++ b1 0 ++ th

/-- A fatal alert, protected once there are keys, and the end of the connection. -/
def fail (c : Conn) (desc : Nat) : Conn :=
  if c.phase == .hello || c.tx.key.size == 0 then
    { c with out := c.out ++ record 21 (b1 2 ++ b1 desc), phase := .closed, done := true }
  else
    let (r, tx) := protect c.tx 21 (b1 2 ++ b1 desc)
    { c with out := c.out ++ r, tx, phase := .closed, done := true }

/-- Answer a ClientHello: the bytes to send and the connection after it. -/
def serverFlight (site : Site) (c : Conn) (chMsg : ByteArray) (h : Hello) : Conn :=
  let ent := site.entropy.getD .empty
  let srand := sha256 (site.seed ++ ent ++ str "server random" ++ h.random)
  let eph := sha256 (site.seed ++ ent ++ str "ecdhe" ++ h.random)
  let pub := x25519 eph basepoint9
  let shared := x25519 eph h.share
  -- Ed25519 when offered, else P-256 when offered and there is such a
  -- certificate; neither is handshake_failure, before anything else
  let useP := !h.ed && h.p256 && site.certP256.size > 0
  if !h.ed && !useP then fail c 40 else
  -- a share of small order gives zeros: RFC 8446 §7.4.2, abort with illegal_parameter
  if shared.toList.all (· == 0) then fail c 47 else
  let certBytes := if useP then site.certP256 else site.cert
  let exts := b2 43 ++ b2 2 ++ b2 0x0304 ++ b2 51 ++ b2 36 ++ b2 0x001d ++ b2 32 ++ pub
  let sh := handshake 2 (b2 0x0303 ++ srand ++ b1 h.sid.size ++ h.sid ++ b2 0x1303 ++ b1 0 ++ b2 exts.size ++ exts)
  let t1 := chMsg ++ sh
  let early := hkdfExtract (zeros 32) (zeros 32)
  let hsSecret := hkdfExtract (deriveSecret early "derived" .empty) shared
  let cHs := deriveSecret hsSecret "c hs traffic" t1
  let sHs := deriveSecret hsSecret "s hs traffic" t1
  let ee := handshake 8 (b2 0)
  let entry := b3 certBytes.size ++ certBytes ++ b2 0
  let cert := handshake 11 (b1 0 ++ b3 entry.size ++ entry)
  let t2 := t1 ++ ee ++ cert
  let sig := if useP then p256Sign site.keyP256 (certVerifyContent (sha256 t2))
    else edSign site.key (certVerifyContent (sha256 t2))
  let cv := handshake 15 (b2 (if useP then 0x0403 else 0x0807) ++ b2 sig.size ++ sig)
  let t3 := t2 ++ cv
  let sFin := handshake 20 (hmac256 (expandLabel sHs "finished" .empty 32) (sha256 t3))
  let t4 := t3 ++ sFin
  let master := hkdfExtract (deriveSecret hsSecret "derived" .empty) (zeros 32)
  let (encHs, _) := protect (trafficKeys sHs) 22 (ee ++ cert ++ cv ++ sFin)
  let flight := record 22 sh ++ record 20 (b1 1) ++ encHs
  { c with out := c.out ++ flight, phase := .finished, hs := t4,
           rx := trafficKeys cHs, cFin := expandLabel cHs "finished" .empty 32,
           cAp := deriveSecret master "c ap traffic" t4, sAp := deriveSecret master "s ap traffic" t4 }

/-- The HTTP response in records of at most `chunk` bytes, then `close_notify`. -/
def respond (site : Site) (c : Conn) (resp : ByteArray) : Conn := Id.run do
  let mut c := c
  let mut off := 0
  while off < resp.size do
    let n := min site.chunk (resp.size - off)
    let (r, tx) := protect c.tx 23 (resp.extract off (off + n))
    c := { c with out := c.out ++ r, tx }
    off := off + n
  let (r, tx) := protect c.tx 21 (b1 1 ++ b1 0)
  return { c with out := c.out ++ r, tx, phase := .closed, done := true }

/-- A response on a kept connection (plan M9.5): its records, no `close_notify`. -/
def respondKeep (site : Site) (c : Conn) (resp : ByteArray) : Conn := Id.run do
  let mut c := c
  let mut off := 0
  while off < resp.size do
    let n := min site.chunk (resp.size - off)
    let (r, tx) := protect c.tx 23 (resp.extract off (off + n))
    c := { c with out := c.out ++ r, tx }
    off := off + n
  return c

/-- Application data on a site with control routes or kept connections:
byte by byte, so that a request after a kept response, in the same record,
is the next one. -/
def appData (site : Site) (g : Http.Ctl) (c : Conn) (m : ByteArray) : Http.Ctl × Conn := Id.run do
  let mut g := g
  let mut c := c
  for b in m.toList do
    if c.phase == .closed then break
    let (g', hc) := Http.stepCtl site.http (g, c.http) b
    g := g'
    if hc.decided then
      if hc.closeAfter then c := respond site { c with http := hc } hc.resp
      else c := { respondKeep site c hc.resp with http := {} }
    else c := { c with http := hc }
  return (g, c)

/-- One whole record (`g`: the HTTP application's shared state, M9.5). -/
def onRecord (site : Site) (g : Http.Ctl) (c : Conn) (hdr body : ByteArray) : Http.Ctl × Conn :=
  let ty := get8 hdr 0
  match c.phase with
  | .closed => (g, c)
  | .hello =>
    if ty != 22 then (g, fail c 10) else
    match parseHello body with
    | some h => (g, serverFlight site c body h)
    | none => (g, fail c 40)
  | .finished =>
    if ty == 20 then (if body.toList == [1] then (g, c) else (g, fail c 10)) else
    if ty != 23 then (g, fail c 10) else
    match unprotect c.rx hdr body with
    | none => (g, fail c 20)
    | some (ity, m, _) =>
      let want := handshake 20 (hmac256 c.cFin (sha256 c.hs))
      if ity == 22 && m.toList == want.toList then
        (g, { c with phase := .app, rx := trafficKeys c.cAp, tx := trafficKeys c.sAp, hs := .empty })
      else (g, fail c 51)
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

/-- Take every whole record from `inb`. -/
partial def drain (site : Site) (g : Http.Ctl) (c : Conn) : Http.Ctl × Conn :=
  if c.inb.size < 5 || c.phase == .closed then (g, c) else
  let len := get16 c.inb 3
  if len > site.recMax then (g, fail { c with inb := .empty } 22) else
  if c.inb.size < 5 + len then (g, c) else
  let hdr := c.inb.extract 0 5
  let body := c.inb.extract 5 (5 + len)
  let (g, c) := onRecord site g { c with inb := c.inb.extract (5 + len) c.inb.size } hdr body
  drain site g c

def app (site : Site) : App where
  σ := Conn
  port := site.port
  init := {}
  room c cap := if c.phase == .closed then cap else min cap (site.recMax + 5 - c.inb.size)
  recv c d := if c.phase == .closed then c else (drain site {} { c with inb := c.inb ++ d }).2
  avail c := c.out.size
  bytes c off n := Bytes.slice c.out off n
  acked c n := { c with out := c.out.extract n c.out.size }
  close c := c.done
  idleClose := true
  reuseTimeWait := true
  G := Http.Ctl
  ginit := {}
  recvG g c d := if c.phase == .closed then (g, c) else drain site g { c with inb := c.inb ++ d }

def hexBytes (s : String) : ByteArray := Id.run do
  let v (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let cs := s.toList.toArray
  let mut b := ByteArray.empty
  for i in [0:cs.size / 2] do b := b.push (UInt8.ofNat (v cs[2 * i]! * 16 + v cs[2 * i + 1]!))
  return b

/-- A self-signed demo certificate for `ember.local` and its Ed25519 seed
(made with `openssl req -x509` once; a demo key, published here). -/
def demoCert : ByteArray := hexBytes
  "308201423081f5a0030201020214367e5974ad7e639d6cdff92c7a63aded72c3cda6300506032b657030163114301206035504030c0b656d6265722e6c6f63616c3020170d3236313130363034333335305a180f32313236313031333034333335305a30163114301206035504030c0b656d6265722e6c6f63616c302a300506032b6570032100eae9b4a7f9fa434d22015795c97893b8c764066f0ae1db4d72d77697fc62689ba3533051301d0603551d0e04160414d9043e5f700f398b6e38f36009830d9d2bd18117301f0603551d23041830168014d9043e5f700f398b6e38f36009830d9d2bd18117300f0603551d130101ff040530030101ff300506032b6570034100605ce169bef41143be1300e362c6803b30be5033729ac6a7c300d624b20fbac45f82fa8fa26351844d4be08dc1cc6a8afd90277d2ae11ec761bd9ffde928690f"

def demoKey : ByteArray := hexBytes "548be1fd94c375e3ac74f69b842a44817f2918b076d9e2d1059b5be52d4aac92"

/-- A self-signed demo certificate for `ember.local` (and 10.0.0.1) with a
P-256 key, and that key's private scalar (`openssl req -x509` once; a demo
key, published here). -/
def demoCertP256 : ByteArray := hexBytes
  "308201a130820147a00302010202142a7e65bc3b4797ca59a6e8d5d86df25fc454e5c5300a06082a8648ce3d04030230163114301206035504030c0b656d6265722e6c6f63616c3020170d3236313130363037353133395a180f32313236313031333037353133395a30163114301206035504030c0b656d6265722e6c6f63616c3059301306072a8648ce3d020106082a8648ce3d03010703420004a6b2980f6806e1c20c18baf70d5d40e5143dc84cf58e0b9e061b9e09c24f64747e3fdbe1bc1b1414692432f9c3800040af4abbd4e13b2eca10930ab7e2ac5f56a371306f301d0603551d0e041604145bc16637eb5cfec58502862563c8d7f39e8a6fc3301f0603551d230418301680145bc16637eb5cfec58502862563c8d7f39e8a6fc3300f0603551d130101ff040530030101ff301c0603551d1104153013820b656d6265722e6c6f63616c87040a000001300a06082a8648ce3d0403020348003045022041ffdfe99c92be23b2e844ab6b99ffe01c61f4792dd7ea61206627d94832de9f0221008afd3809aadafa29a78f515b9beeeae1b6c52c47f95748841a8db19646095254"

def demoKeyP256 : Nat := 0xfa0a49c1c8cfbd402e655dd050d28ec0721a5e16a8db9e8baf0a60702a542a75

def demo : Site where
  http := Http.demo
  cert := demoCert
  key := demoKey
  certP256 := demoCertP256
  keyP256 := demoKeyP256
  seed := str "ember demo seed: not for production"

/-- `demo` with the protected routes of `Http.demoAuth` (plan M9.3). -/
def demoAuth : Site := { demo with http := Http.demoAuth }

/-- `demo` with the control route and kept connections of `Http.demoCtl` (plan M9.5). -/
def demoCtl : Site := { demo with http := Http.demoCtl }

end Ember.Spec.Srv.Tls
