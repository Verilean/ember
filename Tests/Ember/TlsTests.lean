import Ember.Spec.Srv.Tls
import Tests.Ember.HttpTests
import Tests.Ember.CryptoTests

/-!
# `Ember.Spec.Srv.Tls` (plan M8.6)

* the key schedule against RFC 8448 §3 (the simple 1-RTT handshake):
  the trace there uses `TLS_AES_128_GCM_SHA256` and an RSA certificate,
  but its key schedule is SHA-256 and HKDF as here, so the early,
  handshake and master secrets, the handshake traffic secrets, the
  server's handshake key and IV (16 bytes there) and its finished key are
  checked; the record protection (AES-GCM there) and the signature (RSA)
  are not;
* ClientHellos built here, sent over TCP to the stack: a key share of
  small order (u = 0, 1, a point of order 8) gets only an
  `illegal_parameter` alert, a valid share a ServerHello; a ClientHello
  with a length that runs past what contains it, or short of it, gets
  only `handshake_failure`.
-/

namespace Ember.Tests.TlsTests
open Ember Ember.Spec Ember.Spec.Crypto Ember.Spec.Srv.Tls Ember.Trace
open Ember.Tests.CryptoTests (hex toHex)

def rfc8448 : List (String × ByteArray × String) :=
  let ch := hex "010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283024dece7000006130113031302010000910000000b0009000006736572766572ff01000100000a00140012001d0017001800190100010101020103010400230000003300260024001d002099381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c002b0003020304000d0020001e040305030603020308040805080604010501060102010402050206020202002d00020101001c00024001"
  let sh := hex "020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155772ed3e2692800130100002e00330024001d0020c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f002b00020304"
  let ikm := hex "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"
  let early := hkdfExtract (zeros 32) (zeros 32)
  let derived := deriveSecret early "derived" .empty
  let hs := hkdfExtract derived ikm
  let sHs := deriveSecret hs "s hs traffic" (ch ++ sh)
  let derived2 := deriveSecret hs "derived" .empty
  [("transcript hash CH..SH", sha256 (ch ++ sh), "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"),
   ("early secret", early, "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"),
   ("derived", derived, "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"),
   ("handshake secret", hs, "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"),
   ("c hs traffic", deriveSecret hs "c hs traffic" (ch ++ sh), "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"),
   ("s hs traffic", sHs, "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"),
   ("derived for master", derived2, "43de77e0c77713859a944db9db2590b53190a65b3ee2e4f12dd7a0bb7ce254b4"),
   ("master secret", hkdfExtract derived2 (zeros 32), "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"),
   ("server handshake key (16)", expandLabel sHs "key" .empty 16, "3fce516009c21727d0f2e4e86ee403bc"),
   ("server handshake iv", expandLabel sHs "iv" .empty 12, "5d313eb2671276ee13000b30"),
   ("server finished key", expandLabel sHs "finished" .empty 32, "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8")]

/-- A ClientHello this server accepts but for the key share. -/
def clientHello (share : ByteArray) (sigalg : Nat := 0x0807) : ByteArray :=
  let ext (ty : Nat) (d : ByteArray) := b2 ty ++ b2 d.size ++ d
  let exts := ext 43 (b1 2 ++ b2 0x0304) ++ ext 13 (b2 2 ++ b2 sigalg) ++ ext 10 (b2 2 ++ b2 0x001d) ++
    ext 51 (b2 (4 + share.size) ++ b2 0x001d ++ b2 share.size ++ share)
  let body := b2 0x0303 ++ ByteArray.mk (Array.replicate 32 7) ++ b1 0 ++ b2 2 ++ b2 0x1303 ++ b1 1 ++ b1 0 ++
    b2 exts.size ++ exts
  record 22 (handshake 1 body)

def lowOrder : List (String × ByteArray) :=
  [("u = 0", zeros 32), ("u = 1", natLe 1 32),
   ("order 8", hex "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800")]

/-! ## Malformed ClientHellos: every length is checked -/

def ext (ty : Nat) (d : ByteArray) : ByteArray := b2 ty ++ b2 d.size ++ d
def goodShare : ByteArray := x25519 (natLe 12345 32) basepoint9
def versionsExt : ByteArray := ext 43 (b1 2 ++ b2 0x0304)
def sigExt : ByteArray := ext 13 (b2 2 ++ b2 0x0807)
def shareExt : ByteArray := ext 51 (b2 36 ++ b2 0x001d ++ b2 32 ++ goodShare)

/-- A ClientHello from its parts, lengths given as they are to be declared. -/
def hello (sidLen : Nat) (sid : ByteArray) (suiteLen : Nat) (suites : ByteArray) (compLen : Nat) (comp : ByteArray)
    (extLen : Nat) (exts : ByteArray) (hsLen : Option Nat := none) : ByteArray :=
  let body := b2 0x0303 ++ ByteArray.mk (Array.replicate 32 7) ++ b1 sidLen ++ sid ++ b2 suiteLen ++ suites ++
    b1 compLen ++ comp ++ b2 extLen ++ exts
  record 22 (b1 1 ++ b3 (hsLen.getD body.size) ++ body)

def okExts : ByteArray := versionsExt ++ sigExt ++ shareExt

def std0 : ByteArray := hello 0 .empty 2 (b2 0x1303) 1 (b1 0) okExts.size okExts

/-- A ClientHello of exactly `recMax` (2048) bytes whose last extension is an
empty supported_versions: its data would start at the end of the record
(and of the Ember program's buffer of the connection). -/
def fullRecordEmptyVersions : ByteArray :=
  let tail := ext 43 .empty
  let fixed := 4 + 2 + 32 + 1 + 2 + 2 + 1 + 1 + 2 + (sigExt ++ shareExt).size + 4 + tail.size
  let pad := ext 21 (zeros (2048 - fixed))
  let exts := sigExt ++ shareExt ++ pad ++ tail
  hello 0 .empty 2 (b2 0x1303) 1 (b1 0) exts.size exts

/-- Each must be answered with `handshake_failure` alone. -/
def malformed : List (String × ByteArray) :=
  let suites := b2 0x1303
  let std (exts : ByteArray) (extLen : Nat) := hello 0 .empty 2 suites 1 (b1 0) extLen exts
  -- an extension after the good ones that declares more than it has: 10 declared, 4 there
  let overrun := okExts ++ b2 0xff01 ++ b2 10 ++ ByteArray.mk #[1, 2, 3, 4]
  [("well formed (control: not malformed)", .empty),
   ("a later extension longer than the message", std overrun overrun.size),
   ("extensions longer than declared", std okExts (okExts.size - 3)),
   ("extensions shorter than declared", std okExts (okExts.size + 5)),
   ("bytes after the last extension", std (okExts ++ ByteArray.mk #[0, 0]) (okExts.size + 2)),
   ("session id of 33 bytes", hello 33 (zeros 33) 2 suites 1 (b1 0) okExts.size okExts),
   ("session id past the message", hello 32 (zeros 4) 0 .empty 0 .empty 0 .empty),
   ("odd cipher suites", hello 0 .empty 3 (suites.push 0) 1 (b1 0) okExts.size okExts),
   ("cipher suites past the message", hello 0 .empty 200 suites 1 (b1 0) okExts.size okExts),
   ("compression past the message", hello 0 .empty 2 suites 200 (b1 0) okExts.size okExts),
   ("supported_versions with a wrong inner length",
      std (ext 43 (b1 4 ++ b2 0x0304) ++ sigExt ++ shareExt) (okExts.size + 0)),
   ("supported_versions of 3 bytes (a version and one byte more)",
      std (ext 43 (b1 3 ++ b2 0x0304 ++ b1 0) ++ sigExt ++ shareExt) (okExts.size + 1)),
   ("supported_versions empty", std (ext 43 (b1 0) ++ sigExt ++ shareExt) (okExts.size - 2)),
   ("signature_algorithms of 3 bytes (ed25519 and one byte more)",
      std (versionsExt ++ ext 13 (b2 3 ++ b2 0x0807 ++ b1 0) ++ shareExt) (okExts.size + 1)),
   ("signature_algorithms empty", std (versionsExt ++ ext 13 (b2 0) ++ shareExt) (okExts.size - 2)),
   ("signature_algorithms with a wrong inner length",
      std (versionsExt ++ ext 13 (b2 4 ++ b2 0x0807) ++ shareExt) okExts.size),
   ("key_share list with a wrong length",
      std (versionsExt ++ sigExt ++ ext 51 (b2 40 ++ b2 0x001d ++ b2 32 ++ goodShare)) okExts.size),
   ("key_share entry past its list",
      std (versionsExt ++ sigExt ++ ext 51 (b2 36 ++ b2 0x001d ++ b2 40 ++ goodShare)) okExts.size),
   ("handshake length wrong", hello 0 .empty 2 suites 1 (b1 0) okExts.size okExts (some 10)),
   ("a message of 3 bytes", record 22 (ByteArray.mk #[1, 0, 0])),
   ("an empty supported_versions at the very end of a full record", fullRecordEmptyVersions)]

/-- The sessions of the small-order shares and of a valid share, for the Ember checks. -/
def sessions : List (String × Array Input) :=
  let app := Srv.Tls.app Srv.Tls.demo
  (lowOrder.map fun (name, share) => (s!"low-order share {name}", (HttpTests.exchange app (clientHello share)).inputs)) ++
    [("valid share", (HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9))).inputs),
     ("an empty supported_versions at the end of a full record", (HttpTests.exchange app fullRecordEmptyVersions).inputs),
     ("P-256 only (ecdsa_secp256r1_sha256)",
       (HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9) 0x0403)).inputs),
     ("neither Ed25519 nor P-256 (rsa_pss_rsae_sha256)",
       (HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9) 0x0804)).inputs)]


def run : IO Nat := do
  let mut bad := 0
  for (name, got, want) in rfc8448 do
    if toHex got != want then
      bad := bad + 1
      IO.println s!"FAIL tls RFC 8448 {name}: {toHex got} want {want}"
  let app := Srv.Tls.app Srv.Tls.demo
  for (name, share) in lowOrder do
    let ex := HttpTests.exchange app (clientHello share)
    let alert := record 21 (b1 2 ++ b1 47)
    if ex.resp.toList != alert.toList || !ex.fin then
      bad := bad + 1
      IO.println s!"FAIL tls low-order share {name}: got {toHex ex.resp} (fin {ex.fin}), want only {toHex alert}"
  let good := HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9))
  -- the full record of the boundary case: 2048 bytes of body, as meant
  if fullRecordEmptyVersions.size != 5 + 2048 then
    bad := bad + 1
    IO.println s!"FAIL tls: the full-record case is {fullRecordEmptyVersions.size} bytes, not 5 + 2048"
  -- malformed ClientHellos: handshake_failure and nothing else; the well-formed control gets a ServerHello
  for (name, raw) in malformed do
    let raw := if raw.size == 0 then std0 else raw
    let ex := HttpTests.exchange app raw
    let alert := record 21 (b1 2 ++ b1 40)
    let isControl := name.startsWith "well formed"
    let ok := if isControl then ex.resp.size > 6 && ex.resp[0]! == 22 && ex.resp[5]! == 2
      else ex.resp.toList == alert.toList && ex.fin
    if !ok then
      bad := bad + 1
      IO.println s!"FAIL tls malformed ClientHello: {name}: got {toHex (ex.resp.extract 0 16)} (fin {ex.fin})"
  -- a client offering P-256 only gets the P-256 certificate; one offering neither, handshake_failure
  let pOnly := HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9) 0x0403)
  if pOnly.resp.size < 6 || pOnly.resp[0]! != 22 || pOnly.resp[5]! != 2 then
    bad := bad + 1
    IO.println s!"FAIL tls P-256 only: no ServerHello: {toHex (pOnly.resp.extract 0 16)}"
  let neither := HttpTests.exchange app (clientHello (x25519 (natLe 12345 32) basepoint9) 0x0804)
  if neither.resp.toList != (record 21 (b1 2 ++ b1 40)).toList then
    bad := bad + 1
    IO.println s!"FAIL tls neither signature: {toHex neither.resp}"
  -- a handshake record (22, 3 3) whose message is a ServerHello (2)
  if good.resp.size < 6 || (good.resp.extract 0 3).toList != [22, 3, 3] || good.resp[5]! != 2 then
    bad := bad + 1
    IO.println s!"FAIL tls valid share: the answer does not start with a ServerHello: {toHex (good.resp.extract 0 16)}"
  IO.println s!"tls: RFC 8448 key schedule ({rfc8448.length} values), small-order key shares answered with illegal_parameter ({lowOrder.length}), a valid share with a ServerHello, {malformed.length - 1} malformed ClientHellos with handshake_failure; {bad} failures"
  return bad

end Ember.Tests.TlsTests
