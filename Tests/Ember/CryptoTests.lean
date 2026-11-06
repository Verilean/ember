import Ember.Spec.Crypto.Curve25519
import Ember.Spec.Crypto.P256
import Ember.Util.Rand
import Ember.Net.Crypto.Test
import Ember.Tools.Cc

/-!
# The crypto reference against the RFCs' test vectors (plan M8.5a)

SHA-256 and SHA-512 (FIPS 180-2 examples), HMAC-SHA256 (RFC 4231),
HKDF-SHA256 (RFC 5869), ChaCha20, Poly1305 and their AEAD (RFC 8439),
X25519 (RFC 7748), Ed25519 (RFC 8032).
-/

namespace Ember.Tests.CryptoTests
open Ember Ember.Spec.Crypto

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def hex (s : String) : ByteArray := Id.run do
  let cs := (s.toList.filter (· != ' ')).toArray
  let mut b := ByteArray.empty
  for i in [0:cs.size / 2] do
    b := b.push (UInt8.ofNat (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!))
  return b

def toHex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let d (n : Nat) := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.mk [d (x.toNat / 16), d (x.toNat % 16)])

def str (s : String) : ByteArray := s.toUTF8

def range (a n : Nat) : ByteArray := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (a + i))

/-- Each case: a name, what is computed, the expected bytes (hex). -/
def cases : List (String × ByteArray × String) := [
  ("sha256 empty", sha256 .empty, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("sha256 abc", sha256 (str "abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
  ("sha256 448 bits", sha256 (str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
  ("sha256 million a", sha256 (ByteArray.mk (Array.replicate 1000000 97)),
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"),
  ("sha512 empty", sha512 .empty,
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
  ("sha512 abc", sha512 (str "abc"),
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
  ("sha512 896 bits", sha512 (str "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
    "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"),
  ("hmac 4231.1", hmac256 (ByteArray.mk (Array.replicate 20 0x0b)) (str "Hi There"),
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
  ("hmac 4231.2", hmac256 (str "Jefe") (str "what do ya want for nothing?"),
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
  ("hmac 4231.6 long key", hmac256 (ByteArray.mk (Array.replicate 131 0xaa)) (str "Test Using Larger Than Block-Size Key - Hash Key First"),
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
  ("hkdf 5869.1 prk", hkdfExtract (range 0 13) (ByteArray.mk (Array.replicate 22 0x0b)),
    "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"),
  ("hkdf 5869.1 okm", hkdfExpand (hex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5") (range 0xf0 10) 42,
    "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"),
  ("hkdf 5869.3 no salt", hkdfExpand (hkdfExtract .empty (ByteArray.mk (Array.replicate 22 0x0b))) .empty 42,
    "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"),
  ("chacha20 block 2.3.2", chachaBlock (range 0 32) 1 (hex "000000090000004a00000000"),
    "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"),
  ("chacha20 2.4.2", chacha20 (range 0 32) 1 (hex "000000000000004a00000000")
      (str "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."),
    "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"),
  ("poly1305 2.5.2", poly1305 (hex "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
      (str "Cryptographic Forum Research Group"),
    "a8061dc1305136c6c22b8baf0c0127a9"),
  ("aead 2.8.2", aeadSeal (range 0x80 32) (hex "070000004041424344454647") (hex "50515253c0c1c2c3c4c5c6c7")
      (str "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."),
    "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116" ++
    "1ae10b594f09e26a7e902ecbd0600691"),
  ("x25519 7748 5.2.1", x25519 (hex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
      (hex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"),
    "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"),
  ("x25519 7748 5.2.2", x25519 (hex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
      (hex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"),
    "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"),
  ("x25519 alice public", x25519 (hex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a") basepoint9,
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"),
  ("x25519 shared", x25519 (hex "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
      (hex "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"),
    "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"),
  ("ed25519 8032.1 public", edPublic (hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"),
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"),
  ("ed25519 8032.1 sign", edSign (hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60") .empty,
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
  ("ed25519 8032.2 sign", edSign (hex "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb") (hex "72"),
    "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00")]

/-! ## Against OpenSSL on random inputs (skipped without `openssl`) -/

def tmp : System.FilePath := ".lake/ember-crypto"

def openssl (args : Array String) : IO (Option ByteArray) := do
  try
    let r ← IO.Process.output { cmd := "openssl", args }
    if r.exitCode != 0 then return none
    return some (← IO.FS.readBinFile (tmp / "out.bin"))
  catch _ => return none

def haveOpenssl : IO Bool := do
  try return (← IO.Process.output { cmd := "openssl", args := #["version"] }).exitCode == 0
  catch _ => return false

/-- Raw X25519 / Ed25519 keys in DER (PKCS#8 private, SPKI public). -/
def derPriv (oid : UInt8) (k : ByteArray) : ByteArray := hex s!"302e020100300506032b65{toHex (ByteArray.mk #[oid])}04220420" ++ k
def derPub (oid : UInt8) (k : ByteArray) : ByteArray := hex s!"302a300506032b65{toHex (ByteArray.mk #[oid])}032100" ++ k

def againstOpenssl (count seed : Nat) : IO Nat := do
  if !(← haveOpenssl) then
    IO.println "crypto vs OpenSSL: no openssl, skipped"
    return 0
  IO.FS.createDirAll tmp
  let out := (tmp / "out.bin").toString
  let msgF := (tmp / "msg.bin").toString
  let mut bad := 0
  let mut k := 0
  let mut rng := Rng.ofSeed seed
  for i in [0:count] do
    let ((m, key, nonce, ctr, a, b), rng') := (do
      let n ← randNat 300
      return (← randBytes n, ← randBytes 32, ← randBytes 12, ← randNat 1000, ← randBytes 32, ← randBytes 32) : RandM _).run rng
    rng := rng'
    IO.FS.writeBinFile msgF m
    let mut rs : Array (String × ByteArray × Option ByteArray) := #[]
    rs := rs.push ("sha256", sha256 m, ← openssl #["dgst", "-sha256", "-binary", "-out", out, msgF])
    rs := rs.push ("sha512", (sha512 m), ← openssl #["dgst", "-sha512", "-binary", "-out", out, msgF])
    rs := rs.push ("hmac-sha256", hmac256 key m, ← openssl #["mac", "-digest", "SHA256", "-macopt", s!"hexkey:{toHex key}", "-binary", "-in", msgF, "-out", out, "HMAC"])
    rs := rs.push ("poly1305", (poly1305 key m), ← openssl #["mac", "-macopt", s!"hexkey:{toHex key}", "-binary", "-in", msgF, "-out", out, "Poly1305"])
    let iv := natLe ctr 4 ++ nonce
    rs := rs.push ("chacha20", (chacha20 key (UInt32.ofNat ctr) nonce m), ← openssl #["enc", "-chacha20", "-K", toHex key, "-iv", toHex iv, "-in", msgF, "-out", out])
    -- X25519: our scalar a with the peer's public key x25519 b 9
    let pubB := x25519 b basepoint9
    IO.FS.writeBinFile (tmp / "a.der") (derPriv 0x6e a)
    IO.FS.writeBinFile (tmp / "b.der") (derPub 0x6e pubB)
    let _ ← IO.Process.output { cmd := "openssl", args := #["pkey", "-inform", "DER", "-in", (tmp / "a.der").toString, "-out", (tmp / "a.pem").toString] }
    let _ ← IO.Process.output { cmd := "openssl", args := #["pkey", "-pubin", "-inform", "DER", "-in", (tmp / "b.der").toString, "-pubout", "-out", (tmp / "b.pem").toString] }
    rs := rs.push ("x25519", (x25519 a pubB), ← openssl #["pkeyutl", "-derive", "-inkey", (tmp / "a.pem").toString, "-peerkey", (tmp / "b.pem").toString, "-out", out])
    -- Ed25519: sign m with the seed a
    IO.FS.writeBinFile (tmp / "e.der") (derPriv 0x70 a)
    let _ ← IO.Process.output { cmd := "openssl", args := #["pkey", "-inform", "DER", "-in", (tmp / "e.der").toString, "-out", (tmp / "e.pem").toString] }
    rs := rs.push ("ed25519", (edSign a m), ← openssl #["pkeyutl", "-sign", "-rawin", "-inkey", (tmp / "e.pem").toString, "-in", msgF, "-out", out])
    for (what, mine, theirs) in rs do
      k := k + 1
      if theirs.map (·.toList) != some mine.toList then
        bad := bad + 1
        IO.println s!"FAIL crypto vs OpenSSL {what} #{i}: mine {toHex mine} openssl {(theirs.map toHex).getD "error"}"
  IO.println s!"crypto vs OpenSSL: {k} random cases (SHA-256, SHA-512, HMAC, Poly1305, ChaCha20, X25519, Ed25519), {bad} failures"
  return bad

/-! ## The Ember crypto (interpreter and host C) against the reference -/

def request (op : Nat) (data : ByteArray) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat op, UInt8.ofNat (data.size / 256), UInt8.ofNat (data.size % 256)] ++ data

/-- Requests with the answers the reference gives. -/
def emberCases (count seed : Nat) : Array (String × ByteArray × ByteArray) := Id.run do
  let mut out := #[]
  for m in [ByteArray.empty, str "abc", str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            ByteArray.mk (Array.replicate 55 97), ByteArray.mk (Array.replicate 56 97),
            ByteArray.mk (Array.replicate 64 97), ByteArray.mk (Array.replicate 1000 97)] do
    out := out.push (s!"sha256 {m.size} bytes", request 1 m, sha256 m)
  let mut rng := Rng.ofSeed seed
  for i in [0:count] do
    let ((m, kl, key, prk, l, info), rng') := (do
      let n ← randNat 400
      let kl ← randNat 100
      let l ← randNat 255
      let il ← randNat 200
      return (← randBytes n, kl, ← randBytes kl, ← randBytes 32, l, ← randBytes il) : RandM _).run rng
    let ((nonce, ctr, aad), rng') := (do
      let al ← randNat 40
      return (← randBytes 12, ← randNat 100000, ← randBytes al) : RandM _).run rng'
    out := out.push (s!"chacha20 random {i}", request 4 (prk ++ nonce ++ natLe ctr 4 ++ m), chacha20 prk (UInt32.ofNat ctr) nonce m)
    out := out.push (s!"poly1305 random {i}", request 5 (prk ++ m), poly1305 prk m)
    let sealed := aeadSeal prk nonce aad m
    let openReq (ct : ByteArray) := request 10 (prk ++ nonce ++ ByteArray.mk #[UInt8.ofNat (aad.size / 256), UInt8.ofNat (aad.size % 256)] ++ aad ++ ct)
    let openAns (ct : ByteArray) := match aeadOpen prk nonce aad ct with
      | some pt => ByteArray.mk #[1] ++ pt
      | none => ByteArray.mk #[0]
    out := out.push (s!"aead open random {i}", openReq sealed, openAns sealed)
    -- a changed byte of the cipher text, of the tag, of the AAD: rejected
    if m.size > 0 then
      let bad := sealed.set! (i % m.size) (sealed[i % m.size]! ^^^ 0x40)
      out := out.push (s!"aead open changed text {i}", openReq bad, openAns bad)
    let badTag := sealed.set! (sealed.size - 1 - i % 16) (sealed[sealed.size - 1 - i % 16]! ^^^ 1)
    out := out.push (s!"aead open changed tag {i}", openReq badTag, openAns badTag)
    let saltLen := i % 40
    let salt := ByteArray.mk ((List.range saltLen).toArray.map fun k => UInt8.ofNat (k * 7 + i))
    out := out.push (s!"hkdf-extract random {i} (salt {saltLen})",
      request 11 (ByteArray.mk #[UInt8.ofNat saltLen] ++ salt ++ m), hkdfExtract salt m)
    out := out.push (s!"aead random {i}", request 6 (prk ++ nonce ++ ByteArray.mk #[UInt8.ofNat (aad.size / 256), UInt8.ofNat (aad.size % 256)] ++ aad ++ m),
      aeadSeal prk nonce aad m)
    rng := rng'
    out := out.push (s!"sha256 random {i}", request 1 m, sha256 m)
    out := out.push (s!"hmac random {i} (key {kl})", request 2 (ByteArray.mk #[UInt8.ofNat kl] ++ key ++ m), hmac256 key m)
    out := out.push (s!"hkdf-expand random {i} ({l} bytes)", request 3 (prk ++ ByteArray.mk #[UInt8.ofNat l] ++ info),
      hkdfExpand prk info l)
  out := out.push ("hmac 4231.1", request 2 (ByteArray.mk #[20] ++ ByteArray.mk (Array.replicate 20 0x0b) ++ str "Hi There"),
    hmac256 (ByteArray.mk (Array.replicate 20 0x0b)) (str "Hi There"))
  -- salts at and beyond a block: 64 bytes go in as they are, longer ones are hashed first
  for sl in [63, 64, 65, 100, 200, 255] do
    let salt := ByteArray.mk ((List.range sl).toArray.map fun k => UInt8.ofNat (k * 13 + 1))
    let ikm := str "input keying material"
    out := out.push (s!"hkdf-extract salt {sl}", request 11 (ByteArray.mk #[UInt8.ofNat sl] ++ salt ++ ikm), hkdfExtract salt ikm)
  out := out.push ("hkdf 5869.1 prk", request 11 (ByteArray.mk #[13] ++ range 0 13 ++ ByteArray.mk (Array.replicate 22 0x0b)),
    hex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5")
  out := out.push ("hkdf 5869.1 okm", request 3 (hex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5" ++
      ByteArray.mk #[42] ++ range 0xf0 10), hex "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
  -- X25519: the RFC 7748 vectors, the key exchange, u values at and above p, and random ones
  out := out.push ("x25519 7748 5.2.1", request 7 (hex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4" ++
      hex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"),
    hex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
  out := out.push ("x25519 7748 5.2.2", request 7 (hex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d" ++
      hex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"),
    hex "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957")
  out := out.push ("x25519 shared", request 7 (hex "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb" ++
      hex "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"),
    hex "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
  for (nm, u) in [("u = p", natLe p25519 32), ("u = p + 1", natLe (p25519 + 1) 32), ("u = 2^255 - 1", natLe (2 ^ 255 - 1) 32),
                  ("u = 0", natLe 0 32), ("u = 1", natLe 1 32), ("u all ones", ByteArray.mk (Array.replicate 32 0xff))] do
    let k := hex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
    out := out.push (s!"x25519 {nm}", request 7 (k ++ u), x25519 k u)
  let mut rng2 := Rng.ofSeed (seed + 7)
  for i in [0:12] do
    let ((k, u), r') := (do return (← randBytes 32, ← randBytes 32) : RandM _).run rng2
    rng2 := r'
    out := out.push (s!"x25519 random {i}", request 7 (k ++ u), x25519 k u)
  -- Ed25519: the RFC 8032 vectors and random seeds and messages; reduction mod L at its edges
  out := out.push ("ed25519 8032.1", request 8 (hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"),
    hex "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
  out := out.push ("ed25519 8032.2", request 8 (hex "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb" ++ hex "72"),
    hex "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00")
  for i in [0:6] do
    let ((sk, m), r') := (do let n ← randNat 300; return (← randBytes 32, ← randBytes n) : RandM _).run rng2
    rng2 := r'
    out := out.push (s!"ed25519 random {i}", request 8 (sk ++ m), edSign sk m)
  for (nm, v) in [("0", 0), ("L - 1", edQ - 1), ("L", edQ), ("L + 1", edQ + 1), ("2^512 - 1", 2 ^ 512 - 1), ("L^2", edQ * edQ)] do
    out := out.push (s!"mod L {nm}", request 9 (natLe v 64), natLe (v % edQ) 32)
  for i in [0:10] do
    let (b, r') := (randBytes 64 : RandM _).run rng2
    rng2 := r'
    out := out.push (s!"mod L random {i}", request 9 b, natLe (leNat b % edQ) 32)
  -- P-256: RFC 6979 A.2.5 and random keys and messages
  let d6979 := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  for m in [str "sample", str "test"] do
    out := out.push (s!"p256 RFC 6979 {String.fromUTF8! m}", request 12 (natBe d6979 32 ++ m), p256Sign d6979 m)
  for i in [0:4] do
    let ((kb, m), r') := (do let n ← randNat 200; return (← randBytes 32, ← randBytes n) : RandM _).run rng2
    rng2 := r'
    let d := beNat kb % (n256 - 1) + 1
    out := out.push (s!"p256 random {i}", request 12 (natBe d 32 ++ m), p256Sign d m)
  out := out.push ("chacha20 2.4.2", request 4 (range 0 32 ++ hex "000000000000004a00000000" ++ natLe 1 4 ++
      str "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."),
    chacha20 (range 0 32) 1 (hex "000000000000004a00000000")
      (str "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."))
  out := out.push ("poly1305 2.5.2", request 5 (hex "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b" ++
      str "Cryptographic Forum Research Group"), hex "a8061dc1305136c6c22b8baf0c0127a9")
  -- Poly1305 edge: a key whose r is all ones in its allowed bits, and h near p
  out := out.push ("poly1305 high", request 5 (ByteArray.mk (Array.replicate 32 0xff) ++ ByteArray.mk (Array.replicate 64 0xff)),
    poly1305 (ByteArray.mk (Array.replicate 32 0xff)) (ByteArray.mk (Array.replicate 64 0xff)))
  return out

def emberProg : Ember.Lang.Prog := match Net.Crypto.testProg.check with
  | .ok p => p
  | .error _ => Net.Crypto.testProg

def txs (t : Ember.Trace.Trace) : List ByteArray :=
  t.lines.toList.filterMap fun l => match l.ev with | .tx b => some b | _ => none

def emberRun : IO Nat := do
  match Net.Crypto.testProg.check with
  | .error e => IO.println s!"FAIL ember crypto: the program does not check: {repr e}"; return 1
  | .ok _ => pure ()
  let cs := emberCases 40 21
  let input := cs.foldl (fun acc (_, r, _) => acc ++ r) ByteArray.empty
  let ins : Array Ember.Trace.Input := #[.rx input]
  let r := Ember.Lang.runMachine (Ember.Lang.Machine.init emberProg ins) {} (fuel := 100000000)
  let mut bad := 0
  if let some e := r.error then
    IO.println s!"FAIL ember crypto interpreter: {repr e}"
    return 1
  let got := txs r.trace
  for ((name, _, want), g) in cs.toList.zip got do
    if g.toList != want.toList then
      bad := bad + 1
      IO.println s!"FAIL ember crypto interpreter {name}: {toHex g} want {toHex want}"
  if got.length != cs.size then
    bad := bad + 1
    IO.println s!"FAIL ember crypto interpreter: {got.length} answers for {cs.size} requests"
  IO.println s!"ember crypto (interpreter): {cs.size} requests (SHA-256, HMAC, HKDF-Expand, ChaCha20, Poly1305, AEAD, X25519, Ed25519, mod L, AEAD open, HKDF-Extract, P-256), = reference, {bad} failures"
  -- the emitted C
  if !(← Tools.Cc.available) then
    IO.println "ember crypto (host C): no C compiler, skipped"
    return bad
  let c ← match Tools.Cc.emit "crypto" emberProg with
    | .error e => IO.println s!"FAIL ember crypto: emit: {e}"; return bad + 1
    | .ok c => pure c
  let exe ← match ← Tools.Cc.build { dir := ".lake/ember-crypto-c", flags := #["-O2", "-fsanitize=undefined,address",
      "-fno-sanitize-recover=all"] } [("crypto", c)] with
    | .error e => IO.println s!"FAIL ember crypto: build: {e}"; return bad + 1
    | .ok exe => pure exe
  let f : System.FilePath := ".lake/ember-crypto-c/inputs.trace"
  Tools.Cc.writeInputs f {} ins
  let (t, rc) ← Tools.Cc.run exe 0 f
  let gotC := txs t
  let mut badC := 0
  for ((name, _, want), g) in cs.toList.zip gotC do
    if g.toList != want.toList then
      badC := badC + 1
      IO.println s!"FAIL ember crypto host C {name}: {toHex g} want {toHex want}"
  if rc != 0 || gotC.length != cs.size then
    badC := badC + 1
    IO.println s!"FAIL ember crypto host C: exit {rc}, {gotC.length} answers for {cs.size} requests"
  IO.println s!"ember crypto (host C, -O2, UBSan/ASan): {cs.size} requests, = reference, {badC} failures"
  return bad + badC

/-- `EMBER_CRYPTO_DUMP=DIR`: the requests with the reference's answers as
fixtures (20 requests each), for the replay on the ESP32-C3 image
`crypto-test` (`qemu-test.sh`). -/
def dump (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let cs := emberCases 40 21
  let groups := (List.range ((cs.size + 19) / 20)).map fun g => cs.extract (20 * g) (20 * g + 20)
  let mut i := 0
  for grp in groups do
    let input := grp.foldl (fun acc (_, r, _) => acc ++ r) ByteArray.empty
    let evs : List Ember.Trace.Event := grp.toList.map fun (_, _, a) => .tx a
    let t := Ember.Trace.Trace.ofSteps { profile := "rv32" } #[(.rx input, evs)]
    let lines := t.print.splitOn "\n"
    IO.FS.writeFile (dir / s!"crypto-{i}.trace")
      (lines.head! ++ s!"\n# crypto requests {20 * i}..: answers of Ember.Spec.Crypto\n" ++ "\n".intercalate lines.tail!)
    i := i + 1
  IO.println s!"crypto: {cs.size} requests in {i} fixtures written to {dir}"

/-! ## P-256 ECDSA against RFC 6979 A.2.5 and OpenSSL (plan M8.8) -/

def p256Cases : List (String × Bool) :=
  let d := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  let pub := p256Public d
  let (r1, s1) := p256SignRS d (str "sample")
  let (r2, s2) := p256SignRS d (str "test")
  [("p256 public key (RFC 6979 A.2.5)", toHex pub ==
      "04" ++ "60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6" ++
      "7903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299"),
   ("p256 nonce for sample", (rfc6979 d (sha256 (str "sample")) 1).head? ==
      some 0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60),
   ("p256 sign sample", (r1, s1) == (0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716,
      0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8)),
   ("p256 sign test", (r2, s2) == (0xF1ABB023518351CD71D881567B1EA663ED3EFCF6C5132B354F28D3B0B7D38367,
      0x019F4113742A2B14BD25926B49C649155F267E60D3814B4C0CC84250E46F0083)),
   ("p256 verify", p256Verify pub (str "sample") r1 s1),
   ("p256 verify rejects another message", !p256Verify pub (str "samplf") r1 s1),
   ("p256 verify rejects s + 1", !p256Verify pub (str "sample") r1 (s1 + 1)),
   -- the complete projective ladder (the Ember form) = the affine reference
   ("p256 complete ladder", [1, 2, 3, d, n256 - 1, n256 - 2, 2 ^ 255 + 12345, 0xdeadbeef].all fun k =>
      ppMulG k == ptMul k (some g256)),
   ("p256 complete ladder of n is the point at infinity", ppMulG n256 == none)]

/-- Signatures of random messages under random keys, verified by OpenSSL
(`openssl pkeyutl -verify` with the DER signature). -/
def p256Openssl (count seed : Nat) : IO Nat := do
  if !(← haveOpenssl) then
    IO.println "p256 vs OpenSSL: no openssl, skipped"
    return 0
  IO.FS.createDirAll tmp
  let mut bad := 0
  let mut rng := Rng.ofSeed seed
  for i in [0:count] do
    let ((kb, m), r') := (do let n ← randNat 200; return (← randBytes 32, ← randBytes n) : RandM _).run rng
    rng := r'
    let d := beNat kb % (n256 - 1) + 1
    let pub := p256Public d
    -- the public key as SubjectPublicKeyInfo (id-ecPublicKey, prime256v1)
    IO.FS.writeBinFile (tmp / "p.der") (hex "3059301306072a8648ce3d020106082a8648ce3d030107034200" ++ pub)
    IO.FS.writeBinFile (tmp / "m.bin") m
    IO.FS.writeBinFile (tmp / "s.der") (p256Sign d m)
    let _ ← IO.Process.output { cmd := "openssl", args := #["pkey", "-pubin", "-inform", "DER", "-in", (tmp / "p.der").toString, "-out", (tmp / "p.pem").toString] }
    let r ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-verify", (tmp / "p.pem").toString,
      "-signature", (tmp / "s.der").toString, (tmp / "m.bin").toString] }
    if r.exitCode != 0 then
      bad := bad + 1
      IO.println s!"FAIL p256 vs OpenSSL #{i}: {r.stdout}{r.stderr}"
  IO.println s!"p256 vs OpenSSL: {count} random signatures verified by openssl, {bad} failures"
  return bad

def run : IO Nat := do
  let mut bad := 0
  for (name, got, want) in cases do
    if toHex got != want then
      bad := bad + 1
      IO.println s!"FAIL crypto {name}\n  got  {toHex got}\n  want {want}"
  -- verification and rejection
  let pk := hex "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
  let pk1 := hex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let sig1 := hex "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
  let sig := hex "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"
  let checks := [("ed25519 verify", edVerify pk (hex "72") sig),
                 ("ed25519 rejects another message", !edVerify pk (hex "73") sig),
                 ("ed25519 rejects a changed R", !edVerify pk (hex "72") (sig.set! 0 (sig[0]! ^^^ 1))),
                 ("ed25519 rejects a changed S", !edVerify pk (hex "72") (sig.set! 40 (sig[40]! ^^^ 1))),
                 ("ed25519 rejects S + L", !edVerify pk (hex "72")
                    (sig.extract 0 32 ++ natLe ((leNat (sig.extract 32 64) + edQ) % 2 ^ 256) 32)),
                 ("ed25519 rejects another public key", !edVerify pk1 (hex "72") sig),
                 ("ed25519 rejects a signature of another key", !edVerify pk1 .empty sig),
                 ("ed25519 rejects zeros", !edVerify pk (hex "72") (ByteArray.mk (Array.replicate 64 0))),
                 ("ed25519 rejects R not on the curve", !edVerify pk (hex "72")
                    (natLe (p25519 + 1) 32 ++ sig.extract 32 64)),
                 ("ed25519 rejects a public key not on the curve", !edVerify (natLe (p25519 + 1) 32) (hex "72") sig),
                 ("ed25519 test 1 verifies", edVerify pk1 .empty sig1),
                 ("ed25519 test 1 rejects test 2's message", !edVerify pk1 (hex "72") sig1),
                 -- edEqual on points whose cross products differ by more than p:
                 -- 2/(p-1) = -2 and (p-1)/1 = -1 differ, y is 1 in both
                 ("edEqual: different points", !edEqual { x := 2, y := p25519 - 1, z := p25519 - 1, t := 0 }
                    { x := p25519 - 1, y := 1, z := 1, t := 0 }),
                 ("edEqual: the same point, scaled", edEqual { x := 2, y := 3, z := 1, t := 0 } { x := 4, y := 6, z := 2, t := 0 }),
                 ("aead opens", (aeadOpen (range 0x80 32) (hex "070000004041424344454647") (hex "50515253c0c1c2c3c4c5c6c7")
                     (aeadSeal (range 0x80 32) (hex "070000004041424344454647") (hex "50515253c0c1c2c3c4c5c6c7") (str "hello"))).map (·.toList) == some (str "hello").toList),
                 ("aead rejects a changed tag", (aeadOpen (range 0x80 32) (hex "070000004041424344454647") .empty
                     ((aeadSeal (range 0x80 32) (hex "070000004041424344454647") .empty (str "hello")).set! 5 0)).isNone)]
  for (name, ok) in checks do
    if !ok then
      bad := bad + 1
      IO.println s!"FAIL crypto {name}"
  bad := bad + (← againstOpenssl 30 11)
  for (name, ok) in p256Cases do
    if !ok then
      bad := bad + 1
      IO.println s!"FAIL crypto {name}"
  bad := bad + (← p256Openssl 12 13)
  bad := bad + (← emberRun)
  IO.println s!"crypto: {cases.length + checks.length} RFC vectors and checks (SHA-256/512, HMAC, HKDF, ChaCha20-Poly1305, X25519, Ed25519), {bad} failures"
  return bad

end Ember.Tests.CryptoTests
