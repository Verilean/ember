import Ember.Spec.Srv.Http
import Tests.Ember.CryptoTests

/-!
# OIDC access tokens: the reference check (plan M9.1)

base64url (strict), the JSON scanner, the ES256 signature of RFC 7515
A.3, the claims, and the answers of a protected route.  Tokens are made
by `Auth.sign` (RFC 6979) and, when `openssl` is there, by OpenSSL — and
OpenSSL checks ours.
-/

namespace Ember.Tests.AuthTests
open Ember Ember.Spec.Crypto Ember.Spec.Srv
open Ember.Tests.CryptoTests (hex toHex openssl haveOpenssl tmp)

def str (s : String) : ByteArray := s.toUTF8
def bs (s : String) : List UInt8 := s.toUTF8.toList

/-! ## RFC 7515 A.3 -/

def a3Header := "eyJhbGciOiJFUzI1NiJ9"
def a3Payload := "eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"
def a3Sig := "DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
def a3Pub : ByteArray :=
  ByteArray.mk #[4] ++ ((Auth.b64urlDecode (bs "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU")).getD .empty)
    ++ ((Auth.b64urlDecode (bs "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0")).getD .empty)
def a3D : Nat := beNat ((Auth.b64urlDecode (bs "jpsQnnGQmL-YBIffH1136cspYG6-0iY7X1fCE9-E9LI")).getD .empty)
def a3Token : ByteArray := str s!"{a3Header}.{a3Payload}.{a3Sig}"

def a3Cfg (aud : String) : Auth.Cfg := { keys := [{ kid := "a3", pub := a3Pub }], iss := "joe", aud }

/-! ## Our test keys -/

def d1 : Nat := 0x1b6e4c7d0f2a3958ac7e61d4b05f2390c8e7a6d5f40312e9b8c7d6a5f4e3d2c1
def d2 : Nat := 0x2c7f5d8e1a3b4069bd8f72e5c1603401d9f8b7e6051423fac9d8e7b6a5f4e3d2
def k1 : Auth.Key := { kid := "k1", pub := p256Public d1 }
def k2 : Auth.Key := { kid := "k2", pub := p256Public d2 }
def iss := "https://idp.example"
def aud := "ember-drone"
def now : Nat := 1_800_000_000
def cfg : Auth.Cfg := { keys := [k1, k2], iss, aud }
def cfg1 : Auth.Cfg := { keys := [k1], iss, aud }

def hdr1 := "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"k1\"}"
def claims (extra : String := "") (exp : String := s!"{now + 300}") : String :=
  s!"\{\"iss\":\"{iss}\",\"aud\":\"{aud}\",\"exp\":{exp},\"sub\":\"pilot\"{extra}}"
def good := Auth.sign d1 hdr1 (claims ",\"scope\":\"drone:control camera:read\"")

/-- A token with its last signature character changed. -/
def flipLast (t : ByteArray) : ByteArray :=
  let l := t.toList
  ByteArray.mk (l.dropLast ++ [if l.getLast? == some 65 then 66 else 65]).toArray

/-- Each case: a name, the configuration, the token, the scopes it must
grant (`none`: refused). -/
def checks : List (String × Auth.Cfg × ByteArray × Option (List String)) := [
  ("good", cfg, good, some ["drone:control", "camera:read"]),
  ("no scope claim", cfg, Auth.sign d1 hdr1 (claims), some []),
  ("scope with spaces around", cfg, Auth.sign d1 hdr1 (claims ",\"scope\":\"  a  b \""), some ["a", "b"]),
  ("no kid, one key", cfg1, Auth.sign d1 "{\"alg\":\"ES256\"}" (claims), some []),
  ("no kid, two keys", cfg, Auth.sign d1 "{\"alg\":\"ES256\"}" (claims), none),
  ("kid k2, key 2", cfg, Auth.sign d2 "{\"alg\":\"ES256\",\"kid\":\"k2\"}" (claims), some []),
  ("kid k1, signed by key 2", cfg, Auth.sign d2 hdr1 (claims), none),
  ("unknown kid", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":\"k9\"}" (claims), none),
  ("kid not a string", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":1}" (claims), none),
  ("alg none", cfg, Auth.sign d1 "{\"alg\":\"none\",\"kid\":\"k1\"}" (claims), none),
  ("alg HS256", cfg, Auth.sign d1 "{\"alg\":\"HS256\",\"kid\":\"k1\"}" (claims), none),
  ("alg RS256", cfg, Auth.sign d1 "{\"alg\":\"RS256\",\"kid\":\"k1\"}" (claims), none),
  ("alg es256", cfg, Auth.sign d1 "{\"alg\":\"es256\",\"kid\":\"k1\"}" (claims), none),
  ("alg missing", cfg, Auth.sign d1 "{\"kid\":\"k1\"}" (claims), none),
  ("alg twice", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"alg\":\"none\",\"kid\":\"k1\"}" (claims), none),
  ("crit", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":\"k1\",\"crit\":[\"x\"],\"x\":1}" (claims), none),
  ("signature altered", cfg, flipLast good, none),
  ("unsigned (two parts)", cfg, ByteArray.mk ((good.toList.reverse.dropWhile (· != 46)).reverse.dropLast.toArray), none),
  ("empty signature", cfg, ByteArray.mk ((good.toList.reverse.dropWhile (· != 46)).reverse.toArray), none),
  ("four parts", cfg, good ++ str ".AA", none),
  ("padding", cfg, good ++ str "=", none),
  ("wrong iss", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"https://evil\",\"aud\":\"{aud}\",\"exp\":{now + 300}}", none),
  ("iss missing", cfg, Auth.sign d1 hdr1 s!"\{\"aud\":\"{aud}\",\"exp\":{now + 300}}", none),
  ("iss with \\/ escapes", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"https:\\/\\/idp.example\",\"aud\":\"{aud}\",\"exp\":{now + 300}}", some []),
  ("iss with a \\u escape", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"https://idp.exampl\\u0065\",\"aud\":\"{aud}\",\"exp\":{now + 300}}", none),
  ("iss twice", cfg, Auth.sign d1 hdr1 (claims s!",\"iss\":\"{iss}\""), none),
  ("wrong aud", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":\"other\",\"exp\":{now + 300}}", none),
  ("aud array with ours", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[\"other\",\"{aud}\"],\"exp\":{now + 300}}", some []),
  ("aud array without ours", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[\"other\"],\"exp\":{now + 300}}", none),
  ("aud array with a number", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[\"{aud}\",1],\"exp\":{now + 300}}", none),
  ("aud missing", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"exp\":{now + 300}}", none),
  ("exp missing", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":\"{aud}\"}", none),
  ("exp passed", cfg, Auth.sign d1 hdr1 (claims (exp := s!"{now - 60}")), none),
  ("exp within the skew", cfg, Auth.sign d1 hdr1 (claims (exp := s!"{now - 59}")), some []),
  ("exp a string", cfg, Auth.sign d1 hdr1 (claims (exp := s!"\"{now + 300}\"")), none),
  ("exp a fraction", cfg, Auth.sign d1 hdr1 (claims (exp := s!"{now + 300}.5")), none),
  ("exp with an exponent", cfg, Auth.sign d1 hdr1 (claims (exp := "1.8e9")), none),
  ("exp negative", cfg, Auth.sign d1 hdr1 (claims (exp := "-1")), none),
  ("exp of 13 digits", cfg, Auth.sign d1 hdr1 (claims (exp := "1000000000000")), none),
  ("exp with a leading zero", cfg, Auth.sign d1 hdr1 (claims (exp := s!"0{now + 300}")), none),
  ("nbf in the future", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":{now + 61}"), none),
  ("nbf within the skew", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":{now + 60}"), some []),
  ("nbf a string", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":\"0\""), none),
  ("nbf behind an escape", cfg, Auth.sign d1 hdr1 (claims s!",\"n\\u0062f\":{now + 999}"), none),
  ("scope not a string", cfg, Auth.sign d1 hdr1 (claims ",\"scope\":[\"a\"]"), none),
  ("nested claims skipped", cfg,
    Auth.sign d1 hdr1 (claims ",\"realm_access\":{\"roles\":[\"a\",{\"b\":[null,true,false,-1.5e+3]}]},\"scope\":\"x\""), some ["x"]),
  ("nested key named exp", cfg, Auth.sign d1 hdr1 (claims ",\"o\":{\"exp\":1}"), some []),
  ("white space everywhere", cfg,
    Auth.sign d1 " { \"alg\" : \"ES256\" ,\t\"kid\":\"k1\" } \r\n" s!"\n\{ \"iss\" : \"{iss}\" , \"aud\" : \"{aud}\" , \"exp\" : {now + 300} }\n", some []),
  ("trailing garbage", cfg, Auth.sign d1 hdr1 (claims ++ "x"), none),
  ("two objects", cfg, Auth.sign d1 hdr1 (claims ++ "{}"), none),
  ("aud array with ours and a trailing comma", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[\"{aud}\",],\"exp\":{now + 300}}", none),
  ("aud array with ours, a trailing comma and white space", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[\"{aud}\" , ],\"exp\":{now + 300}}", none),
  ("aud array of a comma", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[,],\"exp\":{now + 300}}", none),
  ("aud array empty", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":[],\"exp\":{now + 300}}", none),
  ("nested array with a trailing comma", cfg, Auth.sign d1 hdr1 (claims ",\"x\":[1,2,]"), none),
  ("nested object with a trailing comma", cfg, Auth.sign d1 hdr1 (claims ",\"x\":{\"a\":1,}"), none),
  ("two commas in an array", cfg, Auth.sign d1 hdr1 (claims ",\"x\":[1,,2]"), none),
  ("trailing comma", cfg, Auth.sign d1 hdr1 s!"\{\"iss\":\"{iss}\",\"aud\":\"{aud}\",\"exp\":{now + 300},}", none),
  ("control character in a string", cfg, Auth.sign d1 hdr1 (claims ",\"x\":\"a\tb\""), none),
  ("bad escape", cfg, Auth.sign d1 hdr1 (claims ",\"x\":\"a\\qb\""), none),
  ("short \\u escape", cfg, Auth.sign d1 hdr1 (claims ",\"x\":\"\\u12\""), none),
  ("depth 16", cfg, Auth.sign d1 hdr1 (claims s!",\"x\":{String.join (List.replicate 15 "[")}{String.join (List.replicate 15 "]")}"), some []),
  ("depth 17", cfg, Auth.sign d1 hdr1 (claims s!",\"x\":{String.join (List.replicate 16 "[")}{String.join (List.replicate 16 "]")}"), none),
  ("RFC 7515 A.3, no aud", a3Cfg "x", a3Token, none),
  -- each key the check reads, twice (`Auth.field` gives `none`, which `←` turns into a refusal)
  ("crit twice, unsupported", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":\"k1\",\"crit\":[\"exp2\"],\"crit\":[\"exp2\"],\"exp2\":1}" (claims), none),
  ("crit twice, empty and unsupported", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":\"k1\",\"crit\":[],\"crit\":[\"b64\"],\"b64\":false}" (claims), none),
  ("kid twice", cfg, Auth.sign d1 "{\"alg\":\"ES256\",\"kid\":\"k1\",\"kid\":\"k1\"}" (claims), none),
  ("nbf twice, past then future", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":{now - 100},\"nbf\":{now + 999}"), none),
  ("nbf twice, future then past", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":{now + 999},\"nbf\":{now - 100}"), none),
  ("nbf twice, both past", cfg, Auth.sign d1 hdr1 (claims s!",\"nbf\":{now - 100},\"nbf\":{now - 100}"), none),
  ("exp twice", cfg, Auth.sign d1 hdr1 (claims s!",\"exp\":{now - 100}"), none),
  ("aud twice", cfg, Auth.sign d1 hdr1 (claims s!",\"aud\":\"{aud}\""), none),
  ("scope twice", cfg, Auth.sign d1 hdr1 (claims ",\"scope\":\"a\",\"scope\":\"b\""), none),
  ("a claim the check does not read, twice", cfg, Auth.sign d1 hdr1 (claims ",\"jti\":\"a\",\"jti\":\"b\""), some [])
]

def b64Cases : List (String × Option (List UInt8)) := [
  ("", some []), ("AA", some [0]), ("AAA", some [0, 0]), ("AAAA", some [0, 0, 0]),
  ("A", none), ("AB", none), ("AAB", none), ("AA==", none), ("A+A/", none), ("_-8", some [0xff, 0xef]),
  ("eyJhbGciOiJFUzI1NiJ9", some (bs "{\"alg\":\"ES256\"}"))
]

/-! ## A protected route -/

def site : Http.Site :=
  { Http.demo with
    routes := Http.demo.routes ++
      [{ path := "/status", ctype := "application/json", body := str "{\"battery\":87}\n", scope := some "" },
       { path := "/control", ctype := "text/plain", body := str "ok\n", scope := some "drone:control" },
       { path := "/camera", ctype := "text/plain", body := str "frame\n", scope := some "camera:read" }]
    auth := some cfg, now := some now }

def statusLine (b : ByteArray) : String :=
  String.fromUTF8! (ByteArray.mk (b.toList.takeWhile (· != 13)).toArray)

def hasField (b : ByteArray) (f : String) : Bool :=
  let s := String.fromUTF8! b
  (s.splitOn ("\r\n" ++ f ++ "\r\n")).length > 1

def get (path : String) (fields : List String) : ByteArray :=
  str (s!"GET {path} HTTP/1.1\r\nHost: ember\r\n" ++ String.join (fields.map (· ++ "\r\n")) ++ "\r\n")

def tok (t : ByteArray) : String := String.fromUTF8! t
def withScope (s : String) := tok (Auth.sign d1 hdr1 (claims s!",\"scope\":\"{s}\""))

/-- Each case: a name, the site, the request, the status line and a field the answer must have. -/
def routes : List (String × Http.Site × ByteArray × String × String) := [
  ("public route, no token", site, get "/hello.txt" [], "HTTP/1.1 200 OK", "Connection: close"),
  ("public route, bad token", site, get "/hello.txt" ["Authorization: Bearer x", "Authorization: y"], "HTTP/1.1 200 OK", "Connection: close"),
  ("no token", site, get "/status" [], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\""),
  ("Basic", site, get "/status" ["Authorization: Basic dXNlcjpwYXNz"], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\""),
  ("good token", site, get "/status" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 200 OK", "Connection: close"),
  ("scheme and name in other case", site, get "/status" [s!"aUTHORIZATION:  bEARER   {tok good}  \t"], "HTTP/1.1 200 OK", "Connection: close"),
  ("two Authorization fields", site, get "/status" [s!"Authorization: Bearer {tok good}", s!"Authorization: Bearer {tok good}"], "HTTP/1.1 400 Bad Request", "Connection: close"),
  ("space inside the token", site, get "/status" [s!"Authorization: Bearer {tok good} x"], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\", error=\"invalid_token\""),
  ("empty token", site, get "/status" ["Authorization: Bearer"], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\", error=\"invalid_token\""),
  ("altered token", site, get "/status" [s!"Authorization: Bearer {tok (flipLast good)}"], "HTTP/1.1 401 Unauthorized", "WWW-Authenticate: Bearer realm=\"ember\", error=\"invalid_token\""),
  ("control with its scope", site, get "/control" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 200 OK", "Connection: close"),
  ("control without its scope", site, get "/control" [s!"Authorization: Bearer {withScope "camera:read"}"], "HTTP/1.1 403 Forbidden",
    "WWW-Authenticate: Bearer realm=\"ember\", error=\"insufficient_scope\", scope=\"drone:control\""),
  ("a scope's prefix is not the scope", site, get "/control" [s!"Authorization: Bearer {withScope "drone:control2 drone"}"], "HTTP/1.1 403 Forbidden", "Connection: close"),
  ("camera with its scope", site, get "/camera" [s!"Authorization: Bearer {withScope "camera:read"}"], "HTTP/1.1 200 OK", "Connection: close"),
  ("time unknown", { site with now := none }, get "/status" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 503 Service Unavailable", "Connection: close"),
  ("no keys", { site with auth := none }, get "/status" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 503 Service Unavailable", "Connection: close"),
  ("expired by the clock", { site with now := some (now + 361) }, get "/status" [s!"Authorization: Bearer {tok good}"], "HTTP/1.1 401 Unauthorized", "Connection: close"),
  ("HEAD, no token", site, str "HEAD /status HTTP/1.1\r\n\r\n", "HTTP/1.1 401 Unauthorized", "Connection: close")
]

/-- The answer of the HTTP application to a request (byte by byte). -/
def answerOf (s : Http.Site) (req : ByteArray) : ByteArray := (Http.recv s {} req).resp

/-! ## Against OpenSSL -/

/-- `r ‖ s` from a DER `SEQUENCE { INTEGER r, INTEGER s }`. -/
def rsOfDer (d : ByteArray) : Option ByteArray := do
  if d.size < 8 || d[0]! != 0x30 then none
  let rl := d[3]!.toNat
  let r := d.extract 4 (4 + rl)
  let sl := d[5 + rl]!.toNat
  let s := d.extract (6 + rl) (6 + rl + sl)
  pure (natBe (beNat r) 32 ++ natBe (beNat s) 32)

def againstOpenssl : IO Nat := do
  if !(← haveOpenssl) then
    IO.println "auth vs OpenSSL: no openssl, skipped"
    return 0
  IO.FS.createDirAll tmp
  let key := (tmp / "es256.pem").toString
  let pubF := (tmp / "es256.pub.der").toString
  let inF := (tmp / "input.bin").toString
  let out := (tmp / "out.bin").toString
  let mut bad := 0
  let _ ← IO.Process.output { cmd := "openssl", args := #["ecparam", "-name", "prime256v1", "-genkey", "-noout", "-out", key] }
  let _ ← IO.Process.output { cmd := "openssl", args := #["ec", "-in", key, "-pubout", "-outform", "DER", "-out", pubF] }
  let spki ← IO.FS.readBinFile pubF
  let pub := spki.extract (spki.size - 65) spki.size
  let c : Auth.Cfg := { keys := [{ kid := "o", pub }], iss, aud }
  -- OpenSSL signs, we check
  let input := Auth.b64urlEncode (str "{\"alg\":\"ES256\",\"kid\":\"o\"}") ++ [46] ++ Auth.b64urlEncode (str (claims ",\"scope\":\"s\""))
  IO.FS.writeBinFile inF (ByteArray.mk input.toArray)
  let some der ← openssl #["dgst", "-sha256", "-sign", key, "-out", out, inF]
    | IO.println "  FAIL openssl dgst -sign"; return 1
  let some rs := rsOfDer der | IO.println "  FAIL DER of OpenSSL's signature"; return 1
  let t := ByteArray.mk (input ++ ([46] : List UInt8) ++ Auth.b64urlEncode rs).toArray
  if Auth.check c now t != some [str "s"] then
    IO.println "  FAIL a token signed by OpenSSL refused"; bad := bad + 1
  if Auth.check c now (flipLast t) != none then
    IO.println "  FAIL an altered token signed by OpenSSL accepted"; bad := bad + 1
  -- we sign, OpenSSL checks
  let sigF := (tmp / "sig.der").toString
  let pubPem := (tmp / "k1.pub.der").toString
  IO.FS.writeBinFile pubPem (hex "3059301306072a8648ce3d020106082a8648ce3d030107034200" ++ k1.pub)
  let parts := Auth.splitOn 46 good.toList
  let inputG := ByteArray.mk (parts[0]! ++ ([46] : List UInt8) ++ parts[1]!).toArray
  IO.FS.writeBinFile inF inputG
  let sig := (Auth.b64urlDecode parts[2]!).getD .empty
  let body := derInt (beNat (sig.extract 0 32)) ++ derInt (beNat (sig.extract 32 64))
  IO.FS.writeBinFile sigF (ByteArray.mk #[0x30, UInt8.ofNat body.size] ++ body)
  let r ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-verify", pubPem, "-keyform", "DER", "-signature", sigF, inF] }
  if r.exitCode != 0 then
    IO.println s!"  FAIL OpenSSL refuses our token's signature: {r.stdout}{r.stderr}"; bad := bad + 1
  IO.println s!"auth vs OpenSSL: a token signed by OpenSSL accepted and refused when altered; ours verified by OpenSSL, {bad} failures"
  return bad

def run : IO Nat := do
  let mut bad := 0
  -- base64url
  for (s, want) in b64Cases do
    let got := (Auth.b64urlDecode (bs s)).map (·.toList)
    if got != want then
      IO.println s!"  FAIL b64url {s}: {got}"; bad := bad + 1
    if let some w := want then
      if Auth.b64urlEncode (ByteArray.mk w.toArray) != bs s then
        IO.println s!"  FAIL b64url encode {s}"; bad := bad + 1
  -- RFC 7515 A.3: the signature, the payload's members, our key from d
  if !p256Verify a3Pub (str s!"{a3Header}.{a3Payload}")
      (beNat (((Auth.b64urlDecode (bs a3Sig)).getD .empty).extract 0 32))
      (beNat (((Auth.b64urlDecode (bs a3Sig)).getD .empty).extract 32 64)) then
    IO.println "  FAIL RFC 7515 A.3 signature"; bad := bad + 1
  if p256Public a3D != a3Pub then
    IO.println "  FAIL RFC 7515 A.3 key"; bad := bad + 1
  match Auth.parseObj ((Auth.b64urlDecode (bs a3Payload)).getD .empty) with
  | some kvs =>
    let ks := kvs.map fun (k, v) => (String.fromUTF8! k, match v with | .str (some s) => String.fromUTF8! s | .num n => toString n | _ => "?")
    if ks != [("iss", "joe"), ("exp", "1300819380"), ("http://example.com/is_root", "?")] then
      IO.println s!"  FAIL RFC 7515 A.3 payload: {ks}"; bad := bad + 1
  | none => IO.println "  FAIL RFC 7515 A.3 payload not parsed"; bad := bad + 1
  -- the claims of A.3 with an `aud`-free configuration of its own: refused for the missing aud
  -- (the case list), accepted by the signature alone above
  for (name, c, t, want) in checks do
    let got := (Auth.check c now t).map (·.map String.fromUTF8!)
    if got != want then
      IO.println s!"  FAIL check {name}: {got}, want {want}"; bad := bad + 1
  for (name, s, req, line, field) in routes do
    let a := answerOf s req
    if statusLine a != line || !hasField a field then
      IO.println s!"  FAIL route {name}: {String.fromUTF8! a}"; bad := bad + 1
    -- cut into single bytes or whole: the same answer
    if answerOf s req != Http.answer s req req then
      IO.println s!"  FAIL route {name}: byte by byte differs"; bad := bad + 1
  bad := bad + (← againstOpenssl)
  IO.println s!"auth: {b64Cases.length} base64url, RFC 7515 A.3, {checks.length} tokens, {routes.length} requests, {bad} failures"
  return bad

end Ember.Tests.AuthTests
