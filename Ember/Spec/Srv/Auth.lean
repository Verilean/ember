import Ember.Spec.Crypto.P256

/-!
# Ember.Spec.Srv.Auth — OIDC access tokens: JWTs signed with ES256 (plan M9.1)

The reference for the token check of `Ember.Net.Http`.  A token is the
JWS compact serialization `B64(header) . B64(payload) . B64(signature)`
(RFC 7515), base64url without padding (strict: a length of 1 mod 4, or
non-zero bits left over at the end, is refused).

The two JSON objects are parsed strictly (RFC 8259): one object, nothing
but white space after it, at most `maxDepth` levels of nesting.  Only the
top level is looked at; a nested value is checked to be well formed and
otherwise skipped.  Strings are decoded for the one-character escapes;
a string with a `\u` escape has no value here (`str none`), so a claim
that must be compared and has one is refused.  A top-level key with any
escape is refused, so that `"nbf"` cannot hide `nbf`.  A number is a
value (`num`) only if it is a non-negative integer of at most 12 digits.
The keys this module reads may appear once: a key that `check` reads and
that is there twice refuses the token.

The token is accepted when (RFC 7515, 7519, 9068):

* `alg` is `"ES256"` (so `none`, `HS256`, `RS256` are refused) and there is
  no `crit`;
* `kid` names one of the configured keys, or there is no `kid` and there
  is exactly one key;
* the signature (`r ‖ s`, 64 bytes) verifies over the ASCII of
  `B64(header) . B64(payload)` with that key (ECDSA P-256, SHA-256);
* `iss` equals the configured issuer; `aud` equals the configured
  audience, or is an array of strings that contains it;
* `exp` is there and `now < exp + skew`; `nbf`, if there, has
  `nbf ≤ now + skew`; `iat`, if there, is a number (`checkIat` returns
  it: a control request needs one at or after the device's start, plan M9.4);
* `scope`, if there, is a string; its words (split at spaces) are the
  scopes the token grants.
-/

namespace Ember.Spec.Srv.Auth
open Ember.Spec.Crypto

/-! ## base64url -/

def b64Val (c : UInt8) : Option Nat :=
  if 65 ≤ c && c ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c && c ≤ 122 then some (c.toNat - 71)
  else if 48 ≤ c && c ≤ 57 then some (c.toNat + 4)
  else if c == 45 then some 62
  else if c == 95 then some 63
  else none

/-- base64url without padding, strict. -/
def b64urlDecode (s : List UInt8) : Option ByteArray := do
  let vs ← s.mapM b64Val
  if vs.length % 4 == 1 then none
  let (acc, _, out) := vs.foldl (fun (acc, nbits, out) v =>
    let acc := acc * 64 + v
    let nbits := nbits + 6
    if nbits ≥ 8 then (acc % 2 ^ (nbits - 8), nbits - 8, out.push (UInt8.ofNat (acc / 2 ^ (nbits - 8))))
    else (acc, nbits, out)) ((0 : Nat), (0 : Nat), ByteArray.empty)
  if acc != 0 then none
  pure out

def b64urlEncode (b : ByteArray) : List UInt8 := Id.run do
  let alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toUTF8
  let mut out : Array UInt8 := #[]
  let mut acc := 0
  let mut nbits := 0
  for x in b.toList do
    acc := acc * 256 + x.toNat
    nbits := nbits + 8
    while nbits ≥ 6 do
      out := out.push alpha[acc / 2 ^ (nbits - 6)]!
      acc := acc % 2 ^ (nbits - 6)
      nbits := nbits - 6
  if nbits > 0 then out := out.push alpha[acc * 2 ^ (6 - nbits)]!
  return out.toList

/-! ## JSON -/

inductive JVal where
  /-- A string; `none` if it has a `\u` escape. -/
  | str (s : Option ByteArray)
  /-- A non-negative integer of at most 12 digits. -/
  | num (n : Nat)
  /-- An array whose elements are all strings. -/
  | strs (xs : List (Option ByteArray))
  | other
  deriving Inhabited

def maxDepth : Nat := 16

def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isHex (c : UInt8) : Bool := isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)

def skipWs (b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if i < b.size && isWs b[i]! then skipWs b f (i + 1) else i

/-- The string whose opening quote is at `i - 1`: its value (`none` if it has
a `\u` escape), whether it had an escape at all, and the position after
its closing quote. -/
def str (b : ByteArray) : Nat → Nat → ByteArray → Bool → Bool → Option (Option ByteArray × Bool × Nat)
  | 0, _, _, _, _ => none
  | f + 1, i, out, esc, u =>
    if i ≥ b.size then none else
    let c := b[i]!
    if c == 34 then some (if u then none else some out, esc, i + 1)
    else if c < 32 then none
    else if c == 92 then
      if i + 1 ≥ b.size then none else
      let e := b[i + 1]!
      let one : Option UInt8 :=
        if e == 34 then some 34 else if e == 92 then some 92 else if e == 47 then some 47
        else if e == 98 then some 8 else if e == 102 then some 12 else if e == 110 then some 10
        else if e == 114 then some 13 else if e == 116 then some 9 else none
      match one with
      | some x => str b f (i + 2) (out.push x) true u
      | none =>
        if e == 117 && i + 5 < b.size && isHex b[i + 2]! && isHex b[i + 3]! && isHex b[i + 4]! && isHex b[i + 5]! then
          str b f (i + 6) out true true
        else none
    else str b f (i + 1) (out.push c) esc u

def digits (b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if i < b.size && isDigit b[i]! then digits b f (i + 1) else i

/-- A number at `i`: its value, if a short non-negative integer, and the position after it. -/
def number (b : ByteArray) (i : Nat) : Option (JVal × Nat) := do
  let f := b.size + 1
  let neg := i < b.size && b[i]! == 45
  let j := if neg then i + 1 else i
  if j ≥ b.size || !isDigit b[j]! then none
  let k := if b[j]! == 48 then j + 1 else digits b f j
  let intEnd := k
  let k ← if k < b.size && b[k]! == 46 then
      let d := digits b f (k + 1)
      if d == k + 1 then none else some d
    else some k
  let k ← if k < b.size && (b[k]! == 101 || b[k]! == 69) then
      let s := if k + 1 < b.size && (b[k + 1]! == 43 || b[k + 1]! == 45) then k + 2 else k + 1
      let d := digits b f s
      if d == s then none else some d
    else some k
  let plain := !neg && k == intEnd && intEnd - j ≤ 12
  let n := (b.extract j intEnd).toList.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
  pure (if plain then .num n else .other, k)

def lit (b : ByteArray) (i : Nat) (w : String) : Option Nat :=
  let w := w.toUTF8
  if i + w.size ≤ b.size && b.extract i (i + w.size) == w then some (i + w.size) else none

mutual
/-- A value at `i` (white space skipped already) at nesting `depth`. -/
def value (b : ByteArray) : Nat → Nat → Nat → Option (JVal × Nat)
  | 0, _, _ => none
  | f + 1, depth, i =>
    if i ≥ b.size then none else
    let c := b[i]!
    if c == 34 then do
      let (s, _, j) ← str b (b.size + 1) (i + 1) .empty false false
      pure (.str s, j)
    else if c == 123 then do
      if depth + 1 > maxDepth then none
      let (_, j) ← members b f (depth + 1) false (skipWs b (b.size + 1) (i + 1)) [] true
      pure (.other, j)
    else if c == 91 then do
      if depth + 1 > maxDepth then none
      elems b f (depth + 1) (skipWs b (b.size + 1) (i + 1)) (some []) true
    else if c == 116 then (lit b i "true").map (.other, ·)
    else if c == 102 then (lit b i "false").map (.other, ·)
    else if c == 110 then (lit b i "null").map (.other, ·)
    else number b i

/-- The members of an object from `i`, up to and past its `}`; `top`: the
outermost object, whose keys may have no escape. -/
def members (b : ByteArray) : Nat → Nat → Bool → Nat → List (ByteArray × JVal) → Bool →
    Option (List (ByteArray × JVal) × Nat)
  | 0, _, _, _, _, _ => none
  | f + 1, depth, top, i, acc, first =>
    if i ≥ b.size then none else
    if first && b[i]! == 125 then some (acc, i + 1) else
    if b[i]! != 34 then none else do
    let (k, esc, j) ← str b (b.size + 1) (i + 1) .empty false false
    if top && esc then none
    let k := k.getD .empty
    let j := skipWs b (b.size + 1) j
    if j ≥ b.size || b[j]! != 58 then none
    let (v, j) ← value b f depth (skipWs b (b.size + 1) (j + 1))
    let acc := acc ++ [(k, v)]
    let j := skipWs b (b.size + 1) j
    if j ≥ b.size then none
    if b[j]! == 125 then some (acc, j + 1)
    else if b[j]! == 44 then members b f depth top (skipWs b (b.size + 1) (j + 1)) acc false
    else none

/-- The elements of an array from `i`, up to and past its `]`; `strs`: the
strings so far, while every element is one. -/
def elems (b : ByteArray) : Nat → Nat → Nat → Option (List (Option ByteArray)) → Bool → Option (JVal × Nat)
  | 0, _, _, _, _ => none
  | f + 1, depth, i, strs, first =>
    if i ≥ b.size then none else
    let done (j : Nat) : JVal × Nat := (match strs with | some xs => .strs xs | none => .other, j)
    if first && b[i]! == 93 then some (done (i + 1)) else do
    let (v, j) ← value b f depth i
    let strs := match strs, v with
      | some xs, .str s => some (xs ++ [s])
      | _, _ => none
    let j := skipWs b (b.size + 1) j
    if j ≥ b.size then none
    if b[j]! == 93 then some (match strs with | some xs => .strs xs | none => .other, j + 1)
    else if b[j]! == 44 then elems b f depth (skipWs b (b.size + 1) (j + 1)) strs false
    else none
end

/-- A whole JSON text that is one object: its top-level members. -/
def parseObj (b : ByteArray) : Option (List (ByteArray × JVal)) := do
  let i := skipWs b (b.size + 1) 0
  if i ≥ b.size || b[i]! != 123 then none
  -- every call of `members`, `elems` and `value` but the nested ones takes a
  -- byte or more, so this fuel does not run out
  let (kvs, j) ← members b (2 * b.size + 2 * maxDepth + 4) 1 true (skipWs b (b.size + 1) (i + 1)) [] true
  if skipWs b (b.size + 1) j != b.size then none
  pure kvs

/-- The member `k`: `some none` if absent, `some (some v)` if there once,
`none` if there twice or more.  `check` reads every member with `←` in
`Option`, so a key there twice refuses the token, also for the optional
`crit`, `kid`, `nbf` and `scope` (the cases `… twice` of `AuthTests`). -/
def field (kvs : List (ByteArray × JVal)) (k : String) : Option (Option JVal) :=
  match kvs.filter (·.1 == k.toUTF8) with
  | [] => some none
  | [(_, v)] => some (some v)
  | _ => none

/-! ## The check -/

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

def splitOn (c : UInt8) (l : List UInt8) : List (List UInt8) :=
  let (cur, acc) := l.foldl (fun (cur, acc) b =>
    if b == c then ([], acc ++ [cur]) else (cur ++ [b], acc)) (([] : List UInt8), ([] : List (List UInt8)))
  acc ++ [cur]

/-- The words of a `scope` value: split at spaces, empty words dropped. -/
def words (s : ByteArray) : List ByteArray :=
  (splitOn 32 s.toList).filter (!·.isEmpty) |>.map (ByteArray.mk ·.toArray)

def isStr (v : Option JVal) (s : String) : Bool :=
  match v with
  | some (.str (some x)) => x == s.toUTF8
  | _ => false

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
  let aud ← field pj "aud"
  let audOk := match aud with
    | some (.str (some x)) => x == cfg.aud.toUTF8
    | some (.strs xs) => xs.any (· == some cfg.aud.toUTF8)
    | _ => false
  if !audOk then none
  let exp ← field pj "exp"
  match exp with
  | some (.num e) => if now < e + cfg.skew then pure () else none
  | _ => none
  let nbf ← field pj "nbf"
  match nbf with
  | none => pure ()
  | some (.num n) => if n ≤ now + cfg.skew then pure () else none
  | some _ => none
  -- `iat`, when there, a number (plan M9.4: control needs one after the start)
  let iat ← field pj "iat"
  let iat ← match iat with
    | none => pure none
    | some (.num i) => pure (some i)
    | some _ => none
  let scope ← field pj "scope"
  match scope with
  | none => pure ([], iat)
  | some (.str (some x)) => pure (words x, iat)
  | some _ => none

/-- The scopes of an accepted token. -/
def check (cfg : Cfg) (now : Nat) (tok : ByteArray) : Option (List ByteArray) :=
  (checkIat cfg now tok).map (·.1)

/-- A signed token, for the tests: the compact serialization of `header`
and `payload` (JSON texts) signed with the private scalar `d` (RFC 6979). -/
def sign (d : Nat) (header payload : String) : ByteArray :=
  let input := b64urlEncode header.toUTF8 ++ [46] ++ b64urlEncode payload.toUTF8
  let (r, s) := p256SignRS d (ByteArray.mk input.toArray)
  ByteArray.mk (input ++ [46] ++ b64urlEncode (natBe r 32 ++ natBe s 32)).toArray

/-! ## The demo identity provider (for `ember-host --auth` and the recorded sessions) -/

/-- The demo provider's private scalar: a demo key, published here, never
for a real provider. -/
def demoIdpKey : Nat := 0x3c1e7a5d9b2f408e6a1c3b5d7f9e0a2c4e6b8d0f1a3c5e7b9d2f4a6c8e0b1d3f

def demoCfg : Cfg :=
  { keys := [{ kid := "demo", pub := p256Public demoIdpKey }], iss := "https://idp.ember.local", aud := "ember-drone" }

/-- The time the recorded sessions were made at (2027-01-15). -/
def demoNow : Nat := 1_800_000_000

/-- A token of the demo provider with `scope`, valid for an hour from `now`. -/
def demoToken (scope : String) (now : Nat := demoNow) : ByteArray :=
  sign demoIdpKey "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"demo\"}"
    s!"\{\"iss\":\"https://idp.ember.local\",\"aud\":\"ember-drone\",\"sub\":\"pilot\",\"iat\":{now},\"exp\":{now + 3600},\"scope\":\"{scope}\"}"

end Ember.Spec.Srv.Auth
