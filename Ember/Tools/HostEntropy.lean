import Ember.Spec.Srv.Tls

/-!
# Ember.Tools.HostEntropy — the TLS randomness of `ember-host` (plan M9.4)

`ember-host --https` serves `Spec.Srv.Tls`, whose server random and
ephemeral key come from the site's seed, the site's `entropy` and the
client's random.  The host takes the 32 bytes of `entropy` from the
operating system's cryptographic generator when it starts
(`IO.getRandomBytes`: `/dev/urandom` on Linux, the Lean runtime's source);
if that fails, or gives 32 bytes that are eight equal words (which
`Spec.Srv.Tls.stuck` would refuse handshake by handshake), the host does
not start.  For the tests the bytes can be given (`--entropy HEX`), and
`--no-entropy` keeps the fixed seed of M8 alone, which the recorded
fixtures were made with (a test configuration: a replayed ClientHello
then gets the same key share).

Within one run of the host the entropy is fixed: two handshakes differ by
the clients' randoms, so a ClientHello replayed byte for byte gets the
same ServerHello (it cannot finish without the client's private key).
The ESP32-C3 reads its RNG for every handshake.
-/

namespace Ember.Tools.HostEntropy

/-- Where the 32 bytes come from. -/
inductive Source where
  | os
  | given (hex : String)
  | none
  deriving Inhabited, BEq

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- 64 hexadecimal digits as 32 bytes. -/
def ofHex (s : String) : Option ByteArray := do
  let cs := s.toList
  if cs.length != 64 then none
  let mut out := ByteArray.empty
  for i in [0:32] do
    let hi ← hexVal cs[2 * i]!
    let lo ← hexVal cs[2 * i + 1]!
    out := out.push (hi * 16 + lo).toUInt8
  return out

/-- The site's `entropy` for `src`, or why the host must not start. -/
def get (src : Source) (random : Nat → IO ByteArray := fun n => IO.getRandomBytes n.toUSize) :
    IO (Except String (Option ByteArray)) := do
  match src with
  | .none => return .ok none
  | .given hex =>
    match ofHex hex with
    | some b => return .ok (some b)
    | none => return .error s!"--entropy wants 64 hexadecimal digits, not {hex}"
  | .os =>
    let b ← match ← (random 32).toBaseIO with
      | .ok b => pure b
      | .error e => return .error s!"no randomness from the system: {e}"
    if b.size != 32 then return .error s!"the system gave {b.size} random bytes, not 32"
    if Spec.Srv.Tls.stuck b then return .error "the system's random bytes are eight equal words"
    return .ok (some b)

end Ember.Tools.HostEntropy
