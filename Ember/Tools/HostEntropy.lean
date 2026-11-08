import Ember.Spec.Srv.Tls

/-!
# Ember.Tools.HostEntropy — the TLS randomness of `ember-host` (plan M9.4)

`ember-host --https` serves `Spec.Srv.Tls`, whose server random and
ephemeral key come from the site's seed, the entropy of the handshake and
the client's random.  By default the host takes fresh entropy for every
handshake: before each input it puts 32 bytes from the operating system's
cryptographic generator (`IO.getRandomBytes`: `/dev/urandom` on Linux,
the Lean runtime's source) in the shared state (`Http.Ctl.ent`), and the
site is `fresh` (`Spec.Srv.Tls.Site.fresh`): a handshake takes them once,
and a handshake without them ends with `internal_error`.  So a ClientHello
sent twice, byte for byte, gets two different server randoms and key
shares (RFC 8446 §4.1.3).  If the system gives no bytes, fewer than 32,
or eight equal words, the host stops (at start, or at that input).

For the tests only: `--entropy HEX` gives fixed bytes for every handshake
(as the board's tests set the RNG register), and `--no-entropy` keeps the
fixed seed of M8 alone, which the recorded fixtures were made with.  Both
make a replayed ClientHello get the same key share; the host says so on
stderr.
-/

namespace Ember.Tools.HostEntropy

/-- Where the entropy comes from. -/
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

/-- The system's generator. -/
def system : Nat → IO ByteArray := fun n => IO.getRandomBytes n.toUSize

/-- 32 fresh bytes from `random`, or why there are none. -/
def next (random : Nat → IO ByteArray := system) : IO (Except String ByteArray) := do
  let b ← match ← (random 32).toBaseIO with
    | .ok b => pure b
    | .error e => return .error s!"no randomness from the system: {e}"
  if b.size != 32 then return .error s!"the system gave {b.size} random bytes, not 32"
  if Spec.Srv.Tls.stuck b then return .error "the system's random bytes are eight equal words"
  return .ok b

/-- The TLS site for `src`: fresh entropy per handshake from the system
(checked once here, so that a host without a working generator does not
start), fixed bytes, or none; or why the host must not start. -/
def site (base : Spec.Srv.Tls.Site) (src : Source) (random : Nat → IO ByteArray := system) :
    IO (Except String Spec.Srv.Tls.Site) := do
  match src with
  | .none => return .ok { base with entropy := none, fresh := false }
  | .given hex =>
    match ofHex hex with
    | some b => return .ok { base with entropy := some b, fresh := false }
    | none => return .error s!"--entropy wants 64 hexadecimal digits, not {hex}"
  | .os =>
    match ← next random with
    | .ok _ => return .ok { base with entropy := none, fresh := true }
    | .error e => return .error e

/-- The shared state with fresh entropy for the next handshake. -/
def refill (g : Spec.Srv.Http.Ctl) (random : Nat → IO ByteArray := system) : IO (Except String Spec.Srv.Http.Ctl) := do
  match ← next random with
  | .ok b => return .ok { g with ent := some b }
  | .error e => return .error e

end Ember.Tools.HostEntropy
