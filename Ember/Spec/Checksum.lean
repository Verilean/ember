import Ember.Util.Bytes

/-!
# Ember.Spec.Checksum — the Internet checksum (RFC 1071, RFC 1624)

Sums are kept in 16 bits with end-around carry (never a 32-bit
accumulator), which is the form `Ember.Net` uses on small targets.
-/

namespace Ember.Spec.Checksum
open Ember

/-- One's-complement addition of two 16-bit words. -/
@[inline] def add (a b : UInt16) : UInt16 :=
  let s := a.toUInt32 + b.toUInt32
  ((s &&& (0xFFFF : UInt32)) + (s >>> (16 : UInt32))).toUInt16

/-- One's-complement sum of `b[off, off+len)` as big-endian words, an odd
final byte padded with zero, starting from `init`. -/
def sum (b : ByteArray) (off len : Nat) (init : UInt16 := 0) : UInt16 := Id.run do
  let mut s := init
  let mut i := 0
  while i + 1 < len do
    s := add s (Bytes.get16 b (off + i))
    i := i + 2
  if i < len then
    s := add s ((Bytes.get b (off + i)).toUInt16 <<< 8)
  return s

/-- The Internet checksum of a byte range: complement of the sum. -/
def checksum (b : ByteArray) (off len : Nat) (init : UInt16 := 0) : UInt16 :=
  ~~~ (sum b off len init)

/-- Sum of the IPv4 pseudo-header used by UDP and TCP. -/
def pseudo (src dst : UInt32) (proto : UInt8) (len : Nat) : UInt16 :=
  let s := add (src >>> 16).toUInt16 src.toUInt16
  let s := add s (dst >>> 16).toUInt16
  let s := add s dst.toUInt16
  let s := add s proto.toUInt16
  add s (UInt16.ofNat len)

/-- RFC 1624 eqn. 3: new checksum after a 16-bit field changes from `m` to
`m'`, without touching the rest of the data: `HC' = ~(~HC + ~m + m')`. -/
def incremental (hc m m' : UInt16) : UInt16 :=
  ~~~ (add (add (~~~ hc) (~~~ m)) m')

/-- Data with a correct checksum field sums to `0xFFFF` (or `0` = −0). -/
def verifies (s : UInt16) : Bool := s == 0xFFFF || s == 0

end Ember.Spec.Checksum
