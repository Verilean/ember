import Ember.Spec.Checksum
import Ember.Spec.Config

/-!
# Ember.Spec.Ipv4 — IPv4 header validation and construction

Validation order (and the drop reason of each check) is part of the
specification: `Ember.Net` performs the same checks in the same order,
so both report the same `drop reason=` for a malformed packet.

1. fewer than 20 bytes ............................. `short-packet`
2. version ≠ 4 ..................................... `bad-version`
3. IHL < 5 or IHL·4 > packet size .................. `bad-ihl`
4. header checksum wrong ........................... `bad-ip-checksum`
5. total length < IHL·4 or > packet size ........... `bad-length`
6. MF set or fragment offset ≠ 0 ................... `fragment`
7. TTL = 0 ......................................... `ttl-zero`
8. destination neither ours nor 255.255.255.255 .... `not-for-us`

Options are skipped (the payload starts at IHL·4); bytes beyond the total
length (link padding) are ignored.  Replies always carry a fresh 20-byte
header: TTL 64, identification from a counter, DF as Linux sets it.
-/

namespace Ember.Spec.Ipv4
open Ember

def protoIcmp : UInt8 := 1
def protoTcp : UInt8 := 6
def protoUdp : UInt8 := 17
def broadcast : UInt32 := 0xFFFFFFFF

structure Hdr where
  ihl      : Nat
  totalLen : Nat
  id       : UInt16
  ttl      : UInt8
  proto    : UInt8
  src      : UInt32
  dst      : UInt32
  deriving Inhabited, Repr

/-- Validate a received packet; on success the header and the payload. -/
def validate (p : ByteArray) (ourIp : UInt32) : Except String (Hdr × ByteArray) := do
  if p.size < 20 then throw "short-packet"
  let vihl := Bytes.get p 0
  if vihl >>> 4 != 4 then throw "bad-version"
  let ihl := (vihl &&& 0x0F).toNat * 4
  if ihl < 20 || ihl > p.size then throw "bad-ihl"
  if !Checksum.verifies (Checksum.sum p 0 ihl) then throw "bad-ip-checksum"
  let tl := (Bytes.get16 p 2).toNat
  if tl < ihl || tl > p.size then throw "bad-length"
  let ff := Bytes.get16 p 6
  if ff &&& 0x3FFF != 0 then throw "fragment"
  let ttl := Bytes.get p 8
  if ttl == 0 then throw "ttl-zero"
  let dst := Bytes.get32 p 16
  if dst != ourIp && dst != broadcast then throw "not-for-us"
  let h : Hdr := { ihl, totalLen := tl, id := Bytes.get16 p 4, ttl,
                   proto := Bytes.get p 9, src := Bytes.get32 p 12, dst }
  return (h, Bytes.slice p ihl (tl - ihl))

/-- Ember sets DF exactly where Linux does: on UDP and TCP, not on ICMP
echo replies (it never fragments either way). -/
def dfFor (proto : UInt8) : Bool := proto != protoIcmp

/-- A 20-byte header (no options, TOS 0) with its checksum. -/
def header (proto : UInt8) (id : UInt16) (src dst : UInt32) (payloadLen : Nat)
    (ttl : UInt8 := ttlDefault) : ByteArray :=
  let l := [0x45, 0x00] ++ Bytes.be16 (UInt16.ofNat (20 + payloadLen)) ++ Bytes.be16 id ++
    [if dfFor proto then 0x40 else 0x00, 0x00, ttl, proto, 0x00, 0x00] ++ Bytes.be32 src ++ Bytes.be32 dst
  let h := Bytes.ofList l
  Bytes.set16 h 10 (Checksum.checksum h 0 20)

def packet (proto : UInt8) (id : UInt16) (src dst : UInt32) (payload : ByteArray) : ByteArray :=
  header proto id src dst payload.size ++ payload

def ipToString (a : UInt32) : String :=
  s!"{(a >>> 24).toNat}.{((a >>> 16) &&& 0xFF).toNat}.{((a >>> 8) &&& 0xFF).toNat}.{(a &&& 0xFF).toNat}"

end Ember.Spec.Ipv4
