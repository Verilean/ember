import Ember.Spec.Ipv4

/-!
# Ember.Spec.Icmp — echo reply, built in place

The reply keeps the request's ICMP message and changes one byte (type
8 → 0), updating the checksum incrementally (RFC 1624) rather than
recomputing it.  Checks, in order: fewer than 8 bytes `short-icmp`;
checksum `bad-icmp-checksum`; type other than echo request
`unsupported-icmp-type`.
-/

namespace Ember.Spec.Icmp
open Ember

def typeEchoReply : UInt8 := 0
def typeEchoRequest : UInt8 := 8

/-- The ICMP message answering `msg`, or a drop reason. -/
def reply (msg : ByteArray) : Except String ByteArray := do
  if msg.size < 8 then throw "short-icmp"
  if !Checksum.verifies (Checksum.sum msg 0 msg.size) then throw "bad-icmp-checksum"
  if Bytes.get msg 0 != typeEchoRequest then throw "unsupported-icmp-type"
  let old := Bytes.get16 msg 0
  let new := (typeEchoReply.toUInt16 <<< 8) ||| (old &&& 0x00FF)
  let m := Bytes.set16 msg 0 new
  return Bytes.set16 m 2 (Checksum.incremental (Bytes.get16 msg 2) old new)

end Ember.Spec.Icmp
