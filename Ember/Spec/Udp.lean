import Ember.Spec.Ipv4

/-!
# Ember.Spec.Udp — datagram validation and the echo service

Checks, in order: fewer than 8 bytes `short-udp`; length field < 8 or
larger than the IP payload `bad-udp-length`; non-zero checksum that does
not verify `bad-udp-checksum` (a zero checksum means "none", RFC 768).
Bytes beyond the UDP length are ignored.  Replies always carry a
checksum (a computed 0 is sent as 0xFFFF).
-/

namespace Ember.Spec.Udp
open Ember

structure Dgram where
  sport : UInt16
  dport : UInt16
  data  : ByteArray
  deriving Inhabited

def parse (src dst : UInt32) (p : ByteArray) : Except String Dgram := do
  if p.size < 8 then throw "short-udp"
  let ul := (Bytes.get16 p 4).toNat
  if ul < 8 || ul > p.size then throw "bad-udp-length"
  let cs := Bytes.get16 p 6
  if cs != 0 then
    let s := Checksum.sum p 0 ul (Checksum.pseudo src dst Ipv4.protoUdp ul)
    if !Checksum.verifies s then throw "bad-udp-checksum"
  return { sport := Bytes.get16 p 0, dport := Bytes.get16 p 2, data := Bytes.slice p 8 (ul - 8) }

/-- A UDP datagram with its checksum. -/
def emit (src dst : UInt32) (sport dport : UInt16) (data : ByteArray) : ByteArray :=
  let ul := 8 + data.size
  let h := Bytes.ofList (Bytes.be16 sport ++ Bytes.be16 dport ++ Bytes.be16 (UInt16.ofNat ul) ++ [0, 0])
  let d := h ++ data
  let c := Checksum.checksum d 0 ul (Checksum.pseudo src dst Ipv4.protoUdp ul)
  Bytes.set16 d 6 (if c == 0 then 0xFFFF else c)

end Ember.Spec.Udp
