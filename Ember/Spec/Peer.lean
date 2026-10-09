import Ember.Spec.Stack

/-!
# Ember.Spec.Peer — packets as the peer (10.0.0.2) sends them

Builders used by unit tests, hand-written fixtures and the generators.
-/

namespace Ember.Spec.Peer
open Ember Ember.Trace

def ip : UInt32 := peerIpDefault
def ours : UInt32 := ourIpDefault

/-- The 56-byte payload of Linux `ping`: 8 bytes of timestamp, then 0x10, 0x11, … -/
def pingPayload (n : Nat) (stamp : UInt64 := 0) : ByteArray :=
  let ts := (List.range 8).map fun i => UInt8.ofNat ((stamp >>> (8 * (7 - i).toUInt64)).toNat)
  let body := (List.range (n - min n 8)).map fun i => UInt8.ofNat (0x10 + i)
  Bytes.ofList ((ts ++ body).take n)

def icmpEcho (id seq : UInt16) (payload : ByteArray) : ByteArray :=
  let h := Bytes.ofList ([8, 0, 0, 0] ++ Bytes.be16 id ++ Bytes.be16 seq)
  let m := h ++ payload
  Bytes.set16 m 2 (Checksum.checksum m 0 m.size)

def ping (id seq : UInt16) (payload : ByteArray) (ipId : UInt16 := 0x1234)
    (src := ip) (dst := ours) : ByteArray :=
  Ipv4.packet Ipv4.protoIcmp ipId src dst (icmpEcho id seq payload)

def udp (sport dport : UInt16) (data : ByteArray) (ipId : UInt16 := 0x2345)
    (src := ip) (dst := ours) : ByteArray :=
  Ipv4.packet Ipv4.protoUdp ipId src dst (Udp.emit src dst sport dport data)

def tcp (sport : UInt16) (seq ack : UInt32) (flags : UInt8) (data : ByteArray := .empty)
    (wnd : UInt16 := 64240) (mss : Option UInt16 := none) (dport : UInt16 := echoPort)
    (ipId : UInt16 := 0x3456) (src := ip) (dst := ours) : ByteArray :=
  Ipv4.packet Ipv4.protoTcp ipId src dst
    (Tcp.emit src dst { sport, dport, seq, ack, flags, wnd, mss, data })

/-- A TCP segment with arbitrary option bytes (padded with EOL to a
multiple of 4). -/
def tcpOpts (sport : UInt16) (seq ack : UInt32) (flags : UInt8) (opts : List UInt8)
    (data : ByteArray := .empty) (wnd : UInt16 := 64240) (dport : UInt16 := echoPort)
    (src := ip) (dst := ours) : ByteArray :=
  let o := opts ++ List.replicate ((4 - opts.length % 4) % 4) 0
  let off := 20 + o.length
  let h := Bytes.be16 sport ++ Bytes.be16 dport ++ Bytes.be32 seq ++ Bytes.be32 ack ++
    [UInt8.ofNat ((off / 4) * 16), flags] ++ Bytes.be16 wnd ++ [0, 0, 0, 0] ++ o
  let d := Bytes.ofList h ++ data
  let d := Bytes.set16 d 16 (Checksum.checksum d 0 d.size (Checksum.pseudo src dst Ipv4.protoTcp d.size))
  Ipv4.packet Ipv4.protoTcp 0x3456 src dst d

/-- Recompute the IPv4 header checksum after a test mutated the header. -/
def fixIpChecksum (p : ByteArray) : ByteArray :=
  let ihl := ((Bytes.get p 0) &&& 0x0F).toNat * 4
  let q := Bytes.set16 p 10 0
  Bytes.set16 q 10 (Checksum.checksum q 0 (min ihl p.size))

/-- A packet as a SLIP-framed `rx` input. -/
def slip (pkt : ByteArray) : Input := .rx (Slip.encode pkt)

def str (s : String) : ByteArray := s.toUTF8

end Ember.Spec.Peer
