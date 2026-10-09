import Ember.Spec.Ipv4

/-!
# Ember.Spec.Arp — Ethernet II framing and ARP (RFC 826), M1.11

The second link layer, for Wi-Fi raw frames (M4w).  A four-entry cache,
replaced round-robin.  Following RFC 826's merge rule, a request updates
the sender's entry if it exists and adds it when the request is for us;
replies always update.  Received IPv4 frames also refresh the cache with
their source (as uIP's `arp_ipin` does), so replies rarely miss.  On a
miss the outgoing packet is dropped (`arp-miss`) and an ARP request is
sent instead; the peer's retransmission then finds the entry.

Frame checks, in order: fewer than 14 bytes `short-frame`; destination
neither our MAC nor broadcast `not-our-mac`; IPv4 payload over the MTU
`oversize-frame`; EtherType other than IPv4/ARP `unsupported-ethertype`.
ARP checks: fewer than 28 bytes `short-arp`; not Ethernet/IPv4
`bad-arp`; a request for another address `arp-not-for-us`.
-/

namespace Ember.Spec.Arp
open Ember

def ourMacDefault : ByteArray := Bytes.ofList [0x02, 0x00, 0x00, 0x00, 0x00, 0x01]
def broadcastMac : ByteArray := Bytes.ofList [0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
def typeIpv4 : UInt16 := 0x0800
def typeArp : UInt16 := 0x0806
def cacheSize : Nat := 4

structure Cache where
  entries : Array (UInt32 × ByteArray) := #[]
  next    : Nat := 0
  deriving Inhabited

def Cache.lookup (c : Cache) (ip : UInt32) : Option ByteArray :=
  (c.entries.find? (·.1 == ip)).map (·.2)

/-- Update an existing entry; `insert` also adds a missing one. -/
def Cache.update (c : Cache) (ip : UInt32) (mac : ByteArray) (insert : Bool) : Cache :=
  match c.entries.findIdx? (·.1 == ip) with
  | some i => { c with entries := c.entries.set! i (ip, mac) }
  | none =>
    if !insert then c
    else if c.entries.size < cacheSize then { c with entries := c.entries.push (ip, mac) }
    else { entries := c.entries.set! c.next (ip, mac), next := (c.next + 1) % cacheSize }

/-- An Ethernet II frame.  Not padded to 60 bytes: as with Linux on a TAP
device, padding is the driver's job (and 802.11 has no minimum). -/
def frame (dst src : ByteArray) (ty : UInt16) (payload : ByteArray) : ByteArray :=
  dst ++ src ++ Bytes.ofList (Bytes.be16 ty) ++ payload

def packet (op : UInt16) (sha : ByteArray) (spa : UInt32) (tha : ByteArray) (tpa : UInt32) : ByteArray :=
  Bytes.ofList ([0, 1, 0x08, 0x00, 6, 4] ++ Bytes.be16 op) ++ sha ++ Bytes.ofList (Bytes.be32 spa) ++
  tha ++ Bytes.ofList (Bytes.be32 tpa)

def request (ourMac : ByteArray) (ourIp target : UInt32) : ByteArray :=
  frame broadcastMac ourMac typeArp (packet 1 ourMac ourIp (Bytes.ofList [0,0,0,0,0,0]) target)

/-- Handle an ARP packet: the new cache, and a reply frame or a drop reason. -/
def input (c : Cache) (ourMac : ByteArray) (ourIp : UInt32) (p : ByteArray) :
    Cache × Except String (Option ByteArray) :=
  if p.size < 28 then (c, .error "short-arp")
  else if Bytes.get16 p 0 != 1 || Bytes.get16 p 2 != typeIpv4 || Bytes.get p 4 != 6 ||
          Bytes.get p 5 != 4 then (c, .error "bad-arp")
  else
    let op := Bytes.get16 p 6
    let sha := Bytes.slice p 8 6
    let spa := Bytes.get32 p 14
    let tpa := Bytes.get32 p 24
    let forUs := tpa == ourIp && ourIp != 0
    let c := c.update spa sha (insert := forUs || op == 2)
    if op == 1 then
      if forUs then (c, .ok (some (frame sha ourMac typeArp (packet 2 ourMac ourIp sha spa))))
      else (c, .error "arp-not-for-us")
    else (c, .ok none)

end Ember.Spec.Arp
