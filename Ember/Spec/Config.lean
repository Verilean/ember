/-!
# Ember.Spec.Config — constants shared by the reference stack and `Ember.Net`
-/

namespace Ember.Spec

/-- 10.0.0.1: Ember's address on the SLIP link. -/
def ourIpDefault : UInt32 := 0x0A000001
/-- 10.0.0.2: the peer used by fixtures and generators. -/
def peerIpDefault : UInt32 := 0x0A000002

/-- SLIP's customary MTU; also the size of Ember's one packet buffer.
This is the default; the Ethernet build uses `mtuEth` (`Config.mtu`). -/
def mtu : Nat := 296
/-- Ethernet / Wi-Fi build: RFC 2131 requires DHCP clients to accept
576-byte datagrams, and a BOOTP reply alone is at least 328 bytes. -/
def mtuEth : Nat := 576
/-- TCP MSS announced on SYN-ACK: MTU minus IP and TCP headers. -/
def mssFor (mtu : Nat) : Nat := mtu - 40
def ourMss : Nat := mssFor mtu
def ttlDefault : UInt8 := 64
def echoPort : UInt16 := 7

/-! Timers, in ticks.  One tick is nominally 500 ms. -/

/-- Initial retransmission timeout. -/
def rtoInit : Nat := 3
/-- Upper bound of the exponential back-off. -/
def rtoMax : Nat := 48
/-- Retransmissions before the connection is reset. -/
def maxRetries : Nat := 8
/-- TIME-WAIT duration (2 MSL). -/
def timeWaitTicks : Nat := 20
/-- The echo application closes an idle connection after this many ticks. -/
def idleTicks : Nat := 60
/-- First TCP initial sequence number; each new connection adds `issStep`. -/
def issInit : UInt32 := 0x00010000
def issStep : UInt32 := 0x00010000

/-- Back-off schedule: `rtoInit · 2^k`, capped at `rtoMax`. -/
def rto (k : Nat) : Nat := min rtoMax (rtoInit * 2 ^ (min k 16))

end Ember.Spec
