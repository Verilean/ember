import Ember.Spec.Udp

/-!
# Ember.Spec.Dhcp — DHCP client (RFC 2131), M1.12, optional

Phases: INIT → (DISCOVER) SELECTING → (OFFER, REQUEST) REQUESTING →
(ACK) BOUND → at T1 = lease/2, REQUEST again (renewing) → ACK → BOUND.
A NAK, or no answer within `retryTicks`, returns to INIT (and forgets the
address).  Messages are broadcast with the broadcast flag set, so replies
reach us before we have an address.  Leases are in seconds; one tick is
500 ms.  The transaction id is `xidBase + n` for the n-th exchange.

Checks on a message to port 68, in order: shorter than 240 bytes or not a
BOOTREPLY `bad-dhcp`; wrong xid or hardware address `dhcp-not-ours`; no
message type, or one not expected in the current phase `dhcp-unexpected`.
-/

namespace Ember.Spec.Dhcp
open Ember

def clientPort : UInt16 := 68
def serverPort : UInt16 := 67
def xidBase : UInt32 := 0x454D4200
def retryTicks : Nat := 8
def ticksPerSecond : Nat := 2
def magic : UInt32 := 0x63825363

inductive Phase where
  | init | selecting | requesting | bound
  deriving Inhabited, BEq, Repr

structure St where
  phase   : Phase := .init
  xid     : UInt32 := xidBase
  server  : UInt32 := 0
  offered : UInt32 := 0
  timer   : Nat := 0
  deriving Inhabited

/-- Options as (code, value) pairs; stops at END or a malformed length. -/
def options (p : ByteArray) : List (UInt8 × ByteArray) := Id.run do
  let mut i := 240
  let mut out : Array (UInt8 × ByteArray) := #[]
  for _ in [0:p.size] do
    if i ≥ p.size then break
    let c := Bytes.get p i
    if c == 255 then break
    if c == 0 then
      i := i + 1
      continue
    if i + 1 ≥ p.size then break
    let l := (Bytes.get p (i+1)).toNat
    if i + 2 + l > p.size then break
    out := out.push (c, Bytes.slice p (i+2) l)
    i := i + 2 + l
  return out.toList

def opt32 (os : List (UInt8 × ByteArray)) (c : UInt8) : Option UInt32 :=
  (os.find? (·.1 == c)).bind fun (_, v) => if v.size ≥ 4 then some (Bytes.get32 v 0) else none

/-- A BOOTREQUEST with the given DHCP message type and extra options. -/
def message (xid : UInt32) (mac : ByteArray) (ciaddr : UInt32) (mtype : UInt8)
    (extra : List UInt8) : ByteArray :=
  let fixed := [1, 1, 6, 0] ++ Bytes.be32 xid ++ [0, 0, 0x80, 0x00] ++ Bytes.be32 ciaddr ++
    List.replicate 12 0
  let chaddr := mac.toList ++ List.replicate 10 0
  let body := fixed ++ chaddr ++ List.replicate 192 0 ++ Bytes.be32 magic ++
    [53, 1, mtype] ++ extra ++ [255]
  Bytes.ofList body

def discover (s : St) (mac : ByteArray) : ByteArray := message s.xid mac 0 1 []

def request (s : St) (mac : ByteArray) (ciaddr : UInt32) : ByteArray :=
  let ask := if ciaddr == 0 then [50, 4] ++ Bytes.be32 s.offered ++ [54, 4] ++ Bytes.be32 s.server else []
  message s.xid mac ciaddr 3 ask

/-- Result of a DHCP step: new state, new address, a message to broadcast. -/
structure Out where
  st   : St
  ip   : UInt32
  send : Option ByteArray := none
  drop : Option String := none
  note : Option String := none

def input (s : St) (ip : UInt32) (mac : ByteArray) (p : ByteArray) : Out := Id.run do
  if p.size < 240 || Bytes.get p 0 != 2 || Bytes.get32 p 236 != magic then
    return { st := s, ip, drop := some "bad-dhcp" }
  if Bytes.get32 p 4 != s.xid || (Bytes.slice p 28 6).toList != mac.toList then
    return { st := s, ip, drop := some "dhcp-not-ours" }
  let os := options p
  let mtype := (os.find? (·.1 == 53)).bind fun (_, v) => if v.size ≥ 1 then some (Bytes.get v 0) else none
  let yi := Bytes.get32 p 16
  match s.phase, mtype with
  | .selecting, some 2 =>
    let s := { s with phase := .requesting, offered := yi,
                      server := (opt32 os 54).getD 0, timer := retryTicks }
    return { st := s, ip, send := some (request s mac 0),
             note := some s!"dhcp offer {Ipv4.ipToString yi} from {Ipv4.ipToString s.server}" }
  | .requesting, some 5 =>
    let lease := ((opt32 os 51).getD 3600).toNat
    let t1 := max 1 (lease * ticksPerSecond / 2)
    return { st := { s with phase := .bound, offered := yi, timer := t1, xid := s.xid + 1 }, ip := yi,
             note := some s!"dhcp bound {Ipv4.ipToString yi} lease={lease}s" }
  | .requesting, some 6 =>
    return { st := { phase := .init, xid := s.xid + 1 }, ip := 0, note := some "dhcp nak" }
  | _, _ => return { st := s, ip, drop := some "dhcp-unexpected" }

def tick (s : St) (ip : UInt32) (mac : ByteArray) : Out :=
  match s.phase with
  | .init =>
    let s := { s with phase := .selecting, timer := retryTicks }
    { st := s, ip, send := some (discover s mac) }
  | .selecting | .requesting =>
    if s.timer ≤ 1 then { st := { phase := .init, xid := s.xid + 1 }, ip := 0, note := some "dhcp timeout" }
    else { st := { s with timer := s.timer - 1 }, ip }
  | .bound =>
    if s.timer ≤ 1 then
      let s := { s with phase := .requesting, timer := retryTicks }
      { st := s, ip, send := some (request s mac ip), note := some "dhcp renewing" }
    else { st := { s with timer := s.timer - 1 }, ip }

end Ember.Spec.Dhcp
