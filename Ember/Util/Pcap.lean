import Ember.Trace.Event
import Ember.Util.Pretty

/-!
# Ember.Util.Pcap — write a trace's packets as a pcap file

Link type 101 (`RAW`, IPv4) for SLIP traces — the SLIP framing is
removed — and 1 (Ethernet) for `link=eth` traces.  The timestamp is the
step number in seconds plus the event's index within the step in
microseconds, so packets keep the trace's order in Wireshark.
-/

namespace Ember.Pcap
open Ember Ember.Trace

private def le16 (v : Nat) : List UInt8 := [UInt8.ofNat v, UInt8.ofNat (v / 256)]
private def le32 (v : Nat) : List UInt8 :=
  [UInt8.ofNat v, UInt8.ofNat (v / 0x100), UInt8.ofNat (v / 0x10000), UInt8.ofNat (v / 0x1000000)]

def linkType (link : String) : Nat := if link == "eth" then 1 else 101

def globalHeader (link : String) : ByteArray :=
  Bytes.ofList (le32 0xa1b2c3d4 ++ le16 2 ++ le16 4 ++ le32 0 ++ le32 0 ++ le32 65535 ++
    le32 (linkType link))

def record (sec usec : Nat) (pkt : ByteArray) : ByteArray :=
  Bytes.ofList (le32 sec ++ le32 usec ++ le32 pkt.size ++ le32 pkt.size) ++ pkt

/-- The pcap bytes of every packet in the `rx`/`tx` lines of a trace. -/
def ofTrace (t : Trace) : ByteArray := Id.run do
  let link := t.header.link
  let mut out := globalHeader link
  let mut lastStep := 0
  let mut sub := 0
  for l in t.lines do
    if l.step != lastStep then
      lastStep := l.step
      sub := 0
    match l.ev with
    | .rx b | .tx b =>
      for f in Pretty.frames link b do
        out := out ++ record l.step sub f
        sub := sub + 1
    | _ => pure ()
  return out

end Ember.Pcap
