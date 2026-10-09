import Ember.Spec.Slip
import Ember.Spec.Ipv4
import Ember.Util.Str

/-!
# Ember.Util.Pretty — the one packet decoder

Every implementation's `pkt` lines and every field-by-field comparison in
`ember-diff` go through this decoder, so two implementations never
disagree about how a packet is *printed* (plan §3.1).
-/

namespace Ember.Pretty
open Ember Ember.Spec

def ip := Ipv4.ipToString

def macToString (b : ByteArray) (off : Nat) : String :=
  ":".intercalate ((List.range 6).map fun i => Bytes.hex8 (Bytes.get b (off + i)))

def tcpFlags (f : UInt8) : String :=
  let pick (bit : UInt8) (c : String) := if f &&& bit != 0 then c else ""
  let s := pick 0x02 "S" ++ pick 0x01 "F" ++ pick 0x04 "R" ++ pick 0x08 "P" ++ pick 0x10 "."
  "[" ++ (if s.isEmpty then "none" else s) ++ "]"

/-- Named fields of an IPv4 packet, in wire order. -/
def ipFields (p : ByteArray) : List (String × String) := Id.run do
  if p.size < 20 then return [("ipv4.truncated", toString p.size)]
  let g8 i := toString (Bytes.get p i).toNat
  let g16 i := toString (Bytes.get16 p i).toNat
  let g32 i := toString (Bytes.get32 p i).toNat
  let ihl := ((Bytes.get p 0) &&& 0x0F).toNat * 4
  let proto := Bytes.get p 9
  let mut fs := [("ipv4.ver", toString ((Bytes.get p 0) >>> 4).toNat), ("ipv4.ihl", toString ihl),
    ("ipv4.tos", g8 1), ("ipv4.len", g16 2), ("ipv4.id", g16 4),
    ("ipv4.flags", toString ((Bytes.get16 p 6) >>> 13).toNat),
    ("ipv4.frag", toString ((Bytes.get16 p 6) &&& 0x1FFF).toNat),
    ("ipv4.ttl", g8 8), ("ipv4.proto", g8 9), ("ipv4.csum", g16 10),
    ("ipv4.src", ip (Bytes.get32 p 12)), ("ipv4.dst", ip (Bytes.get32 p 16))]
  let o := ihl
  let pl := p.size - o
  let g8o i := g8 (o + i)
  let g16o i := g16 (o + i)
  if proto == 1 && pl ≥ 8 then
    fs := fs ++ [("icmp.type", g8o 0), ("icmp.code", g8o 1), ("icmp.csum", g16o 2),
                 ("icmp.id", g16o 4), ("icmp.seq", g16o 6), ("icmp.data", toString (pl - 8))]
  else if proto == 17 && pl ≥ 8 then
    fs := fs ++ [("udp.sport", g16o 0), ("udp.dport", g16o 2), ("udp.len", g16o 4),
                 ("udp.csum", g16o 6), ("udp.data", Bytes.toHex (Bytes.slice p (o+8) (pl-8)))]
  else if proto == 6 && pl ≥ 20 then
    let off := ((Bytes.get p (o+12)) >>> 4).toNat * 4
    fs := fs ++ [("tcp.sport", g16o 0), ("tcp.dport", g16o 2), ("tcp.seq", g32 (o+4)),
                 ("tcp.ack", g32 (o+8)), ("tcp.off", toString off),
                 ("tcp.flags", tcpFlags (Bytes.get p (o+13))), ("tcp.win", g16o 14),
                 ("tcp.csum", g16o 16), ("tcp.urg", g16o 18),
                 ("tcp.opts", Bytes.toHex (Bytes.slice p (o+20) (off - 20))),
                 ("tcp.data", Bytes.toHex (Bytes.slice p (o+off) (pl - off)))]
  else if pl > 0 then
    fs := fs ++ [("ipv4.payload", Bytes.toHex (Bytes.slice p o pl))]
  return fs

/-- One-line summary of an IPv4 packet. -/
def ipSummary (p : ByteArray) : String := Id.run do
  if p.size < 20 then return s!"ipv4 truncated len={p.size}"
  let ihl := ((Bytes.get p 0) &&& 0x0F).toNat * 4
  let proto := Bytes.get p 9
  let pre := s!"ipv4 {ip (Bytes.get32 p 12)}>{ip (Bytes.get32 p 16)}"
  let o := ihl
  let pl := p.size - min o p.size
  let len := (Bytes.get16 p 2).toNat
  if proto == 1 && pl ≥ 8 then
    let ty := Bytes.get p o
    let kind := if ty == 8 then "echo-req" else if ty == 0 then "echo-rep" else s!"type={ty.toNat}"
    return s!"{pre} icmp {kind} id={(Bytes.get16 p (o+4)).toNat} seq={(Bytes.get16 p (o+6)).toNat} len={len}"
  if proto == 17 && pl ≥ 8 then
    return s!"{pre} udp {(Bytes.get16 p o).toNat}>{(Bytes.get16 p (o+2)).toNat} len={len}"
  if proto == 6 && pl ≥ 20 then
    let off := ((Bytes.get p (o+12)) >>> 4).toNat * 4
    return s!"{pre} tcp {(Bytes.get16 p o).toNat}>{(Bytes.get16 p (o+2)).toNat} {tcpFlags (Bytes.get p (o+13))} seq={(Bytes.get32 p (o+4)).toNat} ack={(Bytes.get32 p (o+8)).toNat} win={(Bytes.get16 p (o+14)).toNat} data={pl - min off pl}"
  return s!"{pre} proto={proto.toNat} len={len}"

/-! Ethernet II / ARP frames (the M1.11 link layer). -/

def arpFields (p : ByteArray) (o : Nat) : List (String × String) :=
  [("arp.op", toString (Bytes.get16 p (o+6)).toNat),
   ("arp.sha", macToString p (o+8)), ("arp.spa", ip (Bytes.get32 p (o+14))),
   ("arp.tha", macToString p (o+18)), ("arp.tpa", ip (Bytes.get32 p (o+24)))]

def ethFields (f : ByteArray) : List (String × String) :=
  if f.size < 14 then [("eth.truncated", toString f.size)] else
  let ty := Bytes.get16 f 12
  let base := [("eth.dst", macToString f 0), ("eth.src", macToString f 6),
               ("eth.type", "0x" ++ Bytes.hex8 (ty >>> 8).toUInt8 ++ Bytes.hex8 ty.toUInt8)]
  let rest := f.extract 14 f.size
  if ty == 0x0800 then base ++ ipFields rest
  else if ty == 0x0806 && rest.size ≥ 28 then base ++ arpFields f 14
  else base

def ethSummary (f : ByteArray) : String :=
  if f.size < 14 then s!"eth truncated len={f.size}" else
  let ty := Bytes.get16 f 12
  let pre := s!"eth {macToString f 6}>{macToString f 0}"
  if ty == 0x0800 then pre ++ " " ++ ipSummary (f.extract 14 f.size)
  else if ty == 0x0806 && f.size ≥ 42 then
    let op := Bytes.get16 f 20
    if op == 1 then s!"{pre} arp who-has {ip (Bytes.get32 f 38)} tell {ip (Bytes.get32 f 28)}"
    else if op == 2 then s!"{pre} arp {ip (Bytes.get32 f 28)} is-at {macToString f 22}"
    else s!"{pre} arp op={op.toNat}"
  else s!"{pre} type=0x{Bytes.hex8 (ty >>> 8).toUInt8}{Bytes.hex8 ty.toUInt8} len={f.size}"

/-- Packets carried by the raw bytes of an `rx`/`tx` line on a given link. -/
def frames (link : String) (raw : ByteArray) : List ByteArray :=
  if link == "eth" then [raw] else Slip.decodeAll raw (maxLen := 65535)

def summary (link : String) (frame : ByteArray) : String :=
  if link == "eth" then ethSummary frame else ipSummary frame

def fields (link : String) (frame : ByteArray) : List (String × String) :=
  if link == "eth" then ethFields frame else ipFields frame

end Ember.Pretty
