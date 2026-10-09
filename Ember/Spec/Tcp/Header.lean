import Ember.Spec.Ipv4

/-!
# Ember.Spec.Tcp.Header — segment parsing and emission

Checks, in order: fewer than 20 bytes `short-tcp`; data offset < 20 or
beyond the segment `bad-tcp-header`; checksum `bad-tcp-checksum`.
Options: MSS (kind 2, length 4) is read; NOP and every other option of
a valid length are skipped; a malformed option ends option parsing
(the segment is still processed).  The only option Ember sends is MSS,
on SYN-ACK.
-/

namespace Ember.Spec.Tcp
open Ember

def FIN : UInt8 := 0x01
def SYN : UInt8 := 0x02
def RST : UInt8 := 0x04
def PSH : UInt8 := 0x08
def ACK : UInt8 := 0x10

@[inline] def has (flags f : UInt8) : Bool := flags &&& f != 0

structure Seg where
  sport : UInt16
  dport : UInt16
  seq   : UInt32
  ack   : UInt32
  flags : UInt8
  wnd   : UInt16
  mss   : Option UInt16 := none
  data  : ByteArray := .empty
  deriving Inhabited

/-- Sequence space taken by the segment: data plus SYN and FIN. -/
def Seg.len (s : Seg) : Nat :=
  s.data.size + (if has s.flags SYN then 1 else 0) + (if has s.flags FIN then 1 else 0)

/-- Parse the MSS option from `p[20, off)`. -/
def parseMss (p : ByteArray) (off : Nat) : Option UInt16 := Id.run do
  let mut i := 20
  let mut mss : Option UInt16 := none
  for _ in [0:40] do
    if i ≥ off then break
    let k := Bytes.get p i
    if k == 0 then break
    if k == 1 then
      i := i + 1
      continue
    if i + 1 ≥ off then break
    let l := (Bytes.get p (i+1)).toNat
    if l < 2 || i + l > off then break
    if k == 2 && l == 4 then mss := some (Bytes.get16 p (i+2))
    i := i + l
  return mss

def parse (src dst : UInt32) (p : ByteArray) : Except String Seg := do
  if p.size < 20 then throw "short-tcp"
  let off := ((Bytes.get p 12) >>> 4).toNat * 4
  if off < 20 || off > p.size then throw "bad-tcp-header"
  let s := Checksum.sum p 0 p.size (Checksum.pseudo src dst Ipv4.protoTcp p.size)
  if !Checksum.verifies s then throw "bad-tcp-checksum"
  return { sport := Bytes.get16 p 0, dport := Bytes.get16 p 2,
           seq := Bytes.get32 p 4, ack := Bytes.get32 p 8,
           flags := Bytes.get p 13 &&& 0x3F, wnd := Bytes.get16 p 14,
           mss := parseMss p off, data := Bytes.slice p off (p.size - off) }

/-- Serialise a segment with its checksum; `mss` adds the MSS option. -/
def emit (src dst : UInt32) (s : Seg) : ByteArray :=
  let opts := match s.mss with
    | some m => [2, 4] ++ Bytes.be16 m
    | none => []
  let off := 20 + opts.length
  let h := Bytes.be16 s.sport ++ Bytes.be16 s.dport ++ Bytes.be32 s.seq ++ Bytes.be32 s.ack ++
    [UInt8.ofNat ((off / 4) * 16), s.flags] ++ Bytes.be16 s.wnd ++ [0, 0, 0, 0] ++ opts
  let d := Bytes.ofList h ++ s.data
  Bytes.set16 d 16 (Checksum.checksum d 0 d.size (Checksum.pseudo src dst Ipv4.protoTcp d.size))

end Ember.Spec.Tcp
