import Ember.Lang.Surface
import Ember.Lang.Eval

/-!
# Ember.Lang.Examples — the M2 example library (M2.9)

Small programs written in Ember, each compared with a Lean reference on
random inputs (`Tests.Ember.LangTests`) and, as emitted C, with the
interpreter.  They are also the inputs of the golden C tests.

All of them read the input oracle one item per call of `main`.
-/

namespace Ember.Lang.Examples
open Ember.Lang

/-! ## Internet checksum

Bytes accumulate into a 16-bit one's-complement sum (end-around carry,
never a 32-bit accumulator); a tick emits the checksum of the bytes so
far, big-endian, and starts over. -/
namespace Checksum

ember global sum : u16
ember global hi : u8
ember global odd : bool

ember def csum_add (acc w : u16) : u16 := do
  let s : u16 := acc + w
  if s < acc then
    return s + 1
  return s

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    if odd then
      sum ← csum_add(sum, (hi : u16) <<< 8)
    let c : u16 := ~~~ sum
    out.byte((c >>> 8 : u8))
    out.byte((c : u8))
    out.end()
    sum := 0
    odd := false
    return
  if odd then
    sum ← csum_add(sum, ((hi : u16) <<< 8) ||| k)
    odd := false
  else
    hi := (k : u8)
    odd := true

def prog : Prog := { globals := [sum, hi, odd], fns := [csum_add, main] }

end Checksum

/-! ## SLIP decoder (RFC 1055), byte at a time

The same choices as `Ember.Spec.Slip`: `END` always ends a frame, `ESC`
before an ordinary byte keeps it, empty frames are ignored, a frame over
`MAXLEN` is dropped whole.  Each decoded frame is transmitted. -/
namespace Slip

ember const MAXLEN : u16 := 296
ember global buf : [u8; 296]
ember global len : u16
ember global esc : bool
ember global over : bool

ember def store (b : u8) := do
  if over then
    esc := false
    return
  if len < MAXLEN then
    buf[len] := b
    len := len + 1
  else
    over := true
    len := 0
  esc := false

ember def frame_end := do
  if over then
    trace.drop(0)
  else
    if len > 0 then
      for i in [0, len) do
        out.byte(buf[i])
      out.end()
  len := 0
  esc := false
  over := false

ember def main := do
  let k : u16 ← input.next()
  if k > 0xFF then
    return
  let c : u8 := (k : u8)
  if c == 0xC0 then
    frame_end()
  else
    if esc then
      if c == 0xDC then
        store(0xC0)
      else
        if c == 0xDD then
          store(0xDB)
        else
          store(c)
    else
      if c == 0xDB then
        esc := true
      else
        store(c)

def prog : Prog := { globals := [MAXLEN, buf, len, esc, over], fns := [store, frame_end, main],
                     dropReasons := ["oversize-frame"] }

end Slip

/-! ## SPSC ring buffer

Input bytes are pushed into a 16-byte ring (dropped and counted when it
is full); a tick pops up to 4 bytes and transmits them, then the overrun
count. -/
namespace Ring

ember global ring : [u8; 16]
ember global head : u8
ember global tail : u8
ember global overruns : u8

ember def push (b : u8) := do
  let next : u8 := (head + 1) &&& 15
  if next == tail then
    overruns := overruns + 1
    return
  ring[head] := b
  head := next

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    loop (max := 4) do
      if tail == head then
        break
      out.byte(ring[tail])
      tail := (tail + 1) &&& 15
    out.byte(overruns)
    out.end()
    return
  push((k : u8))

def prog : Prog := { globals := [ring, head, tail, overruns], fns := [push, main] }

end Ring

/-! ## CRC-32 (IEEE 802.3, reflected, bit at a time)

A tick emits the CRC of the bytes since the last tick (little-endian, as
Ethernet sends it) and starts over. -/
namespace Crc32

ember global crc : u32 := 0xFFFFFFFF

ember def update (c : u32) (b : u8) : u32 := do
  let mut x : u32 := c ^^^ (b : u32)
  for i in [0, 8) do
    if (x &&& 1) == 1 then
      x := (x >>> 1) ^^^ 0xEDB88320
    else
      x := x >>> 1
  return x

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    let r : u32 := ~~~ crc
    out.byte((r : u8))
    out.byte((r >>> 8 : u8))
    out.byte((r >>> 16 : u8))
    out.byte((r >>> 24 : u8))
    out.end()
    crc := 0xFFFFFFFF
    return
  crc ← update(crc, (k : u8))

def prog : Prog := { globals := [crc], fns := [update, main] }

end Crc32

/-! ## Every construct

One program using every construct of the language, at least once; its
trace is known (`Tests.Ember.LangTests`), its C is a golden file, and it
runs in the differential tests.  The last statement traps unless the
input byte is below 4. -/
namespace Constructs

ember struct Pair where
  lo : u8
  hi : u32
  bytes : [u8; 4]

ember global p : Pair
ember global tab : [u16; 4] := [10, 20, 30, 40]
ember global flag : bool
ember const LIMIT : u8 := 200

/-- Fill a pair through references. -/
ember def fill (q : ref Pair) (arr : ref [u16; 4]) (v : u8) := do
  q.lo := v
  q.hi := (arr[3] : u32) * 1000
  for i in [0, 4) do
    q.bytes[i] := (i : u8) + v

ember def sum4 (arr : ref [u16; 4]) : u16 := do
  let mut s : u16 := 0
  for i : u8 in [0, 4) do
    s := s + arr[i]
  return s

ember def main := do
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    trace.note(0, 42)
    return
  let b : u8 := (k : u8)
  -- arithmetic modulo 2^w, division by zero, shifts past the width
  out.byte(b + 250)
  out.byte(b * 3)
  out.byte((200 : u8) / (b - b))
  out.byte((200 : u8) % (b - b))
  out.byte((1 : u8) <<< 9)
  out.byte((128 : u8) >>> (b &&& 7))
  out.byte(~~~b)
  out.byte(-b)
  out.byte(((b : u64) <<< 60 >>> 56 : u8))
  out.byte((if b > LIMIT then 1 else 2 : u8))
  out.byte((b > 10 && b < 100 : u8))
  out.byte((!(b == 5) || flag : u8))
  -- records and references
  fill(p, tab, b)
  out.byte(p.lo)
  out.byte((p.hi >>> 8 : u8))
  out.byte(p.bytes[3])
  let s : u16 ← sum4(tab)
  out.byte((s : u8))
  -- loops
  let mut n : u8 := 0
  loop (max := 10) do
    n := n + 1
    if n == 4 then
      break
  out.byte(n)
  for j in [0, (3 : u8)) do
    if j == 1 then
      break
    out.byte(j)
  -- out of range unless the byte is small: the trap is part of the test
  out.byte(p.bytes[b])
  out.end()
  flag := !flag
  mmio.write32(0x1000, (b : u32))
  let r : u32 ← mmio.read32(0x1000)
  if r != (b : u32) then
    trace.drop(0)

def prog : Prog := { structs := [Pair], globals := [p, tab, flag, LIMIT], fns := [fill, sum4, main],
                     dropReasons := ["mmio-mismatch"], notes := ["tick"] }

end Constructs

/-- Every example, by name (for `ember-emit` and the tests). -/
def all : List (String × Prog) :=
  [("checksum", Checksum.prog), ("slip", Slip.prog), ("ring", Ring.prog), ("crc32", Crc32.prog),
   ("constructs", Constructs.prog)]

end Ember.Lang.Examples
