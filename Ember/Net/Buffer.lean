import Ember.Net.Layout

/-!
# Ember.Net.Buffer — field access and checksums on `buf` (M3.2)

Big-endian reads and writes, and the Internet checksum accumulated in 16
bits with end-around carry — the form `Ember.Spec.Checksum` specifies.
-/

namespace Ember.Net
open Ember.Lang

ember def get16 (o : u16) : u16 := do
  return ((buf[o] : u16) <<< 8) ||| (buf[o + 1] : u16)

ember def get32 (o : u16) : u32 := do
  let hi : u16 ← get16(o)
  let lo : u16 ← get16(o + 2)
  return ((hi : u32) <<< 16) ||| (lo : u32)

ember def set16 (o : u16) (v : u16) := do
  buf[o] := (v >>> 8 : u8)
  buf[o + 1] := (v : u8)

ember def set32 (o : u16) (v : u32) := do
  set16(o, (v >>> 16 : u16))
  set16(o + 2, (v : u16))

/-- One's-complement addition. -/
ember def add16 (a : u16) (b : u16) : u16 := do
  let s : u16 := a + b
  if s < a then
    return s + 1
  return s

/-- One's-complement sum of `buf[o, o+n)`, starting from `init`. -/
ember def csum (o : u16) (n : u16) (init : u16) : u16 := do
  let mut s : u16 := init
  for i in [0, n / 2) do
    let w : u16 ← get16(o + 2 * i)
    s ← add16(s, w)
  if (n &&& 1) == 1 then
    s ← add16(s, (buf[o + n - 1] : u16) <<< 8)
  return s

/-- Sum of the IPv4 pseudo-header. -/
ember def pseudo (src : u32) (dst : u32) (proto : u8) (n : u16) : u16 := do
  let mut s : u16 ← add16((src >>> 16 : u16), (src : u16))
  s ← add16(s, (dst >>> 16 : u16))
  s ← add16(s, (dst : u16))
  s ← add16(s, (proto : u16))
  s ← add16(s, n)
  return s

/-- RFC 1624 eqn. 3. -/
ember def csum_update (hc : u16) (old : u16) (new : u16) : u16 := do
  let mut s : u16 ← add16(~~~hc, ~~~old)
  s ← add16(s, new)
  return ~~~s

ember def verifies (s : u16) : bool := do
  return s == 0xFFFF || s == 0

def fns : List Fn := [get16, get32, set16, set32, add16, csum, pseudo, csum_update, verifies]

end Ember.Net
