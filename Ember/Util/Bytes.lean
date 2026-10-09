/-!
# Ember.Util.Bytes

Byte-buffer helpers shared by every Ember layer: big-endian field access
on `ByteArray`, construction from lists, hex encoding and decoding.

All accessors are total: reads out of range return 0 and writes out of
range are ignored.  Callers check lengths before parsing; the totality
only keeps the reference stack free of panics on malformed input.
-/

namespace Ember.Bytes

/-- Byte at `i`, or 0 when out of range. -/
@[inline] def get (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- Overwrite byte `i` (no-op when out of range). -/
@[inline] def set (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if i < b.size then b.set! i v else b

/-- Big-endian 16-bit read. -/
def get16 (b : ByteArray) (i : Nat) : UInt16 :=
  ((get b i).toUInt16 <<< 8) ||| (get b (i+1)).toUInt16

/-- Big-endian 32-bit read. -/
def get32 (b : ByteArray) (i : Nat) : UInt32 :=
  ((get b i).toUInt32 <<< 24) ||| ((get b (i+1)).toUInt32 <<< 16) |||
  ((get b (i+2)).toUInt32 <<< 8) ||| (get b (i+3)).toUInt32

/-- Big-endian 16-bit write. -/
def set16 (b : ByteArray) (i : Nat) (v : UInt16) : ByteArray :=
  (set b i (v >>> 8).toUInt8) |> (set · (i+1) v.toUInt8)

/-- Big-endian 32-bit write. -/
def set32 (b : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  let b := set b i (v >>> 24).toUInt8
  let b := set b (i+1) (v >>> 16).toUInt8
  let b := set b (i+2) (v >>> 8).toUInt8
  set b (i+3) v.toUInt8

def be16 (v : UInt16) : List UInt8 := [(v >>> 8).toUInt8, v.toUInt8]
def be32 (v : UInt32) : List UInt8 :=
  [(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

def ofList (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `b[off, off+len)`, clipped to the buffer. -/
def slice (b : ByteArray) (off len : Nat) : ByteArray :=
  b.extract off (off + len)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Two lower-case hex digits. -/
def hex8 (v : UInt8) : String :=
  String.ofList [hexDigit (v.toNat / 16), hexDigit (v.toNat % 16)]

/-- Bytes as space-separated hex pairs: `c0 45 00`. -/
def toHex (b : ByteArray) : String :=
  " ".intercalate (b.toList.map hex8)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Parse hex pairs, ignoring whitespace.  `none` on a bad digit or an
odd number of digits. -/
def ofHex (s : String) : Option ByteArray := Id.run do
  let ds := s.toList.filter (fun c => !c.isWhitespace)
  let mut out := ByteArray.empty
  let mut rest := ds
  while true do
    match rest with
    | [] => return some out
    | [_] => return none
    | a :: b :: r =>
      match hexVal a, hexVal b with
      | some x, some y => out := out.push (UInt8.ofNat (x * 16 + y)); rest := r
      | _, _ => return none
  return none

/-- Classic hex dump, 16 bytes per line, with offsets. -/
def hexDump (b : ByteArray) : String := Id.run do
  let mut s := ""
  let mut i := 0
  while i < b.size do
    let row := slice b i 16
    let off := String.ofList ((Nat.toDigits 16 i).leftpad 4 '0')
    s := s ++ off ++ "  " ++ toHex row ++ "\n"
    i := i + 16
  return s

end Ember.Bytes
