import Ember.Spec.Config

/-!
# Ember.Spec.Slip — RFC 1055 framing

The decoder is a byte-at-a-time state machine, as the runtime feeds it.
Choices where RFC 1055 leaves room (they follow the Linux driver):

* `END` always ends a frame, even right after `ESC`;
* `ESC` followed by anything other than `ESC_END`/`ESC_ESC` stores that
  byte unchanged;
* empty frames (back-to-back `END`s) are ignored;
* a frame longer than the MTU is dropped as a whole (`oversize-frame`).

The encoder writes `END payload END` (the double-END convention).
-/

namespace Ember.Spec.Slip

def END : UInt8 := 0xC0
def ESC : UInt8 := 0xDB
def ESC_END : UInt8 := 0xDC
def ESC_ESC : UInt8 := 0xDD

structure Dec where
  buf  : ByteArray := .empty
  esc  : Bool := false
  over : Bool := false
  deriving Inhabited

inductive Result where
  | none
  | frame (b : ByteArray)
  | drop (reason : String)

/-- Store a decoded payload byte, switching to the oversize state at the limit. -/
def Dec.store (d : Dec) (v : UInt8) (maxLen : Nat) : Dec :=
  if d.over then { d with esc := false }
  else if d.buf.size < maxLen then { d with buf := d.buf.push v, esc := false }
  else { d with over := true, esc := false, buf := .empty }

/-- Feed one byte. -/
def Dec.feed (d : Dec) (c : UInt8) (maxLen : Nat := mtu) : Dec × Result :=
  if c == END then
    let r := if d.over then Result.drop "oversize-frame"
             else if d.buf.size == 0 then Result.none
             else Result.frame d.buf
    ({}, r)
  else if d.esc then
    let v := if c == ESC_END then END else if c == ESC_ESC then ESC else c
    (d.store v maxLen, .none)
  else if c == ESC then ({ d with esc := true }, .none)
  else (d.store c maxLen, .none)

/-- Escape one payload byte. -/
def encodeByte (b : UInt8) : List UInt8 :=
  if b == END then [ESC, ESC_END] else if b == ESC then [ESC, ESC_ESC] else [b]

def encode (p : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty.push END
  for b in p.toList do
    for e in encodeByte b do out := out.push e
  return out.push END

/-- Decode a whole byte stream into its frames (drops omitted). -/
def decodeAll (s : ByteArray) (maxLen : Nat := mtu) : List ByteArray := Id.run do
  let mut d : Dec := {}
  let mut out : Array ByteArray := #[]
  for c in s.toList do
    let (d', r) := d.feed c maxLen
    d := d'
    if let .frame f := r then out := out.push f
  return out.toList

end Ember.Spec.Slip
