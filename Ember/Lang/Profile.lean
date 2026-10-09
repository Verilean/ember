import Ember.Lang.Syntax

/-!
# Ember.Lang.Profile — target profiles (M2.5)

C converts any operand narrower than `int` to *signed* `int` before an
operation.  With a 32-bit `int`, `u16 * u16` can overflow a signed int —
undefined behaviour; with SDCC's 16-bit `int`, `u8 * u8` already can
(255·255 > 32767).  The emitter therefore computes every operation in
`opType w`: plain `unsigned` (the unsigned type exactly as wide as `int`)
when the operand fits in it, otherwise the operand's own `uintN_t`, and
truncates the result with an explicit cast.  Unsigned arithmetic wraps,
so no operation can overflow.
-/

namespace Ember.Lang

structure Profile where
  name    : String
  /-- Width of C's `int` (and `unsigned`). -/
  intBits : Nat
  /-- Native register width, for the size/cycle reports. -/
  regBits : Nat
  deriving Inhabited, BEq, Repr

def Profile.host64 : Profile := { name := "host64", intBits := 32, regBits := 64 }
def Profile.rv32 : Profile := { name := "rv32", intBits := 32, regBits := 32 }
def Profile.sdccZ80 : Profile := { name := "sdcc-z80", intBits := 16, regBits := 8 }

def Profile.all : List Profile := [.host64, .rv32, .sdccZ80]

def Profile.ofName? (s : String) : Option Profile := Profile.all.find? (·.name == s)

/-- The C type of an Ember integer width. -/
def cTypeOf (w : Width) : String := s!"uint{w.bits}_t"

/-- The unsigned C type an operation of width `w` is computed in. -/
def Profile.opType (p : Profile) (w : Width) : String :=
  if w.bits ≤ p.intBits then "unsigned" else cTypeOf w

/-- Is an operation of width `w` computed in `unsigned int`? -/
def Profile.promotes (p : Profile) (w : Width) : Bool := w.bits ≤ p.intBits

end Ember.Lang
