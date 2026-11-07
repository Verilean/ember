import Ember.Spec.Crypto.Sha2

/-!
# Ember.Spec.Crypto.ChaCha — ChaCha20, Poly1305 and their AEAD (RFC 8439; plan M8.5)

Reference implementations.  Poly1305 is computed with `Nat` (mod
2^130 - 5), as the RFC states it.
-/

namespace Ember.Spec.Crypto

def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

def putLe32 (b : ByteArray) (x : UInt32) : ByteArray :=
  b |>.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

@[inline] def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

def quarter (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl32 (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl32 (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl32 (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl32 (s[b]! ^^^ s[c]!) 7)
  return s

/-- One 64-byte block of key stream (RFC 8439 §2.3). -/
def chachaBlock (key : ByteArray) (counter : UInt32) (nonce : ByteArray) : ByteArray := Id.run do
  let init : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
    (List.range 8).toArray.map (fun i => le32 key (4 * i)) ++ #[counter] ++
    (List.range 3).toArray.map (fun i => le32 nonce (4 * i))
  let mut s := init
  for _ in [0:10] do
    s := quarter s 0 4 8 12; s := quarter s 1 5 9 13; s := quarter s 2 6 10 14; s := quarter s 3 7 11 15
    s := quarter s 0 5 10 15; s := quarter s 1 6 11 12; s := quarter s 2 7 8 13; s := quarter s 3 4 9 14
  let mut out := ByteArray.empty
  for i in [0:16] do out := putLe32 out (s[i]! + init[i]!)
  return out

/-- ChaCha20 encryption (§2.4): the key stream from block `counter` on. -/
def chacha20 (key : ByteArray) (counter : UInt32) (nonce msg : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for j in [0:(msg.size + 63) / 64] do
    let ks := chachaBlock key (counter + UInt32.ofNat j) nonce
    for i in [64 * j:min msg.size (64 * j + 64)] do
      out := out.push (msg[i]! ^^^ ks[i - 64 * j]!)
  return out

def leNat (b : ByteArray) : Nat := b.toList.foldr (fun x acc => acc * 256 + x.toNat) 0

def natLe (n len : Nat) : ByteArray := ByteArray.mk ((List.range len).toArray.map fun i => UInt8.ofNat (n >>> (8 * i)))

/-- Poly1305 (§2.5). -/
def poly1305 (key msg : ByteArray) : ByteArray := Id.run do
  let p := 2 ^ 130 - 5
  let r := leNat (key.extract 0 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  let s := leNat (key.extract 16 32)
  let mut acc := 0
  for j in [0:(msg.size + 15) / 16] do
    let blk := msg.extract (16 * j) (min msg.size (16 * j + 16))
    let n := leNat blk + 2 ^ (8 * blk.size)
    acc := (acc + n) * r % p
  return natLe ((acc + s) % 2 ^ 128) 16

def pad16 (b : ByteArray) : ByteArray :=
  if b.size % 16 == 0 then b else b ++ ByteArray.mk (Array.replicate (16 - b.size % 16) 0)

def macData (aad ct : ByteArray) : ByteArray :=
  pad16 aad ++ pad16 ct ++ natLe aad.size 8 ++ natLe ct.size 8

/-- AEAD_CHACHA20_POLY1305 sealing (§2.8): cipher text followed by the 16-byte tag. -/
def aeadSeal (key nonce aad pt : ByteArray) : ByteArray :=
  let otk := (chachaBlock key 0 nonce).extract 0 32
  let ct := chacha20 key 1 nonce pt
  ct ++ poly1305 otk (macData aad ct)

/-- Opening: the plain text, or `none` when the tag does not match. -/
def aeadOpen (key nonce aad ctTag : ByteArray) : Option ByteArray :=
  if ctTag.size < 16 then none else
  let ct := ctTag.extract 0 (ctTag.size - 16)
  let tag := ctTag.extract (ctTag.size - 16) ctTag.size
  let otk := (chachaBlock key 0 nonce).extract 0 32
  if (poly1305 otk (macData aad ct)).toList == tag.toList then some (chacha20 key 1 nonce ct) else none

end Ember.Spec.Crypto
