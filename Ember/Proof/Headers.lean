import Ember.Spec.Udp
import Ember.Spec.Tcp.Header
import Ember.Proof.Checksum

/-!
# Ember.Proof.Headers — header parse ∘ emit = id (plan M5.2)

For each of IPv4, UDP and TCP: what the Spec's emitter writes, the
Spec's parser reads back, including the checksum it verifies.

* `Ipv4.validate_packet`: under `20 + payload.size ≤ 65535` (the total
  length field), a destination that is ours or broadcast, and a non-zero
  TTL;
* `Udp.parse_emit`: under `8 + data.size ≤ 65535` (the length field);
* `Tcp.parse_emit`: under `flags &&& 0x3F = flags` (the parser masks the
  two reserved bits); no length condition, since TCP has no length field
  and both sides put the same `UInt16.ofNat` of the size in the
  pseudo-header.
-/

namespace Ember.Bytes

/-- A 16-bit read from its two bytes. -/
theorem get16_eq {b : ByteArray} {i : Nat} {v : UInt16} (h1 : get b i = (v >>> 8).toUInt8)
    (h2 : get b (i + 1) = v.toUInt8) : get16 b i = v := by
  rw [get16, h1, h2, join16]

/-- A 32-bit read from its four bytes. -/
theorem get32_eq {b : ByteArray} {i : Nat} {v : UInt32} (h1 : get b i = (v >>> 24).toUInt8)
    (h2 : get b (i + 1) = (v >>> 16).toUInt8) (h3 : get b (i + 2) = (v >>> 8).toUInt8)
    (h4 : get b (i + 3) = v.toUInt8) : get32 b i = v := by
  rw [get32, h1, h2, h3, h4, join32]

theorem getD_append_left {l l' : List UInt8} {i : Nat} (h : i < l.length) (d : UInt8) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l l' : List UInt8} {i : Nat} (h : l.length ≤ i) (d : UInt8) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

end Ember.Bytes

namespace Ember.Spec.Ipv4
open Ember

/-- `validate` accepts a packet with a 20-byte header that passes every
check, and returns the header fields and the payload. -/
theorem validate_ok {p : ByteArray} {ourIp : UInt32} (hsz : 20 ≤ p.size) (h0 : Bytes.get p 0 = 0x45)
    (hsum : Checksum.sum p 0 20 = 0xFFFF)
    (htl1 : 20 ≤ (Bytes.get16 p 2).toNat) (htl2 : (Bytes.get16 p 2).toNat ≤ p.size)
    (hff : Bytes.get16 p 6 &&& 0x3FFF = 0) (httl : Bytes.get p 8 ≠ 0)
    (hdst : Bytes.get32 p 16 = ourIp ∨ Bytes.get32 p 16 = broadcast) :
    validate p ourIp = .ok
      ({ ihl := 20, totalLen := (Bytes.get16 p 2).toNat, id := Bytes.get16 p 4, ttl := Bytes.get p 8,
         proto := Bytes.get p 9, src := Bytes.get32 p 12, dst := Bytes.get32 p 16 },
       Bytes.slice p 20 ((Bytes.get16 p 2).toNat - 20)) := by
  have h1 : ¬ p.size < 20 := by omega
  have h2 : ((0x45 : UInt8) >>> 4 != 4) = false := by decide
  have h3 : ((0x45 : UInt8) &&& 0x0F).toNat * 4 = 20 := by decide
  have h4 : ¬ (Bytes.get16 p 2).toNat < 20 := by omega
  have h5 : ¬ (Bytes.get16 p 2).toNat > p.size := by omega
  have h6 : (Bytes.get32 p 16 != ourIp && Bytes.get32 p 16 != broadcast) = false := by
    rcases hdst with h | h <;> simp [h]
  simp [validate, h0, h1, h2, hsum, Checksum.verifies, h4, h5, hff, httl, h6]
  rfl

/-- The header bytes before the checksum is filled in. -/
def headerBytes (proto : UInt8) (id : UInt16) (src dst : UInt32) (payloadLen : Nat) (ttl : UInt8) :
    List UInt8 :=
  [0x45, 0x00, (UInt16.ofNat (20 + payloadLen) >>> 8).toUInt8, (UInt16.ofNat (20 + payloadLen)).toUInt8,
   (id >>> 8).toUInt8, id.toUInt8, if dfFor proto then 0x40 else 0x00, 0x00, ttl, proto, 0x00, 0x00,
   (src >>> 24).toUInt8, (src >>> 16).toUInt8, (src >>> 8).toUInt8, src.toUInt8,
   (dst >>> 24).toUInt8, (dst >>> 16).toUInt8, (dst >>> 8).toUInt8, dst.toUInt8]

theorem header_eq (proto : UInt8) (id : UInt16) (src dst : UInt32) (payloadLen : Nat) (ttl : UInt8) :
    header proto id src dst payloadLen ttl =
      Bytes.set16 (Bytes.ofList (headerBytes proto id src dst payloadLen ttl)) 10
        (Checksum.checksum (Bytes.ofList (headerBytes proto id src dst payloadLen ttl)) 0 20) := rfl

@[simp] theorem size_header (proto : UInt8) (id : UInt16) (src dst : UInt32) (payloadLen : Nat)
    (ttl : UInt8) : (header proto id src dst payloadLen ttl).size = 20 := by
  simp [header_eq, headerBytes]

/-- The header of `header` sums to `0xFFFF`: its checksum verifies. -/
theorem sum_header (proto : UInt8) (id : UInt16) (src dst : UInt32) (payloadLen : Nat) (ttl : UInt8) :
    Checksum.sum (header proto id src dst payloadLen ttl) 0 20 = 0xFFFF := by
  rw [header_eq]
  exact Checksum.sum_set16_checksum (off := 0) (k := 5) (len := 20) (by decide)
    (by simp [headerBytes]) (by simp [Bytes.get16, Bytes.get_ofList, headerBytes]) 0

/-- M5.2, IPv4: `validate` reads back the header `header` wrote and
returns the payload, when the total length fits its 16-bit field, the
TTL is not zero and the destination is ours or broadcast. -/
theorem validate_header_append (proto : UInt8) (id : UInt16) (src dst : UInt32) (payload : ByteArray)
    (ttl : UInt8) (ourIp : UInt32) (hlen : 20 + payload.size ≤ 65535) (httl : ttl ≠ 0)
    (hdst : dst = ourIp ∨ dst = broadcast) :
    validate (header proto id src dst payload.size ttl ++ payload) ourIp = .ok
      ({ ihl := 20, totalLen := 20 + payload.size, id, ttl, proto, src, dst }, payload) := by
  have hsize : (header proto id src dst payload.size ttl).size = 20 := size_header ..
  -- every header byte of the packet is the corresponding byte of `header`
  have hget : ∀ i, i < 20 → Bytes.get (header proto id src dst payload.size ttl ++ payload) i
      = Bytes.get (header proto id src dst payload.size ttl) i := by
    intro i hi; rw [Bytes.get_append, if_pos (by omega)]
  have hb : ∀ i, i < 20 → i ≠ 10 → i ≠ 11 →
      Bytes.get (header proto id src dst payload.size ttl ++ payload) i
        = (headerBytes proto id src dst payload.size ttl).getD i 0 := by
    intro i hi h10 h11
    rw [hget i hi, header_eq, Bytes.get_set16_ne (by omega), Bytes.get_ofList]
  have htl : Bytes.get16 (header proto id src dst payload.size ttl ++ payload) 2
      = UInt16.ofNat (20 + payload.size) :=
    Bytes.get16_eq (by rw [hb 2 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 3 (by decide) (by decide) (by decide)]; rfl)
  have htl' : (UInt16.ofNat (20 + payload.size)).toNat = 20 + payload.size := by
    simp [UInt16.toNat_ofNat']; omega
  have hid : Bytes.get16 (header proto id src dst payload.size ttl ++ payload) 4 = id :=
    Bytes.get16_eq (by rw [hb 4 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 5 (by decide) (by decide) (by decide)]; rfl)
  have hsrc : Bytes.get32 (header proto id src dst payload.size ttl ++ payload) 12 = src :=
    Bytes.get32_eq (by rw [hb 12 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 13 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 14 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 15 (by decide) (by decide) (by decide)]; rfl)
  have hdst' : Bytes.get32 (header proto id src dst payload.size ttl ++ payload) 16 = dst :=
    Bytes.get32_eq (by rw [hb 16 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 17 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 18 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hb 19 (by decide) (by decide) (by decide)]; rfl)
  have hff : Bytes.get16 (header proto id src dst payload.size ttl ++ payload) 6 &&& 0x3FFF = 0 := by
    rw [Bytes.get16, hb 6 (by decide) (by decide) (by decide), hb 7 (by decide) (by decide) (by decide)]
    simp only [headerBytes]
    cases dfFor proto <;> simp <;> decide
  have h8 : Bytes.get (header proto id src dst payload.size ttl ++ payload) 8 = ttl := by
    rw [hb 8 (by decide) (by decide) (by decide)]; rfl
  have h9 : Bytes.get (header proto id src dst payload.size ttl ++ payload) 9 = proto := by
    rw [hb 9 (by decide) (by decide) (by decide)]; rfl
  have hsum : Checksum.sum (header proto id src dst payload.size ttl ++ payload) 0 20 = 0xFFFF := by
    rw [← sum_header proto id src dst payload.size ttl]
    exact Checksum.sum_congr (fun i hi => by simpa using hget i hi) 0
  have hres := validate_ok (p := header proto id src dst payload.size ttl ++ payload) (ourIp := ourIp)
    (by rw [ByteArray.size_append, hsize]; omega)
    (by rw [hb 0 (by decide) (by decide) (by decide)]; rfl) hsum
    (by rw [htl, htl']; omega) (by rw [htl, htl', ByteArray.size_append, hsize]; omega) hff
    (by rw [h8]; exact httl) (by rw [hdst']; exact hdst)
  rw [hres, htl, htl', hid, h8, h9, hsrc, hdst']
  have hsl : Bytes.slice (header proto id src dst payload.size ttl ++ payload) 20
      (20 + payload.size - 20) = payload := by
    have := Bytes.slice_append_right (header proto id src dst payload.size ttl) payload
    rw [hsize] at this
    rwa [Nat.add_sub_cancel_left]
  rw [hsl]

/-- The same for `packet`, which uses the default TTL. -/
theorem validate_packet (proto : UInt8) (id : UInt16) (src dst : UInt32) (payload : ByteArray)
    (ourIp : UInt32) (hlen : 20 + payload.size ≤ 65535) (hdst : dst = ourIp ∨ dst = broadcast) :
    validate (packet proto id src dst payload) ourIp = .ok
      ({ ihl := 20, totalLen := 20 + payload.size, id, ttl := ttlDefault, proto, src, dst }, payload) :=
  validate_header_append proto id src dst payload ttlDefault ourIp hlen (by decide) hdst

end Ember.Spec.Ipv4

namespace Ember.Spec.Udp
open Ember

/-- `parse` accepts a datagram that passes every check. -/
theorem parse_ok {src dst : UInt32} {p : ByteArray} (hsz : 8 ≤ p.size)
    (hul1 : 8 ≤ (Bytes.get16 p 4).toNat) (hul2 : (Bytes.get16 p 4).toNat ≤ p.size)
    (hsum : Checksum.sum p 0 (Bytes.get16 p 4).toNat
      (Checksum.pseudo src dst Ipv4.protoUdp (Bytes.get16 p 4).toNat) = 0xFFFF) :
    parse src dst p = .ok
      { sport := Bytes.get16 p 0, dport := Bytes.get16 p 2,
        data := Bytes.slice p 8 ((Bytes.get16 p 4).toNat - 8) } := by
  have h1 : ¬ p.size < 8 := by omega
  have h2 : ¬ (Bytes.get16 p 4).toNat < 8 := by omega
  have h3 : ¬ (Bytes.get16 p 4).toNat > p.size := by omega
  simp [parse, h1, h2, h3, hsum, Checksum.verifies]
  rfl

/-- M5.2, UDP: `parse` reads back what `emit` wrote, when the datagram
length fits its 16-bit field. -/
theorem parse_emit (src dst : UInt32) (sport dport : UInt16) (data : ByteArray)
    (hlen : 8 + data.size ≤ 65535) :
    parse src dst (emit src dst sport dport data) = .ok { sport, dport, data } := by
  -- the emitted datagram: header bytes with the checksum, then the data
  let hb : List UInt8 := [(sport >>> 8).toUInt8, sport.toUInt8, (dport >>> 8).toUInt8, dport.toUInt8,
    (UInt16.ofNat (8 + data.size) >>> 8).toUInt8, (UInt16.ofNat (8 + data.size)).toUInt8, 0, 0]
  let d := Bytes.ofList hb ++ data
  let c := Checksum.checksum d 0 (8 + data.size) (Checksum.pseudo src dst Ipv4.protoUdp (8 + data.size))
  let v : UInt16 := if c == 0 then 0xFFFF else c
  have hemit : emit src dst sport dport data = Bytes.set16 (Bytes.ofList hb) 6 v ++ data := by
    show Bytes.set16 d 6 v = _
    exact Bytes.set16_append_left (by simp [hb]) v
  have hsz8 : (Bytes.set16 (Bytes.ofList hb) 6 v).size = 8 := by simp [hb]
  have hget : ∀ i, i < 6 → Bytes.get (emit src dst sport dport data) i = hb.getD i 0 := by
    intro i hi
    rw [hemit, Bytes.get_append, if_pos (by omega), Bytes.get_set16_ne (by omega), Bytes.get_ofList]
  have hsport : Bytes.get16 (emit src dst sport dport data) 0 = sport :=
    Bytes.get16_eq (by rw [hget 0 (by decide)]; rfl) (by rw [hget 1 (by decide)]; rfl)
  have hdport : Bytes.get16 (emit src dst sport dport data) 2 = dport :=
    Bytes.get16_eq (by rw [hget 2 (by decide)]; rfl) (by rw [hget 3 (by decide)]; rfl)
  have hul : Bytes.get16 (emit src dst sport dport data) 4 = UInt16.ofNat (8 + data.size) :=
    Bytes.get16_eq (by rw [hget 4 (by decide)]; rfl) (by rw [hget 5 (by decide)]; rfl)
  have hul' : (UInt16.ofNat (8 + data.size)).toNat = 8 + data.size := by
    simp [UInt16.toNat_ofNat']; omega
  have hsize : (emit src dst sport dport data).size = 8 + data.size := by
    rw [hemit, ByteArray.size_append, hsz8]
  have hsum : Checksum.sum (emit src dst sport dport data) 0 (8 + data.size)
      (Checksum.pseudo src dst Ipv4.protoUdp (8 + data.size)) = 0xFFFF := by
    show Checksum.sum (Bytes.set16 d 6 v) 0 (8 + data.size) _ = _
    exact Checksum.sum_set16_checksum_nonzero (off := 0) (k := 3) (by omega)
      (by simp [d, hb, ByteArray.size_append]; omega)
      (by
        have : Bytes.get16 d 6 = Bytes.get16 (Bytes.ofList hb) 6 :=
          Bytes.get16_append_left (by simp [hb])
        rw [show 0 + 2 * 3 = 6 from rfl, this]
        simp [Bytes.get16, Bytes.get_ofList, hb]) _
  have hres := parse_ok (src := src) (dst := dst) (p := emit src dst sport dport data)
    (by rw [hsize]; omega) (by rw [hul, hul']; omega) (by rw [hul, hul', hsize]; omega)
    (by rw [hul, hul']; exact hsum)
  rw [hres, hsport, hdport, hul, hul', hemit]
  have hsl : Bytes.slice (Bytes.set16 (Bytes.ofList hb) 6 v ++ data) 8 (8 + data.size - 8) = data := by
    have := Bytes.slice_append_right (Bytes.set16 (Bytes.ofList hb) 6 v) data
    rw [hsz8] at this
    rwa [Nat.add_sub_cancel_left]
  rw [hsl]

end Ember.Spec.Udp

namespace Ember.Spec.Tcp
open Ember

/-- Without options (data offset 20) there is no MSS. -/
theorem parseMss_20 (p : ByteArray) : parseMss p 20 = none := by
  simp [parseMss, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ]

/-- The one option `emit` writes: kind 2, length 4, then the MSS. -/
theorem parseMss_24 {p : ByteArray} {m : UInt16} (h20 : Bytes.get p 20 = 2) (h21 : Bytes.get p 21 = 4)
    (h22 : Bytes.get16 p 22 = m) : parseMss p 24 = some m := by
  simp [parseMss, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ, h20, h21, h22]

/-- `parse` accepts a segment that passes every check. -/
theorem parse_ok {src dst : UInt32} {p : ByteArray} {off : Nat} (hsz : 20 ≤ p.size)
    (hoff : ((Bytes.get p 12) >>> 4).toNat * 4 = off) (h20 : 20 ≤ off) (hle : off ≤ p.size)
    (hsum : Checksum.sum p 0 p.size (Checksum.pseudo src dst Ipv4.protoTcp p.size) = 0xFFFF) :
    parse src dst p = .ok
      { sport := Bytes.get16 p 0, dport := Bytes.get16 p 2, seq := Bytes.get32 p 4,
        ack := Bytes.get32 p 8, flags := Bytes.get p 13 &&& 0x3F, wnd := Bytes.get16 p 14,
        mss := parseMss p off, data := Bytes.slice p off (p.size - off) } := by
  have h1 : ¬ p.size < 20 := by omega
  have h2 : ¬ off < 20 := by omega
  have h3 : ¬ off > p.size := by omega
  have e : (Bytes.get p 12 >>> 4).toNat = (Bytes.get p 12).toNat >>> 4 := by simp
  rw [e] at hoff
  simp [parse, h1, hoff, h2, h3, hsum, Checksum.verifies]
  rfl

/-- The fixed part of the header `emit` writes, checksum and urgent pointer zero. -/
def headerBytes (s : Seg) (off : Nat) : List UInt8 :=
  [(s.sport >>> 8).toUInt8, s.sport.toUInt8, (s.dport >>> 8).toUInt8, s.dport.toUInt8,
   (s.seq >>> 24).toUInt8, (s.seq >>> 16).toUInt8, (s.seq >>> 8).toUInt8, s.seq.toUInt8,
   (s.ack >>> 24).toUInt8, (s.ack >>> 16).toUInt8, (s.ack >>> 8).toUInt8, s.ack.toUInt8,
   UInt8.ofNat ((off / 4) * 16), s.flags, (s.wnd >>> 8).toUInt8, s.wnd.toUInt8, 0, 0, 0, 0]

/-- Reading back a segment made of `headerBytes`, options `opts`
(`off = 20 + opts.length`) and data, with the checksum filled in. -/
private theorem parse_emit_aux (src dst : UInt32) (s : Seg) (opts : List UInt8) (off : Nat)
    (hoff : off = 20 + opts.length) (hflags : s.flags &&& 0x3F = s.flags)
    (hdo : (UInt8.ofNat ((off / 4) * 16) >>> 4).toNat * 4 = off)
    (hmss : ∀ p : ByteArray, (∀ i, 20 ≤ i → i < off → Bytes.get p i = opts.getD (i - 20) 0) →
      parseMss p off = s.mss) :
    let d := Bytes.ofList (headerBytes s off ++ opts) ++ s.data
    parse src dst (Bytes.set16 d 16
        (Checksum.checksum d 0 d.size (Checksum.pseudo src dst Ipv4.protoTcp d.size))) = .ok s := by
  intro d
  let c := Checksum.checksum d 0 d.size (Checksum.pseudo src dst Ipv4.protoTcp d.size)
  have hhl : (headerBytes s off ++ opts).length = off := by simp [headerBytes, hoff]; omega
  have hhs : (Bytes.ofList (headerBytes s off ++ opts)).size = off := by rw [Bytes.size_ofList, hhl]
  have hds : d.size = off + s.data.size := by simp only [d, ByteArray.size_append, hhs]
  have hset : Bytes.set16 d 16 c = Bytes.set16 (Bytes.ofList (headerBytes s off ++ opts)) 16 c ++ s.data :=
    Bytes.set16_append_left (by rw [hhs]; omega) c
  have hsize : (Bytes.set16 d 16 c).size = off + s.data.size := by rw [Bytes.size_set16, hds]
  -- header and option bytes, except the checksum field
  have hget : ∀ i, i < off → i ≠ 16 → i ≠ 17 →
      Bytes.get (Bytes.set16 d 16 c) i = (headerBytes s off ++ opts).getD i 0 := by
    intro i hi h16 h17
    rw [hset, Bytes.get_append, if_pos (by rw [Bytes.size_set16, hhs]; exact hi),
      Bytes.get_set16_ne (by omega), Bytes.get_ofList]
  have hfix : ∀ i, i < 20 → i ≠ 16 → i ≠ 17 →
      Bytes.get (Bytes.set16 d 16 c) i = (headerBytes s off).getD i 0 := by
    intro i hi h16 h17
    rw [hget i (by omega) h16 h17, Bytes.getD_append_left (by simpa [headerBytes] using hi)]
  have hsport : Bytes.get16 (Bytes.set16 d 16 c) 0 = s.sport :=
    Bytes.get16_eq (by rw [hfix 0 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 1 (by decide) (by decide) (by decide)]; rfl)
  have hdport : Bytes.get16 (Bytes.set16 d 16 c) 2 = s.dport :=
    Bytes.get16_eq (by rw [hfix 2 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 3 (by decide) (by decide) (by decide)]; rfl)
  have hseq : Bytes.get32 (Bytes.set16 d 16 c) 4 = s.seq :=
    Bytes.get32_eq (by rw [hfix 4 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 5 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 6 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 7 (by decide) (by decide) (by decide)]; rfl)
  have hack : Bytes.get32 (Bytes.set16 d 16 c) 8 = s.ack :=
    Bytes.get32_eq (by rw [hfix 8 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 9 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 10 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 11 (by decide) (by decide) (by decide)]; rfl)
  have h12 : Bytes.get (Bytes.set16 d 16 c) 12 = UInt8.ofNat ((off / 4) * 16) := by
    rw [hfix 12 (by decide) (by decide) (by decide)]; rfl
  have h13 : Bytes.get (Bytes.set16 d 16 c) 13 = s.flags := by
    rw [hfix 13 (by decide) (by decide) (by decide)]; rfl
  have hwnd : Bytes.get16 (Bytes.set16 d 16 c) 14 = s.wnd :=
    Bytes.get16_eq (by rw [hfix 14 (by decide) (by decide) (by decide)]; rfl)
      (by rw [hfix 15 (by decide) (by decide) (by decide)]; rfl)
  have hsum : Checksum.sum (Bytes.set16 d 16 c) 0 (Bytes.set16 d 16 c).size
      (Checksum.pseudo src dst Ipv4.protoTcp (Bytes.set16 d 16 c).size) = 0xFFFF := by
    rw [Bytes.size_set16]
    exact Checksum.sum_set16_checksum (off := 0) (k := 8) (by omega) (by omega)
      (by
        have h1 : Bytes.get16 d 16 = Bytes.get16 (Bytes.ofList (headerBytes s off ++ opts)) 16 :=
          Bytes.get16_append_left (by rw [hhs]; omega)
        have h2 : (headerBytes s off ++ opts).getD 16 0 = 0 := by
          rw [Bytes.getD_append_left (by simp [headerBytes])]; rfl
        have h3 : (headerBytes s off ++ opts).getD 17 0 = 0 := by
          rw [Bytes.getD_append_left (by simp [headerBytes])]; rfl
        rw [show 0 + 2 * 8 = 16 from rfl, h1, Bytes.get16, Bytes.get_ofList, Bytes.get_ofList, h2, h3]
        rfl) _
  have hopts : parseMss (Bytes.set16 d 16 c) off = s.mss := by
    apply hmss
    intro i h1 h2
    rw [hget i h2 (by omega) (by omega), Bytes.getD_append_right (by simp [headerBytes]; omega)]
    simp [headerBytes]
  have hres := parse_ok (src := src) (dst := dst) (p := Bytes.set16 d 16 c) (off := off)
    (by rw [hsize]; omega) (by rw [h12]; exact hdo) (by omega) (by rw [hsize]; omega) hsum
  rw [hres, hsport, hdport, hseq, hack, h13, hflags, hwnd, hopts]
  have hsl : Bytes.slice (Bytes.set16 d 16 c) off ((Bytes.set16 d 16 c).size - off) = s.data := by
    have := Bytes.slice_append_right (Bytes.set16 (Bytes.ofList (headerBytes s off ++ opts)) 16 c) s.data
    rw [Bytes.size_set16, hhs] at this
    rw [hsize, Nat.add_sub_cancel_left, hset]
    exact this
  rw [hsl]

/-- M5.2, TCP: `parse` reads back the segment `emit` wrote — ports,
sequence numbers, flags, window, the MSS option and the data — when the
flags use only the six bits the parser keeps. -/
theorem parse_emit (src dst : UInt32) (s : Seg) (hflags : s.flags &&& 0x3F = s.flags) :
    parse src dst (emit src dst s) = .ok s := by
  cases hm : s.mss with
  | none =>
    have := parse_emit_aux src dst s [] 20 rfl hflags (by decide)
      (fun p _ => by rw [parseMss_20, hm])
    simpa [emit, hm, headerBytes, Bytes.be16, Bytes.be32] using this
  | some m =>
    have := parse_emit_aux src dst s [2, 4, (m >>> 8).toUInt8, m.toUInt8] 24 rfl hflags (by decide)
      (fun p hp => by
        rw [hm]
        exact parseMss_24 (by rw [hp 20 (by decide) (by decide)]; rfl)
          (by rw [hp 21 (by decide) (by decide)]; rfl)
          (Bytes.get16_eq (by rw [hp 22 (by decide) (by decide)]; rfl)
            (by rw [hp 23 (by decide) (by decide)]; rfl)))
    simpa [emit, hm, headerBytes, Bytes.be16, Bytes.be32] using this

end Ember.Spec.Tcp

/-! ## Axioms -/

/-- info: 'Ember.Spec.Ipv4.validate_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ember.Spec.Ipv4.validate_packet

/-- info: 'Ember.Spec.Udp.parse_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ember.Spec.Udp.parse_emit

/-- info: 'Ember.Spec.Tcp.parse_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ember.Spec.Tcp.parse_emit
