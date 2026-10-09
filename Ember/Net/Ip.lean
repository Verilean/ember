import Ember.Net.Buffer

/-!
# Ember.Net.Ip — SLIP, IPv4, ICMP echo and UDP echo in Ember (M3.2–M3.4)

Mirrors `Ember.Spec.Slip`, `Ipv4`, `Icmp` and `Udp`: the same checks in
the same order, with the same drop reasons.  Replies are built in `buf`:
the received payload stays where it is (options are squeezed out first),
and `ip_send` writes a fresh 20-byte header in front of it.
-/

namespace Ember.Net
open Ember.Lang

/-- Transmit `buf[0, n)` as one SLIP frame (`END payload END`). -/
ember def slip_send (n : u16) := do
  out.byte(0xC0)
  for i in [0, n) do
    let c : u8 := buf[i]
    if c == 0xC0 then
      out.byte(0xDB)
      out.byte(0xDC)
    else
      if c == 0xDB then
        out.byte(0xDB)
        out.byte(0xDD)
      else
        out.byte(c)
  out.byte(0xC0)
  out.end()

/-- Send the `n`-byte payload at `buf[20, 20+n)` to `dst`: TTL 64, the next
identification, DF on UDP and TCP (as Linux). -/
ember def ip_send (proto : u8) (dst : u32) (n : u16) := do
  buf[0] := 0x45
  buf[1] := 0
  set16(2, 20 + n)
  set16(4, ip_id)
  ip_id := ip_id + 1
  if proto == 1 then
    buf[6] := 0
  else
    buf[6] := 0x40
  buf[7] := 0
  buf[8] := TTL
  buf[9] := proto
  set16(10, 0)
  set32(12, OUR_IP)
  set32(16, dst)
  let c : u16 ← csum(0, 20, 0)
  set16(10, ~~~c)
  slip_send(20 + n)

/-- ICMP echo reply in place: type 8 → 0, checksum updated (RFC 1624). -/
ember def icmp_input (src : u32) (n : u16) := do
  if n < 8 then
    trace.drop(D_SHORT_ICMP)
    return
  let s : u16 ← csum(20, n, 0)
  let ok : bool ← verifies(s)
  if !ok then
    trace.drop(D_BAD_ICMP_CHECKSUM)
    return
  if buf[20] != 8 then
    trace.drop(D_UNSUPPORTED_ICMP_TYPE)
    return
  let old : u16 ← get16(20)
  let new : u16 := old &&& 0x00FF
  buf[20] := 0
  let hc : u16 ← get16(22)
  let c : u16 ← csum_update(hc, old, new)
  set16(22, c)
  ip_send(1, src, n)

/-- UDP echo on port 7: ports swapped, checksum recomputed. -/
ember def udp_input (src : u32) (dst : u32) (n : u16) := do
  if n < 8 then
    trace.drop(D_SHORT_UDP)
    return
  let ul : u16 ← get16(24)
  if ul < 8 || ul > n then
    trace.drop(D_BAD_UDP_LENGTH)
    return
  let cs : u16 ← get16(26)
  if cs != 0 then
    let p : u16 ← pseudo(src, dst, 17, ul)
    let s : u16 ← csum(20, ul, p)
    let ok : bool ← verifies(s)
    if !ok then
      trace.drop(D_BAD_UDP_CHECKSUM)
      return
  let sport : u16 ← get16(20)
  let dport : u16 ← get16(22)
  if dport != ECHO_PORT then
    trace.drop(D_UDP_PORT_CLOSED)
    return
  set16(20, dport)
  set16(22, sport)
  set16(26, 0)
  let p2 : u16 ← pseudo(OUR_IP, src, 17, ul)
  let s2 : u16 ← csum(20, ul, p2)
  let c : u16 := ~~~s2
  if c == 0 then
    set16(26, 0xFFFF)
  else
    set16(26, c)
  ip_send(17, src, ul)

/-- Validate the IPv4 packet in `buf[0, len)` and dispatch it. -/
ember def ip_input := do
  if len < 20 then
    trace.drop(D_SHORT_PACKET)
    return
  if (buf[0] >>> 4) != 4 then
    trace.drop(D_BAD_VERSION)
    return
  let ihl : u16 := ((buf[0] &&& 15 : u16)) * 4
  if ihl < 20 || ihl > len then
    trace.drop(D_BAD_IHL)
    return
  let hs : u16 ← csum(0, ihl, 0)
  let hok : bool ← verifies(hs)
  if !hok then
    trace.drop(D_BAD_IP_CHECKSUM)
    return
  let tl : u16 ← get16(2)
  if tl < ihl || tl > len then
    trace.drop(D_BAD_LENGTH)
    return
  let ff : u16 ← get16(6)
  if (ff &&& 0x3FFF) != 0 then
    trace.drop(D_FRAGMENT)
    return
  if buf[8] == 0 then
    trace.drop(D_TTL_ZERO)
    return
  let dst : u32 ← get32(16)
  if dst != OUR_IP && dst != 0xFFFFFFFF then
    trace.drop(D_NOT_FOR_US)
    return
  let src : u32 ← get32(12)
  let proto : u8 := buf[9]
  -- options are skipped: move the payload up to offset 20
  if ihl > 20 then
    for i in [0, tl - ihl) do
      buf[20 + i] := buf[ihl + i]
  let n : u16 := tl - ihl
  if dst == 0xFFFFFFFF && proto != 17 then
    trace.drop(D_BROADCAST)
    return
  if proto == 1 then
    icmp_input(src, n)
  else
    if proto == 17 then
      udp_input(src, dst, n)
    else
      if proto == 6 then
        tcp_input(src, dst, n)
      else
        trace.drop(D_UNSUPPORTED_PROTOCOL)

/-- One received byte: the SLIP decoder of `Ember.Spec.Slip`. -/
ember def slip_store (c : u8) := do
  if over then
    esc := false
    return
  if len < MTU then
    buf[len] := c
    len := len + 1
  else
    over := true
    len := 0
  esc := false

ember def slip_rx (c : u8) := do
  if c == 0xC0 then
    if over then
      trace.drop(D_OVERSIZE)
    else
      if len > 0 then
        ip_input()
    len := 0
    esc := false
    over := false
    return
  if esc then
    if c == 0xDC then
      slip_store(0xC0)
    else
      if c == 0xDD then
        slip_store(0xDB)
      else
        slip_store(c)
    return
  if c == 0xDB then
    esc := true
  else
    slip_store(c)

def ipFns : List Fn := [slip_send, ip_send, icmp_input, udp_input, ip_input, slip_store, slip_rx]

end Ember.Net
