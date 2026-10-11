import Ember.Net.Main

/-!
# Ember.Net.Eth — the stack on Ethernet frames, with ARP and DHCP (plan M4w, host part)

The second link layer of `Ember.Spec` (`Spec.Arp`, `Spec.Dhcp`,
`Spec.Stack.ethInput`) in Ember, for Wi-Fi raw frames.  IP, ICMP and TCP
are the functions of the SLIP build, unchanged: an Ember function names
its globals, so the same code runs here against a 576-byte buffer, an
MSS of 536 and an address that is a variable (DHCP assigns it).

What is new:

* frames arrive whole (`input.frame`): the 14-byte header goes to `eth`,
  the payload to `buf[0, …)`, where the IP code expects its packet;
* `eth_send` in place of `slip_send`: the destination's MAC from the ARP
  cache (four entries, replaced round-robin), an ARP request and the drop
  `arp-miss` when it is not there;
* `udp_input` also hands port 68 to the DHCP client;
* two programs: `prog` (static address) and `progDhcp`.

The checks and their order are the Spec's, so that the `drop` lines of
the two traces agree.
-/

namespace Ember.Net.Eth
open Ember.Lang

/-! ## What differs from the SLIP build's globals -/

ember const MTU : u16 := 576
ember const OUR_MSS : u16 := 536
ember const MAC : [u8; 6] := [2, 0, 0, 0, 0, 1]

ember global buf : [u8; 576]
ember global pend : [u8; 536]

/-- The frame being received: its header, and how many bytes came. -/
ember global eth : [u8; 14]
ember global flen : u16

/-- The ARP cache; `am` is the address being entered. -/
ember global arp_ip : [u32; 4]
ember global arp_mac : [u8; 24]
ember global arp_n : u8
ember global arp_next : u8
ember global am : [u8; 6]

/-! DHCP client: phase 0 INIT, 1 SELECTING, 2 REQUESTING, 3 BOUND. -/
ember global d_phase : u8
ember global d_xid : u32 := 1162691072
ember global d_server : u32
ember global d_offered : u32
ember global d_timer : u32

ember const D_SHORT_FRAME : u8 := 37
ember const D_NOT_OUR_MAC : u8 := 38
ember const D_UNSUPPORTED_ETHERTYPE : u8 := 39
ember const D_SHORT_ARP : u8 := 40
ember const D_BAD_ARP : u8 := 41
ember const D_ARP_NOT_FOR_US : u8 := 42
ember const D_ARP_MISS : u8 := 43
ember const D_BAD_DHCP : u8 := 44
ember const D_DHCP_NOT_OURS : u8 := 45
ember const D_DHCP_UNEXPECTED : u8 := 46

def dropReasons : List String :=
  Net.dropReasons ++ ["short-frame", "not-our-mac", "unsupported-ethertype", "short-arp", "bad-arp",
    "arp-not-for-us", "arp-miss", "bad-dhcp", "dhcp-not-ours", "dhcp-unexpected"]

ember const N_DHCP_OFFER : u8 := 1
ember const N_DHCP_BOUND : u8 := 2
ember const N_DHCP_NAK : u8 := 3
ember const N_DHCP_TIMEOUT : u8 := 4
ember const N_DHCP_RENEWING : u8 := 5

def notes : List String :=
  Net.notes ++ ["dhcp-offer", "dhcp-bound", "dhcp-nak", "dhcp-timeout", "dhcp-renewing"]

/-! ## Frames out -/

ember def out32 (v : u32) := do
  out.byte((v >>> 24 : u8))
  out.byte((v >>> 16 : u8))
  out.byte((v >>> 8 : u8))
  out.byte((v : u8))

ember def mac_out := do
  for j in [0, (6 : u8)) do
    out.byte(MAC[j])

/-- Index of an address in the cache, 255 when it is not there. -/
ember def arp_find (ip : u32) : u8 := do
  for i in [0, arp_n) do
    if arp_ip[i] == ip then
      return i
  return 255

/-- `Spec.Arp.Cache.update`, the MAC taken from `am`. -/
ember def arp_update (ip : u32) (insert : bool) := do
  let mut k : u8 ← arp_find(ip)
  if k == 255 then
    if !insert then
      return
    if arp_n < 4 then
      k := arp_n
      arp_n := arp_n + 1
    else
      k := arp_next
      arp_next := (arp_next + 1) % 4
  arp_ip[k] := ip
  for j in [0, (6 : u8)) do
    arp_mac[k * 6 + j] := am[j]

/-- "Who has `target`?", broadcast. -/
ember def arp_request (target : u32) := do
  for j in [0, (6 : u8)) do
    out.byte(0xFF)
  mac_out()
  out.byte(0x08)
  out.byte(0x06)
  out.byte(0)
  out.byte(1)
  out.byte(0x08)
  out.byte(0)
  out.byte(6)
  out.byte(4)
  out.byte(0)
  out.byte(1)
  mac_out()
  out32(OUR_IP)
  for z in [0, (6 : u8)) do
    out.byte(0)
  out32(target)
  out.end()

/-- `buf[0, n)` as an IPv4 frame to `dst`. -/
ember def eth_send (dst : u32) (n : u16) := do
  let mut k : u8 := 254
  if dst != 0xFFFFFFFF then
    k ← arp_find(dst)
    if k == 255 then
      arp_request(dst)
      trace.drop(D_ARP_MISS)
      return
  for j in [0, (6 : u8)) do
    if k == 254 then
      out.byte(0xFF)
    else
      out.byte(arp_mac[k * 6 + j])
  mac_out()
  out.byte(0x08)
  out.byte(0x00)
  for i in [0, n) do
    out.byte(buf[i])
  out.end()

/-- As the SLIP build's `ip_send`, onto Ethernet. -/
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
  eth_send(dst, 20 + n)

/-! ## ARP in -/

ember def arp_input (n : u16) := do
  if n < 28 then
    trace.drop(D_SHORT_ARP)
    return
  let ht : u16 ← get16(0)
  let pt : u16 ← get16(2)
  if ht != 1 || pt != 0x0800 || buf[4] != 6 || buf[5] != 4 then
    trace.drop(D_BAD_ARP)
    return
  let op : u16 ← get16(6)
  let spa : u32 ← get32(14)
  let tpa : u32 ← get32(24)
  let for_us : bool := tpa == OUR_IP && OUR_IP != 0
  for j in [0, (6 : u8)) do
    am[j] := buf[8 + j]
  arp_update(spa, for_us || op == 2)
  if op == 1 then
    if for_us then
      for a in [0, (6 : u8)) do
        out.byte(am[a])
      mac_out()
      out.byte(0x08)
      out.byte(0x06)
      out.byte(0)
      out.byte(1)
      out.byte(0x08)
      out.byte(0)
      out.byte(6)
      out.byte(4)
      out.byte(0)
      out.byte(2)
      mac_out()
      out32(OUR_IP)
      for b in [0, (6 : u8)) do
        out.byte(am[b])
      out32(spa)
      out.end()
    else
      trace.drop(D_ARP_NOT_FOR_US)

/-! ## DHCP -/

/-- A BOOTREQUEST (`Spec.Dhcp.message`) built at `buf[28, …)` and
broadcast; `ask` adds the requested address and the server identifier. -/
ember def dhcp_send (mtype : u8) (ciaddr : u32) (ask : bool) := do
  for i in [(28 : u16), 268) do
    buf[i] := 0
  buf[28] := 1
  buf[29] := 1
  buf[30] := 6
  set32(32, d_xid)
  buf[38] := 0x80
  set32(40, ciaddr)
  for j in [0, (6 : u8)) do
    buf[56 + (j : u16)] := MAC[j]
  set32(264, 0x63825363)
  buf[268] := 53
  buf[269] := 1
  buf[270] := mtype
  let mut e : u16 := 271
  if ask then
    buf[271] := 50
    buf[272] := 4
    set32(273, d_offered)
    buf[277] := 54
    buf[278] := 4
    set32(279, d_server)
    e := 283
  buf[e] := 255
  let ul : u16 := e - 19
  set16(20, 68)
  set16(22, 67)
  set16(24, ul)
  set16(26, 0)
  let p : u16 ← pseudo(OUR_IP, 0xFFFFFFFF, 17, ul)
  let s : u16 ← csum(20, ul, p)
  let c : u16 := ~~~s
  if c == 0 then
    set16(26, 0xFFFF)
  else
    set16(26, c)
  ip_send(17, 0xFFFFFFFF, ul)

ember def dhcp_reset := do
  d_phase := 0
  d_xid := d_xid + 1
  d_server := 0
  d_offered := 0
  d_timer := 0
  OUR_IP := 0

/-- A message to port 68: `n` bytes of UDP at `buf[20, …)`, the DHCP
message from `buf[28]` on. -/
ember def dhcp_input (n : u16) := do
  let ms : u16 := n - 8
  if ms < 240 then
    trace.drop(D_BAD_DHCP)
    return
  let mg : u32 ← get32(264)
  if buf[28] != 2 || mg != 0x63825363 then
    trace.drop(D_BAD_DHCP)
    return
  let xid : u32 ← get32(32)
  let mut mine : bool := xid == d_xid
  for j in [0, (6 : u8)) do
    if buf[56 + (j : u16)] != MAC[j] then
      mine := false
  if !mine then
    trace.drop(D_DHCP_NOT_OURS)
    return
  -- the options: the first message type, server identifier and lease
  let mut i : u16 := 240
  let mut has_type : bool := false
  let mut mtype : u8 := 0
  let mut seen53 : bool := false
  let mut seen54 : bool := false
  let mut seen51 : bool := false
  let mut server : u32 := 0
  let mut lease : u32 := 3600
  loop (max := 600) do
    if i >= ms then
      break
    let c : u8 := buf[28 + i]
    if c == 255 then
      break
    if c == 0 then
      i := i + 1
    else
      if i + 1 >= ms then
        break
      let l : u16 := (buf[29 + i] : u16)
      if i + 2 + l > ms then
        break
      if c == 53 && !seen53 then
        seen53 := true
        if l >= 1 then
          has_type := true
          mtype := buf[30 + i]
      if c == 54 && !seen54 then
        seen54 := true
        if l >= 4 then
          server ← get32(30 + i)
      if c == 51 && !seen51 then
        seen51 := true
        if l >= 4 then
          lease ← get32(30 + i)
      i := i + 2 + l
  let yi : u32 ← get32(44)
  if d_phase == 1 && has_type && mtype == 2 then
    d_phase := 2
    d_offered := yi
    d_server := server
    d_timer := 8
    trace.note(N_DHCP_OFFER, yi)
    dhcp_send(3, 0, true)
    return
  if d_phase == 2 && has_type && mtype == 5 then
    d_phase := 3
    d_offered := yi
    if lease == 0 then
      d_timer := 1
    else
      d_timer := lease
    d_xid := d_xid + 1
    OUR_IP := yi
    trace.note(N_DHCP_BOUND, yi)
    return
  if d_phase == 2 && has_type && mtype == 6 then
    dhcp_reset()
    trace.note(N_DHCP_NAK, 0)
    return
  trace.drop(D_DHCP_UNEXPECTED)

ember def dhcp_tick := do
  if d_phase == 0 then
    d_phase := 1
    d_timer := 8
    dhcp_send(1, 0, false)
    return
  if d_phase == 3 then
    if d_timer <= 1 then
      d_phase := 2
      d_timer := 8
      trace.note(N_DHCP_RENEWING, OUR_IP)
      dhcp_send(3, OUR_IP, OUR_IP == 0)
      return
    d_timer := d_timer - 1
    return
  if d_timer <= 1 then
    dhcp_reset()
    trace.note(N_DHCP_TIMEOUT, 0)
  else
    d_timer := d_timer - 1

/-! ## UDP and frames in -/

/-- As the SLIP build's `udp_input`, with port 68 for the DHCP client. -/
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
    if dport == 68 && DHCP then
      dhcp_input(n)
      return
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

/-- `Spec.Ipv4.validate` without the drops: would `ip_input` accept
`buf[0, len)`?  (The sender of a well-formed packet is learnt.) -/
ember def ip_ok : bool := do
  if len < 20 then
    return false
  if (buf[0] >>> 4) != 4 then
    return false
  let ihl : u16 := ((buf[0] &&& 15 : u16)) * 4
  if ihl < 20 || ihl > len then
    return false
  let hs : u16 ← csum(0, ihl, 0)
  let hok : bool ← verifies(hs)
  if !hok then
    return false
  let tl : u16 ← get16(2)
  if tl < ihl || tl > len then
    return false
  let ff : u16 ← get16(6)
  if (ff &&& 0x3FFF) != 0 then
    return false
  if buf[8] == 0 then
    return false
  let dst : u32 ← get32(16)
  if dst != OUR_IP && dst != 0xFFFFFFFF then
    return false
  return true

/-- A frame is complete: header in `eth`, `flen − 14` bytes of payload in `buf`. -/
ember def eth_input := do
  if flen < 14 then
    trace.drop(D_SHORT_FRAME)
    return
  let mut ours : bool := true
  let mut bcast : bool := true
  for j in [0, (6 : u8)) do
    if eth[j] != MAC[j] then
      ours := false
    if eth[j] != 0xFF then
      bcast := false
  if !ours && !bcast then
    trace.drop(D_NOT_OUR_MAC)
    return
  let ty : u16 := ((eth[12] : u16) <<< 8) ||| (eth[13] : u16)
  len := flen - 14
  if ty == 0x0806 then
    arp_input(len)
    return
  if ty == 0x0800 then
    if over then
      trace.drop(D_OVERSIZE)
      return
    let ok : bool ← ip_ok()
    if ok then
      let src : u32 ← get32(12)
      if src != 0 then
        for a in [0, (6 : u8)) do
          am[a] := eth[6 + a]
        arp_update(src, true)
    ip_input()
    return
  trace.drop(D_UNSUPPORTED_ETHERTYPE)

/-- One byte of a frame. -/
ember def eth_store (c : u8) := do
  if flen < 14 then
    eth[flen] := c
  else
    let i : u16 := flen - 14
    if i < MTU then
      buf[i] := c
    else
      over := true
  if flen < 0xFFFF then
    flen := flen + 1

ember def main := do
  if !booted then
    tcb_reset()
    booted := true
  let k : u16 ← input.frame()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    tcp_tick()
    if DHCP then
      dhcp_tick()
    return
  if k == 0x0200 then
    eth_input()
    flen := 0
    over := false
    return
  eth_store((k : u8))

/-! ## The two programs -/

def ethFns : List Fn :=
  [out32, mac_out, arp_find, arp_update, arp_request, eth_send, ip_send, arp_input, dhcp_send, dhcp_reset,
   dhcp_input, dhcp_tick, udp_input, ip_ok, eth_input, eth_store, main]

/-- The SLIP build's functions that are used as they are. -/
def sharedFns : List Fn := Net.fns ++ [Net.icmp_input, Net.ip_input] ++ Net.tcpFns

def ethConsts : List Global :=
  [D_SHORT_FRAME, D_NOT_OUR_MAC, D_UNSUPPORTED_ETHERTYPE, D_SHORT_ARP, D_BAD_ARP, D_ARP_NOT_FOR_US, D_ARP_MISS,
   D_BAD_DHCP, D_DHCP_NOT_OURS, D_DHCP_UNEXPECTED, N_DHCP_OFFER, N_DHCP_BOUND, N_DHCP_NAK, N_DHCP_TIMEOUT,
   N_DHCP_RENEWING, MAC]

/-- The globals: the SLIP build's with the buffer sizes, the MTU and the
MSS replaced, the address a variable, and the Ethernet state added. -/
def globalsFor (dhcp : Bool) (mtu : Nat := 576) : List Global :=
  let replaced := ["OUR_IP", "MTU", "OUR_MSS", "buf", "pend", "esc"]
  (Net.constants ++ Net.state).filter (fun g => !replaced.contains g.name) ++
  [{ MTU with init := [mtu] }, { OUR_MSS with init := [mtu - 40] },
   { buf with ty := .arr .u8 mtu }, { pend with ty := .arr .u8 (mtu - 40) },
   eth, flen, arp_ip, arp_mac, arp_n, arp_next, am,
   d_phase, d_xid, d_server, d_offered, d_timer, Net.booted,
   { name := "OUR_IP", ty := .u32, init := [if dhcp then 0 else 167772161] },
   { name := "DHCP", ty := .bool, init := [if dhcp then 1 else 0], const := true }] ++ ethConsts

/-- `mtu` is the size of the packet buffer: 576 (RFC 2131 needs it for
DHCP), or SLIP's 296 for a static address. -/
def progFor (dhcp : Bool) (mtu : Nat := 576) : Prog :=
  { structs := Net.structs, globals := globalsFor dhcp mtu, fns := sharedFns ++ ethFns,
    dropReasons := dropReasons, notes := notes }

/-- Static address 10.0.0.1. -/
def prog : Prog := progFor false
/-- The address comes from a DHCP server. -/
def progDhcp : Prog := progFor true

end Ember.Net.Eth
