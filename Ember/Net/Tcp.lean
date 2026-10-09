import Ember.Net.Ip

/-!
# Ember.Net.Tcp — the TCP connection in Ember (M3.5, M3.6)

Mirrors `Ember.Spec.Tcp.{Header,Output,Input,Timer}` function by
function: `tcp_input` = `parse`, `tcp_segment` = `input`, `listen_input`,
`ack_input`, `output`, `rexmit`, `tick`.  At most one segment is sent per
input, always after everything needed from the received segment has been
read, so the reply can be built in `buf` over it.  The echo application's
bytes live in `pend`; there is no retransmission buffer — a
retransmission regenerates `pend[0, sent)`.
-/

namespace Ember.Net
open Ember.Lang

/-- `rto k = min(48, 3 · 2^k)`. -/
ember def rto (k : u8) : u8 := do
  let mut r : u16 := 3
  for i in [0, k) do
    r := r * 2
    if r > 48 then
      r := 48
  return (r : u8)

/-- Back to LISTEN with every field at its `Ember.Spec.Tcp.Tcb` default. -/
ember def tcb_reset := do
  t.st := LISTEN
  t.rip := 0
  t.rport := 0
  t.snd_una := 0
  t.snd_nxt := 0
  t.rcv_nxt := 0
  t.pend_len := 0
  t.sent := 0
  t.fin_sent := false
  t.peer_mss := 536
  t.our_mss := OUR_MSS
  t.last_wnd := 0
  t.rt_timer := 0
  t.retries := 0
  t.tw_timer := 0
  t.idle := 0
  t.close_req := false

ember def cap : u16 := do
  if t.our_mss < t.peer_mss then
    return t.our_mss
  return t.peer_mss

ember def wnd : u16 := do
  let c : u16 ← cap()
  return c - t.pend_len

ember def seg_len : u32 := do
  let mut l : u32 := (sg.dlen : u32)
  if (sg.flags &&& F_SYN) != 0 then
    l := l + 1
  if (sg.flags &&& F_FIN) != 0 then
    l := l + 1
  return l

/-- Build a segment in `buf[20, …)` — data from `pend[src_off, src_off+n)`,
the MSS option when `mss` — and send it. -/
ember def tcp_emit (dst : u32) (sport : u16) (dport : u16) (seq : u32) (ack : u32) (flags : u8) (w : u16) (mss : bool) (src_off : u16) (n : u16) := do
  let mut off : u16 := 20
  if mss then
    off := 24
  for i in [0, n) do
    buf[20 + off + i] := pend[src_off + i]
  set16(20, sport)
  set16(22, dport)
  set32(24, seq)
  set32(28, ack)
  buf[32] := ((off / 4) * 16 : u8)
  buf[33] := flags
  set16(34, w)
  set16(36, 0)
  set16(38, 0)
  if mss then
    buf[40] := 2
    buf[41] := 4
    set16(42, t.our_mss)
  let total : u16 := off + n
  let p : u16 ← pseudo(OUR_IP, dst, 6, total)
  let s : u16 ← csum(20, total, p)
  set16(36, ~~~s)
  ip_send(6, dst, total)

/-- A segment of the connection; records the window announced. -/
ember def send_seg (flags : u8) (seq : u32) (src_off : u16) (n : u16) (mss : bool) := do
  let w : u16 ← wnd()
  tcp_emit(t.rip, ECHO_PORT, t.rport, seq, t.rcv_nxt, flags, w, mss, src_off, n)
  t.last_wnd := w

ember def send_syn_ack := do
  send_seg(F_SYN ||| F_ACK, t.snd_una, 0, 0, true)

/-- RFC 793 reset for the segment in `sg`. -/
ember def send_reset := do
  if (sg.flags &&& F_ACK) != 0 then
    tcp_emit(sg.src, sg.dport, sg.sport, sg.ack, 0, F_RST, 0, false, 0, 0)
  else
    let l : u32 ← seg_len()
    tcp_emit(sg.src, sg.dport, sg.sport, 0, sg.seq + l, F_RST ||| F_ACK, 0, false, 0, 0)

ember def output (ack_now : bool) := do
  if t.st == ESTABLISHED || t.st == CLOSE_WAIT then
    let unsent : u16 := t.pend_len - t.sent
    let closing : bool := (t.st == CLOSE_WAIT || t.close_req) && !t.fin_sent
    if unsent > 0 || closing then
      let was : bool := t.snd_una != t.snd_nxt
      let mut flags : u8 := F_ACK
      if unsent > 0 then
        flags := flags ||| F_PSH
      if closing then
        flags := flags ||| F_FIN
      let seq : u32 := t.snd_nxt
      let from_off : u16 := t.sent
      if closing then
        if t.st == CLOSE_WAIT then
          t.st := LAST_ACK
        else
          t.st := FIN_WAIT_1
        t.fin_sent := true
      t.sent := t.pend_len
      t.snd_nxt := t.snd_nxt + (unsent : u32) + (closing : u32)
      send_seg(flags, seq, from_off, unsent, false)
      if !was then
        t.rt_timer := RTO_INIT
        t.retries := 0
      return
  if t.st == LISTEN || t.st == SYN_RCVD then
    return
  let w : u16 ← wnd()
  if ack_now || (t.last_wnd == 0 && w > 0) then
    send_seg(F_ACK, t.snd_nxt, 0, 0, false)

/-- Retransmission: regenerate everything unacknowledged. -/
ember def rexmit := do
  if t.st == SYN_RCVD then
    send_syn_ack()
    return
  let mut flags : u8 := F_ACK
  if t.sent > 0 then
    flags := flags ||| F_PSH
  if t.fin_sent then
    flags := flags ||| F_FIN
  send_seg(flags, t.snd_una, 0, t.sent, false)

ember def acceptable : bool := do
  let w : u16 ← wnd()
  let l : u32 ← seg_len()
  let a : u32 := sg.seq - t.rcv_nxt
  if w == 0 then
    return sg.seq == t.rcv_nxt
  if l == 0 then
    return a < (w : u32)
  let b : u32 := sg.seq + l - 1 - t.rcv_nxt
  return a < (w : u32) || b < (w : u32)

/-- A segment in LISTEN, or for a tuple that is not the connection. -/
ember def listen_input := do
  if t.st != LISTEN then
    if (sg.flags &&& F_RST) != 0 then
      trace.drop(D_RST_NO_CONNECTION)
    else
      send_reset()
      trace.drop(D_SECOND_CONNECTION)
    return
  if (sg.flags &&& F_RST) != 0 then
    trace.drop(D_RST_IN_LISTEN)
    return
  if (sg.flags &&& F_ACK) != 0 then
    send_reset()
    trace.drop(D_ACK_IN_LISTEN)
    return
  if (sg.flags &&& F_SYN) == 0 then
    trace.drop(D_NO_SYN_IN_LISTEN)
    return
  let i0 : u32 := iss
  iss := iss + ISS_STEP
  tcb_reset()
  t.st := SYN_RCVD
  t.rip := sg.src
  t.rport := sg.sport
  t.rcv_nxt := sg.seq + 1
  t.snd_una := i0
  t.snd_nxt := i0 + 1
  if sg.has_mss then
    if sg.mss == 0 then
      t.peer_mss := 1
    else
      t.peer_mss := sg.mss
  t.rt_timer := RTO_INIT
  send_syn_ack()

/-- ACK processing in a synchronized state; `false` when the segment is done. -/
ember def ack_input : bool := do
  let d : u32 := sg.ack - t.snd_una
  let outn : u32 := t.snd_nxt - t.snd_una
  if d > outn then
    send_seg(F_ACK, t.snd_nxt, 0, 0, false)
    trace.drop(D_ACK_OF_UNSENT)
    return false
  if d == 0 then
    return true
  let mut acked : u16 := t.sent
  if d < (t.sent : u32) then
    acked := (d : u16)
  let fin_acked : bool := d > (acked : u32)
  for i in [0, t.pend_len - acked) do
    pend[i] := pend[i + acked]
  t.pend_len := t.pend_len - acked
  t.sent := t.sent - acked
  t.snd_una := sg.ack
  t.retries := 0
  if t.snd_una != t.snd_nxt then
    t.rt_timer := RTO_INIT
  else
    t.rt_timer := 0
  if fin_acked then
    if t.st == FIN_WAIT_1 then
      t.st := FIN_WAIT_2
    else
      if t.st == CLOSING then
        t.st := TIME_WAIT
        t.tw_timer := TIME_WAIT_TICKS
      else
        if t.st == LAST_ACK then
          tcb_reset()
          return false
  return true

/-- A parsed segment (in `sg`, data at `buf[sg.doff, …)`). -/
ember def tcp_segment := do
  if sg.dport != ECHO_PORT then
    if (sg.flags &&& F_RST) == 0 then
      send_reset()
    trace.drop(D_TCP_PORT_CLOSED)
    return
  if t.st == LISTEN || sg.src != t.rip || sg.sport != t.rport then
    listen_input()
    return
  t.idle := 0
  -- 1. acceptability
  let ok : bool ← acceptable()
  if !ok then
    if (sg.flags &&& F_RST) != 0 then
      trace.drop(D_RST_OUT_OF_WINDOW)
      return
    if t.st == SYN_RCVD && (sg.flags &&& F_SYN) != 0 && (sg.flags &&& F_ACK) == 0 && sg.seq + 1 == t.rcv_nxt then
      send_syn_ack()
      trace.drop(D_DUPLICATE_SYN)
      return
    send_seg(F_ACK, t.snd_nxt, 0, 0, false)
    trace.drop(D_OUT_OF_WINDOW)
    return
  -- 2. RST
  if (sg.flags &&& F_RST) != 0 then
    tcb_reset()
    trace.note(0, 0)
    return
  -- 3. SYN in the window
  if (sg.flags &&& F_SYN) != 0 then
    tcp_emit(t.rip, ECHO_PORT, t.rport, t.snd_nxt, 0, F_RST, 0, false, 0, 0)
    tcb_reset()
    trace.drop(D_SYN_IN_WINDOW)
    return
  -- 4. ACK required
  if (sg.flags &&& F_ACK) == 0 then
    trace.drop(D_NO_ACK)
    return
  -- 5. ACK
  if t.st == SYN_RCVD then
    if sg.ack != t.snd_nxt then
      send_reset()
      trace.drop(D_BAD_ACK_SYN_RCVD)
      return
    t.st := ESTABLISHED
    t.snd_una := sg.ack
    t.rt_timer := 0
    t.retries := 0
  else
    let go : bool ← ack_input()
    if !go then
      return
  -- 6. data
  let mut ack_now : bool := false
  let mut in_order : bool := true
  let fin : bool := (sg.flags &&& F_FIN) != 0
  if (sg.dlen > 0 || fin) && (t.rcv_nxt - sg.seq) >= 0x80000000 then
    send_seg(F_ACK, t.snd_nxt, 0, 0, false)
    trace.drop(D_OUT_OF_ORDER)
    return
  if sg.dlen > 0 then
    if t.st == ESTABLISHED || t.st == FIN_WAIT_1 || t.st == FIN_WAIT_2 then
      let skip : u32 := t.rcv_nxt - sg.seq
      let mut fresh : u16 := 0
      if skip < (sg.dlen : u32) then
        fresh := sg.dlen - (skip : u16)
      let w : u16 ← wnd()
      let mut take : u16 := fresh
      if w < take then
        take := w
      if t.st == ESTABLISHED then
        for i in [0, take) do
          pend[t.pend_len + i] := buf[sg.doff + (skip : u16) + i]
        t.pend_len := t.pend_len + take
      t.rcv_nxt := t.rcv_nxt + (take : u32)
      ack_now := true
      in_order := take == fresh
  -- 7. FIN, in order only
  if fin && in_order && sg.seq + (sg.dlen : u32) == t.rcv_nxt then
    if t.st == ESTABLISHED then
      t.st := CLOSE_WAIT
      t.rcv_nxt := t.rcv_nxt + 1
      ack_now := true
    else
      if t.st == FIN_WAIT_1 then
        t.st := CLOSING
        t.rcv_nxt := t.rcv_nxt + 1
        ack_now := true
      else
        if t.st == FIN_WAIT_2 then
          t.st := TIME_WAIT
          t.tw_timer := TIME_WAIT_TICKS
          t.rcv_nxt := t.rcv_nxt + 1
          ack_now := true
  -- 8. output
  output(ack_now)

/-- The MSS option among the options in `buf[40, 20+off)`. -/
ember def parse_mss (off : u16) := do
  sg.has_mss := false
  sg.mss := 0
  let mut i : u16 := 20
  loop (max := 40) do
    if i >= off then
      break
    let k : u8 := buf[20 + i]
    if k == 0 then
      break
    if k == 1 then
      i := i + 1
    else
      if i + 1 >= off then
        break
      let l : u16 := (buf[20 + i + 1] : u16)
      if l < 2 || i + l > off then
        break
      if k == 2 && l == 4 then
        sg.has_mss := true
        sg.mss ← get16(20 + i + 2)
      i := i + l

/-- Parse and check the TCP segment at `buf[20, 20+n)`. -/
ember def tcp_input (src : u32) (dst : u32) (n : u16) := do
  if n < 20 then
    trace.drop(D_SHORT_TCP)
    return
  let off : u16 := ((buf[32] >>> 4 : u16)) * 4
  if off < 20 || off > n then
    trace.drop(D_BAD_TCP_HEADER)
    return
  let p : u16 ← pseudo(src, dst, 6, n)
  let s : u16 ← csum(20, n, p)
  let ok : bool ← verifies(s)
  if !ok then
    trace.drop(D_BAD_TCP_CHECKSUM)
    return
  sg.src := src
  sg.sport ← get16(20)
  sg.dport ← get16(22)
  sg.seq ← get32(24)
  sg.ack ← get32(28)
  sg.flags := buf[33] &&& 0x3F
  sg.doff := 20 + off
  sg.dlen := n - off
  parse_mss(off)
  tcp_segment()

/-- One tick (`Ember.Spec.Tcp.tick`). -/
ember def tcp_tick := do
  if t.st == LISTEN then
    return
  if t.st == TIME_WAIT then
    if t.tw_timer <= 1 then
      tcb_reset()
    else
      t.tw_timer := t.tw_timer - 1
    return
  if t.st == FIN_WAIT_2 then
    if t.idle + 1 >= IDLE_TICKS then
      tcb_reset()
      trace.drop(D_FIN_WAIT_2_TIMEOUT)
    else
      t.idle := t.idle + 1
    return
  if t.snd_una != t.snd_nxt then
    if t.rt_timer <= 1 then
      let r : u8 := t.retries + 1
      if r > MAX_RETRIES then
        tcp_emit(t.rip, ECHO_PORT, t.rport, t.snd_nxt, t.rcv_nxt, F_RST ||| F_ACK, 0, false, 0, 0)
        tcb_reset()
        trace.drop(D_GIVE_UP)
      else
        t.retries := r
        t.rt_timer ← rto(r)
        rexmit()
    else
      t.rt_timer := t.rt_timer - 1
    return
  if t.st == ESTABLISHED && t.pend_len == 0 then
    if t.idle + 1 >= IDLE_TICKS then
      t.close_req := true
      t.idle := 0
      output(false)
    else
      t.idle := t.idle + 1

def tcpFns : List Fn :=
  [rto, tcb_reset, cap, wnd, seg_len, tcp_emit, send_seg, send_syn_ack, send_reset, output, rexmit,
   acceptable, listen_input, ack_input, tcp_segment, parse_mss, tcp_input, tcp_tick]

end Ember.Net
