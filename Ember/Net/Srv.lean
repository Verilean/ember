import Ember.Net.Main

/-!
# Ember.Net.Srv — the stack in Ember with an application interface (plan M8.1)

`Ember.Spec.Srv` in Ember.  `Ember.Net` — the echo program `Net.prog`,
which the proofs are about — stays as it is; this program reuses its
functions where nothing changes (`rto`, `cap`, `seg_len`,
`send_syn_ack`, `send_reset`, `acceptable`, `rexmit`, `parse_mss`,
`tcp_input`, the IP and SLIP code: calls go by name) and replaces the
ones where the echo buffer or the one connection was.

**Connections.**  `n` of them, a parameter of the program (`prog n app`).
Ember has no arrays of records, so each field of the TCB has an array
`c_<field> : [_; n]`; the connection being worked on is loaded into the
record `t` (`tcb_load`), as in `Ember.Net`, and stored back (`tcb_save`).
`cur` is its number.

**The application** is a set of Ember functions with fixed names, which
work on the connection `cur` (its state is the application's own
globals, one slot per connection):

| function | `Ember.Spec.Srv.App` |
|---|---|
| `app_reset()` | `init` (the connection is new, or closed) |
| `app_room(cap : u16) : u16` | `room` |
| `app_recv(off : u16, n : u16)` | `recv`: the data is `buf[off, off + n)` |
| `app_avail() : u16` | `avail` |
| `app_fill(from : u16, n : u16, dst : u16)` | `bytes`: write bytes `[from, from + n)` of the stream from `snd.una` to `buf[dst, …)` |
| `app_acked(n : u16)` | `acked` |
| `app_close() : bool` | `close` |

and two constants, `APP_PORT` and `APP_IDLE_CLOSE`.  `echo n mss` is
`Spec.Srv.echo` written so.
-/

namespace Ember.Net.Srv
open Ember.Lang

/-- The fields of `Net.Tcb` but the echo buffer's length (the application keeps that). -/
ember struct Tcb where
  st : u8
  rip : u32
  rport : u16
  snd_una : u32
  snd_nxt : u32
  rcv_nxt : u32
  sent : u16
  fin_sent : bool
  peer_mss : u16
  our_mss : u16
  last_wnd : u16
  rt_timer : u8
  retries : u8
  tw_timer : u8
  idle : u8
  close_req : bool

ember global t : Tcb
/-- The connection in `t`. -/
ember global cur : u16

/-- The arrays that hold the connections' TCBs. -/
def connGlobals (n : Nat) : List Global :=
  Tcb.fields.map fun (f, ty) => { name := "c_" ++ f, ty := .arr ty n }

def nConns (n : Nat) : Global := { name := "N_CONNS", ty := .u16, init := [n], const := true }

ember def tcb_load (i : u16) := do
  cur := i
  t.st := c_st[i]
  t.rip := c_rip[i]
  t.rport := c_rport[i]
  t.snd_una := c_snd_una[i]
  t.snd_nxt := c_snd_nxt[i]
  t.rcv_nxt := c_rcv_nxt[i]
  t.sent := c_sent[i]
  t.fin_sent := c_fin_sent[i]
  t.peer_mss := c_peer_mss[i]
  t.our_mss := c_our_mss[i]
  t.last_wnd := c_last_wnd[i]
  t.rt_timer := c_rt_timer[i]
  t.retries := c_retries[i]
  t.tw_timer := c_tw_timer[i]
  t.idle := c_idle[i]
  t.close_req := c_close_req[i]

ember def tcb_save := do
  c_st[cur] := t.st
  c_rip[cur] := t.rip
  c_rport[cur] := t.rport
  c_snd_una[cur] := t.snd_una
  c_snd_nxt[cur] := t.snd_nxt
  c_rcv_nxt[cur] := t.rcv_nxt
  c_sent[cur] := t.sent
  c_fin_sent[cur] := t.fin_sent
  c_peer_mss[cur] := t.peer_mss
  c_our_mss[cur] := t.our_mss
  c_last_wnd[cur] := t.last_wnd
  c_rt_timer[cur] := t.rt_timer
  c_retries[cur] := t.retries
  c_tw_timer[cur] := t.tw_timer
  c_idle[cur] := t.idle
  c_close_req[cur] := t.close_req

/-- Back to LISTEN, the application's state with it (`Spec.Srv.closeConn`). -/
ember def tcb_reset := do
  t.st := LISTEN
  t.rip := 0
  t.rport := 0
  t.snd_una := 0
  t.snd_nxt := 0
  t.rcv_nxt := 0
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
  app_reset()

ember def wnd : u16 := do
  let c : u16 ← cap()
  let w : u16 ← app_room(c)
  return w

/-- `Net.tcp_emit` with the data from the application. -/
ember def tcp_emit (dst : u32) (sport : u16) (dport : u16) (seq : u32) (ack : u32) (flags : u8) (w : u16) (mss : bool) (src_off : u16) (n : u16) := do
  let mut off : u16 := 20
  if mss then
    off := 24
  if n > 0 then
    app_fill(src_off, n, 20 + off)
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

ember def send_seg (flags : u8) (seq : u32) (src_off : u16) (n : u16) (mss : bool) := do
  let w : u16 ← wnd()
  tcp_emit(t.rip, APP_PORT, t.rport, seq, t.rcv_nxt, flags, w, mss, src_off, n)
  t.last_wnd := w

/-- `Spec.Srv.output`: at most `cap - sent` new bytes; the FIN with the last of them. -/
ember def output (ack_now : bool) := do
  if t.st == ESTABLISHED || t.st == CLOSE_WAIT then
    let avail : u16 ← app_avail()
    let unsent : u16 := avail - t.sent
    let c : u16 ← cap()
    let mut n : u16 := 0
    if t.sent < c then
      n := c - t.sent
    if unsent < n then
      n := unsent
    let done : bool ← app_close()
    let closing : bool := (t.st == CLOSE_WAIT || t.close_req || done) && !t.fin_sent
    let fin : bool := closing && n == unsent
    if n > 0 || fin then
      let was : bool := t.snd_una != t.snd_nxt
      let mut flags : u8 := F_ACK
      if n > 0 then
        flags := flags ||| F_PSH
      if fin then
        flags := flags ||| F_FIN
      let seq : u32 := t.snd_nxt
      let from_off : u16 := t.sent
      if fin then
        if t.st == CLOSE_WAIT then
          t.st := LAST_ACK
        else
          t.st := FIN_WAIT_1
        t.fin_sent := true
      t.sent := t.sent + n
      t.snd_nxt := t.snd_nxt + (n : u32) + (fin : u32)
      send_seg(flags, seq, from_off, n, false)
      if !was then
        t.rt_timer := RTO_INIT
        t.retries := 0
      return
  if t.st == LISTEN || t.st == SYN_RCVD then
    return
  let w : u16 ← wnd()
  if ack_now || (t.last_wnd == 0 && w > 0) then
    send_seg(F_ACK, t.snd_nxt, 0, 0, false)

/-- A segment for a tuple that is no connection, when none is free. -/
ember def busy_input := do
  if (sg.flags &&& F_RST) != 0 then
    trace.drop(D_RST_NO_CONNECTION)
  else
    send_reset()
    trace.drop(D_SECOND_CONNECTION)

/-- A segment for a connection in LISTEN. -/
ember def listen_input := do
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
  app_acked(acked)
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

/-- A segment of the connection in `t` (`Spec.Srv.connInput`). -/
ember def conn_input := do
  t.idle := 0
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
  if (sg.flags &&& F_RST) != 0 then
    tcb_reset()
    trace.note(0, 0)
    return
  if (sg.flags &&& F_SYN) != 0 then
    tcp_emit(t.rip, APP_PORT, t.rport, t.snd_nxt, 0, F_RST, 0, false, 0, 0)
    tcb_reset()
    trace.drop(D_SYN_IN_WINDOW)
    return
  if (sg.flags &&& F_ACK) == 0 then
    trace.drop(D_NO_ACK)
    return
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
      if t.st == ESTABLISHED && take > 0 then
        app_recv(sg.doff + (skip : u16), take)
      t.rcv_nxt := t.rcv_nxt + (take : u32)
      ack_now := true
      in_order := take == fresh
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
  output(ack_now)

/-- A parsed segment: to its connection, to a free one, or reset. -/
ember def tcp_segment := do
  if sg.dport != APP_PORT then
    if (sg.flags &&& F_RST) == 0 then
      send_reset()
    trace.drop(D_TCP_PORT_CLOSED)
    return
  for i in [0, N_CONNS) do
    if c_st[i] != LISTEN && c_rip[i] == sg.src && c_rport[i] == sg.sport then
      tcb_load(i)
      conn_input()
      tcb_save()
      return
  for j in [0, N_CONNS) do
    if c_st[j] == LISTEN then
      tcb_load(j)
      listen_input()
      tcb_save()
      return
  busy_input()

/-- One tick of the connection in `t` (`Net.tcp_tick`; the idle close is the application's). -/
ember def conn_tick := do
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
        tcp_emit(t.rip, APP_PORT, t.rport, t.snd_nxt, t.rcv_nxt, F_RST ||| F_ACK, 0, false, 0, 0)
        tcb_reset()
        trace.drop(D_GIVE_UP)
      else
        t.retries := r
        t.rt_timer ← rto(r)
        rexmit()
    else
      t.rt_timer := t.rt_timer - 1
    return
  let avail : u16 ← app_avail()
  if APP_IDLE_CLOSE && t.st == ESTABLISHED && avail == 0 then
    if t.idle + 1 >= IDLE_TICKS then
      t.close_req := true
      t.idle := 0
      output(false)
    else
      t.idle := t.idle + 1

ember def tcp_tick := do
  for i in [0, N_CONNS) do
    tcb_load(i)
    conn_tick()
    tcb_save()

ember global booted : bool
ember global tick_due : bool

/-- `Net.main` with every connection reset on the first call. -/
ember def main := do
  if !booted then
    for i in [0, N_CONNS) do
      cur := i
      tcb_reset()
      tcb_save()
    booted := true
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    if len == 0 then
      tcp_tick()
      return
    if !tick_due then
      tick_due := true
      return
    over := true
    len := 0
    esc := false
    tick_due := false
    tcp_tick()
    tcp_tick()
    return
  slip_rx((k : u8))
  if tick_due && len == 0 then
    tick_due := false
    tcp_tick()

/-! ## The echo application -/

namespace Echo

ember def app_reset := do
  e_len[cur] := 0

ember def app_room (c : u16) : u16 := do
  return c - e_len[cur]

ember def app_recv (off : u16) (n : u16) := do
  let base : u16 := cur * OUR_MSS + e_len[cur]
  for i in [0, n) do
    pend[base + i] := buf[off + i]
  e_len[cur] := e_len[cur] + n

ember def app_avail : u16 := do
  return e_len[cur]

ember def app_fill (src : u16) (n : u16) (dst : u16) := do
  let base : u16 := cur * OUR_MSS + src
  for i in [0, n) do
    buf[dst + i] := pend[base + i]

ember def app_acked (n : u16) := do
  let base : u16 := cur * OUR_MSS
  for i in [0, e_len[cur] - n) do
    pend[base + i] := pend[base + i + n]
  e_len[cur] := e_len[cur] - n

ember def app_close : bool := do
  return false

end Echo

/-- An application: its globals and its functions. -/
structure App where
  globals : List Global
  fns : List Fn

/-- The echo application for `n` connections with segments of `mss` bytes. -/
def echo (n mss : Nat) : App where
  globals :=
    [{ name := "APP_PORT", ty := .u16, init := [7], const := true },
     { name := "APP_IDLE_CLOSE", ty := .bool, init := [1], const := true },
     { name := "e_len", ty := .arr .u16 n },
     { name := "pend", ty := .arr .u8 (n * mss) }]
  fns := [Echo.app_reset, Echo.app_room, Echo.app_recv, Echo.app_avail, Echo.app_fill,
          Echo.app_acked, Echo.app_close]

/-- The SLIP build with `n` connections and the application `app`. -/
def prog (n : Nat) (app : App) : Prog :=
  let reused := [Net.rto, Net.cap, Net.seg_len, Net.send_syn_ack, Net.send_reset, Net.acceptable,
                 Net.rexmit, Net.parse_mss, Net.tcp_input]
  let tcp := [tcb_load, tcb_save, tcb_reset, wnd, tcp_emit, send_seg, output, busy_input,
              listen_input, ack_input, conn_input, tcp_segment, conn_tick, tcp_tick]
  let netState := Net.state.filter fun g => g.name != "t" && g.name != "pend"
  { structs := [Tcb, Net.Seg],
    globals := Net.constants ++ netState ++ [nConns n, t, cur] ++ connGlobals n ++ app.globals ++
      [booted, tick_due],
    fns := Net.fns ++ Net.ipFns ++ app.fns ++ reused ++ tcp ++ [main],
    dropReasons := Net.dropReasons, notes := Net.notes }

/-- The echo program on `n` connections (`Spec.Srv.echo`, SLIP, MTU 296). -/
def echoProg (n : Nat := 1) : Prog := prog n (echo n 256)

end Ember.Net.Srv
