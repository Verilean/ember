import Ember.Lang.Surface

/-!
# Ember.Net.Layout — data layout of the stack in Ember (M3.1)

One packet buffer, used for receiving and for transmitting: replies are
built in place.  The TCB is one record; the echo application's buffer is
the only other array.  RAM, host64 profile (see `Ember/Net/README.md`):

| | bytes |
|---|---|
| `buf` (MTU 296) | 296 |
| `pend` (one MSS) | 256 |
| `t : Tcb` | 44 |
| scalars | 13 |

The numbering of drop reasons (`D_*` constants) is the index into
`dropReasons`, which names them exactly as `Ember.Spec` does, so the two
traces' `drop reason=` lines can be compared.
-/

namespace Ember.Net
open Ember.Lang

/-! ## Constants (shared values with `Ember.Spec.Config`) -/

ember const OUR_IP : u32 := 167772161
ember const MTU : u16 := 296
ember const OUR_MSS : u16 := 256
ember const ECHO_PORT : u16 := 7
ember const TTL : u8 := 64
ember const RTO_INIT : u8 := 3
ember const RTO_MAX : u8 := 48
ember const MAX_RETRIES : u8 := 8
ember const TIME_WAIT_TICKS : u8 := 20
ember const IDLE_TICKS : u8 := 60
ember const ISS_INIT : u32 := 65536
ember const ISS_STEP : u32 := 65536

/-! TCP states: the codes of `Ember.Spec.Tcp.St.code`. -/
ember const LISTEN : u8 := 0
ember const SYN_RCVD : u8 := 1
ember const ESTABLISHED : u8 := 2
ember const CLOSE_WAIT : u8 := 3
ember const LAST_ACK : u8 := 4
ember const FIN_WAIT_1 : u8 := 5
ember const FIN_WAIT_2 : u8 := 6
ember const CLOSING : u8 := 7
ember const TIME_WAIT : u8 := 8

/-! TCP flags. -/
ember const F_FIN : u8 := 1
ember const F_SYN : u8 := 2
ember const F_RST : u8 := 4
ember const F_PSH : u8 := 8
ember const F_ACK : u8 := 16

/-- Drop reasons, by code; the names are `Ember.Spec`'s. -/
def dropReasons : List String :=
  ["oversize-frame", "short-packet", "bad-version", "bad-ihl", "bad-ip-checksum", "bad-length",
   "fragment", "ttl-zero", "not-for-us", "broadcast", "unsupported-protocol",
   "short-icmp", "bad-icmp-checksum", "unsupported-icmp-type",
   "short-udp", "bad-udp-length", "bad-udp-checksum", "udp-port-closed",
   "short-tcp", "bad-tcp-header", "bad-tcp-checksum", "tcp-port-closed",
   "rst-no-connection", "unsupported-second-connection", "rst-in-listen", "ack-in-listen",
   "no-syn-in-listen", "rst-out-of-window", "duplicate-syn", "out-of-window", "syn-in-window",
   "no-ack", "bad-ack-in-syn-rcvd", "ack-of-unsent", "out-of-order",
   "give-up", "fin-wait-2-timeout"]

ember const D_OVERSIZE : u8 := 0
ember const D_SHORT_PACKET : u8 := 1
ember const D_BAD_VERSION : u8 := 2
ember const D_BAD_IHL : u8 := 3
ember const D_BAD_IP_CHECKSUM : u8 := 4
ember const D_BAD_LENGTH : u8 := 5
ember const D_FRAGMENT : u8 := 6
ember const D_TTL_ZERO : u8 := 7
ember const D_NOT_FOR_US : u8 := 8
ember const D_BROADCAST : u8 := 9
ember const D_UNSUPPORTED_PROTOCOL : u8 := 10
ember const D_SHORT_ICMP : u8 := 11
ember const D_BAD_ICMP_CHECKSUM : u8 := 12
ember const D_UNSUPPORTED_ICMP_TYPE : u8 := 13
ember const D_SHORT_UDP : u8 := 14
ember const D_BAD_UDP_LENGTH : u8 := 15
ember const D_BAD_UDP_CHECKSUM : u8 := 16
ember const D_UDP_PORT_CLOSED : u8 := 17
ember const D_SHORT_TCP : u8 := 18
ember const D_BAD_TCP_HEADER : u8 := 19
ember const D_BAD_TCP_CHECKSUM : u8 := 20
ember const D_TCP_PORT_CLOSED : u8 := 21
ember const D_RST_NO_CONNECTION : u8 := 22
ember const D_SECOND_CONNECTION : u8 := 23
ember const D_RST_IN_LISTEN : u8 := 24
ember const D_ACK_IN_LISTEN : u8 := 25
ember const D_NO_SYN_IN_LISTEN : u8 := 26
ember const D_RST_OUT_OF_WINDOW : u8 := 27
ember const D_DUPLICATE_SYN : u8 := 28
ember const D_OUT_OF_WINDOW : u8 := 29
ember const D_SYN_IN_WINDOW : u8 := 30
ember const D_NO_ACK : u8 := 31
ember const D_BAD_ACK_SYN_RCVD : u8 := 32
ember const D_ACK_OF_UNSENT : u8 := 33
ember const D_OUT_OF_ORDER : u8 := 34
ember const D_GIVE_UP : u8 := 35
ember const D_FIN_WAIT_2_TIMEOUT : u8 := 36

def notes : List String := ["connection-reset-by-peer"]

/-! ## State -/

/-- The one connection (fields as `Ember.Spec.Tcp.Tcb`; `pend` holds the
echo application's bytes). -/
ember struct Tcb where
  st : u8
  rip : u32
  rport : u16
  snd_una : u32
  snd_nxt : u32
  rcv_nxt : u32
  pend_len : u16
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
ember global pend : [u8; 256]
ember global iss : u32 := 65536
ember global ip_id : u16 := 1

/-- The packet buffer and the SLIP receiver's state. -/
ember global buf : [u8; 296]
ember global len : u16
ember global esc : bool
ember global over : bool

/-- The segment being processed (parsed from `buf` by `tcp_input`). -/
ember struct Seg where
  src : u32
  sport : u16
  dport : u16
  seq : u32
  ack : u32
  flags : u8
  has_mss : bool
  mss : u16
  doff : u16
  dlen : u16

ember global sg : Seg

def constants : List Global :=
  [OUR_IP, MTU, OUR_MSS, ECHO_PORT, TTL, RTO_INIT, RTO_MAX, MAX_RETRIES, TIME_WAIT_TICKS, IDLE_TICKS,
   ISS_INIT, ISS_STEP, LISTEN, SYN_RCVD, ESTABLISHED, CLOSE_WAIT, LAST_ACK, FIN_WAIT_1, FIN_WAIT_2,
   CLOSING, TIME_WAIT, F_FIN, F_SYN, F_RST, F_PSH, F_ACK,
   D_OVERSIZE, D_SHORT_PACKET, D_BAD_VERSION, D_BAD_IHL, D_BAD_IP_CHECKSUM, D_BAD_LENGTH, D_FRAGMENT,
   D_TTL_ZERO, D_NOT_FOR_US, D_BROADCAST, D_UNSUPPORTED_PROTOCOL, D_SHORT_ICMP, D_BAD_ICMP_CHECKSUM,
   D_UNSUPPORTED_ICMP_TYPE, D_SHORT_UDP, D_BAD_UDP_LENGTH, D_BAD_UDP_CHECKSUM, D_UDP_PORT_CLOSED,
   D_SHORT_TCP, D_BAD_TCP_HEADER, D_BAD_TCP_CHECKSUM, D_TCP_PORT_CLOSED, D_RST_NO_CONNECTION,
   D_SECOND_CONNECTION, D_RST_IN_LISTEN, D_ACK_IN_LISTEN, D_NO_SYN_IN_LISTEN, D_RST_OUT_OF_WINDOW,
   D_DUPLICATE_SYN, D_OUT_OF_WINDOW, D_SYN_IN_WINDOW, D_NO_ACK, D_BAD_ACK_SYN_RCVD, D_ACK_OF_UNSENT,
   D_OUT_OF_ORDER, D_GIVE_UP, D_FIN_WAIT_2_TIMEOUT]

def state : List Global := [t, pend, iss, ip_id, buf, len, esc, over, sg]
def structs : List StructDef := [Tcb, Seg]

end Ember.Net
