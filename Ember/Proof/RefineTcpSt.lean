import Ember.Proof.RefineTcp
import Ember.Proof.TcpAttr

/-!
# Ember.Proof.RefineTcpSt — the state the TCP code works on, as one value (plan M5.5)

The TCP functions read and write six globals — the connection record
`t`, the segment record `sg`, the echo buffer `pend`, the packet buffer
`buf`, the identification counter `ip_id`, the initial sequence number
`iss` — and append lines to the trace.  `TW` collects them; `tcpSt st w`
is the state `st` with these set from `w`.  Every theorem about a TCP
function then has one shape,

```
call … (tcpSt st w) f args = .ok result (tcpSt st (F w))
```

with `F` a function on `TW` written in Lean, so the theorems compose by
rewriting.
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-- What the TCP code reads and writes. -/
structure TW where
  r : RawTcb
  sg : RawSeg
  pd : ByteArray
  b : ByteArray
  id : UInt16
  iss : UInt32
  /-- Trace lines appended so far. -/
  evs : List Trace.Event

/-- The state `st` with the TCP globals from `w` and `w.evs` appended to the trace. -/
def tcpSt (st : St) (w : TW) : St :=
  setG (setG (setG (setG (setG (setG { st with world := w.evs.foldl World.emit st.world }
    "t" w.r.val) "sg" w.sg.val) "pend" (bufVal w.pd)) "buf" (bufVal w.b)) "ip_id" (u16 w.id)) "iss" (u32 w.iss)

/-- The TCP globals exist, and no frame is half transmitted. -/
structure TcpBase (st : St) : Prop where
  h_t : ∃ v, st.globals.lookup "t" = some v
  h_sg : ∃ v, st.globals.lookup "sg" = some v
  h_pend : ∃ v, st.globals.lookup "pend" = some v
  h_buf : ∃ v, st.globals.lookup "buf" = some v
  h_ip_id : ∃ v, st.globals.lookup "ip_id" = some v
  h_iss : ∃ v, st.globals.lookup "iss" = some v
  frame : st.world.frame = .empty

@[simp] theorem world_tcpSt (st : St) (w : TW) : (tcpSt st w).world = w.evs.foldl World.emit st.world := rfl

theorem lookup_tcpSt_ne (st : St) (w : TW) (x : String) (h0 : x ≠ "t") (h1 : x ≠ "sg") (h2 : x ≠ "pend") (h3 : x ≠ "buf") (h4 : x ≠ "ip_id") (h5 : x ≠ "iss") :
    (tcpSt st w).globals.lookup x = st.globals.lookup x := by
  simp only [tcpSt]
  rw [lookup_setG_ne _ _ _ _ (Ne.symm h5), lookup_setG_ne _ _ _ _ (Ne.symm h4), lookup_setG_ne _ _ _ _ (Ne.symm h3), lookup_setG_ne _ _ _ _ (Ne.symm h2), lookup_setG_ne _ _ _ _ (Ne.symm h1), lookup_setG_ne _ _ _ _ (Ne.symm h0)]

theorem lookup_tcpSt_t (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "t" = some (w.r.val) := by
  obtain ⟨v, hv⟩ := hB.h_t
  simp only [tcpSt]
  rw [lookup_setG_ne _ "iss" "t" _ (by decide), lookup_setG_ne _ "ip_id" "t" _ (by decide), lookup_setG_ne _ "buf" "t" _ (by decide), lookup_setG_ne _ "pend" "t" _ (by decide), lookup_setG_ne _ "sg" "t" _ (by decide), lookup_setG_self]
  simp only [hv, Option.isSome_some, if_true]

theorem setG_tcpSt_t (st : St) (w : TW) (v : RawTcb) :
    setG (tcpSt st w) "t" (v.val) = tcpSt st { w with r := v } := by
  simp only [tcpSt]
  rw [setG_comm _ "iss" "t" _ _ (by decide)]
  rw [setG_comm _ "ip_id" "t" _ _ (by decide)]
  rw [setG_comm _ "buf" "t" _ _ (by decide)]
  rw [setG_comm _ "pend" "t" _ _ (by decide)]
  rw [setG_comm _ "sg" "t" _ _ (by decide)]
  rw [setG_setG]

theorem lookup_tcpSt_sg (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "sg" = some (w.sg.val) := by
  obtain ⟨v, hv⟩ := hB.h_sg
  simp only [tcpSt]
  rw [lookup_setG_ne _ "iss" "sg" _ (by decide), lookup_setG_ne _ "ip_id" "sg" _ (by decide), lookup_setG_ne _ "buf" "sg" _ (by decide), lookup_setG_ne _ "pend" "sg" _ (by decide), lookup_setG_self]
  simp only [lookup_setG_ne _ "t" "sg" _ (by decide), hv, Option.isSome_some, if_true]

theorem setG_tcpSt_sg (st : St) (w : TW) (v : RawSeg) :
    setG (tcpSt st w) "sg" (v.val) = tcpSt st { w with sg := v } := by
  simp only [tcpSt]
  rw [setG_comm _ "iss" "sg" _ _ (by decide)]
  rw [setG_comm _ "ip_id" "sg" _ _ (by decide)]
  rw [setG_comm _ "buf" "sg" _ _ (by decide)]
  rw [setG_comm _ "pend" "sg" _ _ (by decide)]
  rw [setG_setG]

theorem lookup_tcpSt_pend (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "pend" = some (bufVal w.pd) := by
  obtain ⟨v, hv⟩ := hB.h_pend
  simp only [tcpSt]
  rw [lookup_setG_ne _ "iss" "pend" _ (by decide), lookup_setG_ne _ "ip_id" "pend" _ (by decide), lookup_setG_ne _ "buf" "pend" _ (by decide), lookup_setG_self]
  simp only [lookup_setG_ne _ "sg" "pend" _ (by decide), lookup_setG_ne _ "t" "pend" _ (by decide), hv, Option.isSome_some, if_true]

theorem setG_tcpSt_pend (st : St) (w : TW) (v : ByteArray) :
    setG (tcpSt st w) "pend" (bufVal v) = tcpSt st { w with pd := v } := by
  simp only [tcpSt]
  rw [setG_comm _ "iss" "pend" _ _ (by decide)]
  rw [setG_comm _ "ip_id" "pend" _ _ (by decide)]
  rw [setG_comm _ "buf" "pend" _ _ (by decide)]
  rw [setG_setG]

theorem lookup_tcpSt_buf (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "buf" = some (bufVal w.b) := by
  obtain ⟨v, hv⟩ := hB.h_buf
  simp only [tcpSt]
  rw [lookup_setG_ne _ "iss" "buf" _ (by decide), lookup_setG_ne _ "ip_id" "buf" _ (by decide), lookup_setG_self]
  simp only [lookup_setG_ne _ "pend" "buf" _ (by decide), lookup_setG_ne _ "sg" "buf" _ (by decide), lookup_setG_ne _ "t" "buf" _ (by decide), hv, Option.isSome_some, if_true]

theorem setG_tcpSt_buf (st : St) (w : TW) (v : ByteArray) :
    setG (tcpSt st w) "buf" (bufVal v) = tcpSt st { w with b := v } := by
  simp only [tcpSt]
  rw [setG_comm _ "iss" "buf" _ _ (by decide)]
  rw [setG_comm _ "ip_id" "buf" _ _ (by decide)]
  rw [setG_setG]

theorem lookup_tcpSt_ip_id (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "ip_id" = some (u16 w.id) := by
  obtain ⟨v, hv⟩ := hB.h_ip_id
  simp only [tcpSt]
  rw [lookup_setG_ne _ "iss" "ip_id" _ (by decide), lookup_setG_self]
  simp only [lookup_setG_ne _ "buf" "ip_id" _ (by decide), lookup_setG_ne _ "pend" "ip_id" _ (by decide), lookup_setG_ne _ "sg" "ip_id" _ (by decide), lookup_setG_ne _ "t" "ip_id" _ (by decide), hv, Option.isSome_some, if_true]

theorem setG_tcpSt_ip_id (st : St) (w : TW) (v : UInt16) :
    setG (tcpSt st w) "ip_id" (u16 v) = tcpSt st { w with id := v } := by
  simp only [tcpSt]
  rw [setG_comm _ "iss" "ip_id" _ _ (by decide)]
  rw [setG_setG]

theorem lookup_tcpSt_iss (st : St) (hB : TcpBase st) (w : TW) :
    (tcpSt st w).globals.lookup "iss" = some (u32 w.iss) := by
  obtain ⟨v, hv⟩ := hB.h_iss
  simp only [tcpSt]
  rw [lookup_setG_self]
  simp only [lookup_setG_ne _ "ip_id" "iss" _ (by decide), lookup_setG_ne _ "buf" "iss" _ (by decide), lookup_setG_ne _ "pend" "iss" _ (by decide), lookup_setG_ne _ "sg" "iss" _ (by decide), lookup_setG_ne _ "t" "iss" _ (by decide), hv, Option.isSome_some, if_true]

theorem setG_tcpSt_iss (st : St) (w : TW) (v : UInt32) :
    setG (tcpSt st w) "iss" (u32 v) = tcpSt st { w with iss := v } := by
  simp only [tcpSt]
  rw [setG_setG]


/-! ## GENERATED: constants, fields, effects (tools: scratch generator) -/

/-- The constants of the stack have their values. -/
structure TcpConsts (st : St) : Prop where
  MTU : st.globals.lookup "MTU" = some (u16 296)
  OUR_MSS : st.globals.lookup "OUR_MSS" = some (u16 256)
  ECHO_PORT : st.globals.lookup "ECHO_PORT" = some (u16 7)
  TTL : st.globals.lookup "TTL" = some (u8 64)
  RTO_INIT : st.globals.lookup "RTO_INIT" = some (u8 3)
  RTO_MAX : st.globals.lookup "RTO_MAX" = some (u8 48)
  MAX_RETRIES : st.globals.lookup "MAX_RETRIES" = some (u8 8)
  TIME_WAIT_TICKS : st.globals.lookup "TIME_WAIT_TICKS" = some (u8 20)
  IDLE_TICKS : st.globals.lookup "IDLE_TICKS" = some (u8 60)
  ISS_INIT : st.globals.lookup "ISS_INIT" = some (u32 65536)
  ISS_STEP : st.globals.lookup "ISS_STEP" = some (u32 65536)
  LISTEN : st.globals.lookup "LISTEN" = some (u8 0)
  SYN_RCVD : st.globals.lookup "SYN_RCVD" = some (u8 1)
  ESTABLISHED : st.globals.lookup "ESTABLISHED" = some (u8 2)
  CLOSE_WAIT : st.globals.lookup "CLOSE_WAIT" = some (u8 3)
  LAST_ACK : st.globals.lookup "LAST_ACK" = some (u8 4)
  FIN_WAIT_1 : st.globals.lookup "FIN_WAIT_1" = some (u8 5)
  FIN_WAIT_2 : st.globals.lookup "FIN_WAIT_2" = some (u8 6)
  CLOSING : st.globals.lookup "CLOSING" = some (u8 7)
  TIME_WAIT : st.globals.lookup "TIME_WAIT" = some (u8 8)
  F_FIN : st.globals.lookup "F_FIN" = some (u8 1)
  F_SYN : st.globals.lookup "F_SYN" = some (u8 2)
  F_RST : st.globals.lookup "F_RST" = some (u8 4)
  F_PSH : st.globals.lookup "F_PSH" = some (u8 8)
  F_ACK : st.globals.lookup "F_ACK" = some (u8 16)
  D_OVERSIZE : st.globals.lookup "D_OVERSIZE" = some (u8 0)
  D_SHORT_PACKET : st.globals.lookup "D_SHORT_PACKET" = some (u8 1)
  D_BAD_VERSION : st.globals.lookup "D_BAD_VERSION" = some (u8 2)
  D_BAD_IHL : st.globals.lookup "D_BAD_IHL" = some (u8 3)
  D_BAD_IP_CHECKSUM : st.globals.lookup "D_BAD_IP_CHECKSUM" = some (u8 4)
  D_BAD_LENGTH : st.globals.lookup "D_BAD_LENGTH" = some (u8 5)
  D_FRAGMENT : st.globals.lookup "D_FRAGMENT" = some (u8 6)
  D_TTL_ZERO : st.globals.lookup "D_TTL_ZERO" = some (u8 7)
  D_NOT_FOR_US : st.globals.lookup "D_NOT_FOR_US" = some (u8 8)
  D_BROADCAST : st.globals.lookup "D_BROADCAST" = some (u8 9)
  D_UNSUPPORTED_PROTOCOL : st.globals.lookup "D_UNSUPPORTED_PROTOCOL" = some (u8 10)
  D_SHORT_ICMP : st.globals.lookup "D_SHORT_ICMP" = some (u8 11)
  D_BAD_ICMP_CHECKSUM : st.globals.lookup "D_BAD_ICMP_CHECKSUM" = some (u8 12)
  D_UNSUPPORTED_ICMP_TYPE : st.globals.lookup "D_UNSUPPORTED_ICMP_TYPE" = some (u8 13)
  D_SHORT_UDP : st.globals.lookup "D_SHORT_UDP" = some (u8 14)
  D_BAD_UDP_LENGTH : st.globals.lookup "D_BAD_UDP_LENGTH" = some (u8 15)
  D_BAD_UDP_CHECKSUM : st.globals.lookup "D_BAD_UDP_CHECKSUM" = some (u8 16)
  D_UDP_PORT_CLOSED : st.globals.lookup "D_UDP_PORT_CLOSED" = some (u8 17)
  D_SHORT_TCP : st.globals.lookup "D_SHORT_TCP" = some (u8 18)
  D_BAD_TCP_HEADER : st.globals.lookup "D_BAD_TCP_HEADER" = some (u8 19)
  D_BAD_TCP_CHECKSUM : st.globals.lookup "D_BAD_TCP_CHECKSUM" = some (u8 20)
  D_TCP_PORT_CLOSED : st.globals.lookup "D_TCP_PORT_CLOSED" = some (u8 21)
  D_RST_NO_CONNECTION : st.globals.lookup "D_RST_NO_CONNECTION" = some (u8 22)
  D_SECOND_CONNECTION : st.globals.lookup "D_SECOND_CONNECTION" = some (u8 23)
  D_RST_IN_LISTEN : st.globals.lookup "D_RST_IN_LISTEN" = some (u8 24)
  D_ACK_IN_LISTEN : st.globals.lookup "D_ACK_IN_LISTEN" = some (u8 25)
  D_NO_SYN_IN_LISTEN : st.globals.lookup "D_NO_SYN_IN_LISTEN" = some (u8 26)
  D_RST_OUT_OF_WINDOW : st.globals.lookup "D_RST_OUT_OF_WINDOW" = some (u8 27)
  D_DUPLICATE_SYN : st.globals.lookup "D_DUPLICATE_SYN" = some (u8 28)
  D_OUT_OF_WINDOW : st.globals.lookup "D_OUT_OF_WINDOW" = some (u8 29)
  D_SYN_IN_WINDOW : st.globals.lookup "D_SYN_IN_WINDOW" = some (u8 30)
  D_NO_ACK : st.globals.lookup "D_NO_ACK" = some (u8 31)
  D_BAD_ACK_SYN_RCVD : st.globals.lookup "D_BAD_ACK_SYN_RCVD" = some (u8 32)
  D_ACK_OF_UNSENT : st.globals.lookup "D_ACK_OF_UNSENT" = some (u8 33)
  D_OUT_OF_ORDER : st.globals.lookup "D_OUT_OF_ORDER" = some (u8 34)
  D_GIVE_UP : st.globals.lookup "D_GIVE_UP" = some (u8 35)
  D_FIN_WAIT_2_TIMEOUT : st.globals.lookup "D_FIN_WAIT_2_TIMEOUT" = some (u8 36)

@[tcpsym] theorem c_MTU (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "MTU" = some (u16 296) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.MTU

@[tcpsym] theorem c_OUR_MSS (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "OUR_MSS" = some (u16 256) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.OUR_MSS

@[tcpsym] theorem c_ECHO_PORT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "ECHO_PORT" = some (u16 7) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.ECHO_PORT

@[tcpsym] theorem c_TTL (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "TTL" = some (u8 64) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.TTL

@[tcpsym] theorem c_RTO_INIT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "RTO_INIT" = some (u8 3) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.RTO_INIT

@[tcpsym] theorem c_RTO_MAX (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "RTO_MAX" = some (u8 48) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.RTO_MAX

@[tcpsym] theorem c_MAX_RETRIES (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "MAX_RETRIES" = some (u8 8) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.MAX_RETRIES

@[tcpsym] theorem c_TIME_WAIT_TICKS (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "TIME_WAIT_TICKS" = some (u8 20) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.TIME_WAIT_TICKS

@[tcpsym] theorem c_IDLE_TICKS (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "IDLE_TICKS" = some (u8 60) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.IDLE_TICKS

@[tcpsym] theorem c_ISS_INIT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "ISS_INIT" = some (u32 65536) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.ISS_INIT

@[tcpsym] theorem c_ISS_STEP (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "ISS_STEP" = some (u32 65536) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.ISS_STEP

@[tcpsym] theorem c_LISTEN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "LISTEN" = some (u8 0) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.LISTEN

@[tcpsym] theorem c_SYN_RCVD (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "SYN_RCVD" = some (u8 1) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.SYN_RCVD

@[tcpsym] theorem c_ESTABLISHED (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "ESTABLISHED" = some (u8 2) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.ESTABLISHED

@[tcpsym] theorem c_CLOSE_WAIT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "CLOSE_WAIT" = some (u8 3) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.CLOSE_WAIT

@[tcpsym] theorem c_LAST_ACK (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "LAST_ACK" = some (u8 4) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.LAST_ACK

@[tcpsym] theorem c_FIN_WAIT_1 (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "FIN_WAIT_1" = some (u8 5) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.FIN_WAIT_1

@[tcpsym] theorem c_FIN_WAIT_2 (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "FIN_WAIT_2" = some (u8 6) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.FIN_WAIT_2

@[tcpsym] theorem c_CLOSING (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "CLOSING" = some (u8 7) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.CLOSING

@[tcpsym] theorem c_TIME_WAIT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "TIME_WAIT" = some (u8 8) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.TIME_WAIT

@[tcpsym] theorem c_F_FIN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "F_FIN" = some (u8 1) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.F_FIN

@[tcpsym] theorem c_F_SYN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "F_SYN" = some (u8 2) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.F_SYN

@[tcpsym] theorem c_F_RST (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "F_RST" = some (u8 4) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.F_RST

@[tcpsym] theorem c_F_PSH (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "F_PSH" = some (u8 8) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.F_PSH

@[tcpsym] theorem c_F_ACK (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "F_ACK" = some (u8 16) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.F_ACK

@[tcpsym] theorem c_D_OVERSIZE (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_OVERSIZE" = some (u8 0) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_OVERSIZE

@[tcpsym] theorem c_D_SHORT_PACKET (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SHORT_PACKET" = some (u8 1) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SHORT_PACKET

@[tcpsym] theorem c_D_BAD_VERSION (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_VERSION" = some (u8 2) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_VERSION

@[tcpsym] theorem c_D_BAD_IHL (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_IHL" = some (u8 3) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_IHL

@[tcpsym] theorem c_D_BAD_IP_CHECKSUM (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_IP_CHECKSUM" = some (u8 4) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_IP_CHECKSUM

@[tcpsym] theorem c_D_BAD_LENGTH (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_LENGTH" = some (u8 5) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_LENGTH

@[tcpsym] theorem c_D_FRAGMENT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_FRAGMENT" = some (u8 6) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_FRAGMENT

@[tcpsym] theorem c_D_TTL_ZERO (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_TTL_ZERO" = some (u8 7) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_TTL_ZERO

@[tcpsym] theorem c_D_NOT_FOR_US (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_NOT_FOR_US" = some (u8 8) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_NOT_FOR_US

@[tcpsym] theorem c_D_BROADCAST (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BROADCAST" = some (u8 9) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BROADCAST

@[tcpsym] theorem c_D_UNSUPPORTED_PROTOCOL (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_UNSUPPORTED_PROTOCOL" = some (u8 10) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_UNSUPPORTED_PROTOCOL

@[tcpsym] theorem c_D_SHORT_ICMP (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SHORT_ICMP" = some (u8 11) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SHORT_ICMP

@[tcpsym] theorem c_D_BAD_ICMP_CHECKSUM (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_ICMP_CHECKSUM" = some (u8 12) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_ICMP_CHECKSUM

@[tcpsym] theorem c_D_UNSUPPORTED_ICMP_TYPE (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_UNSUPPORTED_ICMP_TYPE" = some (u8 13) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_UNSUPPORTED_ICMP_TYPE

@[tcpsym] theorem c_D_SHORT_UDP (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SHORT_UDP" = some (u8 14) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SHORT_UDP

@[tcpsym] theorem c_D_BAD_UDP_LENGTH (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_UDP_LENGTH" = some (u8 15) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_UDP_LENGTH

@[tcpsym] theorem c_D_BAD_UDP_CHECKSUM (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_UDP_CHECKSUM" = some (u8 16) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_UDP_CHECKSUM

@[tcpsym] theorem c_D_UDP_PORT_CLOSED (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_UDP_PORT_CLOSED" = some (u8 17) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_UDP_PORT_CLOSED

@[tcpsym] theorem c_D_SHORT_TCP (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SHORT_TCP" = some (u8 18) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SHORT_TCP

@[tcpsym] theorem c_D_BAD_TCP_HEADER (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_TCP_HEADER" = some (u8 19) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_TCP_HEADER

@[tcpsym] theorem c_D_BAD_TCP_CHECKSUM (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_TCP_CHECKSUM" = some (u8 20) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_TCP_CHECKSUM

@[tcpsym] theorem c_D_TCP_PORT_CLOSED (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_TCP_PORT_CLOSED" = some (u8 21) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_TCP_PORT_CLOSED

@[tcpsym] theorem c_D_RST_NO_CONNECTION (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_RST_NO_CONNECTION" = some (u8 22) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_RST_NO_CONNECTION

@[tcpsym] theorem c_D_SECOND_CONNECTION (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SECOND_CONNECTION" = some (u8 23) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SECOND_CONNECTION

@[tcpsym] theorem c_D_RST_IN_LISTEN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_RST_IN_LISTEN" = some (u8 24) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_RST_IN_LISTEN

@[tcpsym] theorem c_D_ACK_IN_LISTEN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_ACK_IN_LISTEN" = some (u8 25) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_ACK_IN_LISTEN

@[tcpsym] theorem c_D_NO_SYN_IN_LISTEN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_NO_SYN_IN_LISTEN" = some (u8 26) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_NO_SYN_IN_LISTEN

@[tcpsym] theorem c_D_RST_OUT_OF_WINDOW (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_RST_OUT_OF_WINDOW" = some (u8 27) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_RST_OUT_OF_WINDOW

@[tcpsym] theorem c_D_DUPLICATE_SYN (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_DUPLICATE_SYN" = some (u8 28) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_DUPLICATE_SYN

@[tcpsym] theorem c_D_OUT_OF_WINDOW (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_OUT_OF_WINDOW" = some (u8 29) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_OUT_OF_WINDOW

@[tcpsym] theorem c_D_SYN_IN_WINDOW (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_SYN_IN_WINDOW" = some (u8 30) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_SYN_IN_WINDOW

@[tcpsym] theorem c_D_NO_ACK (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_NO_ACK" = some (u8 31) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_NO_ACK

@[tcpsym] theorem c_D_BAD_ACK_SYN_RCVD (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_BAD_ACK_SYN_RCVD" = some (u8 32) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_BAD_ACK_SYN_RCVD

@[tcpsym] theorem c_D_ACK_OF_UNSENT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_ACK_OF_UNSENT" = some (u8 33) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_ACK_OF_UNSENT

@[tcpsym] theorem c_D_OUT_OF_ORDER (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_OUT_OF_ORDER" = some (u8 34) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_OUT_OF_ORDER

@[tcpsym] theorem c_D_GIVE_UP (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_GIVE_UP" = some (u8 35) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_GIVE_UP

@[tcpsym] theorem c_D_FIN_WAIT_2_TIMEOUT (st : St) (hK : TcpConsts st) (w : TW) :
    (tcpSt st w).globals.lookup "D_FIN_WAIT_2_TIMEOUT" = some (u8 36) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK.D_FIN_WAIT_2_TIMEOUT

theorem c_OUR_IP (st : St) (ourIp : UInt32) (h : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW) :
    (tcpSt st w).globals.lookup "OUR_IP" = some (u32 ourIp) := by
  rw [lookup_tcpSt_ne st w _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h

attribute [tcpsym] lookup_tcpSt_t lookup_tcpSt_sg lookup_tcpSt_pend lookup_tcpSt_buf lookup_tcpSt_ip_id
  lookup_tcpSt_iss

@[tcpsym] theorem getW_t_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "st") = some (u8 w.r.st) :=
  RawTcb.get_st p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_st (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "st") (u8 x)
      = some (tcpSt st { w with r := { w.r with st := x } }, env) := by
  rw [RawTcb.set_st p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "rip") = some (u32 w.r.rip) :=
  RawTcb.get_rip p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_rip (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "rip") (u32 x)
      = some (tcpSt st { w with r := { w.r with rip := x } }, env) := by
  rw [RawTcb.set_rip p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "rport") = some (u16 w.r.rport) :=
  RawTcb.get_rport p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_rport (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "rport") (u16 x)
      = some (tcpSt st { w with r := { w.r with rport := x } }, env) := by
  rw [RawTcb.set_rport p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "snd_una") = some (u32 w.r.snd_una) :=
  RawTcb.get_snd_una p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_snd_una (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "snd_una") (u32 x)
      = some (tcpSt st { w with r := { w.r with snd_una := x } }, env) := by
  rw [RawTcb.set_snd_una p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "snd_nxt") = some (u32 w.r.snd_nxt) :=
  RawTcb.get_snd_nxt p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_snd_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "snd_nxt") (u32 x)
      = some (tcpSt st { w with r := { w.r with snd_nxt := x } }, env) := by
  rw [RawTcb.set_snd_nxt p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "rcv_nxt") = some (u32 w.r.rcv_nxt) :=
  RawTcb.get_rcv_nxt p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_rcv_nxt (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "rcv_nxt") (u32 x)
      = some (tcpSt st { w with r := { w.r with rcv_nxt := x } }, env) := by
  rw [RawTcb.set_rcv_nxt p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "pend_len") = some (u16 w.r.pend_len) :=
  RawTcb.get_pend_len p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_pend_len (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "pend_len") (u16 x)
      = some (tcpSt st { w with r := { w.r with pend_len := x } }, env) := by
  rw [RawTcb.set_pend_len p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "sent") = some (u16 w.r.sent) :=
  RawTcb.get_sent p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "sent") (u16 x)
      = some (tcpSt st { w with r := { w.r with sent := x } }, env) := by
  rw [RawTcb.set_sent p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "fin_sent") = some (Val.bool w.r.fin_sent) :=
  RawTcb.get_fin_sent p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_fin_sent (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : Bool) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "fin_sent") (Val.bool x)
      = some (tcpSt st { w with r := { w.r with fin_sent := x } }, env) := by
  rw [RawTcb.set_fin_sent p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "peer_mss") = some (u16 w.r.peer_mss) :=
  RawTcb.get_peer_mss p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_peer_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "peer_mss") (u16 x)
      = some (tcpSt st { w with r := { w.r with peer_mss := x } }, env) := by
  rw [RawTcb.set_peer_mss p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "our_mss") = some (u16 w.r.our_mss) :=
  RawTcb.get_our_mss p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_our_mss (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "our_mss") (u16 x)
      = some (tcpSt st { w with r := { w.r with our_mss := x } }, env) := by
  rw [RawTcb.set_our_mss p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "last_wnd") = some (u16 w.r.last_wnd) :=
  RawTcb.get_last_wnd p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_last_wnd (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "last_wnd") (u16 x)
      = some (tcpSt st { w with r := { w.r with last_wnd := x } }, env) := by
  rw [RawTcb.set_last_wnd p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "rt_timer") = some (u8 w.r.rt_timer) :=
  RawTcb.get_rt_timer p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_rt_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "rt_timer") (u8 x)
      = some (tcpSt st { w with r := { w.r with rt_timer := x } }, env) := by
  rw [RawTcb.set_rt_timer p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "retries") = some (u8 w.r.retries) :=
  RawTcb.get_retries p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_retries (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "retries") (u8 x)
      = some (tcpSt st { w with r := { w.r with retries := x } }, env) := by
  rw [RawTcb.set_retries p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "tw_timer") = some (u8 w.r.tw_timer) :=
  RawTcb.get_tw_timer p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_tw_timer (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "tw_timer") (u8 x)
      = some (tcpSt st { w with r := { w.r with tw_timer := x } }, env) := by
  rw [RawTcb.set_tw_timer p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "idle") = some (u8 w.r.idle) :=
  RawTcb.get_idle p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_idle (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "idle") (u8 x)
      = some (tcpSt st { w with r := { w.r with idle := x } }, env) := by
  rw [RawTcb.set_idle p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_t_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "t" = none) :
    evalE p (tcpSt st w) env (.field (.var "t") "close_req") = some (Val.bool w.r.close_req) :=
  RawTcb.get_close_req p hS _ env w.r (by simp only [lookup, hl]; exact lookup_tcpSt_t st hB w)

@[tcpsym] theorem setW_t_close_req (p : Prog) (hS : p.struct? "Tcb" = some Net.Tcb) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : Bool) (hl : env.lookup "t" = none) :
    assign p (tcpSt st w) env (.field (.var "t") "close_req") (Val.bool x)
      = some (tcpSt st { w with r := { w.r with close_req := x } }, env) := by
  rw [RawTcb.set_close_req p hS _ env w.r x hl (lookup_tcpSt_t st hB w), setG_tcpSt_t]

@[tcpsym] theorem getW_sg_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "src") = some (u32 w.sg.src) :=
  RawSeg.get_src p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_src (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "src") (u32 x)
      = some (tcpSt st { w with sg := { w.sg with src := x } }, env) := by
  rw [RawSeg.set_src p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "sport") = some (u16 w.sg.sport) :=
  RawSeg.get_sport p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_sport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "sport") (u16 x)
      = some (tcpSt st { w with sg := { w.sg with sport := x } }, env) := by
  rw [RawSeg.set_sport p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "dport") = some (u16 w.sg.dport) :=
  RawSeg.get_dport p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_dport (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "dport") (u16 x)
      = some (tcpSt st { w with sg := { w.sg with dport := x } }, env) := by
  rw [RawSeg.set_dport p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "seq") = some (u32 w.sg.seq) :=
  RawSeg.get_seq p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_seq (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "seq") (u32 x)
      = some (tcpSt st { w with sg := { w.sg with seq := x } }, env) := by
  rw [RawSeg.set_seq p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "ack") = some (u32 w.sg.ack) :=
  RawSeg.get_ack p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_ack (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt32) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "ack") (u32 x)
      = some (tcpSt st { w with sg := { w.sg with ack := x } }, env) := by
  rw [RawSeg.set_ack p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "flags") = some (u8 w.sg.flags) :=
  RawSeg.get_flags p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_flags (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt8) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "flags") (u8 x)
      = some (tcpSt st { w with sg := { w.sg with flags := x } }, env) := by
  rw [RawSeg.set_flags p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "has_mss") = some (Val.bool w.sg.has_mss) :=
  RawSeg.get_has_mss p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_has_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : Bool) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "has_mss") (Val.bool x)
      = some (tcpSt st { w with sg := { w.sg with has_mss := x } }, env) := by
  rw [RawSeg.set_has_mss p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "mss") = some (u16 w.sg.mss) :=
  RawSeg.get_mss p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_mss (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "mss") (u16 x)
      = some (tcpSt st { w with sg := { w.sg with mss := x } }, env) := by
  rw [RawSeg.set_mss p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "doff") = some (u16 w.sg.doff) :=
  RawSeg.get_doff p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_doff (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "doff") (u16 x)
      = some (tcpSt st { w with sg := { w.sg with doff := x } }, env) := by
  rw [RawSeg.set_doff p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

@[tcpsym] theorem getW_sg_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (hl : env.lookup "sg" = none) :
    evalE p (tcpSt st w) env (.field (.var "sg") "dlen") = some (u16 w.sg.dlen) :=
  RawSeg.get_dlen p hS _ env w.sg (by simp only [lookup, hl]; exact lookup_tcpSt_sg st hB w)

@[tcpsym] theorem setW_sg_dlen (p : Prog) (hS : p.struct? "Seg" = some Net.Seg) (st : St) (hB : TcpBase st)
    (w : TW) (env : Env) (x : UInt16) (hl : env.lookup "sg" = none) :
    assign p (tcpSt st w) env (.field (.var "sg") "dlen") (u16 x)
      = some (tcpSt st { w with sg := { w.sg with dlen := x } }, env) := by
  rw [RawSeg.set_dlen p hS _ env w.sg x hl (lookup_tcpSt_sg st hB w), setG_tcpSt_sg]

/-! ## Effects -/

theorem foldl_emit_append (w : World) (evs : List Trace.Event) (e : Trace.Event) :
    (evs ++ [e]).foldl World.emit w = (evs.foldl World.emit w).emit e := by
  rw [List.foldl_append]; rfl

@[tcpsym] theorem dropSt_tcpSt (st : St) (w : TW) (r : String) :
    dropSt (tcpSt st w) r = tcpSt st { w with evs := w.evs ++ [.drop r] } := by
  simp only [dropSt, tcpSt, setG, foldl_emit_append]

/-- The trace-line reasons of the TCP code. -/
structure TcpReasons (p : Prog) : Prop where
  r18 : p.dropReasons[18]? = some "short-tcp"
  r19 : p.dropReasons[19]? = some "bad-tcp-header"
  r20 : p.dropReasons[20]? = some "bad-tcp-checksum"
  r21 : p.dropReasons[21]? = some "tcp-port-closed"
  r22 : p.dropReasons[22]? = some "rst-no-connection"
  r23 : p.dropReasons[23]? = some "unsupported-second-connection"
  r24 : p.dropReasons[24]? = some "rst-in-listen"
  r25 : p.dropReasons[25]? = some "ack-in-listen"
  r26 : p.dropReasons[26]? = some "no-syn-in-listen"
  r27 : p.dropReasons[27]? = some "rst-out-of-window"
  r28 : p.dropReasons[28]? = some "duplicate-syn"
  r29 : p.dropReasons[29]? = some "out-of-window"
  r30 : p.dropReasons[30]? = some "syn-in-window"
  r31 : p.dropReasons[31]? = some "no-ack"
  r32 : p.dropReasons[32]? = some "bad-ack-in-syn-rcvd"
  r33 : p.dropReasons[33]? = some "ack-of-unsent"
  r34 : p.dropReasons[34]? = some "out-of-order"
  r35 : p.dropReasons[35]? = some "give-up"
  r36 : p.dropReasons[36]? = some "fin-wait-2-timeout"
  note0 : p.notes[0]? = some "connection-reset-by-peer"

@[tcpsym] theorem drop_D_SHORT_TCP (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_SHORT_TCP" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_SHORT_TCP"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "short-tcp"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_SHORT_TCP") = some (u8 18) := by
    simp only [evalE, lookup, hl]; exact c_D_SHORT_TCP st hK w
  rw [execS_drop p _ env n _ 18 "short-tcp" he hR.r18, dropSt_tcpSt]

@[tcpsym] theorem drop_D_BAD_TCP_HEADER (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_BAD_TCP_HEADER" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_BAD_TCP_HEADER"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "bad-tcp-header"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_BAD_TCP_HEADER") = some (u8 19) := by
    simp only [evalE, lookup, hl]; exact c_D_BAD_TCP_HEADER st hK w
  rw [execS_drop p _ env n _ 19 "bad-tcp-header" he hR.r19, dropSt_tcpSt]

@[tcpsym] theorem drop_D_BAD_TCP_CHECKSUM (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_BAD_TCP_CHECKSUM" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_BAD_TCP_CHECKSUM"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "bad-tcp-checksum"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_BAD_TCP_CHECKSUM") = some (u8 20) := by
    simp only [evalE, lookup, hl]; exact c_D_BAD_TCP_CHECKSUM st hK w
  rw [execS_drop p _ env n _ 20 "bad-tcp-checksum" he hR.r20, dropSt_tcpSt]

@[tcpsym] theorem drop_D_TCP_PORT_CLOSED (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_TCP_PORT_CLOSED" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_TCP_PORT_CLOSED"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "tcp-port-closed"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_TCP_PORT_CLOSED") = some (u8 21) := by
    simp only [evalE, lookup, hl]; exact c_D_TCP_PORT_CLOSED st hK w
  rw [execS_drop p _ env n _ 21 "tcp-port-closed" he hR.r21, dropSt_tcpSt]

@[tcpsym] theorem drop_D_RST_NO_CONNECTION (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_RST_NO_CONNECTION" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_RST_NO_CONNECTION"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "rst-no-connection"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_RST_NO_CONNECTION") = some (u8 22) := by
    simp only [evalE, lookup, hl]; exact c_D_RST_NO_CONNECTION st hK w
  rw [execS_drop p _ env n _ 22 "rst-no-connection" he hR.r22, dropSt_tcpSt]

@[tcpsym] theorem drop_D_SECOND_CONNECTION (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_SECOND_CONNECTION" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_SECOND_CONNECTION"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "unsupported-second-connection"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_SECOND_CONNECTION") = some (u8 23) := by
    simp only [evalE, lookup, hl]; exact c_D_SECOND_CONNECTION st hK w
  rw [execS_drop p _ env n _ 23 "unsupported-second-connection" he hR.r23, dropSt_tcpSt]

@[tcpsym] theorem drop_D_RST_IN_LISTEN (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_RST_IN_LISTEN" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_RST_IN_LISTEN"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "rst-in-listen"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_RST_IN_LISTEN") = some (u8 24) := by
    simp only [evalE, lookup, hl]; exact c_D_RST_IN_LISTEN st hK w
  rw [execS_drop p _ env n _ 24 "rst-in-listen" he hR.r24, dropSt_tcpSt]

@[tcpsym] theorem drop_D_ACK_IN_LISTEN (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_ACK_IN_LISTEN" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_ACK_IN_LISTEN"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "ack-in-listen"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_ACK_IN_LISTEN") = some (u8 25) := by
    simp only [evalE, lookup, hl]; exact c_D_ACK_IN_LISTEN st hK w
  rw [execS_drop p _ env n _ 25 "ack-in-listen" he hR.r25, dropSt_tcpSt]

@[tcpsym] theorem drop_D_NO_SYN_IN_LISTEN (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_NO_SYN_IN_LISTEN" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_NO_SYN_IN_LISTEN"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "no-syn-in-listen"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_NO_SYN_IN_LISTEN") = some (u8 26) := by
    simp only [evalE, lookup, hl]; exact c_D_NO_SYN_IN_LISTEN st hK w
  rw [execS_drop p _ env n _ 26 "no-syn-in-listen" he hR.r26, dropSt_tcpSt]

@[tcpsym] theorem drop_D_RST_OUT_OF_WINDOW (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_RST_OUT_OF_WINDOW" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_RST_OUT_OF_WINDOW"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "rst-out-of-window"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_RST_OUT_OF_WINDOW") = some (u8 27) := by
    simp only [evalE, lookup, hl]; exact c_D_RST_OUT_OF_WINDOW st hK w
  rw [execS_drop p _ env n _ 27 "rst-out-of-window" he hR.r27, dropSt_tcpSt]

@[tcpsym] theorem drop_D_DUPLICATE_SYN (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_DUPLICATE_SYN" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_DUPLICATE_SYN"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "duplicate-syn"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_DUPLICATE_SYN") = some (u8 28) := by
    simp only [evalE, lookup, hl]; exact c_D_DUPLICATE_SYN st hK w
  rw [execS_drop p _ env n _ 28 "duplicate-syn" he hR.r28, dropSt_tcpSt]

@[tcpsym] theorem drop_D_OUT_OF_WINDOW (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_OUT_OF_WINDOW" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_OUT_OF_WINDOW"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "out-of-window"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_OUT_OF_WINDOW") = some (u8 29) := by
    simp only [evalE, lookup, hl]; exact c_D_OUT_OF_WINDOW st hK w
  rw [execS_drop p _ env n _ 29 "out-of-window" he hR.r29, dropSt_tcpSt]

@[tcpsym] theorem drop_D_SYN_IN_WINDOW (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_SYN_IN_WINDOW" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_SYN_IN_WINDOW"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "syn-in-window"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_SYN_IN_WINDOW") = some (u8 30) := by
    simp only [evalE, lookup, hl]; exact c_D_SYN_IN_WINDOW st hK w
  rw [execS_drop p _ env n _ 30 "syn-in-window" he hR.r30, dropSt_tcpSt]

@[tcpsym] theorem drop_D_NO_ACK (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_NO_ACK" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_NO_ACK"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "no-ack"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_NO_ACK") = some (u8 31) := by
    simp only [evalE, lookup, hl]; exact c_D_NO_ACK st hK w
  rw [execS_drop p _ env n _ 31 "no-ack" he hR.r31, dropSt_tcpSt]

@[tcpsym] theorem drop_D_BAD_ACK_SYN_RCVD (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_BAD_ACK_SYN_RCVD" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_BAD_ACK_SYN_RCVD"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "bad-ack-in-syn-rcvd"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_BAD_ACK_SYN_RCVD") = some (u8 32) := by
    simp only [evalE, lookup, hl]; exact c_D_BAD_ACK_SYN_RCVD st hK w
  rw [execS_drop p _ env n _ 32 "bad-ack-in-syn-rcvd" he hR.r32, dropSt_tcpSt]

@[tcpsym] theorem drop_D_ACK_OF_UNSENT (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_ACK_OF_UNSENT" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_ACK_OF_UNSENT"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "ack-of-unsent"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_ACK_OF_UNSENT") = some (u8 33) := by
    simp only [evalE, lookup, hl]; exact c_D_ACK_OF_UNSENT st hK w
  rw [execS_drop p _ env n _ 33 "ack-of-unsent" he hR.r33, dropSt_tcpSt]

@[tcpsym] theorem drop_D_OUT_OF_ORDER (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_OUT_OF_ORDER" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_OUT_OF_ORDER"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "out-of-order"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_OUT_OF_ORDER") = some (u8 34) := by
    simp only [evalE, lookup, hl]; exact c_D_OUT_OF_ORDER st hK w
  rw [execS_drop p _ env n _ 34 "out-of-order" he hR.r34, dropSt_tcpSt]

@[tcpsym] theorem drop_D_GIVE_UP (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_GIVE_UP" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_GIVE_UP"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "give-up"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_GIVE_UP") = some (u8 35) := by
    simp only [evalE, lookup, hl]; exact c_D_GIVE_UP st hK w
  rw [execS_drop p _ env n _ 35 "give-up" he hR.r35, dropSt_tcpSt]

@[tcpsym] theorem drop_D_FIN_WAIT_2_TIMEOUT (p : Prog) (hR : TcpReasons p) (st : St) (hK : TcpConsts st) (w : TW) (env : Env)
    (n : Nat) (hl : env.lookup "D_FIN_WAIT_2_TIMEOUT" = none) :
    execS (n + 1) p (tcpSt st w) env (.eff none .drop [.var "D_FIN_WAIT_2_TIMEOUT"])
      = .ok (tcpSt st { w with evs := w.evs ++ [.drop "fin-wait-2-timeout"] }) env .normal := by
  have he : evalE p (tcpSt st w) env (.var "D_FIN_WAIT_2_TIMEOUT") = some (u8 36) := by
    simp only [evalE, lookup, hl]; exact c_D_FIN_WAIT_2_TIMEOUT st hK w
  rw [execS_drop p _ env n _ 36 "fin-wait-2-timeout" he hR.r36, dropSt_tcpSt]


end Ember.Proof.Refine
