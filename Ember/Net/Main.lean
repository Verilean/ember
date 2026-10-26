import Ember.Net.Tcp

/-!
# Ember.Net.Main — the main loop and the program (M3.7)

`main` consumes one input item per call — a received byte or a tick —
exactly as the runtime's main loop drains the receive ring.  A tick in
the middle of a frame is deferred to the end of that frame (as in
`Spec.tickArrives`): the one packet buffer holds the frame.
-/

namespace Ember.Net
open Ember.Lang

ember global booted : bool
/-- A tick arrived in the middle of a frame and waits for its end. -/
ember global tick_due : bool

ember def main := do
  if !booted then
    tcb_reset()
    booted := true
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    -- `buf` holds the frame being received, and a tick may send: wait for the end of the frame
    if len == 0 then
      tcp_tick()
      return
    if !tick_due then
      tick_due := true
      return
    -- a second tick: the frame has been incomplete for a tick period; skip the rest of it
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

/-- The whole stack as one Ember program. -/
def prog : Prog :=
  { structs := structs, globals := constants ++ state ++ [booted, tick_due],
    fns := fns ++ ipFns ++ tcpFns ++ [main], dropReasons := dropReasons, notes := notes }

end Ember.Net
