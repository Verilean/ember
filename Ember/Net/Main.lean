import Ember.Net.Tcp

/-!
# Ember.Net.Main — the main loop and the program (M3.7)

`main` consumes one input item per call — a received byte or a tick —
exactly as the runtime's main loop drains the receive ring.
-/

namespace Ember.Net
open Ember.Lang

ember global booted : bool

ember def main := do
  if !booted then
    tcb_reset()
    booted := true
  let k : u16 ← input.next()
  if k == 0xFFFF then
    return
  if k == 0x0100 then
    tcp_tick()
    return
  slip_rx((k : u8))

/-- The whole stack as one Ember program. -/
def prog : Prog :=
  { structs := structs, globals := constants ++ state ++ [booted],
    fns := fns ++ ipFns ++ tcpFns ++ [main], dropReasons := dropReasons, notes := notes }

end Ember.Net
