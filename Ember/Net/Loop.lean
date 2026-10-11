import Ember.Net.Ip

/-!
# Ember.Net.Loop — SLIP loopback (M4.4, M4z.2)

The link test for a new target, run before the stack is linked in: every
SLIP frame received is sent back, through the stack's own `slip_store`
and `slip_send`.  Only the dispatch differs from `slip_rx`: a complete
frame goes to `slip_send` instead of `ip_input`.  A failure here is in
the runtime (start-up, interrupt, ring, transmit), not in a protocol.
-/

namespace Ember.Net.Loop
open Ember.Lang Ember.Net

ember def loop_rx (c : u8) := do
  if c == 0xC0 then
    if over then
      trace.drop(D_OVERSIZE)
    else
      if len > 0 then
        slip_send(len)
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

ember def main := do
  let k : u16 ← input.next()
  if k < 0x0100 then
    loop_rx((k : u8))

/-- The loopback as a program: the SLIP half of the stack and nothing else. -/
def prog : Prog :=
  { globals := [Net.MTU, Net.D_OVERSIZE, Net.buf, Net.len, Net.esc, Net.over],
    fns := [Net.slip_send, Net.slip_store, loop_rx, main],
    dropReasons := ["oversize-frame"] }

end Ember.Net.Loop
