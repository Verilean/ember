import Ember.Spec.Tcp.Input

/-!
# Ember.Spec.Tcp.Timer — what one `tick` does

* TIME-WAIT counts down to LISTEN;
* while anything is outstanding the retransmission timer counts down;
  on expiry the unacknowledged part is regenerated and sent again and the
  timeout doubles (`rto k`, capped); after `maxRetries` the connection is
  reset (`drop reason=give-up`);
* an ESTABLISHED connection with nothing in flight counts idle ticks; at
  `idleTicks` the echo application closes it (active close, FIN-WAIT-1);
* FIN-WAIT-2 waits at most `idleTicks` for the peer's FIN, then closes
  (`drop reason=fin-wait-2-timeout`), as Linux's `tcp_fin_timeout` does.
-/

namespace Ember.Spec.Tcp
open Ember

def tick : TcpM Unit := do
  let t := (← get).tcb
  if t.st == .listen then return
  if t.st == .timeWait then
    if t.twTimer ≤ 1 then closeConn; logTcb
    else modify fun c => { c with tcb := { c.tcb with twTimer := t.twTimer - 1 } }
    return
  if t.outstanding then
    if t.rtTimer ≤ 1 then
      let r := t.retries + 1
      if r > maxRetries then
        send t.rip { sport := echoPort, dport := t.rport, seq := t.sndNxt, ack := t.rcvNxt,
                     flags := RST ||| ACK, wnd := 0 }
        closeConn
        dropR "give-up"
        logTcb
      else
        modify fun c => { c with tcb := { c.tcb with retries := r, rtTimer := rto r } }
        rexmit
        logTcb
    else
      modify fun c => { c with tcb := { c.tcb with rtTimer := t.rtTimer - 1 } }
    return
  if t.st == .finWait2 then
    if t.idle + 1 ≥ idleTicks then closeConn; dropR "fin-wait-2-timeout"; logTcb
    else modify fun c => { c with tcb := { c.tcb with idle := t.idle + 1 } }
    return
  if t.st == .established && t.pending.size == 0 then
    if t.idle + 1 ≥ idleTicks then
      modify fun c => { c with tcb := { c.tcb with closeReq := true, idle := 0 } }
      output false
      logTcb
    else
      modify fun c => { c with tcb := { c.tcb with idle := t.idle + 1 } }

end Ember.Spec.Tcp
