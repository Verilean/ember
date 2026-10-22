import Ember.Proof.Z80StackHGen.F_main

/-!
# Ember.Proof.Z80StackHGen — the image of the stack for the harness: the generator, function by function (plan M7.3)

For each of the 35 functions of the SLIP build the kernel runs the two
passes of the generator (`pass1B`, `pass2B`) and compares what they
give with `FnPart`: the temporaries read from their slot, where reads
of the frame start, the literals so far, the bytes of temporaries — and
the items, which are those of `StackH.items` at the function's place.
A module a function (`Z80StackHGen/F_<name>.lean`), each importing the
one before, so that the kernel checks one function at a time; a
function of more than 40 instructions a stretch of 20 at a time
(`Z80GenChunks`: the states of the generator between the stretches
written out, each with the items of the stretch before it only —
`Z80GenOut`: the generator never reads the items it has generated, so a
stretch is checked from the state before it with none), which keeps what
the kernel holds at once small.
`gens_ok` chains them (`Gens`): `progEnvs` and `genProg` of `Stack.ir`
are known without the kernel running the generator over the program at
once.

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`); the kernel checks each.
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Codegen

/-- RAM from `0x8000`: the accumulator, the harness's count of idle
calls (the loop's own, no routine writes it), the globals, the frames,
the temporaries; the stack above, up to the top.  A routine of the
runtime uses two bytes of stack at most (`rt_cmp32`). -/
def img : ImgIn :=
  { ir := Stack.ir, layout,
    dropReasons := ["oversize-frame",
      "short-packet",
      "bad-version",
      "bad-ihl",
      "bad-ip-checksum",
      "bad-length",
      "fragment",
      "ttl-zero",
      "not-for-us",
      "broadcast",
      "unsupported-protocol",
      "short-icmp",
      "bad-icmp-checksum",
      "unsupported-icmp-type",
      "short-udp",
      "bad-udp-length",
      "bad-udp-checksum",
      "udp-port-closed",
      "short-tcp",
      "bad-tcp-header",
      "bad-tcp-checksum",
      "tcp-port-closed",
      "rst-no-connection",
      "unsupported-second-connection",
      "rst-in-listen",
      "ack-in-listen",
      "no-syn-in-listen",
      "rst-out-of-window",
      "duplicate-syn",
      "out-of-window",
      "syn-in-window",
      "no-ack",
      "bad-ack-in-syn-rcvd",
      "ack-of-unsent",
      "out-of-order",
      "give-up",
      "fin-wait-2-timeout"],
    notes := ["connection-reset-by-peer"],
    ramStart := 0x8000, stackLo := 33565, stackHi := 65536, acc := 32768, rtK := 2, rt := [], items, genOff := 86 }

set_option maxRecDepth 100000

def gens : List FnPart :=
  [g_get16, g_get32, g_set16, g_set32, g_add16, g_csum, g_pseudo, g_csum_update, g_verifies, g_slip_send, g_ip_send, g_icmp_input, g_udp_input, g_ip_input, g_slip_store, g_slip_rx, g_rto, g_tcb_reset, g_cap, g_wnd, g_seg_len, g_tcp_emit, g_send_seg, g_send_syn_ack, g_send_reset, g_output, g_rexmit, g_acceptable, g_listen_input, g_ack_input, g_tcp_segment, g_parse_mss, g_tcp_input, g_tcp_tick, g_main]

theorem fns_eq : Stack.ir.fns = gens.map (·.f) := rfl

/-- The generator, along the program. -/
theorem gens_ok : Gens Stack.ir #[] gens :=
  (.cons p1_get16 p2_get16 (.cons p1_get32 p2_get32 (.cons p1_set16 p2_set16 (.cons p1_set32 p2_set32 (.cons p1_add16 p2_add16 (.cons p1_csum p2_csum (.cons p1_pseudo p2_pseudo (.cons p1_csum_update p2_csum_update (.cons p1_verifies p2_verifies (.cons p1_slip_send p2_slip_send (.cons p1_ip_send p2_ip_send (.cons p1_icmp_input p2_icmp_input (.cons p1_udp_input p2_udp_input (.cons p1_ip_input p2_ip_input (.cons p1_slip_store p2_slip_store (.cons p1_slip_rx p2_slip_rx (.cons p1_rto p2_rto (.cons p1_tcb_reset p2_tcb_reset (.cons p1_cap p2_cap (.cons p1_wnd p2_wnd (.cons p1_seg_len p2_seg_len (.cons p1_tcp_emit p2_tcp_emit (.cons p1_send_seg p2_send_seg (.cons p1_send_syn_ack p2_send_syn_ack (.cons p1_send_reset p2_send_reset (.cons p1_output p2_output (.cons p1_rexmit p2_rexmit (.cons p1_acceptable p2_acceptable (.cons p1_listen_input p2_listen_input (.cons p1_ack_input p2_ack_input (.cons p1_tcp_segment p2_tcp_segment (.cons p1_parse_mss p2_parse_mss (.cons p1_tcp_input p2_tcp_input (.cons p1_tcp_tick p2_tcp_tick (.cons p1_main p2_main (.nil _))))))))))))))))))))))))))))))))))))

end Ember.Proof.Z80Gen.StackH
