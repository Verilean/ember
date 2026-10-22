import Ember.Proof.Z80GenOut
import Ember.Proof.Z80StackHItems

/-!
The frames of the layout `sharedBytes Stack.ir` computes (from 0), and
`shared_eq`: the kernel computes that layout here, once; the checks of
the functions take `sharedOf` of these frames (written by `ember-z80
proof-files`; see `Z80StackHGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Codegen

def sharedFrames : List (String × Nat) := [("get16", 840), ("get32", 740), ("set16", 832), ("set32", 826), ("add16", 840), ("csum", 826), ("pseudo", 817), ("csum_update", 740), ("verifies", 747), ("slip_send", 826), ("ip_send", 817), ("icmp_input", 723), ("udp_input", 723), ("ip_input", 701), ("slip_store", 701), ("slip_rx", 700), ("rto", 701), ("tcb_reset", 773), ("cap", 787), ("wnd", 785), ("seg_len", 772), ("tcp_emit", 785), ("send_seg", 773), ("send_syn_ack", 762), ("send_reset", 762), ("output", 758), ("rexmit", 701), ("acceptable", 758), ("listen_input", 758), ("ack_input", 758), ("tcp_segment", 740), ("parse_mss", 740), ("tcp_input", 723), ("tcp_tick", 700), ("main", 698)]

theorem shared_eq : sharedBytes Stack.ir = sharedOf Stack.ir sharedFrames :=
  sharedBytes_eq _ _ (by decide +kernel)

end Ember.Proof.Z80Gen.StackH
