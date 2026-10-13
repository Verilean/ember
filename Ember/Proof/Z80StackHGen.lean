import Ember.Proof.Z80ImageParts
import Ember.Proof.Z80StackHItems

/-!
# Ember.Proof.Z80StackHGen — the image of the stack for the harness: the generator, function by function (plan M7.3)

For each of the 35 functions of the SLIP build the kernel runs the two
passes of the generator (`pass1B`, `pass2B`) and compares what they
give with `FnPart` written here: the temporaries read from their slot,
where reads of the frame start, the literals so far, the bytes of
temporaries — and the items, which are those of `StackH.items` at the
function's place.  `gens_ok` chains them (`Gens`): `progEnvs` and
`genProg` of `Stack.ir` are known without the kernel running the
generator over the program at once.

The largest function (`tcp_segment`, 170 instructions) takes the kernel
about 11 GB a pass.

Generated (the numbers and arrays are what the generator returns; the
kernel checks each).
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

def g_get16 : FnPart :=
  { f := Stack.fn_get16, missed := #[false, false, false, true, false, false, false], live := some #[true, true],
    code := (items.drop 86).take 31, lits := #[], size := 2 }
theorem p1_get16 : pass1B Stack.ir #[] g_get16 = true := by decide +kernel
theorem p2_get16 : pass2B Stack.ir #[] g_get16 = true := by decide +kernel

def g_get32 : FnPart :=
  { f := Stack.fn_get32, missed := #[false, false, true, false, false], live := some #[true, true, true, true, true, true],
    code := (items.drop 117).take 21, lits := #[], size := 4 }
theorem p1_get32 : pass1B Stack.ir #[] g_get32 = true := by decide +kernel
theorem p2_get32 : pass2B Stack.ir #[] g_get32 = true := by decide +kernel

def g_set16 : FnPart :=
  { f := Stack.fn_set16, missed := #[false], live := some #[true, true, true, true],
    code := (items.drop 138).take 20, lits := #[], size := 0 }
theorem p1_set16 : pass1B Stack.ir #[] g_set16 = true := by decide +kernel
theorem p2_set16 : pass2B Stack.ir #[] g_set16 = true := by decide +kernel

def g_set32 : FnPart :=
  { f := Stack.fn_set32, missed := #[], live := some #[true, true, true, true, true, true],
    code := (items.drop 158).take 12, lits := #[], size := 0 }
theorem p1_set32 : pass1B Stack.ir #[] g_set32 = true := by decide +kernel
theorem p2_set32 : pass2B Stack.ir #[] g_set32 = true := by decide +kernel

def g_add16 : FnPart :=
  { f := Stack.fn_add16, missed := #[false], live := some #[true, true, false, false, false, false],
    code := (items.drop 170).take 13, lits := #[], size := 0 }
theorem p1_add16 : pass1B Stack.ir #[] g_add16 = true := by decide +kernel
theorem p2_add16 : pass2B Stack.ir #[] g_add16 = true := by decide +kernel

def g_csum : FnPart :=
  { f := Stack.fn_csum, missed := #[false, false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, false, true, false],
    code := (items.drop 183).take 61, lits := #[], size := 0 }
theorem p1_csum : pass1B Stack.ir #[] g_csum = true := by decide +kernel
theorem p2_csum : pass2B Stack.ir #[] g_csum = true := by decide +kernel

def g_pseudo : FnPart :=
  { f := Stack.fn_pseudo, missed := #[false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 244).take 31, lits := #[], size := 0 }
theorem p1_pseudo : pass1B Stack.ir #[] g_pseudo = true := by decide +kernel
theorem p2_pseudo : pass2B Stack.ir #[] g_pseudo = true := by decide +kernel

def g_csum_update : FnPart :=
  { f := Stack.fn_csum_update, missed := #[false, false], live := some #[true, true, true, true, true, true, true, true],
    code := (items.drop 275).take 15, lits := #[], size := 0 }
theorem p1_csum_update : pass1B Stack.ir #[] g_csum_update = true := by decide +kernel
theorem p2_csum_update : pass2B Stack.ir #[] g_csum_update = true := by decide +kernel

def g_verifies : FnPart :=
  { f := Stack.fn_verifies, missed := #[false, true, false], live := some #[true, true],
    code := (items.drop 290).take 19, lits := #[], size := 1 }
theorem p1_verifies : pass1B Stack.ir #[] g_verifies = true := by decide +kernel
theorem p2_verifies : pass2B Stack.ir #[] g_verifies = true := by decide +kernel

def g_slip_send : FnPart :=
  { f := Stack.fn_slip_send, missed := #[], live := some #[true, true, true, true, true, true, true],
    code := (items.drop 309).take 50, lits := #[], size := 0 }
theorem p1_slip_send : pass1B Stack.ir #[] g_slip_send = true := by decide +kernel
theorem p2_slip_send : pass2B Stack.ir #[] g_slip_send = true := by decide +kernel

def g_ip_send : FnPart :=
  { f := Stack.fn_ip_send, missed := #[false, false, false], live := some #[true, true, true, true, true, true, true, true, true],
    code := (items.drop 359).take 68, lits := #[(4, 167772161)], size := 0 }
theorem p1_ip_send : pass1B Stack.ir #[] g_ip_send = true := by decide +kernel
theorem p2_ip_send : pass2B Stack.ir #[] g_ip_send = true := by decide +kernel

def g_icmp_input : FnPart :=
  { f := Stack.fn_icmp_input, missed := #[], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 427).take 61, lits := #[(4, 167772161)], size := 0 }
theorem p1_icmp_input : pass1B Stack.ir #[(4, 167772161)] g_icmp_input = true := by decide +kernel
theorem p2_icmp_input : pass2B Stack.ir #[(4, 167772161)] g_icmp_input = true := by decide +kernel

def g_udp_input : FnPart :=
  { f := Stack.fn_udp_input, missed := #[], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 488).take 134, lits := #[(4, 167772161)], size := 0 }
theorem p1_udp_input : pass1B Stack.ir #[(4, 167772161)] g_udp_input = true := by decide +kernel
theorem p2_udp_input : pass2B Stack.ir #[(4, 167772161)] g_udp_input = true := by decide +kernel

def g_ip_input : FnPart :=
  { f := Stack.fn_ip_input, missed := #[false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false],
    code := (items.drop 622).take 218, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }
theorem p1_ip_input : pass1B Stack.ir #[(4, 167772161)] g_ip_input = true := by decide +kernel
theorem p2_ip_input : pass2B Stack.ir #[(4, 167772161)] g_ip_input = true := by decide +kernel

def g_slip_store : FnPart :=
  { f := Stack.fn_slip_store, missed := #[], live := some #[true],
    code := (items.drop 840).take 32, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }
theorem p1_slip_store : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_store = true := by decide +kernel
theorem p2_slip_store : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_store = true := by decide +kernel

def g_slip_rx : FnPart :=
  { f := Stack.fn_slip_rx, missed := #[], live := some #[true],
    code := (items.drop 872).take 56, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }
theorem p1_slip_rx : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_rx = true := by decide +kernel
theorem p2_slip_rx : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_slip_rx = true := by decide +kernel

def g_rto : FnPart :=
  { f := Stack.fn_rto, missed := #[], live := some #[true, true, true, true, true],
    code := (items.drop 928).take 30, lits := #[(4, 167772161), (4, 4294967295)], size := 0 }
theorem p1_rto : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_rto = true := by decide +kernel
theorem p2_rto : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_rto = true := by decide +kernel

def g_tcb_reset : FnPart :=
  { f := Stack.fn_tcb_reset, missed := #[], live := some #[],
    code := (items.drop 958).take 38, lits := #[(4, 167772161), (4, 4294967295), (4, 0)], size := 0 }
theorem p1_tcb_reset : pass1B Stack.ir #[(4, 167772161), (4, 4294967295)] g_tcb_reset = true := by decide +kernel
theorem p2_tcb_reset : pass2B Stack.ir #[(4, 167772161), (4, 4294967295)] g_tcb_reset = true := by decide +kernel

def g_cap : FnPart :=
  { f := Stack.fn_cap, missed := #[], live := some #[],
    code := (items.drop 996).take 11, lits := #[(4, 167772161), (4, 4294967295), (4, 0)], size := 0 }
theorem p1_cap : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_cap = true := by decide +kernel
theorem p2_cap : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_cap = true := by decide +kernel

def g_wnd : FnPart :=
  { f := Stack.fn_wnd, missed := #[false], live := some #[true, true],
    code := (items.drop 1007).take 7, lits := #[(4, 167772161), (4, 4294967295), (4, 0)], size := 0 }
theorem p1_wnd : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_wnd = true := by decide +kernel
theorem p2_wnd : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_wnd = true := by decide +kernel

def g_seg_len : FnPart :=
  { f := Stack.fn_seg_len, missed := #[false, false], live := some #[true, true, true, true],
    code := (items.drop 1014).take 24, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_seg_len : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_seg_len = true := by decide +kernel
theorem p2_seg_len : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0)] g_seg_len = true := by decide +kernel

def g_tcp_emit : FnPart :=
  { f := Stack.fn_tcp_emit, missed := #[false, false, false, false, false, false, false], live := some #[true, true, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false],
    code := (items.drop 1038).take 141, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_tcp_emit : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_tcp_emit = true := by decide +kernel
theorem p2_tcp_emit : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_tcp_emit = true := by decide +kernel

def g_send_seg : FnPart :=
  { f := Stack.fn_send_seg, missed := #[], live := some #[true, true, true, false, false, true, false, true, false, true, true, false],
    code := (items.drop 1179).take 33, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_send_seg : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_seg = true := by decide +kernel
theorem p2_send_seg : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_seg = true := by decide +kernel

def g_send_syn_ack : FnPart :=
  { f := Stack.fn_send_syn_ack, missed := #[], live := some #[],
    code := (items.drop 1212).take 14, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_send_syn_ack : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_syn_ack = true := by decide +kernel
theorem p2_send_syn_ack : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_syn_ack = true := by decide +kernel

def g_send_reset : FnPart :=
  { f := Stack.fn_send_reset, missed := #[false], live := some #[true, true, true, true],
    code := (items.drop 1226).take 63, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_send_reset : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_reset = true := by decide +kernel
theorem p2_send_reset : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_send_reset = true := by decide +kernel

def g_output : FnPart :=
  { f := Stack.fn_output, missed := #[true, false, false, true, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1289).take 155, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 5 }
theorem p1_output : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_output = true := by decide +kernel
theorem p2_output : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_output = true := by decide +kernel

def g_rexmit : FnPart :=
  { f := Stack.fn_rexmit, missed := #[], live := some #[true],
    code := (items.drop 1444).take 37, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 0 }
theorem p1_rexmit : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_rexmit = true := by decide +kernel
theorem p2_rexmit : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_rexmit = true := by decide +kernel

def g_acceptable : FnPart :=
  { f := Stack.fn_acceptable, missed := #[false, false, true, false, false, false, true, true, false, true], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1481).take 77, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)], size := 13 }
theorem p1_acceptable : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_acceptable = true := by decide +kernel
theorem p2_acceptable : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_acceptable = true := by decide +kernel

def g_listen_input : FnPart :=
  { f := Stack.fn_listen_input, missed := #[false, false, false, false], live := some #[true, true, true, true],
    code := (items.drop 1558).take 96, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], size := 0 }
theorem p1_listen_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_listen_input = true := by decide +kernel
theorem p2_listen_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1)] g_listen_input = true := by decide +kernel

def g_ack_input : FnPart :=
  { f := Stack.fn_ack_input, missed := #[true, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 1654).take 149, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)], size := 4 }
theorem p1_ack_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_ack_input = true := by decide +kernel
theorem p2_ack_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_ack_input = true := by decide +kernel

def g_tcp_segment : FnPart :=
  { f := Stack.fn_tcp_segment, missed := #[false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, false],
    code := (items.drop 1803).take 383, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 4 }
theorem p1_tcp_segment : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_tcp_segment = true := by decide +kernel
theorem p2_tcp_segment : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536)] g_tcp_segment = true := by decide +kernel

def g_parse_mss : FnPart :=
  { f := Stack.fn_parse_mss, missed := #[false, false, false, false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true],
    code := (items.drop 2186).take 107, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }
theorem p1_parse_mss : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_parse_mss = true := by decide +kernel
theorem p2_parse_mss : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_parse_mss = true := by decide +kernel

def g_tcp_input : FnPart :=
  { f := Stack.fn_tcp_input, missed := #[false, false, false, false, false, false], live := some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
    code := (items.drop 2293).take 95, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }
theorem p1_tcp_input : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_input = true := by decide +kernel
theorem p2_tcp_input : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_input = true := by decide +kernel

def g_tcp_tick : FnPart :=
  { f := Stack.fn_tcp_tick, missed := #[false, false, false], live := some #[true],
    code := (items.drop 2388).take 125, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }
theorem p1_tcp_tick : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_tick = true := by decide +kernel
theorem p2_tcp_tick : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_tcp_tick = true := by decide +kernel

def g_main : FnPart :=
  { f := Stack.fn_main, missed := #[], live := some #[false, false],
    code := (items.drop 2513).take 59, lits := #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)], size := 0 }
theorem p1_main : pass1B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_main = true := by decide +kernel
theorem p2_main : pass2B Stack.ir #[(4, 167772161), (4, 4294967295), (4, 0), (4, 1), (4, 65536), (4, 2147483648)] g_main = true := by decide +kernel

def gens : List FnPart :=
  [g_get16, g_get32, g_set16, g_set32, g_add16, g_csum, g_pseudo, g_csum_update, g_verifies, g_slip_send, g_ip_send, g_icmp_input, g_udp_input, g_ip_input, g_slip_store, g_slip_rx, g_rto, g_tcb_reset, g_cap, g_wnd, g_seg_len, g_tcp_emit, g_send_seg, g_send_syn_ack, g_send_reset, g_output, g_rexmit, g_acceptable, g_listen_input, g_ack_input, g_tcp_segment, g_parse_mss, g_tcp_input, g_tcp_tick, g_main]

theorem fns_eq : Stack.ir.fns = gens.map (·.f) := rfl

/-- The generator, along the program. -/
theorem gens_ok : Gens Stack.ir #[] gens :=
  .cons p1_get16 p2_get16 (.cons p1_get32 p2_get32 (.cons p1_set16 p2_set16 (.cons p1_set32 p2_set32 (.cons p1_add16 p2_add16 (.cons p1_csum p2_csum (.cons p1_pseudo p2_pseudo (.cons p1_csum_update p2_csum_update (.cons p1_verifies p2_verifies (.cons p1_slip_send p2_slip_send (.cons p1_ip_send p2_ip_send (.cons p1_icmp_input p2_icmp_input (.cons p1_udp_input p2_udp_input (.cons p1_ip_input p2_ip_input (.cons p1_slip_store p2_slip_store (.cons p1_slip_rx p2_slip_rx (.cons p1_rto p2_rto (.cons p1_tcb_reset p2_tcb_reset (.cons p1_cap p2_cap (.cons p1_wnd p2_wnd (.cons p1_seg_len p2_seg_len (.cons p1_tcp_emit p2_tcp_emit (.cons p1_send_seg p2_send_seg (.cons p1_send_syn_ack p2_send_syn_ack (.cons p1_send_reset p2_send_reset (.cons p1_output p2_output (.cons p1_rexmit p2_rexmit (.cons p1_acceptable p2_acceptable (.cons p1_listen_input p2_listen_input (.cons p1_ack_input p2_ack_input (.cons p1_tcp_segment p2_tcp_segment (.cons p1_parse_mss p2_parse_mss (.cons p1_tcp_input p2_tcp_input (.cons p1_tcp_tick p2_tcp_tick (.cons p1_main p2_main (.nil _)))))))))))))))))))))))))))))))))))

end Ember.Proof.Z80Gen.StackH
