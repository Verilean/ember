import Ember.Proof.Z80StackHGen
import Ember.Proof.Z80StackHAsm

/-!
# Ember.Proof.Z80StackHPlan — the image of the stack for the harness: the plan, checked (plan M7.3)

`okB` of the plan of the image, `fnStaticB` of each function in the
environment it is generated in, and what is computed of the assembled
image `asm` (`PartsOn`: the plan's labels, the literal pool, the symbols
of the areas and of the accumulator, the generated items in place, the
size) — by the kernel, a theorem each (one declaration at a time, the
kernel keeps less).  `img_ok`: so the setting of the proofs holds of the
image, and given the routines of the runtime every function does what
the IR's does (`ImgIn.ok_partsOn`).

Written by `ember-z80 proof-files` (`Ember.Tools.ProofGen`).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm Ember.Z80.Codegen
open Ember.Proof.Z80Enc Ember.Proof.IRSim

set_option maxRecDepth 100000
-- one theorem at a time: checked at once, the kernel's work for each adds up
set_option Elab.async false

def plan : Plan := mkPlan (img.planIn (envsOf gens))

theorem plan_okB : okB plan = true := by decide +kernel

theorem st_get16 : fnStaticB plan (genEnv g_get16.f g_get16.missed g_get16.live) = true := by decide +kernel
theorem st_get32 : fnStaticB plan (genEnv g_get32.f g_get32.missed g_get32.live) = true := by decide +kernel
theorem st_set16 : fnStaticB plan (genEnv g_set16.f g_set16.missed g_set16.live) = true := by decide +kernel
theorem st_set32 : fnStaticB plan (genEnv g_set32.f g_set32.missed g_set32.live) = true := by decide +kernel
theorem st_add16 : fnStaticB plan (genEnv g_add16.f g_add16.missed g_add16.live) = true := by decide +kernel
theorem st_csum : fnStaticB plan (genEnv g_csum.f g_csum.missed g_csum.live) = true := by decide +kernel
theorem st_pseudo : fnStaticB plan (genEnv g_pseudo.f g_pseudo.missed g_pseudo.live) = true := by decide +kernel
theorem st_csum_update : fnStaticB plan (genEnv g_csum_update.f g_csum_update.missed g_csum_update.live) = true := by decide +kernel
theorem st_verifies : fnStaticB plan (genEnv g_verifies.f g_verifies.missed g_verifies.live) = true := by decide +kernel
theorem st_slip_send : fnStaticB plan (genEnv g_slip_send.f g_slip_send.missed g_slip_send.live) = true := by decide +kernel
theorem st_ip_send : fnStaticB plan (genEnv g_ip_send.f g_ip_send.missed g_ip_send.live) = true := by decide +kernel
theorem st_icmp_input : fnStaticB plan (genEnv g_icmp_input.f g_icmp_input.missed g_icmp_input.live) = true := by decide +kernel
theorem need_udp_input_0 : (((List.range (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live)) = true := by
  decide +kernel
theorem need_udp_input_20 : (((List.range (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live)) = true := by
  decide +kernel
theorem need_udp_input_40 : (((List.range (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live)) = true := by
  decide +kernel
theorem need_udp_input_len : (List.range (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live).fn.body.size).length ≤ 60 := by decide +kernel
theorem need_udp_input : (((List.range (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live))) = true :=
  all_drop_step _ _ 0 20 need_udp_input_0
    (all_drop_step _ _ 20 20 need_udp_input_20
    (all_drop_step _ _ 40 20 need_udp_input_40
    (all_drop_end _ _ 60 need_udp_input_len)))
theorem st_udp_input : fnStaticB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_udp_input (by decide +kernel)
theorem need_ip_input_0 : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live)) = true := by
  decide +kernel
theorem need_ip_input_20 : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live)) = true := by
  decide +kernel
theorem need_ip_input_40 : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live)) = true := by
  decide +kernel
theorem need_ip_input_60 : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 60).take 20).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live)) = true := by
  decide +kernel
theorem need_ip_input_80 : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 80).take 20).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live)) = true := by
  decide +kernel
theorem need_ip_input_len : (List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).length ≤ 100 := by decide +kernel
theorem need_ip_input : (((List.range (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live))) = true :=
  all_drop_step _ _ 0 20 need_ip_input_0
    (all_drop_step _ _ 20 20 need_ip_input_20
    (all_drop_step _ _ 40 20 need_ip_input_40
    (all_drop_step _ _ 60 20 need_ip_input_60
    (all_drop_step _ _ 80 20 need_ip_input_80
    (all_drop_end _ _ 100 need_ip_input_len)))))
theorem st_ip_input : fnStaticB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_ip_input (by decide +kernel)
theorem st_slip_store : fnStaticB plan (genEnv g_slip_store.f g_slip_store.missed g_slip_store.live) = true := by decide +kernel
theorem st_slip_rx : fnStaticB plan (genEnv g_slip_rx.f g_slip_rx.missed g_slip_rx.live) = true := by decide +kernel
theorem st_rto : fnStaticB plan (genEnv g_rto.f g_rto.missed g_rto.live) = true := by decide +kernel
theorem st_tcb_reset : fnStaticB plan (genEnv g_tcb_reset.f g_tcb_reset.missed g_tcb_reset.live) = true := by decide +kernel
theorem st_cap : fnStaticB plan (genEnv g_cap.f g_cap.missed g_cap.live) = true := by decide +kernel
theorem st_wnd : fnStaticB plan (genEnv g_wnd.f g_wnd.missed g_wnd.live) = true := by decide +kernel
theorem st_seg_len : fnStaticB plan (genEnv g_seg_len.f g_seg_len.missed g_seg_len.live) = true := by decide +kernel
theorem need_tcp_emit_0 : (((List.range (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live)) = true := by
  decide +kernel
theorem need_tcp_emit_20 : (((List.range (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live)) = true := by
  decide +kernel
theorem need_tcp_emit_40 : (((List.range (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live)) = true := by
  decide +kernel
theorem need_tcp_emit_len : (List.range (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live).fn.body.size).length ≤ 60 := by decide +kernel
theorem need_tcp_emit : (((List.range (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live))) = true :=
  all_drop_step _ _ 0 20 need_tcp_emit_0
    (all_drop_step _ _ 20 20 need_tcp_emit_20
    (all_drop_step _ _ 40 20 need_tcp_emit_40
    (all_drop_end _ _ 60 need_tcp_emit_len)))
theorem st_tcp_emit : fnStaticB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_tcp_emit (by decide +kernel)
theorem st_send_seg : fnStaticB plan (genEnv g_send_seg.f g_send_seg.missed g_send_seg.live) = true := by decide +kernel
theorem st_send_syn_ack : fnStaticB plan (genEnv g_send_syn_ack.f g_send_syn_ack.missed g_send_syn_ack.live) = true := by decide +kernel
theorem st_send_reset : fnStaticB plan (genEnv g_send_reset.f g_send_reset.missed g_send_reset.live) = true := by decide +kernel
theorem need_output_0 : (((List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_output.f g_output.missed g_output.live)) = true := by
  decide +kernel
theorem need_output_20 : (((List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_output.f g_output.missed g_output.live)) = true := by
  decide +kernel
theorem need_output_40 : (((List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_output.f g_output.missed g_output.live)) = true := by
  decide +kernel
theorem need_output_60 : (((List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).drop 60).take 20).all (needAtB plan (genEnv g_output.f g_output.missed g_output.live)) = true := by
  decide +kernel
theorem need_output_len : (List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).length ≤ 80 := by decide +kernel
theorem need_output : (((List.range (genEnv g_output.f g_output.missed g_output.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_output.f g_output.missed g_output.live))) = true :=
  all_drop_step _ _ 0 20 need_output_0
    (all_drop_step _ _ 20 20 need_output_20
    (all_drop_step _ _ 40 20 need_output_40
    (all_drop_step _ _ 60 20 need_output_60
    (all_drop_end _ _ 80 need_output_len))))
theorem st_output : fnStaticB plan (genEnv g_output.f g_output.missed g_output.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_output (by decide +kernel)
theorem st_rexmit : fnStaticB plan (genEnv g_rexmit.f g_rexmit.missed g_rexmit.live) = true := by decide +kernel
theorem st_acceptable : fnStaticB plan (genEnv g_acceptable.f g_acceptable.missed g_acceptable.live) = true := by decide +kernel
theorem need_listen_input_0 : (((List.range (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live)) = true := by
  decide +kernel
theorem need_listen_input_20 : (((List.range (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live)) = true := by
  decide +kernel
theorem need_listen_input_40 : (((List.range (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live)) = true := by
  decide +kernel
theorem need_listen_input_len : (List.range (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live).fn.body.size).length ≤ 60 := by decide +kernel
theorem need_listen_input : (((List.range (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live))) = true :=
  all_drop_step _ _ 0 20 need_listen_input_0
    (all_drop_step _ _ 20 20 need_listen_input_20
    (all_drop_step _ _ 40 20 need_listen_input_40
    (all_drop_end _ _ 60 need_listen_input_len)))
theorem st_listen_input : fnStaticB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_listen_input (by decide +kernel)
theorem need_ack_input_0 : (((List.range (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live)) = true := by
  decide +kernel
theorem need_ack_input_20 : (((List.range (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live)) = true := by
  decide +kernel
theorem need_ack_input_40 : (((List.range (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live)) = true := by
  decide +kernel
theorem need_ack_input_len : (List.range (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live).fn.body.size).length ≤ 60 := by decide +kernel
theorem need_ack_input : (((List.range (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live))) = true :=
  all_drop_step _ _ 0 20 need_ack_input_0
    (all_drop_step _ _ 20 20 need_ack_input_20
    (all_drop_step _ _ 40 20 need_ack_input_40
    (all_drop_end _ _ 60 need_ack_input_len)))
theorem st_ack_input : fnStaticB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_ack_input (by decide +kernel)
theorem need_tcp_segment_0 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_20 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_40 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_60 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 60).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_80 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 80).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_100 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 100).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_120 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 120).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_140 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 140).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_160 : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 160).take 20).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live)) = true := by
  decide +kernel
theorem need_tcp_segment_len : (List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).length ≤ 180 := by decide +kernel
theorem need_tcp_segment : (((List.range (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live))) = true :=
  all_drop_step _ _ 0 20 need_tcp_segment_0
    (all_drop_step _ _ 20 20 need_tcp_segment_20
    (all_drop_step _ _ 40 20 need_tcp_segment_40
    (all_drop_step _ _ 60 20 need_tcp_segment_60
    (all_drop_step _ _ 80 20 need_tcp_segment_80
    (all_drop_step _ _ 100 20 need_tcp_segment_100
    (all_drop_step _ _ 120 20 need_tcp_segment_120
    (all_drop_step _ _ 140 20 need_tcp_segment_140
    (all_drop_step _ _ 160 20 need_tcp_segment_160
    (all_drop_end _ _ 180 need_tcp_segment_len)))))))))
theorem st_tcp_segment : fnStaticB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_tcp_segment (by decide +kernel)
theorem need_parse_mss_0 : (((List.range (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live)) = true := by
  decide +kernel
theorem need_parse_mss_20 : (((List.range (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live)) = true := by
  decide +kernel
theorem need_parse_mss_40 : (((List.range (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live)) = true := by
  decide +kernel
theorem need_parse_mss_len : (List.range (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live).fn.body.size).length ≤ 60 := by decide +kernel
theorem need_parse_mss : (((List.range (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live))) = true :=
  all_drop_step _ _ 0 20 need_parse_mss_0
    (all_drop_step _ _ 20 20 need_parse_mss_20
    (all_drop_step _ _ 40 20 need_parse_mss_40
    (all_drop_end _ _ 60 need_parse_mss_len)))
theorem st_parse_mss : fnStaticB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_parse_mss (by decide +kernel)
theorem st_tcp_input : fnStaticB plan (genEnv g_tcp_input.f g_tcp_input.missed g_tcp_input.live) = true := by decide +kernel
theorem need_tcp_tick_0 : (((List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).drop 0).take 20).all (needAtB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live)) = true := by
  decide +kernel
theorem need_tcp_tick_20 : (((List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).drop 20).take 20).all (needAtB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live)) = true := by
  decide +kernel
theorem need_tcp_tick_40 : (((List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).drop 40).take 20).all (needAtB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live)) = true := by
  decide +kernel
theorem need_tcp_tick_60 : (((List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).drop 60).take 20).all (needAtB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live)) = true := by
  decide +kernel
theorem need_tcp_tick_len : (List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).length ≤ 80 := by decide +kernel
theorem need_tcp_tick : (((List.range (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live).fn.body.size).drop 0).all (needAtB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live))) = true :=
  all_drop_step _ _ 0 20 need_tcp_tick_0
    (all_drop_step _ _ 20 20 need_tcp_tick_20
    (all_drop_step _ _ 40 20 need_tcp_tick_40
    (all_drop_step _ _ 60 20 need_tcp_tick_60
    (all_drop_end _ _ 80 need_tcp_tick_len))))
theorem st_tcp_tick : fnStaticB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live) = true :=
  fnStaticB_of _ _ (by decide +kernel) need_tcp_tick (by decide +kernel)
theorem st_main : fnStaticB plan (genEnv g_main.f g_main.missed g_main.live) = true := by decide +kernel

theorem plan_static : ∀ g, g ∈ gens → fnStaticB plan (genEnv g.f g.missed g.live) = true :=
  (List.forall_mem_cons.mpr ⟨st_get16, (List.forall_mem_cons.mpr ⟨st_get32, (List.forall_mem_cons.mpr ⟨st_set16, (List.forall_mem_cons.mpr ⟨st_set32, (List.forall_mem_cons.mpr ⟨st_add16, (List.forall_mem_cons.mpr ⟨st_csum, (List.forall_mem_cons.mpr ⟨st_pseudo, (List.forall_mem_cons.mpr ⟨st_csum_update, (List.forall_mem_cons.mpr ⟨st_verifies, (List.forall_mem_cons.mpr ⟨st_slip_send, (List.forall_mem_cons.mpr ⟨st_ip_send, (List.forall_mem_cons.mpr ⟨st_icmp_input, (List.forall_mem_cons.mpr ⟨st_udp_input, (List.forall_mem_cons.mpr ⟨st_ip_input, (List.forall_mem_cons.mpr ⟨st_slip_store, (List.forall_mem_cons.mpr ⟨st_slip_rx, (List.forall_mem_cons.mpr ⟨st_rto, (List.forall_mem_cons.mpr ⟨st_tcb_reset, (List.forall_mem_cons.mpr ⟨st_cap, (List.forall_mem_cons.mpr ⟨st_wnd, (List.forall_mem_cons.mpr ⟨st_seg_len, (List.forall_mem_cons.mpr ⟨st_tcp_emit, (List.forall_mem_cons.mpr ⟨st_send_seg, (List.forall_mem_cons.mpr ⟨st_send_syn_ack, (List.forall_mem_cons.mpr ⟨st_send_reset, (List.forall_mem_cons.mpr ⟨st_output, (List.forall_mem_cons.mpr ⟨st_rexmit, (List.forall_mem_cons.mpr ⟨st_acceptable, (List.forall_mem_cons.mpr ⟨st_listen_input, (List.forall_mem_cons.mpr ⟨st_ack_input, (List.forall_mem_cons.mpr ⟨st_tcp_segment, (List.forall_mem_cons.mpr ⟨st_parse_mss, (List.forall_mem_cons.mpr ⟨st_tcp_input, (List.forall_mem_cons.mpr ⟨st_tcp_tick, (List.forall_mem_cons.mpr ⟨st_main, (fun _ h => absurd h List.not_mem_nil)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

/-- The plan of the image, without the kernel running the generator over the program. -/
theorem img_plan : img.plan = plan := img.plan_parts gens fns_eq gens_ok

theorem on_labels_all_0 : (((plan.labels).drop 0).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_40 : (((plan.labels).drop 40).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_80 : (((plan.labels).drop 80).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_120 : (((plan.labels).drop 120).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_160 : (((plan.labels).drop 160).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_200 : (((plan.labels).drop 200).take 40).all (fun l => img.items.any (ImgIn.isLab l)) = true := by
  decide +kernel
theorem on_labels_all_len : (plan.labels).length ≤ 240 := by decide +kernel
theorem on_labels_all : (((plan.labels).drop 0).all (fun l => img.items.any (ImgIn.isLab l))) = true :=
  all_drop_step _ _ 0 40 on_labels_all_0
    (all_drop_step _ _ 40 40 on_labels_all_40
    (all_drop_step _ _ 80 40 on_labels_all_80
    (all_drop_step _ _ 120 40 on_labels_all_120
    (all_drop_step _ _ 160 40 on_labels_all_160
    (all_drop_step _ _ 200 40 on_labels_all_200
    (all_drop_end _ _ 240 on_labels_all_len))))))
theorem on_labels : (plan.labels.all fun l => img.items.any (ImgIn.isLab l)) = true := by
  have h := on_labels_all
  simpa using h

theorem on_lits_all_0 : (((plan.lits).drop 0).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_1 : (((plan.lits).drop 1).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_2 : (((plan.lits).drop 2).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_3 : (((plan.lits).drop 3).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_4 : (((plan.lits).drop 4).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_5 : (((plan.lits).drop 5).take 1).all (ImgIn.litB asm img.ramStart) = true := by
  decide +kernel
theorem on_lits_all_len : (plan.lits).length ≤ 6 := by decide +kernel
theorem on_lits_all : (((plan.lits).drop 0).all (ImgIn.litB asm img.ramStart)) = true :=
  all_drop_step _ _ 0 1 on_lits_all_0
    (all_drop_step _ _ 1 1 on_lits_all_1
    (all_drop_step _ _ 2 1 on_lits_all_2
    (all_drop_step _ _ 3 1 on_lits_all_3
    (all_drop_step _ _ 4 1 on_lits_all_4
    (all_drop_step _ _ 5 1 on_lits_all_5
    (all_drop_end _ _ 6 on_lits_all_len))))))
theorem on_lits : plan.lits.all (ImgIn.litB asm img.ramStart) = true := by
  have h := on_lits_all
  simpa using h
theorem on_globals :
    (img.layout.globals.all fun e => asm.labels.reverse.lookup (areaSym (.global e.1)) == some e.2) = true := by
  decide +kernel
theorem on_frames :
    (img.layout.frames.all fun e => asm.labels.reverse.lookup (areaSym (.frame e.1)) == some e.2) = true := by
  decide +kernel
theorem on_code :
    decide ((img.items.drop img.genOff).take (gens.flatMap (·.code)).length = gens.flatMap (·.code)) = true := by
  decide +kernel
theorem on_acc : (img.items.all ImgIn.noAcc || asm.labels.reverse.lookup "rt_acc" == some img.acc) = true := by
  decide +kernel
theorem on_size : decide (asm.bytes.size < 65536) = true := by decide +kernel

/-- **The image of the stack for the harness, checked**: the setting of
the proofs holds of it, and given the routines of the runtime it calls
every function does what the IR's does. -/
theorem img_ok :
    ∃ (a : Assembled) (addrs : List Nat), assemble img.items = .ok a ∧ a.bytes.size < 65536 ∧
      ∀ (W : Type) (bus : W → UInt16 → UInt8) (dev : W → IoEvent → W) (wrel : Ember.Lang.World → W → Prop),
        (∀ w, dev w .none = w) →
        (img.plan.toZ (img.around a addrs W bus dev wrel)).OK ∧
        (RtOK (img.plan.toZ (img.around a addrs W bus dev wrel)) →
          ∀ k g st1, Callee (img.plan.toZ (img.around a addrs W bus dev wrel)) g st1 (IR.Sem.callF k img.ctx g st1)) :=
  img.ok_partsOn gens asm fns_eq gens_ok plan_okB plan_static
    ⟨assemble_items, on_labels, on_lits, on_globals, on_frames, on_code, on_acc, on_size⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.img_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms img_ok

end Ember.Proof.Z80Gen.StackH
