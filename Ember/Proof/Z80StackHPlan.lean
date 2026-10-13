import Ember.Proof.Z80StackHGen

/-!
# Ember.Proof.Z80StackHPlan — the image of the stack for the harness: the plan, checked (plan M7.3)

`okB` of the plan of the image, `fnStaticB` of each function in the
environment it is generated in, and what is computed of the assembled
items (`partsCheck`: the plan's labels, the literal pool, the symbols of
the areas and of the accumulator, the generated items in place, the
size) — by the kernel, a theorem each.  `img_ok`: so the setting of the
proofs holds of the image, and given the routines of the runtime every
function does what the IR's does (`ImgIn.ok_parts`).

Generated (one theorem a function).
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm Ember.Z80.Codegen
open Ember.Proof.Z80Enc Ember.Proof.IRSim

set_option maxRecDepth 100000

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
theorem st_udp_input : fnStaticB plan (genEnv g_udp_input.f g_udp_input.missed g_udp_input.live) = true := by decide +kernel
theorem st_ip_input : fnStaticB plan (genEnv g_ip_input.f g_ip_input.missed g_ip_input.live) = true := by decide +kernel
theorem st_slip_store : fnStaticB plan (genEnv g_slip_store.f g_slip_store.missed g_slip_store.live) = true := by decide +kernel
theorem st_slip_rx : fnStaticB plan (genEnv g_slip_rx.f g_slip_rx.missed g_slip_rx.live) = true := by decide +kernel
theorem st_rto : fnStaticB plan (genEnv g_rto.f g_rto.missed g_rto.live) = true := by decide +kernel
theorem st_tcb_reset : fnStaticB plan (genEnv g_tcb_reset.f g_tcb_reset.missed g_tcb_reset.live) = true := by decide +kernel
theorem st_cap : fnStaticB plan (genEnv g_cap.f g_cap.missed g_cap.live) = true := by decide +kernel
theorem st_wnd : fnStaticB plan (genEnv g_wnd.f g_wnd.missed g_wnd.live) = true := by decide +kernel
theorem st_seg_len : fnStaticB plan (genEnv g_seg_len.f g_seg_len.missed g_seg_len.live) = true := by decide +kernel
theorem st_tcp_emit : fnStaticB plan (genEnv g_tcp_emit.f g_tcp_emit.missed g_tcp_emit.live) = true := by decide +kernel
theorem st_send_seg : fnStaticB plan (genEnv g_send_seg.f g_send_seg.missed g_send_seg.live) = true := by decide +kernel
theorem st_send_syn_ack : fnStaticB plan (genEnv g_send_syn_ack.f g_send_syn_ack.missed g_send_syn_ack.live) = true := by decide +kernel
theorem st_send_reset : fnStaticB plan (genEnv g_send_reset.f g_send_reset.missed g_send_reset.live) = true := by decide +kernel
theorem st_output : fnStaticB plan (genEnv g_output.f g_output.missed g_output.live) = true := by decide +kernel
theorem st_rexmit : fnStaticB plan (genEnv g_rexmit.f g_rexmit.missed g_rexmit.live) = true := by decide +kernel
theorem st_acceptable : fnStaticB plan (genEnv g_acceptable.f g_acceptable.missed g_acceptable.live) = true := by decide +kernel
theorem st_listen_input : fnStaticB plan (genEnv g_listen_input.f g_listen_input.missed g_listen_input.live) = true := by decide +kernel
theorem st_ack_input : fnStaticB plan (genEnv g_ack_input.f g_ack_input.missed g_ack_input.live) = true := by decide +kernel
theorem st_tcp_segment : fnStaticB plan (genEnv g_tcp_segment.f g_tcp_segment.missed g_tcp_segment.live) = true := by decide +kernel
theorem st_parse_mss : fnStaticB plan (genEnv g_parse_mss.f g_parse_mss.missed g_parse_mss.live) = true := by decide +kernel
theorem st_tcp_input : fnStaticB plan (genEnv g_tcp_input.f g_tcp_input.missed g_tcp_input.live) = true := by decide +kernel
theorem st_tcp_tick : fnStaticB plan (genEnv g_tcp_tick.f g_tcp_tick.missed g_tcp_tick.live) = true := by decide +kernel
theorem st_main : fnStaticB plan (genEnv g_main.f g_main.missed g_main.live) = true := by decide +kernel

theorem plan_static : ∀ g, g ∈ gens → fnStaticB plan (genEnv g.f g.missed g.live) = true :=
  (List.forall_mem_cons.mpr ⟨st_get16, (List.forall_mem_cons.mpr ⟨st_get32, (List.forall_mem_cons.mpr ⟨st_set16, (List.forall_mem_cons.mpr ⟨st_set32, (List.forall_mem_cons.mpr ⟨st_add16, (List.forall_mem_cons.mpr ⟨st_csum, (List.forall_mem_cons.mpr ⟨st_pseudo, (List.forall_mem_cons.mpr ⟨st_csum_update, (List.forall_mem_cons.mpr ⟨st_verifies, (List.forall_mem_cons.mpr ⟨st_slip_send, (List.forall_mem_cons.mpr ⟨st_ip_send, (List.forall_mem_cons.mpr ⟨st_icmp_input, (List.forall_mem_cons.mpr ⟨st_udp_input, (List.forall_mem_cons.mpr ⟨st_ip_input, (List.forall_mem_cons.mpr ⟨st_slip_store, (List.forall_mem_cons.mpr ⟨st_slip_rx, (List.forall_mem_cons.mpr ⟨st_rto, (List.forall_mem_cons.mpr ⟨st_tcb_reset, (List.forall_mem_cons.mpr ⟨st_cap, (List.forall_mem_cons.mpr ⟨st_wnd, (List.forall_mem_cons.mpr ⟨st_seg_len, (List.forall_mem_cons.mpr ⟨st_tcp_emit, (List.forall_mem_cons.mpr ⟨st_send_seg, (List.forall_mem_cons.mpr ⟨st_send_syn_ack, (List.forall_mem_cons.mpr ⟨st_send_reset, (List.forall_mem_cons.mpr ⟨st_output, (List.forall_mem_cons.mpr ⟨st_rexmit, (List.forall_mem_cons.mpr ⟨st_acceptable, (List.forall_mem_cons.mpr ⟨st_listen_input, (List.forall_mem_cons.mpr ⟨st_ack_input, (List.forall_mem_cons.mpr ⟨st_tcp_segment, (List.forall_mem_cons.mpr ⟨st_parse_mss, (List.forall_mem_cons.mpr ⟨st_tcp_input, (List.forall_mem_cons.mpr ⟨st_tcp_tick, (List.forall_mem_cons.mpr ⟨st_main, (fun _ h => absurd h List.not_mem_nil)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

theorem parts_check : img.partsCheck gens = true := by decide +kernel

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
  img.ok_parts gens fns_eq gens_ok plan_okB plan_static parts_check

/-- info: 'Ember.Proof.Z80Gen.StackH.img_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms img_ok

end Ember.Proof.Z80Gen.StackH
