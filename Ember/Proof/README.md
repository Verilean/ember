# Ember.Proof — proofs about the reference stack (M5.1 – M5.3), of the Ember code against it (M5.4 – M5.6) and of the emitted C (M5.8)

Properties of `Ember.Spec` ("P1" in `docs/Ember-design.md` §4), stated
over the Spec's own definitions.  Two things in the Spec changed
because of the proofs: the tick in the middle of a frame (a defect, see
"One input item" below), and the body of the per-byte loop of
`Spec.input`, which got names (`slipByte`, `byteInput`) and is otherwise
as it was.  `lake build Ember.Proof` checks everything (it is also part of the
default `lake build`).  There is no `sorry`, no `axiom`, no
`native_decide` and no `bv_decide` in this directory.

Every statement was first run on random inputs (the plan's rule); what
turned out false as first written is listed under "Hypotheses that are
needed".

The second part (P2: the stack written in Ember computes what the Spec
specifies) is at the end of this file: "Refinement".

## Files

| File | Contents | Plan |
|---|---|---|
| `Bytes.lean` | `Ember.Bytes`: `get`/`set`/`get16`/`set16` across `ofList`, `++`; bytes of a word joined give the word | — |
| `Checksum.lean` | `add` is a commutative monoid; `sum` as a fold over words; order independence; filling in a checksum; RFC 1624 | M5.1 |
| `Icmp.lean` | the echo reply, patched with the RFC 1624 update, verifies | M5.1 |
| `Slip.lean` | `encode` and the decoder state machine; decode ∘ encode | M5.2 |
| `Headers.lean` | IPv4, UDP, TCP: parse ∘ emit | M5.2 |
| `Tcp.lean` | `wp` for `TcpM`; `input` as its steps; the invariant `Inv`; delivery; acceptance and window | M5.3 |
| `Stack.lean` | the control block changes only in `runTcp`; induction over `Spec.step` | M5.3 |
| `Symex.lean` | symbolic execution over `Ember.Lang.Sem`: one equation per statement form, calls through the callee's theorem, lemmas that keep `u8`/`u16`/`u32` values in the image of `toUInt64`, the packet buffer as a value | M5.4 |
| `Refine.lean` | functions of `Ember.Net` refine functions of `Ember.Spec`: checksums, 16-bit fields | M5.5 |
| `RefineSlip.lean` | 32-bit fields; `slip_store`, `slip_send`; the SLIP loopback program (`Ember.Net.Loop`) against `Slip.Dec.feed` and `Slip.encode` | M5.5, and M5.6 for the loopback |
| `RefineIp.lean` | `ip_send` transmits `Spec.Ipv4.packet` | M5.5 |
| `RefineIcmp.lean` | `icmp_input` against `Icmp.reply` and `sendIp` | M5.5 |
| `RefineUdp.lean` | `udp_input` against `Udp.parse`, `Udp.emit` and the echo service | M5.5 |
| `RefineIpInput.lean` | `ip_input` against `Ipv4.validate` and the dispatch of `Spec.ipInput`; the loop that skips IP options | M5.5 |
| `RefineRx.lean` | `slip_rx`, the stack's receive path per byte, against `Slip.Dec.feed` followed by `Spec.ipInput` | M5.6 (in part) |
| `RefineTcp.lean` | TCP: the records `t` and `sg` as structures; `tcb_reset`, `cap`, `wnd`, `seg_len`; `tcp_emit` sends `Spec.Tcp.emit` | M5.5 |
| `TcpAttr.lean`, `RefineTcpSt.lean` | the TCP state as one value (`TW`, `tcpSt`); the simp set `tcpsym` that runs TCP code | M5.5 |
| `RefineTcpOut.lean` | `send_seg`, `send_syn_ack`, `send_reset`, `rexmit`, `output`, `acceptable` as Lean functions on `TW` | M5.5 (raw layer) |
| `RefineTcpIn.lean` | `listen_input`, `ack_input`, `tcp_segment` | M5.5 (raw layer) |
| `RefineTcpParse.lean` | `parse_mss`, `tcp_input` | M5.5 (raw layer) |
| `RefineTcpTick.lean` | `rto`, `tcp_tick` | M5.5 (raw layer) |
| `TcpSim.lean` | the transcribed TCP functions against `Ember.Spec.Tcp`: the relations, one correspondence per function, `tcp_segment` = `Tcp.input`, `tcp_tick` = `Tcp.tick` | M5.5 (second layer) |
| `TcpSimParse.lean` | `parse_mss` = `Tcp.parseMss`, the header checks = `Tcp.parse`; `tcp_input_sim`, `tcp_tick_sim`; the two layers joined: `tcp_input_refines`, `tcp_tick_refines` | M5.5 |
| `TcpRx.lean` | TCP inside `ip_input` (`ip_input_tcp`); what `Spec.runTcp` does (`runTcp_keep`); a frame through `ip_input` = a frame through `Spec.ipInput`, every protocol (`frame_refines`) | M5.6 |
| `NetStep.lean` | the invariant `NetInv` between the stack's globals and the Spec's stack state; one received byte (`slip_rx_step`), one tick between frames (`tick_step`) | M5.6 |
| `TcpBound.lean` | the tick counters of the Spec's control block stay within their limits (`Tcp.Bnd`, `reach_bnd`) | M5.3, for M5.6 |
| `Main.lean` | `main`: its code case by case; the invariant `MainInv`; one call = one input item of the Spec (`main_step`); boot (`boot_call`, `boot_inv`) | M5.6 |
| `Driver.lean` | `Spec.input` item by item (`input_items`); the input oracle (`next_spec`); `j` calls of `main` (`main_iter`); from the initial state, against `Spec.step` input by input (`main_run`, `main_run_all`) | M5.6 |
| `CSem.lean` | the C semantics `Ember.C.Sem`: values survive new variables, statements as the beginning of a block, `CExpr.same` | M5.8 |
| `CTypes.lean` | `cval`, `HasTy`, `WT`; type soundness of `evalE`; closed expressions | M5.8 |
| `CArith.lean` | the operators on natural numbers | M5.8 |
| `CExpr.lean` | the emitter's monad (`wpc`), `ERel`, fragments, every operator, places; `expr_ok` | M5.8 (expressions) |
| `CFuel.lean`, `CVoid.lean` | the C semantics again: more fuel changes nothing (`mono1`), statement lists without counting fuel (`Exec`), `(void)x;` changes nothing (`Exec.void`) | M5.8 |
| `CPlace.lean` | a place as a variable and a path (`lpath`); `evalE` and `update` along the path (`evalE_lpath`, `update_lpath`); `setPath_cval` | M5.8 |
| `LangFrame.lean` | `Lang.Sem` only: a statement that does not write `x` leaves it alone (`keeps`); statements that return on every path do not end normally (`returns_all`) | M5.8 |
| `CRel.lean` | names (`Hyg`), the compiled unit (`Unit`), the relation statements keep (`LRel`, `GRel`, `SRel`, `Same`), `assign_sim` | M5.8 |
| `CStmt.lean` | well-typed statements (`WTS`, `WTB`, `FnOK`, `ProgOK`), what a statement's code does (`Sim`, `SPost`), the cases: declaration, assignment, `break`, `return`, `if`, `loop`, `for` | M5.8 (statements) |
| `CCall.lean` | arguments (`exprs_ok`), the result of a call (`store_ok`), the effects (`eff_sim`), calls (`call_sim`, `call_ok`) | M5.8 (statements) |
| `CSim.lean` | `stmt_ok`, `block_ok`: every statement, by recursion on it | M5.8 (statements) |
| `CFn.lean` | `fn_sim`: a compiled function, for any fuel | M5.8 (functions) |
| `CProgram.lean` | `compile_unit`, `init_rel`, `entry_sim`, `iter_sim`: the unit, the initial state, the entry function again and again; `hygU_of_prefix` | M5.8 (programs) |
| `CCheck.lean` | the checker `progOkB` and `progOkB_sound` | M5.8 |
| `CNet.lean` | `stack_c`: the emitted C of the SLIP build against the Spec; the `#guard`s that the builds of the stack are covered | M5.6 + M5.8 |
| `Z80Frame.lean` | `validate_sound`: a frame layout the validator accepts keeps frames apart from globals and from the frames of reachable functions | M7.2 |
| `IRFuel.lean`, `IRMem.lean` | the IR semantics again: more fuel changes nothing (`mono1`); a function's run without counting fuel (`Reach`, `Ends`); `rd` and `wr` | M7.1 |
| `IRTypes.lean`, `IRRel.lean`, `IRPlace.lean` | well-typed expressions (`WT`); a value as bytes at an address (`Holds`); what a layout must give (`LayOK`); the relation statements keep (`LRel`, `GRel`, `SRel`); a place as an address (`PlaceAt`) | M7.1 |
| `IRWp.lean`, `IRArith.lean` | a weakest-precondition calculus for the lowering monad (`wp`, `Ext`, `Final`); the IR's operators as the Ember operators | M7.1 |
| `IRExpr.lean`, `IRJump.lean` | `place_ok`, `expr_ok`, `exprTo_ok`; conditions as jumps (`condJump_ok`) | M7.1 (expressions) |
| `IRStmt.lean`, `IRCall.lean`, `IRBlock.lean` | well-typed statements (`WTS`, `FnOK`, `ProgOK`); assignment, declaration, `break`, `return`; arguments, calls, effects and where results go; blocks, `if`, `loop`, `for` | M7.1 (statements) |
| `IRSim.lean` | `stmt_ok`, `block_ok`, `fn_sim`: every statement, and a lowered function for any fuel | M7.1 (functions) |
| `IRProgram.lean`, `IRInit.lean`, `IRCheck.lean` | the program as lowered (`lowered_of_raw`), the layout check (`layOk_sound`), the initial memory (`init_rel`), the entry function again and again (`iter_sim`, `iter_trap`); the checker `progOkB` and `progOkB_sound` | M7.1 (programs) |
| `IRPass.lean`, `IRLower.lean` | the passes: a simulation between two bodies (`sim_exec`), dropping instructions (`del_sim`), `cleanup`, `dropChecks` (`drop_sim`), `tidy_ref`; `IR.lower` as a whole (`lower_iter`, `lower_trap`) and the checker `irOkB` | M7.1 (passes) |
| `IRNet.lean` | `stack_ir`: the IR of the SLIP build against the Spec; the `#guard`s that the builds of the stack are covered | M5.6 + M7.1 |
| `Z80Encode.lean` | `step_encode`: the CPU model on the bytes of an encoded instruction does what `Asm.exec` (`Ember/Z80/AsmSem.lean`) says the instruction does | M7.4 |
| `Z80Asm.lean` | `assemble_ok`: the assembler puts every item's encoding at its address; labels resolve to the addresses of their items | M7.4 |

## Theorems

Names are relative to `Ember.Spec`.

### M5.1 — checksum algebra

| Theorem | Statement | File |
|---|---|---|
| `Checksum.toNat_add` | `add a b` is `a + b`, minus 0xFFFF when it carries out of 16 bits | `Checksum.lean` |
| `Checksum.add_comm`, `add_assoc`, `add_zero`, `zero_add` | one's-complement addition is a commutative monoid with unit `0` | `Checksum.lean` |
| `Checksum.add_not_self`, `add_ffff`, `add_eq_zero_iff` | `a + ~a = 0xFFFF`; `0xFFFF` is neutral for every `a ≠ 0`; a sum is `0` only if both words are | `Checksum.lean` |
| `Checksum.sum_eq_foldl` | `sum b off len init` is the left fold of `add` over `words b off len` (big-endian pairs, an odd last byte padded with zero) — this is the proof about the `while` loop | `Checksum.lean` |
| `Checksum.foldl_add_perm`, `sum_perm` | **order independence**: ranges whose word lists are permutations of each other have the same sum | `Checksum.lean` |
| `Checksum.sum_append`, `sum_append_comm` | the sum over `a ++ b` continues the sum over `a` (even `a.size`); two blocks of whole words may be swapped | `Checksum.lean` |
| `Checksum.sum_init`, `sum_congr`, `sum_eq_zero_iff` | the start value is one more word; the sum sees only the bytes of the range; it is `0` only for all-zero data and start value | `Checksum.lean` |
| `Checksum.sum_set16_of_zero` | writing `v` into a zero word of the range adds `v` to the sum | `Checksum.lean` |
| `Checksum.sum_set16_checksum`, `verifies_set16_checksum` | a range whose zeroed checksum field is filled with `checksum` sums to `0xFFFF`, so it `verifies` | `Checksum.lean` |
| `Checksum.sum_set16_checksum_nonzero` | the same when a computed `0` is sent as `0xFFFF` (UDP) | `Checksum.lean` |
| `Checksum.incremental_eq_checksum` | **RFC 1624, exactly**: after the `k`-th word changes to `m'`, `incremental` on the old checksum is the recomputed checksum, except that it is `0` where recomputation gives `0xFFFF` (new range sums to `0`) | `Checksum.lean` |
| `Checksum.incremental_eq_recompute` | **RFC 1624 = recomputation** when the new range does not sum to `0` | `Checksum.lean` |
| `Checksum.incremental_eq_recompute_of_ne_zero` | in particular whenever the new word is not `0` | `Checksum.lean` |
| `Checksum.verifies_incremental` | the update keeps a verifying sum verifying (addition modulo 0xFFFF) | `Icmp.lean` |
| `Icmp.reply_verifies` | if `Icmp.reply msg = .ok r` then `r` verifies — the Spec's one use of `incremental` | `Icmp.lean` |

### M5.2 — round trips

| Theorem | Statement | File |
|---|---|---|
| `Slip.toList_encode` | `encode p` is `END`, the escaped bytes of `p`, `END` | `Slip.lean` |
| `Slip.decodeAll_eq_foldl` | `decodeAll` folds the byte-at-a-time `Dec.feed` over the stream (`feedStep`) | `Slip.lean` |
| `Slip.feed_encode` | feeding `encode p` to the decoder **in any state** flushes that state with the leading `END`, delivers exactly `p` and leaves the initial state (`0 < p.size ≤ maxLen`) | `Slip.lean` |
| `Slip.decodeAll_encode` | **decode ∘ encode**: `decodeAll (encode p) maxLen = [p]` for `0 < p.size ≤ maxLen` | `Slip.lean` |
| `Slip.decodeAll_encode_eq` | complete: `[p]` if `0 < p.size ≤ maxLen`, else `[]` (`decodeAll_encode_empty`, `decodeAll_encode_oversize`) | `Slip.lean` |
| `Slip.decodeAll_encode_stream` | a concatenation of encoded frames decodes to the frames, in order | `Slip.lean` |
| `Ipv4.validate_ok` | `validate` accepts a packet with a 20-byte header that passes each check, with these fields | `Headers.lean` |
| `Ipv4.sum_header` | the header `header` builds sums to `0xFFFF` | `Headers.lean` |
| `Ipv4.validate_packet` (`validate_header_append` for any TTL ≠ 0) | **IPv4 parse ∘ emit**: `validate (packet proto id src dst payload) ourIp = .ok ({ihl := 20, totalLen := 20 + payload.size, id, ttl := 64, proto, src, dst}, payload)` if `20 + payload.size ≤ 65535` and `dst` is `ourIp` or broadcast | `Headers.lean` |
| `Udp.parse_emit` | **UDP parse ∘ emit**: `parse src dst (emit src dst sport dport data) = .ok {sport, dport, data}` if `8 + data.size ≤ 65535` | `Headers.lean` |
| `Tcp.parseMss_20`, `parseMss_24` | no options: no MSS; the option `emit` writes is read back | `Headers.lean` |
| `Tcp.parse_emit` | **TCP parse ∘ emit**: `parse src dst (emit src dst s) = .ok s` if `s.flags &&& 0x3F = s.flags` (all eight fields, including the MSS option and the data) | `Headers.lean` |

### M5.3 — TCP invariants

`Tcp.Inv t` is:

```
t.peerMss ≤ 65535
t.pending.size ≤ t.cap                         -- the echo buffer never overflows
t.sent ≤ t.pending.size
dist t.sndNxt t.sndUna = t.sent + ctl t.st     -- ctl = 1 in SYN-RCVD, FIN-WAIT-1, CLOSING, LAST-ACK
0 < t.pending.size → st ∈ {ESTABLISHED, CLOSE-WAIT, LAST-ACK}
st ∈ {SYN-RCVD, ESTABLISHED} → closeReq = false ∧ finSent = false
```

| Theorem | Statement | File |
|---|---|---|
| `Tcp.input_eq` | `Tcp.input` equals its numbered steps (`connStep`, `ackStep`, `dataStep`, `finStep`) composed by continuation; by `rfl` | `Tcp.lean` |
| `Tcp.input_inv`, `Tcp.tick_inv` | `Inv` survives any segment and any tick | `Tcp.lean` |
| `Tcp.Inv.seqGe` | **`snd.una ≤ snd.nxt`**: `seqGe t.sndNxt t.sndUna = true` | `Tcp.lean` |
| `Tcp.Inv.flight_le` | `snd.nxt − snd.una ≤ cap + 1` | `Tcp.lean` |
| `Tcp.input_pending` | **delivery**: outside SYN-RCVD and ESTABLISHED a segment adds nothing to the echo buffer (afterwards it is a suffix of what it was) | `Tcp.lean` |
| `Tcp.input_pending_synRcvd` | in SYN-RCVD the same unless the segment's ACK completes the handshake | `Tcp.lean` |
| `Tcp.input_delivery` | the two together: bytes are added only from ESTABLISHED, or from SYN-RCVD with `s.ack = snd.nxt` | `Tcp.lean` |
| `Tcp.dataStep_pending` | the one step that appends (`dataStep`) does so only when the state is ESTABLISHED at that point | `Tcp.lean` |
| `Tcp.tick_pending` | a tick adds nothing | `Tcp.lean` |
| `Tcp.input_not_acceptable` | **acceptance**: with a connection open, a segment for another port or tuple, or one that is not `acceptable`, changes nothing in the control block except `idle` and `lastWnd` | `Tcp.lean` |
| `Tcp.input_window` | **window**: under `Inv`, with a connection open, the connection is closed or `rcv.nxt` advances by at most `wnd + min (ack − snd.una) sent + (1 if FIN)` | `Tcp.lean` |
| `runTcp_pres`, `txFrame_pres`, `sendIp_pres`, … | the stack's control block changes only where `runTcp` runs a TCP action | `Stack.lean` |
| `step_preserves` | **induction step**: a property of the control block kept by `Tcp.input` and `Tcp.tick` is kept by `Spec.step` | `Stack.lean` |
| `reach_preserves` | **induction**: such a property, true of `{}`, holds in `reach cfg inputs` (the state after the inputs, from `State.init cfg`) | `Stack.lean` |
| `step_inv`, `reach_inv` | `Inv` for `Spec.step` and for every reachable state | `Stack.lean` |
| `reach_seqGe`, `reach_holds`, `reach_pending_le` | in every reachable state: `snd.una ≤ snd.nxt`; data in the buffer only in ESTABLISHED, CLOSE-WAIT, LAST-ACK; the buffer within its capacity | `Stack.lean` |

## Hypotheses that are needed

Found by running the first form of each statement on random inputs.

* **RFC 1624 ≠ recomputation on all-zero data.**  One's complement has
  two zeros.  For four zero bytes, "changing" word 0 from 0 to 0:
  `incremental (checksum z 0 4) 0 0 = 0x0000`, `checksum z 0 4 = 0xFFFF`.
  The update never produces a sum of `0`; recomputation does when every
  word and the start value are `0`.  Hence `incremental_eq_checksum`
  (unconditional, with the case distinction) and
  `incremental_eq_recompute` (hypothesis: the new range does not sum to
  `0`).  `Tests/Ember/SpecTests.lean` already compares up to ±0.
* **Accepted data is not bounded by the window as it was announced.**
  `input` computes the window for trimming after it has processed the
  segment's ACK, which frees buffer space.  With the buffer full
  (`pending = sent = 256 = cap`, window 0), a segment at `rcv.nxt` that
  acknowledges 100 bytes and carries 300 has 100 of them accepted.  The
  bound that holds is `input_window`: window + bytes acknowledged by the
  same segment (+ 1 for FIN, which is taken even at a zero window).
  RFC 9293 describes the trimming in its first step, before the ACK is
  processed; a peer that respects the window never sees the difference,
  and the buffer bound (`Inv.pendingCap`) holds either way.
* **"No data outside ESTABLISHED/CLOSE-WAIT"**, as it holds here: bytes
  enter the buffer only in ESTABLISHED (never in CLOSE-WAIT — the peer
  has sent its FIN), where SYN-RCVD counts when the same segment
  completes the handshake; the buffer *holds* bytes only in ESTABLISHED,
  CLOSE-WAIT and LAST-ACK (unacknowledged echo data stays there until it
  is acknowledged).  In FIN-WAIT-1/2 data is acknowledged and discarded.
* **Length fields.**  `Ipv4.packet` and `Udp.emit` write
  `UInt16.ofNat` of the length: with a 65536-byte payload
  `Ipv4.validate (Ipv4.packet …)` succeeds with an *empty* payload, with
  65516 bytes it fails (`bad-length`).  Hence `20 + payload.size ≤ 65535`
  and `8 + data.size ≤ 65535`.  Inside the stack lengths are bounded by
  the MTU (as long as that is below 65536).  TCP needs no such
  hypothesis.
* **TCP flags.**  `parse` keeps six flag bits; `emit` writes all eight.
* **SLIP.**  An empty frame is ignored and a frame longer than `maxLen`
  is dropped, so decode ∘ encode is the identity only for
  `0 < p.size ≤ maxLen` (`decodeAll_encode_eq` has all three cases).

Observations about the Spec made on the way (none is a defect):
CLOSE-WAIT is never the state between two inputs, because the echo
application closes at once and `output` sends the FIN in the same step
(the invariant still allows it); and the idle close relies on `finSent`
being false in ESTABLISHED, which is why `Inv` carries its last clause.

## Axioms

`#print axioms` is pinned with `#guard_msgs` at the end of each file.
All headline theorems depend on exactly

```
propext, Classical.choice, Quot.sound
```

(`Tcp.Inv.seqGe` on `propext, Quot.sound` only).  These come from core
lemmas, `omega` and `simp`; `Classical.choice` also enters through
`Lean.Loop.forIn_eq_of_monadTail`, core's unfolding lemma for `while`
loops, used once (`Checksum.sum_eq_foldl`).  `Lean.ofReduceBool` does not
occur.

## Not proven

* emit ∘ parse (the other direction); it is false as an equality of
  bytes (options, padding, reserved bits, the two zeros of the checksum).
* Parsers on packets the Spec's own emitters do not produce: IPv4
  options, TCP options other than the one MSS option, link padding.
* SLIP on arbitrary byte streams (resynchronisation after garbage is
  covered only as far as `feed_encode`: any decoder state, then one
  encoded frame).
* ICMP, ARP, DHCP and Ethernet round trips; only `Icmp.reply_verifies`.
* TCP beyond the invariants above: that every byte is echoed, in order
  (the closed-loop generator of `Spec/Gen.lean` tests it); retransmission
  and timer behaviour; the closing handshake; anything about `rcv.nxt`
  relative to the peer's `snd.nxt`.
* The delivery and window theorems are per segment (`Tcp.input`), not
  lifted to `Spec.step`, where one input may carry several frames; only
  state invariants are lifted (`step_preserves`).
* `reach` is the state `Spec.run` threads through its loop, by
  definition of both; no theorem connects it to the `Trace` that `run`
  returns.
* P2 beyond what "Refinement" below lists; P3: the emitted C is proved
  ("The emitted C" below); of the Z80 back end the translation to its
  IR and the encoder are ("The IR of the Z80 back end", "The encoder"
  below), the code generator in part ("The code generator" below).

## How the TCP proofs are organised

`Tcp.input` in `do` notation has early returns and three conditionals
followed by more code; unfolded naively its tail appears 18 times.
`Tcp.lean` therefore defines the numbered steps of its doc comment as
functions taking their continuation, proves `input` equal to their
composition by `rfl` (this is what `do` notation produces anyway), and
proves each property once per step:

```
wp m Q c  :=  Q (m.run c).1 (m.run c).2
ackStep_inv :  (∀ c, Inv c.tcb → wp k (… Inv …) c) → Inv c.tcb → … → wp (ackStep src s t k) (… Inv …) c
```

`wp_simp [defs]` runs straight-line code symbolically, `inv_leaf`
proves `Inv` of the resulting record field by field, and `seq_omega`
sends sequence-number arithmetic (`UInt32`, modulo 2³²) to `omega`.

## Refinement (M5.4, M5.5, M5.6)

### What a statement says

```
theorem csum_refines (p : Prog) (hc : p.fn? "csum" = some csum) … (st : St) (b : ByteArray)
    (hb : st.globals.lookup "buf" = some (bufVal b)) (o n ini : UInt16)
    (hr : o.toNat + n.toNat ≤ b.size) (hsz : b.size ≤ 65536) (d : Nat) :
    Sem.call (d + n.toNat / 2 + 60) p st "csum" [u16 o, u16 n, u16 ini]
      = .ok (some (u16 (Spec.Checksum.sum b o.toNat n.toNat ini))) st
```

In any program `p` that contains these functions, from any state whose
`buf` holds the bytes of `b`, with enough fuel, calling `csum` returns
the Spec's sum and leaves the state unchanged.  Three things stand
between such a theorem and "the C on the target computes the checksum",
and none of them is proved:

1. **`Sem` is not the interpreter.**  `Ember.Lang.Sem` is a second,
   total definition of the semantics (the interpreter has `partial`
   loops the kernel cannot unfold).  The two are *tested* against each
   other: random programs, the examples, and every build of the stack on
   the corpus (`Tests/Ember/LangTests.lean`, "semantics").
2. **The AST is the checker's output at build time.**  `csum` is
   `checked_fn% Net.prog, "csum"`: the type checker (also `partial`) runs
   during elaboration and its result is inserted as a literal; a `#guard`
   next to it re-runs the check and compares.  The theorem is about that
   literal.
3. **The translation to C** is proved (M5.8, "The emitted C" below) for
   programs without by-reference parameters, against the C semantics of
   `Ember/C/Sem.lean` — which is itself a definition, tested against gcc
   and SDCC through the emitted programs, not derived from the C
   standard.  Of the translation to Z80, the step to the IR is proved
   (M7.1) and so is the encoder (M7.4); the code generator is tested,
   not proved.

### Theorems

| Theorem | Statement |
|---|---|
| `add16_refines` | `add16(a, b)` returns `Spec.Checksum.add a b` (one's-complement addition) |
| `verifies_refines` | `verifies(s)` returns `Spec.Checksum.verifies s` |
| `csum_update_refines` | `csum_update(hc, old, new)` returns `Spec.Checksum.incremental hc old new` — RFC 1624, which `Checksum.incremental_eq_recompute` relates to recomputing |
| `pseudo_refines` | `pseudo(src, dst, proto, n)` returns `Spec.Checksum.pseudo src dst proto n` |
| `get16_refines` | `get16(o)` returns `Bytes.get16 b o` when `o + 1` is inside the buffer |
| `csum_refines` | `csum(o, n, init)` returns `Spec.Checksum.sum b o n init` when `[o, o+n)` is inside the buffer — by induction over the loop (`csum_loop`), each iteration through `get16_refines` and `add16_refines` |
| `set16_refines` | `set16(o, v)` leaves the state with `buf` holding `Bytes.set16 b o v` (`withBuf`), when `o + 1` is inside the buffer — the first theorem about a function that changes state |

| `get32_refines`, `set32_refines` | 32-bit fields, big-endian (`Bytes.get32`, `Bytes.set32`), through `get16`/`set16` |
| `slip_store_refines` | on globals that hold a decoder state `d` (`SlipRel`: `len` bytes of `buf` are `d.buf`, `esc`, `over`), `slip_store(c)` leaves globals that hold `Slip.Dec.store d c mtu`; no event, no other global changes |
| `slip_send_refines` | `slip_send(n)` transmits `Slip.encode` of the first `n` bytes of `buf` as one frame (a loop of `out.byte`, by induction; then `out.end`) and changes nothing else |
| `loop_rx_refines` | `loop_rx(c)` of the loopback is `Slip.Dec.feed d c mtu`: next decoder state in the globals, and in the trace what the step yields — nothing, `drop oversize-frame`, or `tx` of the frame encoded |
| `loop_main_refines` | **one call of the loopback's `main` is one step of the decoder**: it reads one input item (`World.next`); a byte steps the decoder as above, a tick or the end of the input changes nothing |
| `loop_initial` | the loopback's initial globals hold the decoder's initial state |
| `ip_send_spec`, `ipHeader_extract`, `ip_send_refines` | `ip_send(proto, dst, n)` writes the 20-byte header in front of the payload at `buf[20, 20+n)`, takes the next identification and transmits the SLIP encoding of **`Spec.Ipv4.packet proto id ourIp dst payload`** — the header bytes and the header checksum are the Spec's, byte for byte |
| `icmp_input_refines` | **`icmp_input` is `Spec.Icmp.reply` followed by `Spec.sendIp`**: the drop line the Spec gives (`short-icmp`, `bad-icmp-checksum`, `unsupported-icmp-type`), or the Spec's reply — built in place, checksum updated by RFC 1624 — in the Spec's packet (`icmp_reply_bytes`) |
| `udp_input_refines` | **`udp_input` is `Spec.Udp.parse` and the echo service**: the Spec's drop line (`short-udp`, `bad-udp-length`, `bad-udp-checksum`, `udp-port-closed`), or for port 7 `Spec.Udp.emit` with the ports swapped in the Spec's packet (`udp_reply_bytes`: the three fields overwritten in place give the datagram `emit` assembles) |
| `validate_eq`, `squeeze_spec`, `sq_loop` | `Spec.Ipv4.validate` as a chain of cases; moving the payload up over IP options (a loop, by induction) puts the bytes the Spec slices out at offset 20 |
| `ip_input_refines` | **`ip_input` is `Spec.Ipv4.validate` and the dispatch of `Spec.ipInput`**, for a packet that is not TCP: the drop line of the first of the eight checks that fails (`short-packet` … `not-for-us`), or `broadcast`, the ICMP handling, the UDP handling, `unsupported-protocol` — on the payload the Spec hands on |
| `ipInput_obs` | `ipSpec` — the `drop`/`tx` lines and the next identification, as a function of the packet — is what the Spec's own `ipInput` (a state monad) produces on a SLIP link, `pkt` diagnostics apart |
| `slip_rx_refines` | **one byte through the stack's receive path is one byte through the Spec's**: `slip_rx(c)` takes globals that hold the decoder state `d` and identification `id` (`RxInv`) to globals that hold `(d.feed c).1` and the Spec's next identification, and appends to the trace exactly the Spec's lines for `(d.feed c).2` — nothing, `drop oversize-frame`, or `ipSpec` of the completed frame |
| `rx_initial` | the stack's initial globals satisfy `RxInv` with the empty decoder and identification 1 |
| `loop_safe` | **the loopback never traps**: from a state that holds a decoder state, any number of calls of `main` on any input run to the end with `mtu + 70` units of fuel each — no index out of range — and the invariant holds after |

All depend on `propext`, `Classical.choice`, `Quot.sound` only.

With `Slip.decodeAll_encode` (M5.2) the loopback theorems say what the
target's link test checks by running: a frame fed in encoded comes back
encoded.

`World.normalize` (skipping exhausted input chunks) was `partial` in the
interpreter; it is now a total function, so that `World.next` — shared
by the interpreter and `Sem` — can be reasoned about (`next_eq`: reading
an item moves the read position and nothing else).

### How the proofs go

`simp only` with the equations of `Symex.lean` steps through the checked
AST one statement at a time.  A call is not unfolded: `execS_call_val`
turns the callee's theorem into an equation for the call statement
(`execS_add16`, `execS_get16`), so each function is verified once.  Fuel
is written `n + k` — what the caller has left plus what the function
needs — and the loop lemma takes `k + 31 + d` for `k` iterations.

A long function (`ip_send`: 16 statements, `udp_input`: 30) is executed
by one `simp only` with a fact per call statement, each for the state and
variables it will meet; an `if` is opened only where its condition is
known (`execS_ite_true`/`_false`), or has a fact of its own.  The
equality of the bytes written with the Spec's packet is a separate, pure
lemma each time.

State changes: `setG st x v` is the state with global `x` set;
`assign_var` and `lookup_setG_self`/`_ne` let `simp` carry a chain of
assignments.  Output: `pushOut st bytes` appends to the frame being
built, `txOut st frame` is the state after `out.end`.  A function whose
result state depends on the case (`slip_store`) has two theorems: one
with the state written out (`slip_store_spec`), one against the Spec
through the relation (`slip_store_refines`).

### TCP: the raw layer

The TCP code is proved in two layers, which `tcp_input_refines` and
`tcp_tick_refines` join into statements about the code (below).

**Raw layer (done).**  The six globals the TCP code works on and the
trace are one value `w : TW`; `tcpSt st w` is the state with them set.
For every function `f` of `Ember/Net/Tcp.lean` there is a Lean function
`fW` on `TW` that is the code transcribed — the same tests in the same
order, on the same machine integers — and a theorem

```
call … (tcpSt st w) "f" args = .ok result (tcpSt st (fW w …))
```

| Ember function | Lean function | Theorem |
|---|---|---|
| `tcb_reset`, `cap`, `wnd`, `seg_len` | `RawTcb.reset`, `RawTcb.cap`, `RawTcb.wnd`, `RawSeg.len` | `tcb_reset_refines`, `cap_refines`, `wnd_refines`, `seg_len_refines` |
| `tcp_emit` | `emitW` — and the segment is **`Spec.Tcp.emit`** in `Spec.Ipv4.packet` (`tcpSegBuf_extract`) | `tcp_emit_refines`, `tcp_emit_tw` |
| `send_seg`, `send_syn_ack`, `send_reset` | `sendSegW`, `resetW` | `send_seg_tw`, `send_syn_ack_tw`, `send_reset_tw` |
| `rexmit`, `output`, `acceptable` | `rexmitW`, `outputW`, `accW` | `rexmit_tw`, `output_tw`, `acceptable_tw` |
| `listen_input`, `ack_input` | `listenW`, `ackW` (with `shiftIn`: acknowledged bytes leave the echo buffer) | `listen_input_tw`, `ack_input_tw` |
| `tcp_segment` | `segW` (`segAckW`, `segDataW` with `cpIn`, `segFinW`, `segTailW`) | `tcp_segment_tw` |
| `parse_mss`, `tcp_input` | `parseMssW` (`mssIter`), `tcpInputW` | `parse_mss_tw`, `tcp_input_tw` |
| `rto`, `tcp_tick` | `rtoIter`, `tickW` | `rto_refines`, `tcp_tick_tw` |

The theorems have hypotheses about sizes (`TWok`: the packet buffer
holds a maximal segment, the echo buffer has 256 bytes) and about the
connection record where a loop or a send needs them (`sent ≤ pend_len ≤
256`, the data to send fits the buffer, `SegTailOk`); they are what the
invariant of the second layer has to supply.  Under them **no TCP
function traps**: every index is in range and the fuel given suffices.

### TCP: against the Spec

**Second layer (done, `TcpSim.lean`, `TcpSimParse.lean`).**  This is
mathematics about two Lean functions; the Ember semantics is not
involved.

* `TcbRel r pd T`: the connection record `r` (machine integers) and the
  echo buffer `pd` (a fixed 256-byte array) hold the Spec's control
  block `T` (naturals, `pending : ByteArray`): every field equal, the
  buffer starts with `T.pending`, and `sent ≤ |pending| ≤ cap`,
  `ourMss ≤ 256`.
* `SegRel s b S`: the segment record holds the Spec's parsed segment
  `S`, whose data lies in the packet buffer `b`.
* `Sim ourIp w c ev0 id0`: `TcbRel`, the same `iss`, and the trace of
  the step so far, **filtered to transmissions and drops** (`keep`), is
  `ev0`, then the segments the Spec queued in `c.out` — each as
  `Spec.runTcp` will transmit it, SLIP-encoded in `Spec.Ipv4.packet`
  with the identification counting up from `id0` — then the drops in
  `c.diag`.

| Theorem | Statement |
|---|---|
| `acc_rel` | `acceptable` is `Spec.Tcp.acceptable` (RFC 9293's four cases) |
| `emit_sim`, `sendSeg_sim`, `sendSynAck_sim`, `sendReset_sim`, `rexmit_sim` | the sends are the Spec's `send`, `sendSeg`, `sendSynAck`, `sendReset`, `rexmit`: same segment bytes, same state |
| `output_wp` | `output` is `Spec.Tcp.output`: new echo data, FIN, ACK or window update, the retransmission timer |
| `listen_wp` | `listen_input` is `Spec.Tcp.listenInput` |
| `ack_wp`, `ack_rel` | `ack_input` is `Spec.Tcp.ackInput`; the loop that moves the echo buffer down leaves `pending.extract acked size` |
| `data_rel`, `fin_wp`, `tail_wp` | the data stage appends the same bytes (`dataStep`), the FIN stage is `finStep`, then `output` |
| `segment_wp` | **`tcp_segment` is `Spec.Tcp.input`** (via `Tcp.input_eq`, its steps) |
| `parseMss_iter`, `mss_rel` | the Spec's option loop (a `for` with `break`/`continue`) is an iteration; `parse_mss` (16-bit indices into the packet buffer) computes it |
| `parse_rel` | the header checks of `tcp_input` are `Spec.Tcp.parse`: same rejections with the same reason; otherwise `SegRel` |
| `tcp_input_sim` | **`tcp_input` is `Spec.Tcp.parse` then `Spec.Tcp.input`**: if the Spec rejects with `r`, `tcpInputW w = dropW w r`; otherwise `Sim (tcpInputW w) ((Tcp.input src S).run c).2` |
| `rto_spec` | `rto` is `Spec.rto` (the doubling loop, capped) for up to 16 retries |
| `tick_wp`, `tcp_tick_sim` | **`tcp_tick` is `Spec.Tcp.tick`**: `Sim (tickW w) (Tcp.tick.run c).2` |

Each is stated with `Spec.Tcp.wp` (M5.3), so that they compose along the
Spec's `do` blocks.  Hypotheses of the two results: `Sim` before the
step with no drop yet in `c.diag`; for a segment, that it lies in the
packet buffer (`20 + n ≤ b.size < 65536`); for the tick, the Spec's
invariant `Tcp.Inv c.tcb` (proven preserved, M5.3 — it is what makes the
stack's order of tests, FIN-WAIT-2 before the retransmission timer,
agree with the Spec's opposite order) and that the idle and retry
counters are below 255.

What the second layer does **not** say:

* the Spec's `tcb` lines and its note (`connection reset by peer`, which
  the stack words differently) are not compared — only transmissions and
  drops;
* the bound on the counters (they stay below 60 and 9) is assumed, not
  proven;
* anything about TCP inside the receive path: these are theorems about
  the calls `tcp_input(src, dst, n)` and `tcp_tick()`, not yet about
  `ip_input` or `slip_rx` reaching them.

**The layers joined (`TcpSimParse.lean`).**  The raw layer's size
hypotheses (`TWok`, `SegTailOk`, `sent ≤ pend_len ≤ 256`) follow from
`TcbRel` and a packet buffer of at least 296 bytes (`TcbRel.raw`,
`segTailOk_of`, `segAck_ok_rel`, `parsed_rel`).  Hence, about the code as
the Ember semantics runs it:

| Theorem | Statement |
|---|---|
| `tcp_input_refines` | from `tcpSt st w` with `Sim ourIp w c ev0 id0`, the segment in `buf[20, 20+n)`: `Sem.call … "tcp_input" [src, dst, n]` **does not trap** and ends in `tcpSt st w'`; if `Spec.Tcp.parse` rejects with `r` then `w' = dropW w r`; otherwise `Sim ourIp w' ((Spec.Tcp.input src S).run c).2 ev0 id0` |
| `tcp_tick_refines` | likewise `Sem.call … "tcp_tick" []` ends in `tcpSt st w'` with `Sim ourIp w' (Spec.Tcp.tick.run c).2 ev0 id0` (under `Tcp.Inv c.tcb` and the counters below 255) |

Since the conclusion is `Sim` again, the statements chain over a
sequence of segments and ticks (the invariant `Tcp.Inv` is preserved by
`Tcp.input_inv` and `Tcp.tick_inv`).

### One input item, TCP included (`TcpRx.lean`, `NetStep.lean`)

`NetInv st s w mtu ourIp N` relates the stack's globals `st` to the
Spec's stack state `s`: the TCP globals hold `w` (`TcpHolds`), the
control block, `iss` and the IP identification agree with `s`
(`StRel`: `TcbRel`, …), the receiver's globals hold the Spec's SLIP
decoder `s.slip` (`RxInv`), the constants have their values.

| Theorem | Statement |
|---|---|
| `ip_input_refines_tcp` (`RefineIpInput.lean`) | `ip_input` with the protocol-6 branch: whatever the call `tcp_input(src, dst, n)` does on the segment at offset 20 |
| `ip_input_tcp` | … which is `Spec.Tcp.parse` and `Spec.Tcp.input` (`tcp_input_refines`) |
| `runTcp_keep` | `Spec.runTcp act` on a SLIP link: the control block and `iss` of the action's result; the queued segments as IPv4 packets with consecutive identifications, then the action's drops |
| `frame_refines` | **a frame through `ip_input` is a frame through `Spec.ipInput`**, ICMP, UDP and TCP: no trap; `StRel` before and after; the two traces get the same transmissions and drops |
| `slip_rx_gen` (`RefineRx.lean`) | `slip_rx(c)` with the handling of a complete frame as a parameter |
| `slip_rx_step` | **one received byte**: from `NetInv`, `slip_rx(c)` does not trap and ends in `NetInv` against the Spec's state after the same byte (`byteM c`, the body of the loop of `Spec.input (.rx …)`); same transmissions and drops |
| `tick_step` | **one tick, between two frames**: `tcp_tick()` likewise against `Spec.tickInput` (under `Tcp.Inv`, counters below 255, and no frame half received) |

Compared are the transmissions and drops (`keep`); the Spec's `pkt`,
`tcb` and note lines are not.

**A defect found by this proof, and its fix.**  `tick_step` needs "no
frame half received" because without it the statement is false: the
stack builds what a tick sends (retransmission, idle-close FIN, give-up
RST) in the one packet buffer, which also holds the frame being
received.  As first written, `main` called `tcp_tick()` whenever a tick
arrived, so a tick that sent in the middle of a frame destroyed that
frame and the stack differed from the Spec; no fixture or generated
session had a tick inside a frame.  Now a tick in the middle of a frame
waits for the end of that frame, in the stack (`main`, `tick_due`) and
in the Spec (`Spec.tickArrives`, `tickDue`); a second tick while one
waits gives the frame up, so that a stray byte cannot stop the timers.
`tcp_tick()` is therefore only called with `len = 0`, which is the
hypothesis of `tick_step`.  Tests: `corpus/timer/midframe-tick-*.trace`
and the `-midtick` variant of every generated lockstep session.

### `main`, and `main` again and again (`TcpBound.lean`, `Main.lean`, `Driver.lean`)

`MainInv st s w …` is `NetInv`, plus: the stack has booted, its
`tick_due` is the Spec's `tickDue`, and the Spec's control block
satisfies `Tcp.Inv` and `Tcp.Bnd` (`idle < 60`, `retries ≤ 8`).

| Theorem | Statement |
|---|---|
| `Spec.Tcp.input_bnd`, `tick_bnd`, `Spec.reach_bnd` | segment arrival and the tick keep `Bnd`; it holds in every reachable state (this is where `tick_step`'s "counters below 255" comes from) |
| `main_none`, `main_tick_now`, `main_tick_defer`, `main_tick_giveup`, `main_byte`, `main_byte_tick` | the code of `main` in each case, with what `slip_rx` and `tcp_tick` do as hypotheses |
| `main_step` | **one call of `main`**: from `MainInv` it does not trap, reads one item `k` (`input.next`) and ends in `MainInv` against the Spec after `itemM k` — nothing, `Spec.tickArrives`, or `Spec.byteInput c`; the same transmissions and drops.  In particular `tcp_tick()` is only ever called with no frame half received |
| `boot_call`, `boot_inv` | the first call from `Sem.initial Net.prog inputs` is a call from the state after `tcb_reset(); booted := true`, which satisfies `MainInv` against `Spec.State.init` |
| `input_items` | `Spec.input i` on a SLIP link is `itemM` over the items of `i` (one for a tick, one per byte of a chunk) |
| `next_spec` | `input.next` hands out the first item not yet read, with the number of its input, and `0xFFFF` when there is none (empty chunks are skipped) |
| `main_iter` | **`j` calls of `main`** from `MainInv`: none traps; `MainInv` against the Spec after the next `j` items; the kept lines (transmissions and drops), each with the number of its input, are the same |
| `runTagged_later` | the Spec over the items of the inputs is `Spec.step` over the inputs: same state, the kept lines of each step |
| `main_run`, `main_run_all` | **from the initial state**: any number of calls of `main` does not trap; once every item is read, the state satisfies `MainInv` against `Spec.reach {} inputs`, and the kept lines of the stack's trace are, input by input, those of `Spec.step` (`specKept`) |

So for every input sequence the stack in Ember — as the semantics
`Ember.Lang.Sem` runs it, for the SLIP configuration `{}` (10.0.0.1, MTU
296, no DHCP) — never traps and transmits and drops exactly what
`Ember.Spec` does, at the same inputs.

What these statements are about, precisely:

* `mainIter fuel p j st` is `j` calls of `main` in a row.  `Sem.run`
  (and `Lang.runMachine`) make those calls in a `while` loop, until the
  input is used up and three more calls read nothing; that loop is
  `partial` in Lean's core and no theorem is about it, nor about how
  `Sem.run` prints the events as `Trace` lines.
* The program is any `p` with the functions of the checked stack
  (`TcpAll p`, `TcpReasons p`, `p.fn? "main" = some main_fn`); that the
  type checker's output for `Net.prog` is such a `p` is checked by
  `#guard`s (evaluation), function by function, not by a theorem.
* The fuel per call is `n + 4716` for any `n`: enough for the longest
  path (a full frame through TCP, then a tick).

### The emitted C (M5.8)

`Ember/C/Sem.lean` (M5.7) gives the C subset a meaning — and none to
what C leaves undefined or would compute in a signed type.  The proofs
relate it to `Ember.Lang.Sem` through the emitter `Ember/C/Compile.lean`
itself (total functions; `wpc` is a weakest-precondition calculus for
its monad): every theorem is about the code that emitter produces.

**The result** (`CNet.lean`):

| Theorem (`CSim`) | Statement |
|---|---|
| **`stack_c`** | for the checked SLIP build and options without a name prefix, any profile with `int` of 16 bits or more: the emitted C, called again and again from its initial state as `Ember.C.Sem.run` calls it, ends every call normally — no `ember_trap`, nothing undefined — and once the input is read, the kept lines of its trace (transmissions and drops, each with the number of its input) are `specKept`: those of `Spec.step`, input by input.  M5.6 (`main_run_all`) and M5.8 (`iter_sim`) together |
| **`iter_sim`**, `iter_trap` (`CProgram.lean`) | for any program the checker accepts: if `j` calls of the entry function end in `Lang.Sem`, they end under `C.Sem`, in a related state (the same world — input position, events, frame, MMIO — and every global holding its value); and if the next call traps, the C traps, with the same events |
| `entry_sim`, `init_rel`, `compile_unit` | one call of the entry function; the initial states are related (every initialiser); what `C.compile` produces has the records, tables and functions of the program |
| **`fn_sim`** (`CFn.lean`) | a compiled function, called with the C values of its arguments from related globals: the result of `Lang.Sem` for its body, with any fuel — the same result value, globals and world related again, the C stack as it was — or a trap when it traps |
| **`stmt_ok`**, `block_ok` (`CSim.lean`) | for a well-typed statement: the code `C.stmt` emits does, from related states, what `Lang.Sem.execS` does with it — ends the same way (normally, `break`, `return` with the same value) in related states, or ends in `ember_trap` when it traps.  Every construct: declarations (zeroed arrays and records too), assignments to variables, fields and elements, `if`, `for`, `loop`, `break`, `return`, the nine effects, calls, and the destination of a result, which is evaluated after the call |
| `store_ok` (`CCall.lean`) | `assignResult`: `l = f(…)` directly when nothing in `l` can change in the call and no check is needed, otherwise through a temporary with the checks after it; either way what `Lang.Sem.storeResult` does |
| `eff_sim` | each function of the runtime interface, as `C.Sem.effect` defines it, does to the world what the effect of `Lang.Sem` does |
| `assign_sim` (`CRel.lean`) | `Lang.Sem.assign` on a typed scalar place is `C.Sem.write` at the location of its lvalue: the states are related again |
| **`expr_ok`**, `place_ok` (`CExpr.lean`) | for a well-typed scalar expression `e`: the statements `C.expr e` emits run from related states, declare temporaries only, and the emitted expression has the C value of `evalE e` — or they end in `ember_trap` when `evalE e` has no value; a place's lvalue designates its variable's storage at its path |
| `binC_ok`, `unC_ok`, `castC_ok`, `condC_ok` | every operator, as emitted (operation in `unsigned` or `uintN_t` and truncating cast; the guards of `/`, `%`, `<<`, `>>`; comparisons folded by `-Wtype-limits` reasoning; the SDCC division helpers), has the value of the Ember operator |
| `evalE_hasTy` (`CTypes.lean`) | a well-typed expression evaluates, in a state whose variables have their types, to a value of its type |
| `progOkB_sound` (`CCheck.lean`) | a program the checker `progOkB` accepts satisfies what the theorems assume (`ProgOK`, `GlobalOK`, an entry function without parameters) |
| `hygU_of_prefix` | without a name prefix, the emitter's names do not collide (globals `g_…`, locals `v_…`, temporaries `t<k>`, functions `e_…`, `entry`, the runtime's `ember_…`) |
| `Sem.mono1`, `Sem.Exec.void` (`CFuel.lean`, `CVoid.lean`) | a run of the C semantics that ends, ends the same way with more fuel; the `(void)x;` statements the emitter adds for `-Wunused` change nothing |
| `keeps`, `returns_all` (`LangFrame.lean`) | in `Lang.Sem`: a `for` body that does not write the counter leaves it alone; a body that returns on every path does not fall off its end |

How it is put together:

* **The relation** (`SRel`): the Ember locals and the C locals are the
  same list position by position, apart from the emitter's temporaries,
  which only C has (`LRel`); every global holds the C value of its value;
  the worlds are equal (`GRel`).  A statement leaves the scope it ran in
  with the same names and the same values in the temporaries (`Same`),
  which is what a loop needs of its bounds.
* **Fuel**: both semantics count fuel, differently.  The theorems say:
  if the Ember side ends with `k` units, there is an amount with which
  the C side ends the same way; more never hurts (`mono1`).
* **The induction**: `stmt_ok` is by recursion on the statement, for
  every fuel up to `N`, given that calls are right with less than `N`
  (`FnSim`); `fn_sim` closes that by induction on `N`.
* **What a program must satisfy** (`WTS`, checked by `progOkB`): the
  typing the emitter relies on, over its own `Env.tyOf`; arrays below
  65 536 elements; `loop` bounds below 2³²; a `for` body that does not
  assign its counter; `break` only in loops; a result on every path of a
  function that has one; parameters that are scalars passed by value.
  The checker is run on the checked builds of the stack — SLIP,
  loopback, Ethernet, Ethernet with DHCP — for the three profiles
  (`#guard`s in `CNet.lean`): all are accepted.

Three things changed in the emitter for the proofs, none in its output
(the golden C is byte-identical): `assignResult` compiles the
destination again after the call's temporary instead of moving the
emitted checks; `compileFn` and `compile` are built from named functions
(`paramC`, `fnEnv`, `globalC`, `entryFn`) instead of loops.  In
`Ember/C/Sem.lean`, locations got decidable equality (the test that
`l` in `l = f()` names the same storage after the call is now `=`).

**Not covered:**

* **by-reference parameters.**  `Lang.Sem` copies an array or record in
  and out, the C passes a pointer; that the two agree needs the type
  checker's no-aliasing rules as a theorem.  The relation has no
  pointers, and `progOkB` rejects such a program.  The stack has no
  by-reference parameter; the examples that have one
  (`Ember/Lang/Examples.lean`) are covered by tests only;
* **options with a name prefix** in `stack_c` (the fuzzer's programs,
  several per C file): `iter_sim` takes the absence of collisions as a
  hypothesis (`HygU`), proved for the empty prefix;
* **the C semantics itself** is a definition (M5.7), and the printer
  `Ember/C/Print.lean` from the C AST to text is trusted: that gcc and
  SDCC give the printed text the meaning `Ember.C.Sem` gives the AST is
  what the differential tests check, not a theorem (CompCert's Clight
  semantics would be the next step for the first part);
* the `while` of the drivers (`C.Sem.run`, `Lang.Sem.run`): the theorems
  are about the calls those loops make, as for M5.6.

### The IR of the Z80 back end (M7.1, M7.2)

`Ember/Z80/IRSem.lean` is the IR's semantics as total functions: one
instruction is one `step`, a function runs on fuel, memory is 64 KB of
bytes at the addresses a `Layout` gives.  The proofs relate it to
`Ember.Lang.Sem` through the lowering `Ember/Z80/IR.lean` itself.

**The result** (`IRNet.lean`):

| Theorem (`IRSim`) | Statement |
|---|---|
| **`stack_ir`** | for the checked SLIP build, the IR `IR.lower` returns for it and a layout the checker `irOkB` accepts: called again and again from its initial memory as `IR.Sem.run` calls it, the IR ends every call normally — no trap — and once the input is read, the kept lines of its trace are `specKept`.  M5.6 (`main_run_all`) and M7.1 (`lower_iter`) together |
| **`lower_iter`**, `lower_trap` (`IRLower.lean`) | for any program `progOkB` accepts and any layout `irOkB` accepts: from the initial state, if `j` calls of the entry function end in `Lang.Sem`, they end in the IR `IR.lower` returns, with the same world; and if the next call traps, the IR traps, with the same events |
| **`tidy_ref`** (`IRPass.lean`) | a call in the program with every body tidied (`cleanup`, then `dropChecks`) ends as in the program as lowered, in the same state |
| `sim_exec`, `del_sim`, `drop_sim` | a relation between the points of two bodies that every step keeps makes the second end as the first; dropping instructions a mask selects is one when what is dropped does nothing where it is (a label nothing jumps to, a jump to the next instruction, what follows a `ret`, `jmp` or `trap`); dropping an index check is one when the facts `dropChecks` collects hold (`facts_step`) |
| **`iter_sim`**, `iter_trap`, `entry_sim` (`IRProgram.lean`) | the same for the program as lowered (`lowerRaw`), from related states |
| `init_rel` (`IRInit.lean`) | the memory `initMem` builds holds every global's initial value |
| **`fn_sim`** (`IRSim.lean`) | a lowered function, its arguments in its frame: the result of `Lang.Sem` for its body, with any fuel — the same result, globals and world related again, memory outside its frames as it was — or a trap when it traps |
| **`stmt_ok`**, `block_ok` | for a well-typed statement: the code the lowering emits does, from related states, what `Lang.Sem.execS` does — goes on, jumps to the end of the loop for `break`, returns the value, or traps.  Every construct, as for the C |
| **`expr_ok`**, `place_ok`, `condJump_ok` (`IRExpr.lean`, `IRJump.lean`) | a well-typed scalar expression: the code leaves its value in the operand returned, or traps when it has none; a place is the address of its storage; a condition jumps or falls through as its value says, `&&` and `||` early only where nothing is skipped that could trap |
| `layOk_sound`, `progOkB_sound`, `slotsOkB_sound` | what the checkers accept satisfies what the theorems assume |
| `validate_sound` (`Z80Frame.lean`, M7.2) | a layout the frame validator accepts keeps every frame apart from the globals and from the frames of the functions it reaches |

How it is put together:

* **The relation** (`SRel`): every Ember local is at its offset in the
  function's frame, every global at its address, as the bytes of its
  value (`Holds`); the worlds are equal.  Frames are static, so what a
  callee may write is what its frame and those it reaches cover
  (`KeepOut`), and the layout keeps those apart from the caller's
  (`LayOK`, from `validate_sound`).
* **Translation validation, twice**: the lowering checks that no label
  is defined twice (`lowerFnChecked`; it never is, the proofs take it
  from the check), and the layout is checked rather than the allocator
  proved.
* **The passes** are proved for any body: `cleanup` needs the labels to
  be unique; `dropChecks` needs a slot the body compares in a branch
  and a slot it writes to be apart in memory unless their offsets
  overlap (`SlotsOK`, checked by `slotsOkB` on the program and layout).
* The checkers are run on the checked builds of the stack — SLIP,
  loopback, Ethernet, Ethernet with DHCP — with the layout
  `IR.Sem.run` computes (`#guard`s in `IRNet.lean`): all are accepted.

The proofs found one defect in the lowering, now fixed with a test
(`regress_strict_and`): `a && b` skipped `b` when `b` was an element at
a constant index that is not a literal and out of range, where the
interpreter traps.  For the proofs the lowering was rewritten with
named functions (identical IR for every build of the stack, the
examples and 400 random programs), `cleanup` and `dropChecks` as
recursive functions on lists, and slots and operands got decidable
equality.

An index has a `bound` besides its check (`Index.bound`): what the
lowering knows the index to be below, kept when `dropChecks` drops the
check.  `IR.Sem` gives a program no meaning (`bad`) where an index is
not below its bound; the theorems show the lowered program never gets
there.  Code generation does not look at it — it is there for the proof
of the code generator, which needs every access to stay in its array.

**Not covered:**

* **by-reference parameters** (as for the C: `progOkB` rejects them);
* **`inlineCalls`** (off by default; `lower_iter` is about `IR.lower`
  without it);
* **the IR semantics against the interpreter**: `IR.Sem` and the
  `partial` interpreter `Ember/Z80/IRInterp.lean` are tested against
  each other, not proved equal;
* **from the IR on**: see "The code generator" below (M7.3, in
  progress).

### The encoder (M7.4)

The CPU model `Ember/Z80/Cpu.lean` has no decoder apart from its
interpreter: `step` reads bytes and acts.  `Ember/Z80/AsmSem.lean`
gives every instruction of `Asm.Instr` a meaning by its mnemonic and
operands (`exec`), written with the model's own helpers (`alu`,
`setReg`, `push`, …), and the theorems connect the three:

| Theorem (`Z80Enc`) | Statement |
|---|---|
| **`step_encode`** (`Z80Encode.lean`) | if `Asm.encode i env = .ok bs`, the bytes `bs` are in memory at the program counter and the CPU is not halted, then `Cpu.step` gives the state `Asm.exec env i` gives — every register, flag, memory, T-states and `R`.  For every form the assembler accepts that has no `IX`/`IY` operand (the back end and its runtime use none): 8- and 16-bit loads, the accumulator operations, `inc`/`dec`, rotates and shifts, `bit`/`res`/`set`, jumps, calls and returns with every condition, `rst`, `push`/`pop`, exchanges, I/O, the interrupt modes, the block instructions |
| **`assemble_ok`** (`Z80Asm.lean`) | in what `Asm.assemble` returns: the first item is at the origin, every item at the address after the encoding of the one before; the bytes at an item's address are its encoding with the labels resolved (`Assembled.env`); a label resolves to the address of its item |

How: with the mnemonic and operands fixed the encoder computes to
bytes, the model's decoding of those bytes computes, and both sides are
equal by `rfl`; an immediate operand is the only part that does not
compute, and three lemmas give its bytes.  For the proofs the `ED` and
`CB` pages of the model were split into the fetch of the opcode and the
rest (`edOp`, `cbOp`), and `assemble` was rewritten as two recursive
functions (`place`, `emit`) with the same output; `emit` checks that an
item has the size the first pass gave it, so "sizes do not depend on
label values" is checked on every program rather than proved.

**Not covered:** the forms with `IX` and `IY` (`exec` is `none` for
them); the block instructions are covered but their meaning is the
model's own `execBlock`; `Asm.relax` (it runs before `assemble`, which
is what the theorem is about); the text parser of the runtime's
assembly.

### The code generator (M7.3, in progress)

`Ember/Z80/Codegen.lean` turns a function of the IR into assembly
items, one instruction at a time, remembering what `A`, `HL` and the
accumulator hold.  The proofs (`Z80Gen`, `Z80Run.lean` … `Z80FnGen.lean`)
are about the generator as it is, through a weakest-precondition
calculus for its monad (`wpg`), over an assembled image (`ZCtx`: the
items, their addresses by `assemble_ok`, the IR program and its layout).

`Rel Z E fr dt regs ist tmps s` — a CPU state `s` and an IR state agree:
the image is in ROM, the shared bytes are equal, a temporary with a slot
has its value there once assigned (`dt`), the registers hold what the
tracker `regs` says, the stack pointer and the stack above it are as the
function found them (`fr`), and nothing outside the function's
footprint (`ZCtx.wr`) has changed.

| Theorem | Statement |
|---|---|
| `loadA_ok`, `loadHL_ok`, `storeA_ok`, `storeHL_ok` | an operand into `A`/`HL`, and those to a destination — a store the generator leaves out included |
| `mov1_ok` … `cmp_ok`, `br_ok`, `jmp_ok`, `label_ok`, `ret_ok`, `trap_ok`, `call_ok` | the code of each instruction, for values of one and two bytes |
| `genAddr_ok`, `lea_ok`, `load1_ok`, `load2_ok`, `store1_ok`, `store2_ok` | an address into `HL` — static root, an index of one or two bytes checked in line or by `rt_bound` and scaled by a power of two — and memory through it; a failed check gets to `rt_trap`, as the IR's instruction traps |
| `shift1_ok`, `shift2_ok`, `shift4_ok` | shifts by a constant: repeated `add`, `srl`/`rr`, a byte moved, or the runtime's routine |
| `loadAcc_ok`, `storeAcc_ok`, `movW_ok`, `binW_ok`, `flagsW_ok`, `ext42_ok`, … (`Z80Acc.lean`, `Z80AccOps.lean`, `Z80ExtW.lean`) | values of four bytes: the operand into the runtime's accumulator (a constant from the literal pool), the operation by a routine of the runtime, the accumulator stored |
| `eff_ok` (`Z80Eff.lean`) | an effect's code calls the effect's routine with its argument in `A` (a note's value in the accumulator): afterwards the machine stands for the world `IR.Sem.effect` gives (`out.byte`, `out.end`, `drop`, `note`, `input.next`, `ring.pop`) |
| **`ins_ok`** (`Z80Ins.lean`) | for a covered instruction and whatever `IR.Sem.step` says it does: the code reaches the next item with the states agreeing after it; or the label's item; or calls the function and stores its result; or returns (`RetSt`); or reaches `rt_trap` — in the machine around the CPU, which stands for the IR's world before and after (`MAfter`).  An instruction without effects is proved to do no I/O whatever the bus would answer (`Steps`, `After`) and lifted (`After.lift`) |
| `genBody_ok`, `Chain.fns` (`Z80Fn.lean`) | the generator's states before and after every instruction of a body, each with the promise of `ins_ok` |
| **`exec_ok`**, **`fn_ok`** | from an instruction of a body with the states agreeing — and so from a function's entry (`Entry`) — the code has the `Outcome` of `IR.Sem.exec`/`callF`: it returns with the result in `A`/`HL`, the shared bytes as the IR left them and only the footprint written, or it is at `rt_trap`; by induction on the fuel, the functions called included |
| `genFn_ok` (`Z80FnGen.lean`) | the run of `genFnCode` whose items are in the image gives what `fn_ok` needs of a function (`FnGen`) |
| **`prog_ok`** (`Z80Prog.lean`) | in an image that holds the items `Codegen.genProg` gives (at any offset), given `RtOK` and `FnStatic` of every function in the environment its second pass ran in (`progEnvs`: the temporaries with a slot, the stores left out): every function with code, entered as `Entry` says, has the outcome of `IR.Sem.callF` |
| `shapeB_sound` (`Z80Shape.lean`) | a checker for the part of `FnStatic` that is about a body alone (covered instructions, the last one does not go on, labels unique); `#guard`: it accepts every function of the SLIP build and of the loopback program |
| `plan_ok`, **`fnStaticB_sound`** (`Z80Plan.lean`, `Z80Check.lean`) | a `Plan` gives what `ZCtx` has as predicates as data (intervals of shared bytes, of bytes a function may write, the slots it uses); `okB` decides what `ZCtx.OK` asks of it and `fnStaticB` decides `FnStatic` of a function in its environment — given that the image has the plan's labels and wide constants (`Labels`, `Lits`) |
| `#guard boardCheck` (`Z80PlanOf.lean`, `Z80BoardPlan.lean`) | the plan `mkPlan` makes of a build for the board passes `okB` and `fnStaticB` of every function: the SLIP build (35 functions) and the loopback program — evaluated at build time, not by the kernel |
| **`loop_static`**, `loop_ok` (`Z80LoopIR.lean`, `Z80Loop.lean`) | the loopback program, by the kernel: the environments of its four functions, `okB` and `fnStaticB` of its plan, the labels in the generated items — on its IR written out as a term (that the term is what `IR.lower` returns, and the layout what `build` computes, are `#guard`s) |
| **`loop_image_ok`** (`Z80LoopItems.lean`, `Z80LoopImage.lean`) | the loopback image for the board without the passes on the assembly (`build (passes := false)`, its 351 items written out; `#guard`): the kernel assembles it, finds the symbols of the areas, the generated items, `rt_trap`, and no instruction naming `rt_acc` — so every function of it does what the IR's function does, given `RtOK` and a machine that an instruction without I/O leaves alone |
| `rt_bound_ok`, `harness_input`, `harness_out_byte`, `harness_out_end`, `harness_drop` (`Z80Rt.lean`) | routines of the runtime, from their items in an image: `rt_bound` returns when `HL < BC` with `A`, `DE`, `HL` kept and is at `rt_trap` when not; the effects of the test harness (`Runtime.harness`: ports of the model, no interrupts) do to the harness's machine (`Harness`) what `IR.Sem.effect` does to the world.  None uses the stack |
| `ImgIn.ok` (`Z80Image.lean`) | the statement of `loop_image_ok` for any image: one check (`ImgIn.check`, run by the kernel on a term) gives `ZCtx.OK` and, with `RtOK`, the functions |
| **`loopH_ok`** (`Z80LoopHItems.lean`, `Z80LoopH.lean`) | the loopback image for the test harness, without the passes on the assembly: every function does what the IR's does **with nothing taken of the runtime** — the four routines it calls are proved, it calls no other, and the plan has `rtK = 0` (a function needs two bytes of stack per call below it) |
| `boot_ok`, `rt_zero_ok`, `ldir_zero` (`Z80Boot.lean`) | the runtime's start-up, from its items: from reset (`di`, `ld sp,0`, `rt_init`) to the head of the loop with the RAM in use cleared — `rt_zero`, an induction over `ldir` |
| `loop_iter`, `loop_run`, **`loopH_run`**, `loopH_run_halt` (`Z80LoopH.lean`) | the harness's loop, from its items: from its head, with the input used up the loop is left and the CPU stops (`di; halt`); else the entry is called as `IR.Sem.callF` says and the CPU is back at the head.  The loop's count of idle calls is zero at the head — a call with input remaining moves the position in the input (`Moves`), which the loop asks of the machine (port `0xD9`) — so the loop is left only with the input used up.  From reset, against `irIter`; with no input left the machine has stopped |
| **`loopH_spec`**, **`loopH_spec_halt`** (`Z80LoopHSpec.lean`, `Z80World.lean`) | the same against the **Ember semantics**: `loop_main_refines`/`loop_safe` (M5.5: the loopback never traps, and takes an item of input in every call) and `lower_iter` (M7.1) composed with `loopH_run`.  From reset, for any input: `j` calls of `main` end in the Ember semantics and the machine holds their world at the head of the loop, or it stopped after `i ≤ j` calls with the world of those and no input left; and — the input being finite (`rem_next`: a call leaves one item less) — **the machine does stop, with the world of the calls that used the input up**.  `LoopSrc p`: what is taken of the Ember program (it is the checked loopback program, lowered to `Loop.ir`, accepted by the checkers of M7.1 for this layout) — each computable part a `#guard` |
| `step_sim`, **`loopH_halts`** (`Z80Machine.lean`) | **the machine the tests run**: in harness mode, with nothing on the serial line and no interrupt pending, one `Ember.Z80.Machine.step` is one step of the proofs' machine and the relation `Sim` (input position, latch, mark, frame, events — a drop by the name of its reason; notes and the trap are not followed) is kept, for every port.  So of `Machine.step` from the machine built as the tests build it (the image `assemble` gives, loaded at 0 by `Cpu.load`, RAM from `0x8000`, harness mode, any input): after some number of steps the CPU is halted and the machine stands for the world the Ember semantics has when the input is used up.  For this `Machine.normalize` became a recursion (it was a `while`) and `Cpu.load` a fold |

**Checked, not proved** (translation validation, on every function
generated): `jumpsOk` — what the generator assumes the registers hold
after a label is what they held at every jump to it and at the fall
into it (the generator records both; `arrive`).

**The machine.**  `ZCtx` has a machine around the CPU: a state `W`,
what its bus answers a read with (`bus`), what a read or a write does to
it (`dev`), and `wrel` — the machine's state stands for the IR's world
(the input still to come, the events so far).  Nothing is assumed of
them but that an instruction without I/O leaves the machine as it is.

**Assumed for now:** `RtOK` — the specifications of the runtime's
routines (`rt_mul8`, `rt_div8`, …, `rt_not16`, `rt_neg16`, the shifts,
`rt_bound`, the routines on the accumulator `rt_ld32`, `rt_st32`,
`rt_add32`, …, `rt_cmp32`, `rt_acc_a`, `rt_acc_hl`, and the routine of
each covered effect: it returns having done to the machine what the
effect does to the world).  Each is taken where the image calls the
routine (`Uses`), and the accumulator's symbol where an instruction
names it (`AccRef`): an image has the routines its code uses and no
others, so the loopback image, without the wide routines and `rt_acc`,
can meet them.  Proved so far: `rt_bound`, and the four effect
routines of the test harness (`Z80Rt.lean`); the board's routines (the
ring filled by the interrupt routine) need interrupts in the machine of
the proofs, which it does not have — `WSteps` runs instructions only —
and the arithmetic and accumulator routines are tested (`rt-check`),
not proved.

**Two changes to the generator the proofs asked for** (the images
changed; the tests and the size gate pass):

* *The temporaries have an area of their own* (`Codegen.tmpArea`).  The
  relation takes the slots of temporaries to be apart from every byte
  the IR sees (`FnLay.nodata`); the layout used to put them on top of
  the frame, where the frame of a function that never runs at the same
  time may lie.  +9 bytes of RAM in the SLIP build.
* *A store to a byte another function's frame shares is made*
  (`keepShared`, `sharedBytes`).  A store the generator leaves out
  (the value is always at hand in a register) leaves the CPU's memory
  unlike the IR's at that byte; where the byte is also a variable of
  another function the relation cannot say so.  +91 bytes of code in
  the SLIP build (15 functions had such stores).  And in its second pass
  the generator now refuses to read the frame from memory where the
  first pass saw no read (`noteRead`) — it never did; the proofs rely on
  it.

**Where this stands for the images.**  Of the loopback image without
the passes on the assembly: for the test harness `loopH_ok` — nothing
assumed of the program, the layout, the image or the runtime; for the
board `loop_image_ok` — the same but for `RtOK`, and in a machine
without interrupts, which is not the board's.  For the harness also from
reset, through start-up and the loop that calls `main` (`loopH_run`).
The machine there is the CPU model with the harness's ports written as
a function of the world (`hbus`, `hdev`); `Ember.Z80.Machine` — the
machine the tests run — steps as it does (`step_sim`), so the statement
is also of `Machine.step` from the machine as the tests build it
(`loopH_halts`: it processes all its input and stops).  What the tests add around it is not in the theorem:
`Target.runHarness` (its loop until `halted`, the printing of the trace).  Of the SLIP build, the checks of the
layout pass (`#guard`, not the kernel), and nothing is connected to its
image yet (it has wide constants: the literal pool; and 1073
instructions to run the checks on in the kernel).  Of the images as
built by default nothing is proved: `build` runs `retThreading`,
`sweep`, `peephole`, `packHigh` and `relax` over the items, 303 bytes
of 7159 in the SLIP build; `ember-z80 own-build --plain` is the image
without them, tested like the other (random programs, the loopback, the
corpus).  Not proved: for the board, start-up, the interrupt routine and the
loop that calls `main`; interrupts in any image.  The stack: `Z.rtK` is what a
routine of the runtime needs below its return address — 0 for the
harness loopback (proved), 32 in the plans of the board builds
(a placeholder: `Ember.Z80.StackBound` computes at most 4 for any
routine of `Runtime.pieces`, not proved).

**Covered** (`Covered`): all 1073 instructions of the SLIP build's IR,
all 79 of the loopback program's, 1559 of the 1562 of the Ethernet
builds'.  **Not covered:** shifts by a variable, `zero`, `not`/`neg`
and memory through an address on four bytes, values of eight bytes, the
MMIO effects and `input.frame`, an address through a pointer
(by-reference parameters).  Of the runtime: the arithmetic and shift
routines, the routines on the accumulator, `rt_note`, the MMIO routines,
and everything of the board's runtime (its effects, start-up, the
interrupt routine and the ring) — proved are `rt_bound`, the harness's
four effect routines, `rt_zero`, and the harness's start-up and loop.
Of the images: the SLIP build's (its plan passes the checks, by
`#guard`; its image is not connected), the board's loopback image
beyond its functions, and every image as built by default — the passes
on the assembly (`retThreading`, `sweep`, `peephole`, `packHigh`,
`relax`) are not proved.  Interrupts are not in the machine of the
proofs.

### Not proven

* the driver loop of `Sem.run` and the printing of the `Trace` (above);
  on the Spec's side `Spec.run` likewise — `Spec.reach` and `specKept`
  are what its loop computes, by definition of `Spec.step`;
* only the SLIP configuration: the Ethernet build (`Ember.Net.Eth`,
  ARP, DHCP) has no refinement proofs;
* lines other than transmissions and drops (`pkt`, `tcb`, notes) are
  not compared;
* the Z80 back end from the IR on: the translation from the IR to machine code (M7.3) is proved in part ("The code generator": instructions of one and two bytes and functions, under assumptions still to be checked) and otherwise tested (the encoder, M7.4, is proved); and what "The emitted C" and "The IR of the Z80 back end" above list as not covered;
* that a function *traps* exactly when the Spec rejects: the theorems
  are for states that satisfy their invariants, and show that from those
  no call traps (the fuel given is enough and every index is in range).
