# Ember.Net — the stack written in Ember (M3)

The reference stack `Ember.Spec` rewritten in the Ember DSL, for the SLIP
link (MTU 296).  It is checked three ways on every input stream of the
corpus and on generated sessions: `Ember.Spec` = the Ember interpreter =
the emitted C compiled for the host, with the two Lean implementations'
**states** compared after every input (lockstep).

Ethernet + ARP (M1.11) and DHCP (M1.12) exist in `Ember.Spec` only; they
are needed for Wi-Fi (M4w), which is not part of this pass.

## Files

| File | Contents | Spec counterpart |
|---|---|---|
| `Layout.lean` | constants, drop-reason codes, `Tcb` and `Seg` records, globals | `Spec/Config.lean`, `Spec/Tcp/Tcb.lean` |
| `Buffer.lean` | big-endian access to `buf`, `csum`, `pseudo`, `csum_update` | `Spec/Checksum.lean` |
| `Ip.lean` | SLIP receive/transmit, `ip_input`, `ip_send`, ICMP and UDP echo | `Spec/Slip.lean`, `Ipv4.lean`, `Icmp.lean`, `Udp.lean`, `Stack.lean` |
| `Tcp.lean` | `tcp_input` (parse), `tcp_segment` (input), `listen_input`, `ack_input`, `output`, `rexmit`, `tcp_tick` | `Spec/Tcp/*.lean` |
| `Main.lean` | `main`: one input item per call; the `Prog` | `Spec.step` |

## Data layout

| Global | Type | Bytes (host64) | Role |
|---|---|---|---|
| `buf` | `[u8; 296]` | 296 | the one packet buffer: a SLIP frame is decoded into it, the reply is built over it |
| `pend` | `[u8; 256]` | 256 | the echo application's bytes (`[0, sent)` sent and unacknowledged, then unsent) |
| `t` | `Tcb` | 44 | the one connection |
| `sg` | `Seg` | 24 | the segment being processed, parsed from `buf` |
| `len`, `esc`, `over` | `u16`, `bool`, `bool` | 4 | SLIP receiver |
| `iss`, `ip_id` | `u32`, `u16` | 6 | ISN and IP identification counters (determinism) |
| `booted` | `bool` | 1 | `tcb_reset` on the first call |

Total RAM 935 bytes on host64 including the drop-reason name table (a
diagnostic, 296 bytes of pointers); 622 bytes with SDCC on the Z80.

### Replies in place

* ICMP: the request stays at `buf[20, …)`; byte 20 changes from 8 to 0 and
  the checksum is updated incrementally (RFC 1624); `ip_send` writes a
  fresh header at `buf[0, 20)`.
* UDP: ports swapped in place, checksum recomputed.
* TCP: everything needed from the received segment is read (into `sg`,
  and data into `pend`) before the single segment of the reply is built in
  `buf[20, …)` — the Spec sends at most one segment per input, always
  last, which is what makes one buffer enough.
* IP options are squeezed out (`buf[ihl, tl)` moved to `buf[20, …)`) so
  every protocol finds its header at offset 20.

### No retransmission buffer

As in uIP, the stack keeps no copy of what it sent.  On a retransmission
timeout `rexmit` regenerates the unacknowledged bytes from the
application's buffer `pend[0, sent)`; the receive window is the room left
in `pend`, so it never holds more than one segment.

## Correspondence with `Ember.Spec`

Every function mirrors one Spec function, with the same checks in the
same order and the same drop reasons (`Layout.lean` numbers them in the
order of `dropReasons`, whose names are the Spec's).  The lockstep
projection (`Ember/Tools/NetCheck.lean`, `specView`/`netView`) compares
after every input: all TCB fields, the echo buffer's live bytes, `iss`,
`ip_id`, and the SLIP receiver (length, flags, bytes).

Differences that are not observable, by design:

* the Spec decodes a whole `rx` chunk per step, the Ember stack one byte
  per call of `main` — states are compared at chunk boundaries;
* the Spec's `pkt` and `tcb` lines are diagnostics the Ember stack does
  not produce; its `note` for an accepted RST is its own.

## Size

`tools/ember/size-report.py` (baseline `bench/ember-size.baseline`):

| | code | RAM |
|---|---|---|
| host64, `gcc -Os` | 5.4 KB | 935 B |
| Z80, SDCC 4.6 `--opt-code-size` | 24.8 KB | 622 B |

The ESP32-C3 budget (16 KB code, 8 KB RAM) is met with a wide margin.
On the Z80 the RAM target (≤ 1 KB) is met and the code target (≤ 8 KB) is
not: SDCC's 32-bit arithmetic (sequence numbers) and the bounds-checked
`u16` indexing into a 296-byte buffer dominate.  That is the M4z.4 work
the plan anticipates (narrower profile arithmetic, bounds checks removed
where proofs allow, then the own back end of M6).
