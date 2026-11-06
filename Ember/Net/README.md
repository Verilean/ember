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

## With an application interface (`Srv.lean`, `Http.lean`; plan M8)

`Net.prog` above is the echo stack the proofs are about; it is unchanged.
`Srv.lean` is the same TCP with the application taken out and given as
Ember functions with fixed names (`app_reset`, `app_room`, `app_recv`,
`app_avail`, `app_fill`, `app_acked`, `app_close`; constants `APP_PORT`,
`APP_IDLE_CLOSE`, `APP_REUSE_TW`), and with `n` connections — `n` is a
parameter of the program (`Srv.prog n app`).  Ember has no arrays of
records, so the TCB fields are arrays `c_<field> : [_; n]`, and the
connection being worked on is copied into `t` (`tcb_load`, `tcb_save`).
Its reference is `Ember.Spec.Srv` (`Spec/Srv/*.lean`).

`Http.lean` is an HTTP/1.1 server on it (`Http.prog n site`): `GET` and
`HEAD` of fixed routes, 404, 400, 501, `Content-Length`, `Connection:
close`.  The site's responses — headers and bodies — are constants
(`h_rom`); a segment's bytes are computed from them by offset, so a
retransmission needs no copy.  Per connection the first `REQ_MAX` bytes of the
request header (the request line) are kept; its end is found as the
bytes come (`h_feed`), up to `HDR_MAX` bytes.  The server closes first, so a SYN that finds no
connection in LISTEN takes one in TIME-WAIT.

`Tls.lean` is TLS 1.3 on it (`Tls.prog n site`, `Spec.Srv.Tls` record for
record and alert for alert) with the crypto of `Crypto/` and the HTTP of
`Http.lean` inside; the certificate is Ed25519's when the client offers it,
P-256's (ECDSA, `Crypto/P256.lean`) otherwise — a browser.  Per connection a buffer of records received and one
of what is sent (the server's flight and the protected response, kept as
the Spec keeps them), the transcript hash's SHA-256 context, the keys and
sequence numbers; records are opened and sealed in place.

`Crypto/P256.lean` also verifies ECDSA P-256 signatures (`p2_verify`, plan
M9.2) on a SHA-256 hash: `r`, `s` in [1, n), the key on the curve,
`u1·G + u2·Q` by double and add with `G + Q` over the same complete
addition (the data are public), `x(R) mod n = r`.  It and its two
registers and inputs are in a program only when asked for
(`p256VerifyFns`, `p256Globals (verify := true)`): the HTTPS image of M8
does not carry them.

`Auth.lean` (plan M9.3) checks OIDC access tokens on the protected routes
of a site (`Spec.Srv.Http`'s `scope`), as `Spec.Srv.Auth.check` and
`Spec.Srv.Http.guard` do, while the header arrives: the `Authorization`
fields are followed byte by byte, the token's base64url is decoded by
segment, the signing input goes into a SHA-256 context of the connection,
the two JSON texts into a scanner that keeps a depth and a bit per level
and compares the top-level claims with the configuration as they come;
the signature is checked (`p2_verify`) only when the header is complete
and the route is protected.  Per connection about 250 bytes (the SHA-256
context, the 64-byte signature, the reader's state), whatever the token's
length.  It takes the place of `Http.lean`'s `h_feed` in a program whose
site has protected routes (`Http.feedFns`), in HTTP and in HTTPS; a site
without them gets the functions of M8, unchanged.

`Ctl.lean` (plan M9.5) serves control requests and kept connections for a
site that has them (`Spec.Srv.Http.Site.ctl`), as `Spec.Srv.Http.stepCtl`
does: the header is read for `authorization`, `content-length`,
`transfer-encoding`, `x-ember-seq` and `connection` at once; a control
request's body goes into a buffer of the connection (at most `bodyMax`
bytes) and into its SHA-256 context; the shared state (`ctl_last`,
`ctl_hash`) decides whether it is executed (its body copied to `ctl_cmd`,
`ctl_new` set for the device), answered again, or refused with 409; the
answer `200 ok N` is the one response made in RAM (`h_dyn`).  A kept
connection takes no data while a response is out (`app_room` 0) and the
next request once it is acknowledged; over plain HTTP the bytes of a
request that come in the same segment after the previous one are
dropped (no pipelining), over TLS they are the next request (`h_kept`
seals the response and resets the request at once).

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
diagnostic, 296 bytes of pointers); 887 bytes with SDCC on the Z80,
receive ring (256 bytes) included.

### The Ethernet build (`Eth.lean`)

For Wi-Fi raw frames (plan M4w).  Frames arrive whole through
`input.frame`; the 14-byte header is kept in `eth`, the payload goes to
`buf[0, …)` — where the IP code of the SLIP build expects its packet, so
`ip_input`, `icmp_input` and all of TCP are used as they are.  Added:

| | |
|---|---|
| `eth_store`, `eth_input` | receive a frame; destination MAC, EtherType, size; learn the sender of a well-formed IPv4 packet |
| `arp_input`, `arp_update`, `arp_find`, `arp_request` | RFC 826 with a cache of four entries, replaced round-robin |
| `eth_send`, `ip_send` | the frame out; an ARP request and the drop `arp-miss` when the destination is not in the cache |
| `dhcp_tick`, `dhcp_input`, `dhcp_send` | the client: DISCOVER, REQUEST, renewal at half the lease, NAK and time-outs |
| `udp_input` | the SLIP build's, with port 68 for DHCP |

Buffers: `buf : [u8; 576]`, `pend : [u8; 536]` (RFC 2131 requires 576);
the address `OUR_IP` is a variable here.  Programs: `Eth.prog` (static
address), `Eth.progDhcp`, and `Eth.progFor false 296`.  Tested on the
host only — Spec = interpreter = host C on the Ethernet fixtures and on
generated sessions (`ember-lockstep --gen eth|dhcp`); no target runtime
delivers frames yet.

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
| ESP32-C3, `riscv32-none-elf-gcc -Os`, no trace | 7.0 KB + 0.8 KB constants | 5.0 KB (4 KB stack) |
| Z80, SDCC 4.6 `--opt-code-size`, no trace | 7.5 KB | 887 B + 179 B of stack |
| Z80, own back end (`Ember/Z80`), no trace | 5.9 KB | 1 051 B + 14 B of stack |

The ESP32-C3 budget (16 KB code, 8 KB RAM) is met.  On the Z80 the code
budget (8 KB) is met by both builds; the RAM budget (1 KB) is missed by
about 40 bytes once the stack is counted — SDCC keeps locals there, the
own back end has static frames and only return addresses on the stack.
A ping costs 16 634 instructions on the C3; on the Z80 184 850 T-states
with SDCC and 183 136 with the own back end (46 ms at 4 MHz), most of it
the wire: 86 bytes each way at 640 T-states per byte.  (An earlier
version of this file said 24.8 KB for SDCC, a mistake of the size
script.)
