# TCP: out of scope (Ember.Spec, M1)

Each item is either answered with RST or dropped with a `drop reason=`.

| Not supported | Behaviour | Reason given |
|---|---|---|
| More than one connection | RST-ACK to a second SYN | `unsupported-second-connection` |
| Active open | — (Ember never connects out) | — |
| Ports other than 7 | RST-ACK | `tcp-port-closed` |
| Out-of-order reassembly | ACK and drop; the peer retransmits | `out-of-order` |
| Data on a SYN | only the SYN is acknowledged; the peer retransmits the data | — |
| Options other than MSS (window scale, SACK, timestamps) | skipped; not echoed in SYN-ACK, so the peer turns them off | — |
| Urgent data | URG ignored, data treated as normal | — |
| Peer's receive window | ignored: Ember never has more than one MSS (≤ 256 bytes) unacknowledged | — |
| Congestion control, RTT estimation | fixed back-off schedule (`rto k`) | — |
| RFC 5961 challenge ACKs | RFC 793 behaviour: RST in window closes, SYN in window resets | `syn-in-window` |
| TIME-WAIT assassination protection (RFC 1337) | RST in TIME-WAIT closes | — |
| IP options | skipped on input, never sent | — |
| Fragmented datagrams | dropped | `fragment` |
