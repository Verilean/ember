# dhcp/ — DHCP client (M1.12), `link=eth mtu=576 dhcp=on`

| Fixture | Provenance |
|---|---|
| `linux-dhcp.trace` | dnsmasq 2.93 on a TAP device (`--dhcp-range=10.0.0.50,10.0.0.50,2m`) and `ember-host --eth --dhcp`: DISCOVER/OFFER/REQUEST/ACK, Linux pings 10.0.0.50, renewal at T1 (60 s = 120 ticks), ping again. |
| others | hand-written (`dhcp` list): DORA and renewal, NAK, timeout, wrong xid, unexpected message. |

Finding from recording: dnsmasq's OFFER is 328 bytes (BOOTP's 300-byte
minimum plus headers) and RFC 2131 requires 576, so the Ethernet build
uses `mtu=576`; the SLIP build keeps 296.
