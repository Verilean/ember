# arp/ — Ethernet II and ARP (M1.11), `link=eth`

| Fixture | Provenance |
|---|---|
| `linux-arp-{request,other,then-ping}.trace` | **Linux as responder** on a TAP device with Ember's MAC (`record-linux.py responder arp`). Ember's frames are byte-equal (`mask=ipv4.id`); frames are not padded to 60 bytes, as on a TAP device. |
| `linux-eth-ping.trace`, `linux-eth-tcp-echo.trace` | Linux as client on a TAP device against `ember-host --eth`: Linux resolves 10.0.0.1 by ARP, then pings / runs the echo scenario. (The plan suggested a veth pair; a TAP device gives the same frames without a second namespace.) |
| others | hand-written (`arp` list): RFC 826 merge rule, learning from IP frames, cache eviction and `arp-miss`. |
