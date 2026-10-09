# udp/ — UDP echo (port 7)

| Fixture | Provenance |
|---|---|
| `linux-udp-echo-{0,1,5,64,255}.trace` | **Linux as responder** (`record-linux.py responder udp`): a datagram of that size to a UDP echo server on Linux's port 7. Byte-equal to Ember's reply with `mask=ipv4.id`; this is where the "DF on UDP and TCP, not on ICMP" rule comes from. |
| `linux-nc-udp.trace` | `printf "hi\n" \| nc -u -w1 10.0.0.1 7` against `ember-host`. |
| `linux-udp-echo.trace` | `tools/ember/tcp-scenarios.py udp-echo` (1, 100, 268 bytes) against `ember-host`; the scenario checks the echoes. |
| others | hand-written scenarios (`udp` list in `Tests/Ember/Scenarios.lean`). |
