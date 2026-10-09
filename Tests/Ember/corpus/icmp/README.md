# icmp/ — ICMP echo

| Fixture | Provenance |
|---|---|
| `linux-ping-s{0,56,200}.trace` | **Linux as responder**: `tools/ember/record-linux.py responder icmp` injects the pings `ping -s {0,56,200}` sends (3 each) into a TUN device where Linux is 10.0.0.1, and records Linux's replies. Ember must answer byte for byte the same; the IP identification (random in Linux) is masked (`mask=ipv4.id`). |
| `linux-ping.trace`, `linux-ping-s200.trace` | **Linux as client**: `ping -c 3 -i 0.3 -s 56 10.0.0.1` (and `-s 200`) through `record-linux.py client`, against `ember-host`. Outputs are the Spec's; `ping` reported 0 % loss. |
| others | hand-written scenarios in `Tests/Ember/Scenarios.lean` (`icmp` list), each with stated expectations. |

Re-record with `tools/ember/record-corpus.sh` (user namespace + `/dev/net/tun`, no root).
