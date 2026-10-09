# Ember

A TCP/IP stack in Lean, a Lean-hosted DSL that emits C without undefined
behaviour, and the stack written in that DSL — three implementations
checked against each other through one trace format, on the way to
small machines (ESP32-C3, Z80) and to proofs.

* Design: [`docs/Ember-design.md`](docs/Ember-design.md)
* Plan and progress: [`docs/Ember-plan.md`](docs/Ember-plan.md) — M1–M3 (host) done
* Tests and tools: [`Tests/Ember/README.md`](Tests/Ember/README.md)
* The stack in Ember: [`Ember/Net/README.md`](Ember/Net/README.md)

| Directory | |
|---|---|
| `Ember/Spec` | reference stack: SLIP, IPv4, ICMP, UDP, TCP (one connection), Ethernet + ARP, DHCP client |
| `Ember/Lang` | the DSL: AST, type checker, interpreter (= semantics), `ember def` syntax, profiles, random programs |
| `Ember/C` | Clight-like C AST, `Lang → C`, printer |
| `Ember/Net` | the stack in Ember (SLIP build) |
| `Ember/Trace`, `Ember/Util` | trace format, `ember-diff`, packet decoder, pcap |
| `runtime/common` | C runtime interface and SPSC ring |
| `Tests/Ember` | corpus (recorded from Linux and hand-written), golden C, host harness, test suites |
| `tools/ember` | fixture recording, size gate, CI script |

```
nix-shell                  # gcc, sdcc, python3, dnsmasq, tshark
lake build
lake test                  # ≈ 3 minutes with every tool present
tools/ember/ci.sh          # lake test + size gate
```
