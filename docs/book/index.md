# Ember — the book

A TCP/IP stack written three times and checked against itself: a
reference stack in Lean (the **Spec**), a small Lean-hosted language
(`ember def`) that emits C without undefined behaviour, and the stack
written in that language — run on the host, on an ESP32-C3 in QEMU and
on a Z80, all compared through one trace format, with proofs that the
Ember stack and its C do what the Spec does.

On top of the stack sit an HTTP/1.1 server, TLS 1.3 (HTTPS with an
ECDSA P-256 certificate), routes protected by OIDC tokens (JWT ES256),
and a small control surface (`/status`, commands at most once, time).

## Read in order

- **0 · [Quickstart](00-quickstart.md)** — from a clone to a running stack, a recorded Linux session and its trace.
- **1 · [Overview](01-overview.md)** — what Ember is, what ships, what is tested and what is proved.
- **2 · [The Ember language](02-language.md)** — `ember def`, types, globals, the checker, the interpreter (= the semantics), and the pitfalls.
- **3 · [The reference stack](03-spec.md)** — SLIP, Ethernet/ARP, IPv4, ICMP, UDP, TCP, DHCP in Lean; the server layer and its `App` boundary.
- **4 · [Traces and testing](04-testing.md)** — the trace format, fixtures recorded from Linux, `ember-diff`, three implementations compared, the size gate.
- **5 · [C and the targets](05-targets.md)** — `Lang → C`, bounds checks and when they go, the ESP32-C3 runtime and QEMU, the Z80 (SDCC and Ember's own back end).
- **6 · [Tutorial: an HTTP app](06-http-app.md)** — routes in the Spec and in Ember, checked equal, tried with curl.
- **7 · [HTTPS and TLS 1.3](07-https.md)** — what the TLS server does, the crypto, certificates and entropy, trying it with curl and a browser.
- **8 · [Protected routes (OIDC / JWT)](08-auth.md)** — tokens of an identity provider checked on the device: ES256, issuer, audience, time, scopes.
- **9 · [Control, status and time](09-control.md)** — `/status`, commands at most once, time and the RNG.
- **10 · [What is proved](10-proofs.md)** — the refinement proofs, the C semantics, the Z80 back end, and exactly where the proofs stop.
- **11 · [Architecture](11-architecture.md)** — the system map: how the pieces fit, where state lives, what is fixed and what is bounded.

## Skim by question

| If you want to … | Start at |
|---|---|
| Build it and see packets | Quickstart |
| Decide whether Ember fits | Overview |
| Write or read `ember def` code | The Ember language |
| Know what TCP does and does not do | The reference stack |
| Add a test or a recorded fixture | Traces and testing |
| Put it on a board | C and the targets |
| Serve your own pages | Tutorial: an HTTP app |
| Serve them over HTTPS | HTTPS and TLS 1.3 |
| Accept only callers with a token | Protected routes |
| Trust a claim about correctness | What is proved |

## Sources

The code is at [github.com/Verilean/ember](https://github.com/Verilean/ember).
The design is in [`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md),
the plan and its progress in [`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md).
Every snippet in this book is copied from the tree, with its file; nothing is pseudocode.
