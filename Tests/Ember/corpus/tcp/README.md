# tcp/ — one connection, passive open on port 7

| Fixture | Provenance |
|---|---|
| `linux-nc-echo.trace` | `printf "hello\n" \| nc -N 10.0.0.1 7` against `ember-host` (`record-linux.py client`). |
| `linux-{echo,bulk,client-rst,second-connection,closed-port,two-sessions}.trace` | `tools/ember/tcp-scenarios.py <name>` run by Linux against `ember-host`; each scenario exits 0 only when Linux saw the expected behaviour (echo intact, RST on a second connection, connection refused on port 8, …). |
| others | hand-written RFC 9293 scenarios (`tcp` list in `Tests/Ember/Scenarios.lean`): RST in every state, segments outside the window, out-of-order data and FIN, duplicate and in-window SYN, simultaneous close, FIN-WAIT-2 timeout, zero window, small MSS, options of every length. |

In the Linux-client fixtures the inputs are Linux's and the outputs the
Spec's (Linux's ISN and options make its own server side incomparable).
What is out of scope is in `UNSUPPORTED.md`.
