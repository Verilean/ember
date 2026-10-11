import Ember.Proof.Bytes
import Ember.Proof.Checksum
import Ember.Proof.Icmp
import Ember.Proof.Slip
import Ember.Proof.Headers
import Ember.Proof.Tcp
import Ember.Proof.Stack
import Ember.Proof.Symex
import Ember.Proof.Refine
import Ember.Proof.RefineSlip
import Ember.Proof.RefineIp
import Ember.Proof.RefineIcmp
import Ember.Proof.RefineUdp
import Ember.Proof.RefineIpInput
import Ember.Proof.RefineRx
import Ember.Proof.RefineTcp
import Ember.Proof.RefineTcpSt
import Ember.Proof.RefineTcpOut
import Ember.Proof.RefineTcpIn
import Ember.Proof.RefineTcpParse
import Ember.Proof.RefineTcpTick
import Ember.Proof.TcpSim
import Ember.Proof.TcpSimParse
import Ember.Proof.TcpRx
import Ember.Proof.NetStep
import Ember.Proof.TcpBound
import Ember.Proof.Main
import Ember.Proof.Driver
import Ember.Proof.CSem
import Ember.Proof.CTypes
import Ember.Proof.CArith
import Ember.Proof.CExpr
import Ember.Proof.CFuel
import Ember.Proof.CPlace
import Ember.Proof.LangFrame
import Ember.Proof.CRel
import Ember.Proof.CStmt
import Ember.Proof.CCall
import Ember.Proof.CSim
import Ember.Proof.CVoid
import Ember.Proof.CFn
import Ember.Proof.CProgram
import Ember.Proof.CCheck
import Ember.Proof.CNet
import Ember.Proof.Z80Frame

/-!
# Ember.Proof — proofs (plan M5): about the reference stack (P1), and that Ember code refines it (P2)

* `Checksum`, `Icmp`: the checksum algebra (M5.1);
* `Slip`, `Headers`: decode ∘ encode and parse ∘ emit (M5.2);
* `Tcp`, `Stack`: invariants of the TCP state machine, for `Tcp.input`
  and `Tcp.tick` and by induction over `Spec.step` (M5.3);
* `Symex`: symbolic execution of Ember code over the total semantics
  `Ember.Lang.Sem` (M5.4);
* `Refine`: functions of the stack in Ember compute the Spec's functions
  (M5.5: the checksum functions, 16-bit fields);
* `RefineSlip`: 32-bit fields; the SLIP receiver and transmitter with
  their effects; the SLIP loopback program as a whole — one call of its
  `main` is one step of the Spec's decoder, and it never traps;
* `RefineIp`: `ip_send` transmits the Spec's IPv4 packet;
* `RefineIcmp`: `icmp_input` is the Spec's ICMP echo handling;
* `RefineUdp`: `udp_input` is the Spec's UDP validation and echo;
* `RefineIpInput`: `ip_input` is the Spec's IPv4 validation and dispatch (TCP apart);
* `RefineRx`: `slip_rx`, the stack's receive path per byte, is the Spec's decoder step
  followed by `Spec.ipInput` (TCP apart);
* `RefineTcp`, `RefineTcpSt`, `RefineTcpOut`, `RefineTcpIn`, `RefineTcpParse`, `RefineTcpTick`: TCP, the
  raw layer — every function of `Ember/Net/Tcp.lean` computes a Lean function on one state value
  (`tcpInputW` for a segment, `tickW` for a tick); `tcp_emit` sends `Spec.Tcp.emit`;
* `TcpSim`, `TcpSimParse`: TCP against the Spec — `tcpInputW` is `Spec.Tcp.parse` then `Spec.Tcp.input`,
  `tickW` is `Spec.Tcp.tick`: from states that agree, the same transmissions and drops and states that agree
  again (`tcp_input_sim`, `tcp_tick_sim`); joined with the raw layer into statements about the calls
  (`tcp_input_refines`, `tcp_tick_refines`);
* `TcpRx`: TCP inside `ip_input` — a frame through `ip_input` is a frame through `Spec.ipInput`, every
  protocol (`frame_refines`);
* `NetStep`: one input item, TCP included — a received byte through `slip_rx` (`slip_rx_step`) and a tick
  between frames (`tick_step`) keep the invariant `NetInv` between the stack's globals and the Spec's stack
  state, with the same transmissions and drops;
* `TcpBound`: the tick counters of the Spec's control block stay within their limits;
* `Main`: one call of `main` is one input item of the Spec (`main_step`); boot;
* `Driver`: `main` called again and again from the initial state never traps and transmits and drops
  what `Spec.step` does, input by input (`main_run_all`).

P3, the emitted C (M5.8) — `Ember.C.Sem` is the semantics of the C subset:

* `CSem`, `CFuel`, `CVoid`: facts about that semantics (more variables in scope change nothing; statements
  run as the beginning of a block; more fuel changes nothing; `(void)x;` changes nothing);
* `CTypes`, `CPlace`: values and their types, well-typed expressions, `evalE` yields a value of the type;
  a place as a variable and a path, `update` as a change along the path;
* `CArith`: the operators as functions on natural numbers;
* `CExpr`: **expressions** — what `C.expr` emits for a well-typed scalar expression runs, from related
  states, to the value `Lang.Sem.evalE` gives, or ends in `ember_trap` exactly when `evalE` has no value
  (`expr_ok`, `place_ok`); for every profile;
* `LangFrame`: what a statement of `Lang.Sem` leaves alone (a `for` counter the body does not write);
* `CRel`: the relation statements keep (locals position by position, globals, the world), and
  `Lang.Sem.assign` as `C.Sem.write` (`assign_sim`);
* `CStmt`, `CCall`, `CSim`: **statements** — what `C.stmt` emits does what `Lang.Sem.execS` does, every
  construct: declarations, assignments, `if`, both loops, `break`, `return`, effects, calls and where their
  results go (`stmt_ok`, `block_ok`);
* `CFn`: **functions** — a compiled function called with the values of its arguments (`fn_sim`);
* `CProgram`: **programs** — `C.compile`'s unit, the initial state, the entry function called again and
  again (`compile_unit`, `init_rel`, `iter_sim`);
* `CCheck`: a checker for what these theorems assume of a program, proved right (`progOkB_sound`);
* `CNet`: **the emitted C of the stack transmits and drops what the Spec does** (`stack_c`) — M5.6 and M5.8
  together; the checker accepts every build of the stack, for every profile.

By-reference parameters are outside M5.8 (the stack has none).

The Z80 back end (M7, begun) — `Ember.Z80.IR.Sem` is the semantics of its IR:

* `Z80Frame`: **the frame validator is right** (M7.2) — a layout `IR.validate` accepts keeps every
  function's frame apart from the globals and from the frame of every function it can reach through
  calls (`validate_sound`).

Every statement is about the definitions of `Ember.Spec` as they are;
`Ember/Proof/README.md` lists the theorems, the hypotheses they need and
what is not proven.  `lake build Ember.Proof` is the gate.
-/
