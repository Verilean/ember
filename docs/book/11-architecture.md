# 11 · Architecture

> This chapter has nothing to run. It is a map of the system.

The earlier chapters introduce the parts one at a time. This chapter
shows how they fit: which layer is the reference for which, what
connects the implementations, where the state of a running stack lives,
where an application plugs in, and which resources are fixed when the
program is built.

## The picture

```
                ┌──────────────────────────────────────────────┐
                │ Ember.Spec          reference stack (Lean)   │
                │   step : State → Input → State × List Event  │
                │ Ember.Spec.Srv      + App, n connections     │
                │   Http · Tls · Auth · (Crypto)               │
                └──────────────────────────────────────────────┘
                        ▲ refines (proved: SLIP echo build)
                        │ lockstep (tested: every build)
                ┌──────────────────────────────────────────────┐
                │ Ember.Lang          the language             │
                │   Syntax (AST) · Types (checker)             │
                │   Eval (interpreter) · Sem (total, proofs)   │
                │   Surface (`ember def`) · Profile            │
                │ Ember.Net           the stack, in Ember      │
                │   Main · Ip · Tcp · Eth · Srv · Http · Tls   │
                │   Auth · Ctl · Crypto/                       │
                └──────────────────────────────────────────────┘
                     │ C.compile                 │ IR.lower
                     ▼                           ▼
     ┌───────────────────────────┐   ┌──────────────────────────────┐
     │ Ember.C                   │   │ Ember.Z80 (own back end)     │
     │  Ast · Sem · Compile      │   │  IR · IRInterp · Frame       │
     │  Print · DropChecks       │   │  Codegen · Asm · Runtime     │
     └───────────────────────────┘   └──────────────────────────────┘
          │ C text (trusted printer)          │ bytes (.ihx)
          ▼                                   ▼
   gcc (host) │ riscv32 gcc │ SDCC      Ember.Z80.Machine (Lean model)
          │           │          │
  Tests/Ember/host  runtime/   runtime/z80
   harness.c        esp32c3    (on the same model)
                    (QEMU)

    every box above writes the same trace  ──►  Ember.Trace, ember-diff
```

Each arrow down produces something that runs on the host first. A
target adds only a runtime (start-up, drivers, interrupts). It never
adds protocol logic. This is principle 3 of
[`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md).

## The layers

| Layer | Modules | Its contract |
|---|---|---|
| Reference | [`Ember/Spec`](https://github.com/Verilean/ember/tree/main/Ember/Spec), [`Ember/Spec/Srv`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Srv), [`Ember/Spec/Crypto`](https://github.com/Verilean/ember/tree/main/Ember/Spec/Crypto) | pure Lean over `ByteArray`; deterministic (counters for the IP identification and the initial sequence number; time is the `tick` input) |
| Language | [`Ember/Lang`](https://github.com/Verilean/ember/tree/main/Ember/Lang) | a checked `Prog`; the interpreter `Eval` is the semantics; `Sem` gives the same semantics as total functions for the proofs (the two are compared by tests, not by a theorem) |
| Stack in Ember | [`Ember/Net`](https://github.com/Verilean/ember/tree/main/Ember/Net) | one Ember function per Spec function, with the same checks in the same order and the same drop reasons |
| C back end | [`Ember/C`](https://github.com/Verilean/ember/tree/main/Ember/C) | `Lang → C AST`, which has no undefined behaviour for any input; a small printer; a C semantics to prove the translation against |
| Z80 back end | [`Ember/Z80`](https://github.com/Verilean/ember/tree/main/Ember/Z80) | `Lang → IR → Z80 assembly → bytes`, all in Lean; static frames, no C compiler |
| Runtimes | [`runtime/common`](https://github.com/Verilean/ember/tree/main/runtime/common), [`runtime/esp32c3`](https://github.com/Verilean/ember/tree/main/runtime/esp32c3), [`runtime/z80`](https://github.com/Verilean/ember/tree/main/runtime/z80), `Ember.Z80.Runtime` | hand-written and trusted: start-up, UART receive interrupt into an SPSC ring, timer tick, trace output |
| Trace | [`Ember/Trace`](https://github.com/Verilean/ember/tree/main/Ember/Trace), [`Ember/Util/Pretty.lean`](https://github.com/Verilean/ember/blob/main/Ember/Util/Pretty.lean) | one format, one packet decoder, one diff |

### The reference: one step function

[`Ember/Spec/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Stack.lean) defines the
whole stack as one step function:

```lean
def step (s : State) (i : Input) : State × List Event :=
  let ((), (s', es)) := (input i).run (s, #[])
  (s', es.toList)
```

`Input` is defined in
[`Ember/Trace/Event.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Event.lean). It is the only
way anything reaches the stack:

```lean
inductive Input where
  | rx (bytes : ByteArray)
  | tick
  deriving Inhabited
```

`Ember.Spec.Srv.step` has the same shape. Its state is generic in the
application ([`Ember/Spec/Srv/Stack.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Stack.lean)).

### The language: a program is data

An Ember program is a value of `Prog`, from
[`Ember/Lang/Syntax.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Syntax.lean):

```lean
structure Prog where
  structs : List StructDef := []
  globals : List Global := []
  fns     : List Fn
  /-- Called repeatedly by the driver while input remains. -/
  entry   : String := "main"
  /-- Names of the `trace.drop` reason codes, by index. -/
  dropReasons : List String := []
  /-- Names of the `trace.note` codes, by index. -/
  notes : List String := []
  deriving Inhabited, BEq, Repr
```

`ember def`, `ember global` and `ember struct`
([`Ember/Lang/Surface.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Surface.lean)) elaborate
to `Fn`, `Global` and `StructDef` values. A program is a Lean list of
them. So a program can be put together by ordinary Lean code. For
example, `Net.Srv.prog n app` builds a server for `n` connections, and
`Net.Http.app n site` turns a site into an application.

A program meets the outside world only through **effects**. Each effect
is an explicit statement:

```lean
def Effect.name : Effect → String
  | .inputNext => "input.next" | .outByte => "out.byte" | .outEnd => "out.end"
  | .drop => "trace.drop" | .note => "trace.note"
  | .mmioRead32 => "mmio.read32" | .mmioWrite32 => "mmio.write32" | .ringPop => "ring.pop"
  | .inputFrame => "input.frame"
```

In the interpreter, an effect reads from an input oracle and appends to
the trace. In C, an effect is a call into the runtime. Each runtime
implements the same interface,
[`runtime/common/ember_rt.h`](https://github.com/Verilean/ember/blob/main/runtime/common/ember_rt.h):

```c
/* Next input item: 0x00..0xFF a byte, 0x0100 a tick, 0xFFFF nothing. */
uint16_t ember_input_next(void);
uint16_t ember_ring_pop(void);
/* On a link that delivers whole frames: as ember_input_next, and 0x0200
 * after the last byte of each frame. */
uint16_t ember_input_frame(void);

/* Transmit: bytes of the current frame, then end of frame. */
void ember_out_byte(uint8_t b);
void ember_out_end(void);
```

The driver calls the entry function, `main`, again and again while
input remains. Each call of the stack's `main` takes one input item: a
byte, a tick, or nothing. This is `Ember/Net/Main.lean`, which
[chapter 3](03-spec.md) and [chapter 10](10-proofs.md) cover in detail.

### Two back ends

- **C** ([`Ember/C/Compile.lean`](https://github.com/Verilean/ember/blob/main/Ember/C/Compile.lean)):
  `compile (p : Prog) (o : Opts := {}) : Except String CUnit`, then
  `Print`. Every operation is done in
  an unsigned type at least as wide as the profile's `int`, with
  explicit casts. Shifts by the width or more, and division by zero,
  are guarded. An index the emitter cannot show to be in range gets a
  check that calls `ember_trap`. `DropChecks` removes those checks, and
  only for the SLIP build, where a proof shows that no run traps.
- **Z80** ([`Ember/Z80/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Z80/README.md)):

  ```
  Ember (checked) ──IR.lower──▶ IR ──Codegen.genProg──▶ Asm items ──Asm.assemble──▶ bytes
                                 │          ▲                 ▲
                           IRInterp.run   Frame.layout    Runtime.select
                          (its semantics) (+ validate)   (the routines used)
  ```

  Ember has no recursion, so every local has a fixed address (static
  frames, overlaid along the call graph). Ember has no pointers, so
  every array access is a known base plus an index. The image runs
  either with the test-harness runtime (`Runtime.harness`: effects are
  ports, no interrupts) or with a board runtime (`Runtime.board`: a
  receive interrupt with a ring and RTS, the ACIA, the trace on a debug
  port).

## The trace connects everything

Every implementation writes this format: the Spec (`Spec.run`), the
interpreter (`Prog.run`, `impl=interp`), the total semantics
(`Sem.run`), the host-compiled C (`Tests/Ember/host/harness.c`), the
ESP32-C3 image (on UART1) and the Z80 image (on the debug port `0xC0`).
The events are in [`Ember/Trace/Event.lean`](https://github.com/Verilean/ember/blob/main/Ember/Trace/Event.lean):

```lean
inductive Event where
  | rx   (bytes : ByteArray)
  | tx   (bytes : ByteArray)
  | tick
  | pkt  (text : String)
  | tcb  (text : String)
  | drop (reason : String)
  | note (text : String)
  deriving Inhabited
```

```lean
def Event.isObservable : Event → Bool
  | .rx _ | .tx _ | .tick => true
  | _ => false
```

- `rx`, `tx` and `tick` are **observable**. Two implementations agree
  when these lines agree.
- `pkt`, `tcb`, `drop` and `note` are **diagnostic**. They explain a
  divergence. `drop` reasons are compared too (`ember-diff --drops`),
  because the Ember stack numbers its drop reasons in the Spec's order.
- The first column is the step number: the index of the input being
  consumed. It is not a time, so traces from a fast and a slow
  implementation line up.

The same trace file is both input and expected output. A fixture's
`rx`/`tick` lines are the inputs, and its other lines are what the Spec
produced. Every implementation is fed those inputs and must reproduce
the observable lines. The trace is the only interface between the Lean
side, the C harness, QEMU and the Z80 model. The tools that compare
traces (`ember-diff`, `ember-lockstep`, `esp32.py corpus`,
`ember-z80 replay`) are covered in [chapter 4](04-testing.md).

## Where state lives

No implementation allocates memory. The state of a running stack is
the stack's **globals**, and each global has a fixed size.

### The echo stack (`Net.prog`, SLIP)

From [`Ember/Net/README.md`](https://github.com/Verilean/ember/blob/main/Ember/Net/README.md), "Data layout":

| Global | Type | Role |
|---|---|---|
| `buf` | `[u8; 296]` | the one packet buffer: a SLIP frame is decoded into it, and the reply is built over it |
| `pend` | `[u8; 256]` | the echo application's bytes (sent and unacknowledged, then unsent) |
| `t` | `Tcb` | the one connection |
| `sg` | `Seg` | the segment being processed |
| `len`, `esc`, `over` | `u16`, `bool`, `bool` | the SLIP receiver |
| `iss`, `ip_id` | `u32`, `u16` | the ISN and IP identification counters |
| `booted` | `bool` | `tcb_reset` on the first call |

There is one buffer for receiving and sending. An ICMP reply changes
one byte in place and updates the checksum incrementally. The stack
keeps no retransmission buffer: on a timeout, `rexmit` generates the
unacknowledged bytes again from the application's buffer, as uIP does.

### The server (`Net.Srv.prog n app`): connection slots

Ember has no arrays of records. So the server keeps each TCB field as
an array with one slot per connection, `c_<field> : [_; n]`. It copies
the connection being worked on into the record `t` (`tcb_load`) and
writes it back afterwards (`tcb_save`). Its number is in `cur`. From
[`Ember/Net/Srv.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Srv.lean):

```lean
/-- The arrays that hold the connections' TCBs. -/
def connGlobals (n : Nat) : List Global :=
  Tcb.fields.map fun (f, ty) => { name := "c_" ++ f, ty := .arr ty n }
```

The application's per-connection state follows the same pattern. Each
array is indexed by `cur`. Echo keeps `e_len[cur]` and a slice of
`pend`. HTTP keeps `h_req` (`REQ_MAX` bytes per connection), `h_kind`,
`h_pos` and a few more. TLS keeps a record buffer `t_inb`, an output
buffer `t_out`, a SHA-256 transcript context, keys and sequence
numbers. State that **all** connections share is a plain global: the
crypto's registers and buffers (one connection is worked on at a time),
and, for a site with control routes, `ctl_last`, `ctl_hash` and the time.

In the reference, the same split is explicit in `Spec.Srv.State`: an
array `conns` of TCBs, each with its application state `A.σ`, and one
shared value `g : A.G`.

### Constants

What the site serves is fixed when the program is built. HTTP puts
every response header and body into one constant array `h_rom`, with
tables of offsets. A segment's bytes are computed from those tables by
offset, so nothing of a response is copied into RAM, and a
retransmission computes the bytes again. The one response built in RAM
is a control request's answer `200 ok N` (`h_dyn`). TLS keeps its
certificates, the keys and the crypto's tables in the image.

## The application boundary

The TCP of the server knows nothing about HTTP. An application is a
record of functions, from
[`Ember/Spec/Srv/Tcp.lean`](https://github.com/Verilean/ember/blob/main/Ember/Spec/Srv/Tcp.lean):

```lean
/-- An application on one listening port; `σ` is its state per connection. -/
structure App where
  σ : Type
  port : UInt16
  /-- The state of a connection that has just been opened. -/
  init : σ
  /-- The receive window, given `cap = min ourMss peerMss`. -/
  room : σ → Nat → Nat
  /-- In-order data in ESTABLISHED, already cut to `room`. -/
  recv : σ → ByteArray → σ
  /-- Bytes of the outgoing stream from `snd.una` on (sent or not). -/
  avail : σ → Nat
  /-- `bytes s off n`: bytes `[off, off + n)` of the stream from `snd.una`. -/
  bytes : σ → Nat → Nat → ByteArray
  /-- The first `n` bytes from `snd.una` were acknowledged. -/
  acked : σ → Nat → σ
  /-- The application is done: FIN once everything it has is sent. -/
  close : σ → Bool
```

The record has more fields: `idleClose`, and, with defaults,
`reuseTimeWait`, the shared state `G`/`ginit`/`recvG`, and
`udpPort`/`udpG`. In Ember the same boundary is a set of functions with
fixed names, which work on the connection `cur`. This table is quoted
from the doc comment of [`Ember/Net/Srv.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Srv.lean):

| function | `Ember.Spec.Srv.App` |
|---|---|
| `app_reset()` | `init` (the connection is new, or closed) |
| `app_room(cap : u16) : u16` | `room` |
| `app_recv(off : u16, n : u16)` | `recv`: the data is `buf[off, off + n)` |
| `app_avail() : u16` | `avail` |
| `app_fill(from : u16, n : u16, dst : u16)` | `bytes`: write bytes `[from, from + n)` of the stream from `snd.una` to `buf[dst, …)` |
| `app_acked(n : u16)` | `acked` |
| `app_close() : bool` | `close` |

The constants `APP_PORT`, `APP_IDLE_CLOSE` and `APP_REUSE_TW` go with
these functions. An application in Ember is its globals and its
functions:

```lean
/-- An application: its globals and its functions. -/
structure App where
  globals : List Global
  fns : List Fn
```

### How HTTP, HTTPS, auth and control sit on it

```
                        Spec (reference)                 Ember
  echo              Spec.Srv.echo                 Net.Srv.echo n mss
  HTTP/1.1          Spec.Srv.Http.app site        Net.Http.app n site
    + tokens          Http.Site.auth, Route.scope   Net.Auth (replaces h_feed)
    + control         Http.appCtl (G := Ctl,        Net.Ctl  (+ time_in on UDP 37)
                        udpPort := timePort)
  TLS 1.3           Spec.Srv.Tls.app site         Net.Tls.app n site
                      (HTTP inside the records)     (Net.Http's parser and tables inside)
                    ───────────────────────────   ───────────────────────────────
  TCP, IP, SLIP     Spec.Srv.Stack                Net.Srv.prog n app
```

- **HTTP** is an application:
  `def prog (n : Nat) (site : Spec.Srv.Http.Site) : Prog := Net.Srv.prog n (app n site)`
  ([`Ember/Net/Http.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Http.lean)). A `Site` is a
  list of routes plus limits: `reqMax`, `hdrMax`, `port`, `bodyMax`.
- **Protected routes** are routes with a `scope`. For a site that has
  them, `Net.Http.feedFns` uses `Net.Auth` in place of `h_feed`, the
  function that reads the header. `Net.Auth` checks the bearer token
  while the header arrives ([chapter 8](08-auth.md)).
- **Control** (`POST` routes, kept connections) uses the shared state
  `G`. Datagrams on UDP port 37 set the time: `Net.Ctl`'s `udp_input`
  takes the place of the stack's `udp_input` ([chapter 9](09-control.md)).
- **TLS** wraps HTTP, not TCP:
  `def prog (n : Nat) (site : Spec.Srv.Tls.Site) : Prog := Net.Srv.prog n (app n site)`
  ([`Ember/Net/Tls.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Tls.lean)). Its `app` uses
  `Net.Http`'s request parser and response tables inside the records
  ([chapter 7](07-https.md)).

`Net.prog`, the echo stack, is not built from `Net.Srv`. The proofs are
about `Net.prog`, and it stays as it was. `Net.Srv` reuses its IP,
SLIP and TCP functions by name, and replaces only the functions where
the echo buffer or the single connection was.

[`Ember/Tools/Emit.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/Emit.lean) names the
programs that the tools and images use: `net`, `sliploop`, `net-eth`
and `net-eth-dhcp` (golden C), plus `http`, `https`, `crypto`,
`https-ctl`, `https-ctl-test` and `https-auth-test`, each on two
connections where it has connections.

## Resources: fixed, bounded, not fixed

This section summarizes [`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md)
§2.7, for one build of the stack:

| Resource | Status | Detail |
|---|---|---|
| Memory | **fixed** | No heap. Every global, parameter, local and temporary has a fixed address. The static RAM of an image is a number the build prints: 1061 bytes for the SLIP build on the Z80 board runtime (273 of runtime, 623 of globals, 165 of frames and temporaries). The build refuses an image that does not fit |
| Stack depth | **bounded** | The call graph has no cycle, and a call pushes only its return address. `Ember.Z80.StackBound` gives 24 bytes for the SLIP build. That number comes from an analysis, not a theorem, and only for images of the shape the analysis models |
| Time per call | **bounded, not fixed** | Loops are bounded, so each call of `main` ends. The proofs give a fuel bound of the Ember semantics (`n + 4716` steps for the SLIP build). That is not a bound in T-states, and nothing is proved about response times |
| Capacities | **build constants** | MTU, number of connections, one segment of echoed data in flight, request and record buffers, an ARP cache of four entries. Changing one means building again, and checking the proofs again for the proved build |

Running out of a resource is a protocol matter, not a memory matter.
Each case has its behaviour written in the Spec and replayed from the
corpus:

- A frame longer than the buffer is dropped (`oversize-frame`).
- A segment for a connection the stack has no slot for is answered with
  a reset (`unsupported-second-connection`).
- The echo application advertises only the window it has room for.
- On the board, the receive ring raises RTS when it is nearly full.
- Connections are given back on close, on reset, after `maxRetries`
  retransmissions and after `idleTicks` without traffic, all driven by
  `tick`.

## Trusted base

The trusted base is everything the proofs and tests do not cover. From
[`docs/Ember-design.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-design.md) §4 and
[`docs/Ember-plan.md`](https://github.com/Verilean/ember/blob/main/docs/Ember-plan.md) M7:

- Lean's kernel.
- The C printer (`Ember/C/Print.lean`, kept small: every compound
  expression is parenthesised).
- The C compiler.
- The assumption that `Ember.C.Sem` agrees with the compiler's reading
  of the printed C.
- The hand-written runtimes.
- On the Z80 path, the Lean model of the machine.

What is proved on top of that, and for which build, is in
[chapter 1](01-overview.md#what-is-proved-and-what-is-only-tested) and
[chapter 10](10-proofs.md).
