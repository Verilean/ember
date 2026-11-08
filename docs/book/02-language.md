# 2 · The Ember language

Ember is a small imperative language hosted in Lean. You write it with
`ember def`, `ember global` and friends inside an ordinary `.lean` file;
each command elaborates to a Lean constant that holds the program's
abstract syntax. A program is then a plain Lean value, a `Prog`, and
three things consume it:

```
ember def ...  ──elab──▶  Fn / Global / StructDef  ──▶  Prog
                                                         │
                                  Prog.check (type checker, elaborates)
                                                         │
                   ┌─────────────────────┬───────────────┴──────────────┐
                   ▼                     ▼                              ▼
         interpreter (Eval)        Lang → C (Ember.C)           Lang → IR → Z80
         = the semantics           chapter 5                    chapter 5
```

The language is deliberately small (design §2.2): every operation is
total and defined, there are no pointers, no recursion, and every loop
has a bound. That is what makes it possible to emit C with no undefined
behaviour ([chapter 5](05-targets.md)) and to prove things about the
programs ([chapter 10](10-proofs.md)).

Every snippet in this chapter is copied from the tree, with its path.
Nothing is pseudocode.

| File | What |
|---|---|
| [`Ember/Lang/Syntax.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Syntax.lean) | the AST: `Ty`, `Expr`, `Stmt`, `Effect`, `Fn`, `Global`, `StructDef`, `Prog` |
| [`Ember/Lang/Surface.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Surface.lean) | the `ember def` / `ember global` / … syntax and its translation to the AST |
| [`Ember/Lang/Types.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Types.lean) | the type checker, `Prog.check` |
| [`Ember/Lang/Eval.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Eval.lean) | the interpreter, which *is* the semantics |
| [`Ember/Lang/Sem.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Sem.lean) | the same semantics as total functions, for proofs |
| [`Ember/Lang/Checked.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Checked.lean) | `checked_fn%`: a checked function as a term, for proofs |
| [`Ember/Lang/Profile.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Profile.lean) | target profiles (`host64`, `rv32`, `sdcc-z80`) |
| [`Ember/Lang/Examples.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Examples.lean) | the example programs (checksum, SLIP, ring, CRC-32, every construct) |
| [`Ember/Lang/Gen.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Gen.lean) | random programs, for the fuzzers |

## A first look — the Internet checksum

From [`Ember/Net/Buffer.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Buffer.lean), the
checksum the whole stack uses:

```lean
/-- One's-complement addition. -/
ember def add16 (a : u16) (b : u16) : u16 := do
  let s : u16 := a + b
  if s < a then
    return s + 1
  return s

/-- One's-complement sum of `buf[o, o+n)`, starting from `init`. -/
ember def csum (o : u16) (n : u16) (init : u16) : u16 := do
  let mut s : u16 := init
  for i in [0, n / 2) do
    let w : u16 ← get16(o + 2 * i)
    s ← add16(s, w)
  if (n &&& 1) == 1 then
    s ← add16(s, (buf[o + n - 1] : u16) <<< 8)
  return s
```

Line by line:

- `ember def csum (o : u16) (n : u16) (init : u16) : u16 := do` — a
  function with three `u16` parameters, passed by value, and a `u16`
  result. A doc comment in front is kept on the Lean constant `csum`
  (a `Fn`).
- `let mut s : u16 := init` — a local. Its type is always written out.
  (`mut` is accepted and ignored: every local can be assigned. The stack
  writes `mut` on the ones it does assign.)
- `for i in [0, n / 2) do` — a counted loop over the half-open range.
  The bounds are evaluated once; `i` is read-only. No width is written
  on `i`, so the checker infers it from the bounds: `n / 2` is a `u16`,
  so `i` is a `u16`, and the literal `0` becomes a `u16` too.
- `let w : u16 ← get16(o + 2 * i)` — declare `w` and store the result
  of a call in it. Calls are statements, never expressions. `get16` reads
  two bytes of the global `buf` big-endian (same file).
- `s ← add16(s, w)` — call `add16` and store its result in an existing
  place.
- `if (n &&& 1) == 1 then` — bitwise *and* is `&&&`, as in Lean; the
  literal `1` takes the width of `n`.
- `(buf[o + n - 1] : u16) <<< 8` — index the global array `buf`
  (`[u8; 296]`), zero-extend the byte to `u16`, shift. The index is
  checked at run time: out of range is an error in the semantics (and a
  trap in the emitted C).
- `return s` — the checker refuses a function with a result unless every
  path returns one.

`buf` is declared in [`Ember/Net/Layout.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Layout.lean):

```lean
/-- The packet buffer and the SLIP receiver's state. -/
ember global buf : [u8; 296]
ember global len : u16
ember global esc : bool
ember global over : bool
```

## Types

| Surface | AST (`Ty`) | |
|---|---|---|
| `u8 u16 u32 u64` | `.int .w8` … `.int .w64` | unsigned, arithmetic modulo 2^w |
| `bool` | `.bool` | |
| `[τ; n]` | `.arr τ n` | fixed size, `n > 0`, elements scalars only |
| a record name | `.record "Tcb"` | declared with `ember struct` |

There are no pointers and no signed types. Records hold scalars and
arrays of scalars; records do not nest, and there are no arrays of
records (`Ember/Net/README.md`: the multi-connection server keeps its
control blocks as arrays `c_<field> : [_; n]` for that reason).

A record, from [`Ember/Net/Layout.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Layout.lean):

```lean
/-- The segment being processed (parsed from `buf` by `tcp_input`). -/
ember struct Seg where
  src : u32
  sport : u16
  dport : u16
  seq : u32
  ack : u32
  flags : u8
  has_mss : bool
  mss : u16
  doff : u16
  dlen : u16

ember global sg : Seg
```

`a.b` is field `b` of record `a`; `a[i].b` is also accepted by the
grammar.

## Globals and constants

```lean
ember global t : Tcb
ember global pend : [u8; 256]
ember global iss : u32 := 65536
ember global ip_id : u16 := 1
```

(`Ember/Net/Layout.lean`.) A global is a `Global` value:

```lean
structure Global where
  name  : String
  ty    : Ty
  /-- Initial value: one number for a scalar, one per element for an
  array (missing elements are 0); records start zeroed. -/
  init  : List Nat := []
  /-- Constants cannot be assigned; the emitter makes them `static const`. -/
  const : Bool := false
```

(`Ember/Lang/Syntax.lean`.) The forms:

| Command | Meaning |
|---|---|
| `ember global x : τ` | zero-initialised |
| `ember global x : u32 := 65536` | scalar with an initial value |
| `ember global tab : [u16; 4] := [10, 20, 30, 40]` | array; missing elements are 0 |
| `ember const MTU : u16 := 296` | read-only scalar (`const := true`) |
| `ember const NAME : [u8; n] := [ … ]` | read-only array |

The checker refuses initialisers that do not fit their type, and any
initialiser on a record global (records start zeroed).

## Functions

```
ember def NAME (p₁ : τ₁) (p₂ p₃ : τ₂) (r : ref [u8; 4]) : τ := do
  statements
```

- Several parameters of one type can share a binder: `(acc w : u16)`
  (`Ember/Lang/Examples.lean`).
- Scalars are passed by value; arrays and records **only** by reference,
  marked `ref`. The checker refuses a scalar `ref` and a non-scalar
  without `ref`.
- The result type is optional (no result) and must be a scalar.

From the example that uses every construct (`Ember/Lang/Examples.lean`,
namespace `Constructs`):

```lean
/-- Fill a pair through references. -/
ember def fill (q : ref Pair) (arr : ref [u16; 4]) (v : u8) := do
  q.lo := v
  q.hi := (arr[3] : u32) * 1000
  for i in [0, 4) do
    q.bytes[i] := (i : u8) + v

ember def sum4 (arr : ref [u16; 4]) : u16 := do
  let mut s : u16 := 0
  for i : u8 in [0, 4) do
    s := s + arr[i]
  return s
```

Two references of one call must not overlap (`two_refs(arr, arr)` is
refused), and a global must not be passed by reference to a function
that also uses it by name, directly or through its callees. So there is
no aliasing to reason about.

## Expressions

Expressions have no side effects and are total. Precedences follow Lean
(`<<<` binds tighter than `+`).

| Operators | Operands | Notes |
|---|---|---|
| `+ - * / %` | same integer width | modulo 2^w; `/` and `%` by 0 give 0 |
| `&&& \|\|\| ^^^` | same integer width | bitwise |
| `<<< >>>` | integer, shift amount of any width | a shift by ≥ w gives 0 |
| `~~~ -` | integer | complement; two's-complement negation mod 2^w |
| `== != < <= > >=` | same type | on `bool` only `==` and `!=` |
| `&& \|\| !` | `bool` | |
| `if c then a else b` | `c : bool`, `a`, `b` scalars of one type | |
| `(e : u16)` | integer or `bool` | zero-extend or truncate; `bool` gives 0/1 |
| `a[i]`, `a.f`, `a[i].f` | | array read (checked), field |

Two rules that matter in practice:

- **Literals take their width from context.** In `x + 1` the `1` gets
  the width of `x`. Where nothing fixes it, write the width:
  `(1 : u16)`. Inside a cast, literals that cannot be inferred otherwise
  take the cast's width: `(if b > LIMIT then 1 else 2 : u8)`.
- **Every operand is evaluated**, including both sides of `&&`, `||`
  and both arms of `if … then … else`. So an out-of-range array read
  anywhere in an expression is an error, even in an arm that is not
  chosen.

## Statements

| Statement | AST (`Stmt`) |
|---|---|
| `let x : τ := e`, `let x : τ` | `.decl` (arrays and records start zeroed; scalars too when no initialiser) |
| `let x : τ ← f(args)` | `.decl` followed by a call storing into `x` |
| `place := e` | `.assign` (a variable, field or element; scalars only) |
| `f(args)` | `.call` without a result, or an effect |
| `place ← f(args)` | `.call` / `.eff` storing the result |
| `if c then … else …` | `.ite` (the `else` part is optional) |
| `for i in [lo, hi) do …`, `for i : u16 in [lo, hi) do …` | `.forRange` |
| `loop (max := N) do …` | `.loop`: at most `N` iterations |
| `break` | `.brk`, inside a loop only |
| `return`, `return e` | `.ret` |

Statements of a block are one per line (an optional `;` may end one),
indented under their header.
Every statement carries its span (file, line, column) in a `Stmt.at`
wrapper; the checker's and the interpreter's errors point there, and so
do the `#line` directives of the emitted C.

### Bounded loops

There is no `while`. A `for` runs over a half-open range whose bounds are
computed once; a `loop` runs at most `max` times and is left with
`break`. From the DHCP option parser
([`Ember/Net/Eth.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Eth.lean)):

```lean
  loop (max := 600) do
    if i >= ms then
      break
    let c : u8 := buf[28 + i]
    if c == 255 then
      break
```

and a counter with an explicit width, from
[`Ember/Net/Crypto/X25519.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Crypto/X25519.lean):

```lean
ember def fe_copy (o : u16) (a : u16) := do
  for i : u16 in [0, 16) do
    fe[o * 16 + i] := fe[a * 16 + i]
```

With both bounds literals and no width written, the counter gets the
narrowest width that holds them; otherwise the width of the bounds. The
checker refuses `loop (max := 0)`.

### Calls, effects and `←`

A call is a statement. If the name is one of the effects below, it is an
effect (`Stmt.eff`); otherwise it is a call of an Ember function
(`Stmt.call`). The call graph must be acyclic, so the stack depth is
static.

Effects are everything a program does besides computing
(`Effect.sig`, `Ember/Lang/Syntax.lean`):

| Effect | Arguments → result | |
|---|---|---|
| `input.next()` | → `u16` | next input item: a byte `0x00..0xFF`, `0x0100` a tick, `0xFFFF` nothing left |
| `input.frame()` | → `u16` | as `input.next`, and `0x0200` after the last byte of each frame (Ethernet) |
| `ring.pop()` | → `u16` | the runtime's receive ring |
| `out.byte(b)` | `u8` | append a byte to the frame being sent |
| `out.end()` | | the frame is complete |
| `trace.drop(code)` | `u8` | diagnostic: `drop reason=<name>` (`Prog.dropReasons`) |
| `trace.note(code, v)` | `u8`, `u32` | diagnostic: `note <name> <value>` (`Prog.notes`) |
| `mmio.read32(addr)` | `u32` → `u32` | |
| `mmio.write32(addr, v)` | `u32`, `u32` | |

The SLIP loopback in
[`Ember/Net/Loop.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Loop.lean) shows an entry
function reading one item per call:

```lean
ember def main := do
  let k : u16 ← input.next()
  if k < 0x0100 then
    loop_rx((k : u8))
```

## Programs

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
```

(`Ember/Lang/Syntax.lean`.) The commands only define constants; a
program lists them. The loopback, from `Ember/Net/Loop.lean`:

```lean
/-- The loopback as a program: the SLIP half of the stack and nothing else. -/
def prog : Prog :=
  { globals := [Net.MTU, Net.D_OVERSIZE, Net.buf, Net.len, Net.esc, Net.over],
    fns := [Net.slip_send, Net.slip_store, loop_rx, main],
    dropReasons := ["oversize-frame"] }
```

and the whole stack, from [`Ember/Net/Main.lean`](https://github.com/Verilean/ember/blob/main/Ember/Net/Main.lean):

```lean
/-- The whole stack as one Ember program. -/
def prog : Prog :=
  { structs := structs, globals := constants ++ state ++ [booted, tick_due],
    fns := fns ++ ipFns ++ tcpFns ++ [main], dropReasons := dropReasons, notes := notes }
```

The entry function takes no arguments and returns nothing. A driver
calls it while input remains — the interpreter's `runMachine`, the host
C harness and the board runtimes all run the same loop
([chapter 5](05-targets.md)).

Because a program is a Lean value, it can be built by Lean code: the
HTTP and HTTPS servers are functions of the number of connections and of
the site (`Net.Http.prog n site`, `Net.Tls.prog n site`;
[chapter 6](06-http-app.md), [chapter 7](07-https.md)).

## The type checker — `Prog.check`

```lean
/-- Type-check and elaborate a program. -/
def Prog.check (p : Prog) : Except Err Prog := Check.check p
```

(`Ember/Lang/Types.lean`.) It validates a program and returns it
**elaborated**: every literal carries its width and every `for` counter
its width, so the interpreter and the emitters never guess. An error
carries a span and the function: `Err.toString` prints
`file:line:col: in fn f: message`.

What it refuses — each rule has a negative test in
[`Tests/Ember/LangPrograms.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/LangPrograms.lean)
(`Bad.cases`), run by `Tests/Ember/LangTests.lean`:

| Rule | Refused program (from `Bad`) | Error contains |
|---|---|---|
| operand widths agree | `let c : u16 := a + b` with `a : u8` | `operands of + have different types (u8 and u16)` |
| literals fit | `let a : u8 := 256` | `literal 256 does not fit u8` |
| literal indices in bounds | `arr[4] := 1` on `[u8; 4]` | `index 4 out of bounds [0, 4)` |
| literal widths inferable | `(3 < 4 : u8)` — two bare literals compared | `cannot infer the width` |
| names unique in a function | `let a` twice | `declared twice` |
| no shadowing of globals | `let g : u8 := 1` with a global `g` | `shadows a global` |
| constants read-only | `C := 2` | `'C' is read-only` |
| `for` counters read-only | `i := 3` in a `for i` | `'i' is read-only` |
| only scalars assigned | `b := arr` | `must be a scalar` |
| references disjoint | `two_refs(arr, arr)` | `overlap` |
| no global by reference to its user | `uses_g(arr)` where `uses_g` writes `arr` | `also uses it by name` |
| no recursion | `rec_a` ↔ `rec_b` | `recursion` |
| every path returns | `if x > 1 then return 1` alone | `not every path returns` |
| `break` in loops only | `break` at top level | `break outside a loop` |
| `bool` is not arithmetic | `a + a` on `bool` | `must be an integer` |
| arity | `two_refs(arr)` | `takes 2 argument(s)` |
| references are places | `two_refs(arr, (g : u8))` | `by reference` |
| names resolve | `out.byte(nope)` | `unknown variable 'nope'` |

Whole-program checks besides: function, global and record names unique;
the entry function exists, takes nothing and returns nothing.

## The interpreter is the semantics

[`Ember/Lang/Eval.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Eval.lean) is the meaning of an
Ember program, and the oracle every other implementation is compared
with (the emitted C, the Z80 images, the reference stack — see
[chapter 4](04-testing.md)):

- arithmetic is modulo 2^w; a shift by ≥ w is 0; `/` and `%` by 0 are 0;
- every operand is evaluated, so an out-of-range array read anywhere is
  an error, reported with the function and the statement path
  (`fn=f at stmt 3.2.1`) and the span;
- statements consume fuel; running out is an error;
- effects are served by a `World`: the input oracle (the inputs of a
  trace, byte by byte, ticks as `0x0100`, `0xFFFF` at the end) and the
  event log (`tx` frames, `drop`, `note`).

The driver calls the entry function while input remains, and stops after
three calls in a row that consume nothing:

```lean
/-- Check and run a program on the inputs of a trace. -/
def Prog.run (p : Prog) (inputs : Array Input) (header : Header := { impl := "interp" })
    (fuel : Nat := 1000000) : Except Err Result := do
  let p ← p.check
  return runMachine (Machine.init p inputs) header fuel
```

A run that stops on an error keeps the events before it; the error
becomes the trace's last line, a `note trap (…)`.

`Ember/Lang/Sem.lean` gives the same semantics as total functions
(structural recursion on expressions, fuel on statements), which is what
the proofs unfold. The two are not proved equal; they are run against
each other on random programs, the examples and the stack
(`Tests/Ember/LangTests.lean`).

### Running a program in a test

Two styles occur in the tests.

**A whole program on a trace's inputs** — `Prog.run`, from
[`Tests/Ember/LangTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/LangTests.lean):

```lean
def constructsInputs : Array Input := #[.rx (Bytes.ofList [2]), .tick, .rx (Bytes.ofList [9])]

def constructsExpected : List String :=
  ["0      rx   02",
   "0      tx   fc 06 00 00 00 20 fd fe 20 02 00 01 02 9c 05 64 04 00 04",
   "1      tick", "1      note tick 42", "2      rx   09"]

def constructsRun : Option Result := (Examples.Constructs.prog.run constructsInputs).toOption
```

The third input, byte 9, makes `out.byte(p.bytes[b])` read out of range;
the test checks that the error names `main`, a statement path and
`index 9 out of bounds [0, 4)`.

**One function, with globals set up** — `Machine.init`, `setGlobal`
and `callFn`, from
[`Tests/Ember/NetTests.lean`](https://github.com/Verilean/ember/blob/main/Tests/Ember/NetTests.lean), which
checks `csum` against the reference stack's checksum on random buffers:

```lean
def machine : Machine := Machine.init NetCheck.netProg #[]

def withBuf (b : ByteArray) : Machine :=
  machine.setGlobal "buf" (.arr ((Array.range 296).map fun i => .int .w8 (Bytes.get b i).toUInt64))

def call (m : Machine) (f : String) (args : List Val) : Option Val :=
  match m.callFn f args with
  | .ok (v, _) => v
  | .error _ => none
```

```lean
    if call m "csum" [v16 o, v16 len, v16 init] != some (v16 (Spec.Checksum.sum b o len init.toUInt16).toNat) then
      bad := bad + 1
```

`NetCheck.netProg` is the stack *checked* once
([`Ember/Tools/NetCheck.lean`](https://github.com/Verilean/ember/blob/main/Ember/Tools/NetCheck.lean)):

```lean
def checked (p : Prog) : Prog := match p.check with
  | .ok q => q
  | .error _ => p

/-- The Net program (SLIP), checked once. -/
def netProg : Prog := checked Net.prog
```

`Prog.run` checks for you; `Machine.init` does not — see the pitfalls
below.

## Profiles

A profile describes a C target: the width of C's `int` and the native
register width ([`Ember/Lang/Profile.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Profile.lean)):

```lean
def Profile.host64 : Profile := { name := "host64", intBits := 32, regBits := 64 }
def Profile.rv32 : Profile := { name := "rv32", intBits := 32, regBits := 32 }
def Profile.sdccZ80 : Profile := { name := "sdcc-z80", intBits := 16, regBits := 8 }
```

The language and its semantics do not depend on the profile; only the
emitted C does: every operation is computed in an unsigned type at least
as wide as `int` and truncated, so C's promotion to *signed* `int` can
never overflow. [Chapter 5](05-targets.md) shows the C.

## For proofs: `checked_fn%`

`Prog.check` is `partial`, so the Lean kernel cannot run it. A proof
that needs the checked AST of a function writes `checked_fn% P, "f"`,
which runs the checker while elaborating and inserts the result as a
literal term ([`Ember/Lang/Checked.lean`](https://github.com/Verilean/ember/blob/main/Ember/Lang/Checked.lean)).
`Ember/Proof` re-checks the equality with `#guard` next to every use.
See [chapter 10](10-proofs.md).

## Pitfalls

- **An `else` binds to the innermost open `if`, whatever its
  indentation.** The statement form is
  `"if " ember_expr " then " ember_seq (" else " ember_seq)?`
  (`Ember/Lang/Surface.lean`) with no column check on `else`, so in

  ```
  if a then
    if b then
      x := 1
  else
    y := 2
  ```

  the `else` belongs to `if b`. When an inner `if` has no `else` of its
  own, put it after the outer `else`'s branch or restructure. The stack
  writes a chain as an `if` nested in the `else` branch, one level
  deeper each time (`Ember/Net/Loop.lean`):

  ```lean
  if esc then
    if c == 0xDC then
      slip_store(0xC0)
    else
      if c == 0xDD then
        slip_store(0xDB)
      else
        slip_store(c)
    return
  ```

- **A local may not be declared twice in one function** — not even in
  two different branches or blocks. The checker remembers every name
  declared in the function so far (`St.seen`) and never forgets one at
  the end of a block, so it refuses the second with
  `'x' is declared twice in this function`. Parameters and `for`
  counters count as declarations: two loops in one function need two
  counter names.
- **A local may not have the name of any global**: `local 'g' shadows a
  global`. This covers constants, so a local cannot be called `MTU`
  in a program that has `ember const MTU`.
- **Record fields take `--` comments, not doc comments.** The field list
  of `ember struct` is `(ppLine ident " : " ember_ty)*`, with no place
  for a `/-- … -/`; a doc comment before a field is a parse error. A
  `--` line comment is ordinary whitespace to Lean and is fine. A doc
  comment before `ember struct` itself is accepted.
- **Check a program before the interpreter runs it.** The surface syntax
  leaves literal widths open (`Expr.lit v none`); only `Prog.check`
  fills them in. `Prog.run` checks first, but `Machine.init p` with
  `callFn`/`step` runs `p` as given, and evaluating an unfilled literal
  fails with `untyped literal (program not checked)`. Run
  `Machine.init` on the result of `p.check` — as `NetCheck.netProg`
  does.
