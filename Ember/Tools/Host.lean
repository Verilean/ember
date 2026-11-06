import Ember.Spec.Stack
import Ember.Spec.Srv.Http
import Ember.Spec.Srv.Tls
import Ember.Spec.Srv.Stack
import Ember.Trace.Text
import Std.Sync.Mutex

/-!
# `ember-host` — the reference stack on stdin/stdout (M1.10)

Reads link bytes from stdin and writes the stack's output to stdout, as
SLIP (default) or, with `--eth`, as Ethernet frames each preceded by a
2-byte big-endian length.  `--mtu N` sets the packet buffer size
(default 296 on SLIP, 576 on Ethernet).  SLIP input is handed to the stack one frame
(up to its closing `END`) per step; the stack itself is a byte-at-a-time
state machine, so the chunking only shapes the trace.  `--tick-ms N` feeds a `tick` every N ms of wall time (default
500; 0 disables).  `--trace FILE` writes the §3.1 trace.  `--replay
TRACE` instead runs the inputs of a trace file and prints the resulting
trace on stdout (no wall clock involved).

`--http` runs `Ember.Spec.Srv` with the HTTP application and its demo
site (`Spec.Srv.Http.demo`, port 80) instead of the echo stack (plan
M8.2); `--https` the TLS 1.3 server of plan M8.6 with the same site on
port 443 (`Spec.Srv.Tls.demo`, a self-signed Ed25519 demo certificate);
`--conns N` gives either N connections (default 1).

`--auth` (plan M9.3) takes the demo sites with protected routes instead
(`Spec.Srv.Http.demoAuth`, `Spec.Srv.Tls.demoAuth`: tokens of the demo
identity provider `Spec.Srv.Auth.demoCfg`); `--now T` sets their time
(seconds since 1970; default `Auth.demoNow`, the time of the recorded
sessions).  `--token SCOPE` prints a token of the demo provider with that
scope, valid for an hour from that time, and exits.  `--ctl` (plan M9.5)
takes the demo sites with a control route (`POST /cmd`, `X-Ember-Seq`)
and kept connections instead (`Spec.Srv.Http.demoCtl`).
-/

namespace Ember.Tools.Host
open Ember Ember.Spec Ember.Trace

structure Opts where
  eth     : Bool := false
  dhcp    : Bool := false
  tickMs  : Nat := 500
  trace   : Option String := none
  replay  : Option String := none
  mtu     : Option Nat := none
  http    : Bool := false
  https   : Bool := false
  conns   : Nat := 1
  auth    : Bool := false
  ctl     : Bool := false
  now     : Nat := Srv.Auth.demoNow
  token   : Option String := none

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--eth" :: r, o => parseArgs r { o with eth := true }
  | "--dhcp" :: r, o => parseArgs r { o with dhcp := true }
  | "--http" :: r, o => parseArgs r { o with http := true }
  | "--https" :: r, o => parseArgs r { o with https := true }
  | "--auth" :: r, o => parseArgs r { o with auth := true }
  | "--ctl" :: r, o => parseArgs r { o with ctl := true }
  | "--now" :: n :: r, o => match n.toNat? with
    | some v => parseArgs r { o with now := v }
    | none => .error s!"bad --now {n}"
  | "--token" :: sc :: r, o => parseArgs r { o with token := some sc }
  | "--conns" :: n :: r, o => match n.toNat? with
    | some v => parseArgs r { o with conns := max 1 v }
    | none => .error s!"bad --conns {n}"
  | "--tick-ms" :: n :: r, o => match n.toNat? with
    | some v => parseArgs r { o with tickMs := v }
    | none => .error s!"bad --tick-ms {n}"
  | "--mtu" :: n :: r, o => match n.toNat? with
    | some v => parseArgs r { o with mtu := some v }
    | none => .error s!"bad --mtu {n}"
  | "--trace" :: f :: r, o => parseArgs r { o with trace := some f }
  | "--replay" :: f :: r, o => parseArgs r { o with replay := some f }
  | a :: _, _ => .error s!"unknown argument {a}"

def configOf (o : Opts) : Config :=
  { link := if o.eth then .eth else .slip, dhcp := o.dhcp, mtu := o.mtu.getD (if o.eth then mtuEth else mtu) }

/-- Read one length-prefixed frame (eth mode). -/
def readFrame (h : IO.FS.Stream) : IO (Option ByteArray) := do
  let hdr ← h.read 2
  if hdr.size < 2 then return none
  let n := (Bytes.get16 hdr 0).toNat
  let mut b := ByteArray.empty
  while b.size < n do
    let c ← h.read (n - b.size).toUSize
    if c.size == 0 then return none
    b := b ++ c
  return some b

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let cfg := configOf o
  if let some sc := o.token then
    IO.println (String.fromUTF8! (Srv.Auth.demoToken sc o.now))
    return 0
  if let some f := o.replay then
    let t ← Trace.readFile f
    let cfg := Config.ofHeader t.header
    IO.print (Spec.run cfg t.inputs).print
    return 0
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let traceH ← match o.trace with
    | some f => some <$> IO.FS.Handle.mk f .write
    | none => pure none
  if let some h := traceH then
    h.putStrLn (cfg.header).print
  let site := if o.ctl then { Srv.Http.demoCtl with now := some o.now }
    else if o.auth then { Srv.Http.demoAuth with now := some o.now } else Srv.Http.demo
  let app := Srv.Http.app site
  let st ← IO.mkRef (State.init cfg)
  let srv ← IO.mkRef (Srv.State.init app { toConfig := cfg, conns := o.conns })
  let tapp := Srv.Tls.app (if o.auth || o.ctl then { Srv.Tls.demoAuth with http := site } else Srv.Tls.demo)
  let tls ← IO.mkRef (Srv.State.init tapp { toConfig := cfg, conns := o.conns })
  let stepN ← IO.mkRef 0
  let lock ← Std.BaseMutex.new
  let doStep' (i : Input) : IO Unit := do
    let es ← if o.https then do
        let (s', es) := Srv.step (← tls.get) i
        tls.set s'
        pure es
      else if o.http then do
        let (s', es) := Srv.step (← srv.get) i
        srv.set s'
        pure es
      else do
        let (s', es) := step (← st.get) i
        st.set s'
        pure es
    let n ← stepN.modifyGet fun n => (n, n + 1)
    if let some h := traceH then
      let e0 : Event := match i with | .rx b => .rx b | .tick => .tick
      h.putStrLn (Line.print ⟨n, e0⟩)
      for e in es do h.putStrLn (Line.print ⟨n, e⟩)
      h.flush
    for b in outputs es do
      if o.eth then stdout.write (Bytes.ofList (Bytes.be16 (UInt16.ofNat b.size)))
      stdout.write b
    stdout.flush
  let doStep (i : Input) : IO Unit := do
    lock.lock
    try doStep' i finally lock.unlock
  let done ← IO.mkRef false
  if o.tickMs > 0 then
    let _ ← IO.asTask (prio := .dedicated) do
      while !(← done.get) do
        IO.sleep o.tickMs.toUInt32
        if !(← done.get) then doStep .tick
  repeat
    if o.eth then
      match ← readFrame stdin with
      | some f => doStep (.rx f)
      | none => break
    else
      -- `read n` blocks until n bytes arrive, so read byte-wise and hand
      -- the stack one chunk per SLIP frame (up to its closing END).
      let mut chunk := ByteArray.empty
      let mut eof := false
      repeat
        let b ← stdin.read 1
        if b.size == 0 then
          eof := true
          break
        chunk := chunk ++ b
        if b.get! 0 == Slip.END && chunk.size > 1 then break
      if chunk.size > 0 then doStep (.rx chunk)
      if eof then break
  done.set true
  return 0

end Ember.Tools.Host
