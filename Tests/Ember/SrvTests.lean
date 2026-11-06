import Ember.Spec.Srv.Stack
import Ember.Spec.Gen
import Ember.Trace.Text
import Tests.Ember.SpecTests
import Ember.Net.Srv
import Ember.Tools.NetCheck
import Ember.Tools.Cc
import Tests.Ember.HttpTests
import Ember.Net.Http
import Ember.Spec.Srv.Tls
import Tests.Ember.TlsTests

/-!
# `Ember.Spec.Srv` against `Ember.Spec` (plan M8.1)

The stack with an application interface, run with the echo application
and one connection, must give `Ember.Spec.Stack`'s trace — every line,
the `tcb`, `drop`, `pkt` and `note` lines included — on every fixture of
the corpus and of `regress/`, and on generated sessions (ICMP, UDP, TCP;
as generated, mutated and re-chunked; on SLIP and on Ethernet; DHCP).
With two connections a second client is served instead of reset.
-/

namespace Ember.Tests.SrvTests
open Ember Ember.Spec Ember.Trace Ember.Lang

def srvCfg (c : Spec.Config) (conns := 1) : Srv.Config := { toConfig := c, conns }

/-- The two stacks' traces as text, or the first line where they differ. -/
def same (cfg : Spec.Config) (ins : Array Input) : Option String :=
  let a := (Spec.run cfg ins).print.splitOn "\n"
  let b := (Srv.run Srv.echo (srvCfg cfg) ins).print.splitOn "\n"
  if a == b then none
  else
    let i := (List.range (max a.length b.length)).find? (fun i => a[i]? != b[i]?) |>.getD 0
    some s!"line {i + 1}:\n  spec: {a[i]?.getD "<end>"}\n  srv:  {b[i]?.getD "<end>"}"

def corpus : IO Nat := do
  let mut bad := 0
  let files := (← SpecTests.traceFiles "Tests/Ember/corpus") ++ (← SpecTests.traceFiles "Tests/Ember/regress")
  for f in files do
    let t ← Trace.readFile f
    if let some d := same (Spec.Config.ofHeader t.header) t.inputs then
      bad := bad + 1
      IO.println s!"FAIL srv corpus {f}: {d}"
  IO.println s!"srv corpus: {files.size} fixtures, Srv echo = Spec, {bad} failures"
  return bad

/-- Generated sessions of every kind, each also mutated and re-chunked. -/
def generated (count seed : Nat) : IO Nat := do
  let mut bad := 0
  let mut n := 0
  let mut rng := Rng.ofSeed (seed * 7919)
  for i in [0:count] do
    let (r, rng') := (do
      let p ← Gen.ping
      let u ← Gen.udp
      let t ← Gen.tcp
      let d ← Gen.dhcp
      let base := [p, u, d] ++ (match t with | .ok s => [s] | .error _ => [])
      let mut all := #[]
      for s in base do
        all := all.push s
        all := all.push (← Gen.mutate s)
        all := all.push (← Gen.rechunk s)
        all := all.push (← Gen.midTicks s)
        if s.cfg.link == .slip && !s.cfg.dhcp then all := all.push (← Gen.toEth s)
      return all : RandM _).run rng
    rng := rng'
    for s in r do
      n := n + 1
      if let some d := same s.cfg s.inputs then
        bad := bad + 1
        IO.println s!"FAIL srv generated {i} {s.kind}: {d}"
  IO.println s!"srv generated: {n} sessions, Srv echo = Spec, {bad} failures"
  return bad

/-- Two clients: one connection resets the second, two serve both. -/
def twoClients : IO Nat := do
  let syn (port : UInt16) := Peer.slip (Peer.tcp port 1000 0 Tcp.SYN (mss := some 536))
  let ins := #[syn 40001, syn 40002]
  let tr (conns : Nat) := Srv.run Srv.echo (srvCfg {} conns) ins
  let tx (conns : Nat) : Array Nat := (List.range ins.size).toArray.map fun i =>
    ((tr conns).lines.filter fun l => l.step == i && (match l.ev with | .tx _ => true | _ => false)).size
  let drops (conns : Nat) : Nat :=
    ((tr conns).lines.filter fun l => match l.ev with | .drop _ => true | _ => false).size
  let one := (tx 1, drops 1)
  let two := (tx 2, drops 2)
  -- one connection: SYN-ACK, then RST and `unsupported-second-connection`
  -- two connections: two SYN-ACKs, nothing dropped
  let ok := one == (#[1, 1], 1) && two == (#[1, 1], 0)
  IO.println s!"srv two clients: conns=1 {one}, conns=2 {two} {if ok then "ok" else "FAIL"}"
  return if ok then 0 else 1


/-! ## `Ember.Net.Srv` (the Ember program, interpreted) against `Ember.Spec.Srv` -/

def netProg (n : Nat) : Prog := Tools.NetCheck.checked (Net.Srv.echoProg n)

/-- The Ember program checks (types, call graph) for one and four connections. -/
def progChecks : IO Nat := do
  let mut bad := 0
  for n in [1, 2, 4] do
    match (Net.Srv.echoProg n).check with
    | .ok _ => pure ()
    | .error e =>
      bad := bad + 1
      IO.println s!"FAIL srv net program n={n} does not check: {repr e}"
  return bad

/-- `none` when the Ember program's observable lines and drops are the Spec's. -/
def netSame (n : Nat) (cfg : Spec.Config) (ins : Array Input) : Option String :=
  let h := cfg.header
  let s := Tools.NetCheck.comparable (Srv.run Srv.echo (srvCfg cfg n) ins)
  let r := runMachine (Machine.init (netProg n) ins) { h with impl := "ember-interp" } (fuel := 1000000)
  if let some e := r.error then some s!"Ember stack trapped: {repr e}" else
  let d := diff s (Tools.NetCheck.comparable r.trace) { observable := false, context := 2 }
  if d.equal then none else some d.report

def slipOnly (c : Spec.Config) : Bool := c.link == .slip && c.mtu == 296 && !c.dhcp

def netCorpus : IO Nat := do
  let mut bad := 0
  let mut k := 0
  let files := (← SpecTests.traceFiles "Tests/Ember/corpus") ++ (← SpecTests.traceFiles "Tests/Ember/regress")
  for f in files do
    let t ← Trace.readFile f
    let cfg := Spec.Config.ofHeader t.header
    if !slipOnly cfg then continue
    for n in [1, 2] do
      k := k + 1
      if let some d := netSame n cfg t.inputs then
        bad := bad + 1
        IO.println s!"FAIL srv net corpus n={n} {f}: {d}"
  IO.println s!"srv net corpus: {k} runs (SLIP fixtures × 1, 2 connections), Ember = Spec.Srv, {bad} failures"
  return bad

def netGenerated (count seed : Nat) : IO Nat := do
  let mut bad := 0
  let mut k := 0
  let mut rng := Rng.ofSeed (seed * 104729)
  for i in [0:count] do
    let (r, rng') := (do
      let u ← Gen.udp
      let t ← Gen.tcp
      let base := [u] ++ (match t with | .ok s => [s] | .error _ => [])
      let mut all := #[]
      for s in base do
        all := all.push s
        all := all.push (← Gen.mutate s)
        all := all.push (← Gen.rechunk s)
        all := all.push (← Gen.midTicks s)
      return all : RandM _).run rng
    rng := rng'
    for s in r do
      for n in [1, 2] do
        k := k + 1
        if let some d := netSame n s.cfg s.inputs then
          bad := bad + 1
          IO.println s!"FAIL srv net generated {i} {s.kind} n={n}: {d}"
  IO.println s!"srv net generated: {k} runs, Ember = Spec.Srv, {bad} failures"
  return bad

/-- Two clients through the Ember program too. -/
def netTwoClients : IO Nat := do
  let syn (port : UInt16) := Peer.slip (Peer.tcp port 1000 0 Tcp.SYN (mss := some 536))
  let ins := #[syn 40001, syn 40002]
  let mut bad := 0
  for n in [1, 2] do
    if let some d := netSame n {} ins then
      bad := bad + 1
      IO.println s!"FAIL srv net two clients n={n}: {d}"
  IO.println s!"srv net two clients: {bad} failures"
  return bad

/-! ## The emitted C (host, `-O2`, UBSan/ASan) against `Ember.Spec.Srv` -/

def hostC (count seed : Nat) : IO Nat := do
  if !(← Tools.Cc.available) then
    IO.println "srv host C: no C compiler, skipped"
    return 0
  let mut units := []
  for n in [1, 2] do
    match Tools.Cc.emit s!"srv{n}" (netProg n) with
    | .error e => IO.println s!"FAIL srv host C: emit n={n}: {e}"; return 1
    | .ok c => units := units ++ [(s!"srv{n}", c)]
  let exe ← match ← Tools.Cc.build { dir := ".lake/ember-srv", flags := #["-O2", "-fsanitize=undefined,address",
      "-fno-sanitize-recover=all"] } units with
    | .error e => IO.println s!"FAIL srv host C: build: {e}"; return 1
    | .ok exe => pure exe
  let mut streams : Array (String × Spec.Config × Array Input) := #[]
  for f in (← SpecTests.traceFiles "Tests/Ember/corpus") ++ (← SpecTests.traceFiles "Tests/Ember/regress") do
    let t ← Trace.readFile f
    let cfg := Spec.Config.ofHeader t.header
    if slipOnly cfg then streams := streams.push (f.toString, cfg, t.inputs)
  let mut rng := Rng.ofSeed (seed * 15485863)
  for i in [0:count] do
    let (r, rng') := (do
      let t ← Gen.tcp
      match t with
      | .ok s => return #[s, ← Gen.mutate s, ← Gen.rechunk s]
      | .error _ => return #[] : RandM _).run rng
    rng := rng'
    for s in r do streams := streams.push (s!"generated {i} {s.kind}", s.cfg, s.inputs)
  let tmp : System.FilePath := ".lake/ember-srv/inputs.trace"
  let mut bad := 0
  let mut k := 0
  for (name, cfg, ins) in streams do
    for (n, idx) in [(1, 0), (2, 1)] do
      k := k + 1
      Tools.Cc.writeInputs tmp cfg.header ins
      let (t, rc) ← Tools.Cc.run exe idx tmp
      let s := Tools.NetCheck.comparable (Srv.run Srv.echo (srvCfg cfg n) ins)
      let d := diff s (Tools.NetCheck.comparable t) { observable := false, context := 2 }
      if rc != 0 || !d.equal then
        bad := bad + 1
        IO.println s!"FAIL srv host C n={n} {name} (exit {rc}): {d.report}"
  IO.println s!"srv host C: {k} runs (-O2, UBSan/ASan), C = Spec.Srv, {bad} failures"
  return bad

/-! ## HTTP: the Ember program (interpreted and as host C) against `Ember.Spec.Srv.Http` -/

def httpProg (n : Nat) : Prog := Tools.NetCheck.checked (Net.Http.prog n Srv.Http.demo)
def httpApp : Srv.App := Srv.Http.app Srv.Http.demo

/-- The exchanges of `HttpTests`, each also mutated and re-chunked. -/
def httpStreams (seed : Nat) : Array (String × Array Input) := Id.run do
  let mut out := #[]
  let mut rng := Rng.ofSeed (seed * 2654435761)
  for (name, ins) in HttpTests.sessions do
    let s : Gen.Session := { kind := "http", inputs := ins }
    let ((m, c, t), rng') := (do return (← Gen.mutate s, ← Gen.rechunk s, ← Gen.midTicks s) : RandM _).run rng
    rng := rng'
    out := out ++ #[(name, ins), (name ++ " mutated", m.inputs), (name ++ " re-chunked", c.inputs),
                    (name ++ " ticks", t.inputs)]
  out := out.push ("three clients in a row", (HttpTests.series httpApp HttpTests.seriesReqs).2)
  return out

/-- The recorded HTTP sessions (`Tests/Ember/http`): `Spec.Srv` must give their trace. -/
def httpFixtures : IO (Nat × Array (String × Array Input)) := do
  let mut bad := 0
  let mut out := #[]
  let files ← SpecTests.traceFiles "Tests/Ember/http"
  for f in files do
    let t ← Trace.readFile f
    let r := Srv.run httpApp (srvCfg (Spec.Config.ofHeader t.header)) t.inputs
    let d := diff t r { observable := true, drops := true }
    if !d.equal then
      bad := bad + 1
      IO.println s!"FAIL http fixture {f}\n{d.report}"
    out := out.push (f.toString, t.inputs)
  IO.println s!"http fixtures: {files.size} recorded sessions, Spec.Srv = recorded, {bad} failures"
  return (bad, out)

def httpSame (n : Nat) (ins : Array Input) : Option String :=
  let h := (Spec.Config.header {})
  let s := Tools.NetCheck.comparable (Srv.run httpApp (srvCfg {} n) ins)
  let r := runMachine (Machine.init (httpProg n) ins) { h with impl := "ember-interp" } (fuel := 4000000)
  if let some e := r.error then some s!"Ember stack trapped: {repr e}" else
  let d := diff s (Tools.NetCheck.comparable r.trace) { observable := false, context := 2 }
  if d.equal then none else some d.report

def httpNet (extra : Array (String × Array Input)) : IO Nat := do
  match (Net.Http.prog 2 Srv.Http.demo).check with
  | .error e => IO.println s!"FAIL http net program does not check: {repr e}"; return 1
  | .ok _ => pure ()
  let mut bad := 0
  let mut k := 0
  for (name, ins) in httpStreams 5 ++ extra do
    for n in [1, 2] do
      k := k + 1
      if let some d := httpSame n ins then
        bad := bad + 1
        IO.println s!"FAIL http net n={n} {name}: {d}"
  IO.println s!"http net: {k} runs (exchanges, mutated, re-chunked, ticks × 1, 2 connections), Ember = Spec.Srv, {bad} failures"
  return bad

def httpHostC (extra : Array (String × Array Input)) : IO Nat := do
  if !(← Tools.Cc.available) then
    IO.println "http host C: no C compiler, skipped"
    return 0
  let mut units := []
  for n in [1, 2] do
    match Tools.Cc.emit s!"http{n}" (httpProg n) with
    | .error e => IO.println s!"FAIL http host C: emit n={n}: {e}"; return 1
    | .ok c => units := units ++ [(s!"http{n}", c)]
  let exe ← match ← Tools.Cc.build { dir := ".lake/ember-http", flags := #["-O2", "-fsanitize=undefined,address",
      "-fno-sanitize-recover=all"] } units with
    | .error e => IO.println s!"FAIL http host C: build: {e}"; return 1
    | .ok exe => pure exe
  let tmp : System.FilePath := ".lake/ember-http/inputs.trace"
  let mut bad := 0
  let mut k := 0
  for (name, ins) in httpStreams 6 ++ extra do
    for (n, idx) in [(1, 0), (2, 1)] do
      k := k + 1
      Tools.Cc.writeInputs tmp (Spec.Config.header {}) ins
      let (t, rc) ← Tools.Cc.run exe idx tmp
      let s := Tools.NetCheck.comparable (Srv.run httpApp (srvCfg {} n) ins)
      let d := diff s (Tools.NetCheck.comparable t) { observable := false, context := 2 }
      if rc != 0 || !d.equal then
        bad := bad + 1
        IO.println s!"FAIL http host C n={n} {name} (exit {rc}): {d.report}"
  IO.println s!"http host C: {k} runs (-O2, UBSan/ASan), C = Spec.Srv, {bad} failures"
  return bad

/-! ## HTTPS: the recorded sessions against `Spec.Srv.Tls` -/

/-- The sessions recorded from Linux clients (`Tests/Ember/https`): curl and
OpenSSL against `ember-host --https`; `Spec.Srv.Tls` must give their trace. -/
def httpsFixtures : IO (Nat × Array (String × Array Input)) := do
  let mut bad := 0
  let mut out := #[]
  let files ← SpecTests.traceFiles "Tests/Ember/https"
  for f in files do
    let t ← Trace.readFile f
    let r := Srv.run (Srv.Tls.app Srv.Tls.demo) (srvCfg (Spec.Config.ofHeader t.header)) t.inputs
    let d := diff t r { observable := true, drops := true }
    if !d.equal then
      bad := bad + 1
      IO.println s!"FAIL https fixture {f}\n{d.report}"
    out := out.push (f.toString, t.inputs)
  IO.println s!"https fixtures: {files.size} recorded sessions (curl, openssl s_client), Spec.Srv.Tls = recorded, {bad} failures"
  return (bad, out)

/-- `EMBER_HTTP_DUMP=DIR`: write the HTTP sessions with `Spec.Srv`'s
traces, for the replay on the ESP32-C3 image (`qemu-test.sh`). -/
def httpDump (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let mut i := 0
  for (name, ins) in httpStreams 7 do
    let t := Srv.run httpApp (srvCfg {} 2) ins
    let lines := t.print.splitOn "\n"
    IO.FS.writeFile (dir / s!"http-{i}.trace")
      (lines.head! ++ s!"\n# {name}: Spec.Srv with Spec.Srv.Http.demo, 2 connections\n" ++ "\n".intercalate lines.tail!)
    i := i + 1
  IO.println s!"http: {i} sessions written to {dir}"

def main : IO UInt32 := do
  let a ← corpus
  let b ← generated 100 1
  let c ← twoClients
  let d ← progChecks
  let e ← netCorpus
  let f ← netGenerated 50 2
  let g ← netTwoClients
  let h ← hostC 50 3
  let i ← HttpTests.run
  let (l, fx) ← httpFixtures
  let (m, _) ← httpsFixtures
  let t ← TlsTests.run
  let j ← httpNet fx
  let k ← httpHostC fx
  return if a + b + c + d + e + f + g + h + i + j + k + l + m + t == 0 then 0 else 1

end Ember.Tests.SrvTests
