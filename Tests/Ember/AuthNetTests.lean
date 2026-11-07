import Tests.Ember.SrvTests
import Tests.Ember.AuthTests
import Tests.Ember.TlsTests
import Ember.Tools.HostEntropy

/-!
# The token check in Ember against the reference (plan M9.3)

Sites with protected routes (`AuthTests.site`: two keys, then one key,
no clock, no keys, a later clock), and requests to them: every token of
`AuthTests.checks` on a protected route, the requests of
`AuthTests.routes`, and the edges of the `Authorization` field that the
streaming reader must take as `Spec.Srv.Http.guard` does (tabs, CRs inside
the value, a bare LF, white space before the colon, …).  Each request is
an exchange of `HttpTests` (whole, and cut into seven pieces).  The
interpreter (one connection, first site) and the host C (1 and 2
connections, every site) must give `Spec.Srv`'s trace.  The answers of
the first site are also checked against `Http.answer` itself.
-/

namespace Ember.Tests.AuthNetTests
open Ember Ember.Spec Ember.Trace Ember.Lang Ember.Tests.SrvTests
open Ember.Tests.AuthTests (get tok good flipLast str)

def sites : List (String × Srv.Http.Site) :=
  [("two keys", AuthTests.site),
   ("one key", { AuthTests.site with auth := some AuthTests.cfg1 }),
   ("no clock", { AuthTests.site with now := none }),
   ("no keys", { AuthTests.site with auth := none }),
   ("a later clock", { AuthTests.site with now := some (AuthTests.now + 361) })]

def raw (s : String) : ByteArray := str s

/-- The edges of the field (each a whole request). -/
def edges : List (String × ByteArray) :=
  let t := tok good
  [("bearer, a tab, the token", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer\t{t}\r\n\r\n"),
   ("bearer, a tab and a space, the token", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer\t {t}\r\n\r\n"),
   ("bearer and a tab", raw "GET /status HTTP/1.1\r\nAuthorization: Bearer\t\r\n\r\n"),
   ("bearer and spaces", raw "GET /status HTTP/1.1\r\nAuthorization: Bearer   \r\n\r\n"),
   ("bearer, a space and a tab", raw "GET /status HTTP/1.1\r\nAuthorization: Bearer \t\r\n\r\n"),
   ("bearer, spaces, a tab, the token", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer  \t{t}\r\n\r\n"),
   ("a CR inside the token", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t}\rx\r\n\r\n"),
   ("a CR after the token", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t}\r\r\n\r\n"),
   ("a CR in the scheme", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bea\rrer {t}\r\n\r\n"),
   ("a CR before the scheme", raw s!"GET /status HTTP/1.1\r\nAuthorization: \rBearer {t}\r\n\r\n"),
   ("the field ends with a bare LF", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t}\nHost: x\r\n\r\n"),
   ("white space before the colon", raw s!"GET /status HTTP/1.1\r\nAuthorization : Bearer {t}\r\n\r\n"),
   ("no colon", raw s!"GET /status HTTP/1.1\r\nAuthorization Bearer {t}\r\n\r\n"),
   ("an empty value", raw "GET /status HTTP/1.1\r\nAuthorization:\r\n\r\n"),
   ("tabs before the scheme", raw s!"GET /status HTTP/1.1\r\nAuthorization:\t \tBearer {t}\r\n\r\n"),
   ("the token, then a tab", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t}\t\r\n\r\n"),
   ("the token, white space, more", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t} \tx\r\n\r\n"),
   ("a longer name", raw s!"GET /status HTTP/1.1\r\nAuthorizations: Bearer {t}\r\n\r\n"),
   ("a shorter name", raw s!"GET /status HTTP/1.1\r\nAuthorizatio: Bearer {t}\r\n\r\n"),
   ("the field first, a second one empty", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearer {t}\r\nauthorization:\r\n\r\n"),
   ("the name inside another field", raw s!"GET /status HTTP/1.1\r\nX-Authorization: Bearer {t}\r\n\r\n"),
   ("Bearer as a longer scheme", raw s!"GET /status HTTP/1.1\r\nAuthorization: Bearers {t}\r\n\r\n"),
   ("the request line only", raw s!"GET /status HTTP/1.1\r\n\r\n"),
   ("HEAD with the token", raw s!"HEAD /status HTTP/1.1\r\nAuthorization: Bearer {t}\r\n\r\n"),
   ("HEAD on control without the scope", raw s!"HEAD /control HTTP/1.1\r\nAuthorization: Bearer {AuthTests.withScope "x"}\r\n\r\n"),
   ("POST to a protected route", raw s!"POST /status HTTP/1.1\r\nAuthorization: Bearer {t}\r\n\r\n"),
   ("a protected route with a query", raw s!"GET /status?x=1 HTTP/1.1\r\nAuthorization: Bearer {t}\r\n\r\n"),
   ("a protected route not found", raw s!"GET /statu HTTP/1.1\r\nAuthorization: Bearer {t}\r\n\r\n")]

/-- The requests: every token on `/status` and on `/control`, the routes'
requests, the edges. -/
def requests : List (String × ByteArray) :=
  (AuthTests.checks.map fun (name, _, t, _) => (s!"token {name}", get "/status" [s!"Authorization: Bearer {tok t}"])) ++
  (AuthTests.checks.take 6 |>.map fun (name, _, t, _) => (s!"control, token {name}", get "/control" [s!"Authorization: Bearer {tok t}"])) ++
  (AuthTests.routes.map fun (name, _, req, _, _) => (s!"route {name}", req)) ++
  edges

/-- The sessions of one site: each request whole and in seven pieces. -/
def sessions (site : Srv.Http.Site) : List (String × Array Input) :=
  let A := Srv.Http.app site
  requests.flatMap fun (name, req) =>
    [(name, (HttpTests.exchange A req).inputs), (name ++ " (7 pieces)", (HttpTests.exchange A req 7).inputs)]

def prog (site : Srv.Http.Site) (n : Nat) : Prog := Tools.NetCheck.checked (Net.Http.prog n site)

/-- What the token check of connection 0 holds (for a failure's report). -/
def state (m : Machine) : String :=
  let one (x : String) : String :=
    match m.global? x with
    | some (Val.arr xs) => match xs[0]? with
      | some (Val.int _ v) => s!"{x}={v}"
      | some (Val.bool b) => s!"{x}={b}"
      | _ => s!"{x}=?"
    | some (Val.int _ v) => s!"{x}={v}"
    | some (Val.bool b) => s!"{x}={b}"
    | _ => s!"{x}=?"
  " ".intercalate (["a_cnt", "a_res", "a_vs", "j_bad", "j_seg", "j_st", "j_slen", "j_seen", "j_algok", "j_kid", "j_issok",
    "j_audok", "j_expok", "j_exp", "j_nbfok", "j_grant", "a_len", "h_kind", "h_now", "h_now_ok"].map one)

def same (site : Srv.Http.Site) (n : Nat) (ins : Array Input) : Option String :=
  let h := Spec.Config.header {}
  let s := Tools.NetCheck.comparable (Srv.run (Srv.Http.app site) (srvCfg {} n) ins)
  let r := runMachine (Machine.init (prog site n) ins) { h with impl := "ember-interp" } (fuel := 4000000000)
  if let some e := r.error then some s!"Ember stack trapped: {repr e}" else
  let d := diff s (Tools.NetCheck.comparable r.trace) { observable := false, context := 2 }
  if d.equal then none else some (d.report ++ "\n  the token check's state of connection 0: " ++ state r.machine)

/-- The answers the exchanges of the first site got are `Http.answer`'s. -/
def answers : IO Nat := do
  let site := AuthTests.site
  let A := Srv.Http.app site
  let mut bad := 0
  for (name, req) in requests do
    let ex := HttpTests.exchange A req
    if ex.resp.toList != (Srv.Http.answer site req req).toList || !ex.fin then
      bad := bad + 1
      IO.println s!"FAIL auth exchange {name}: {String.fromUTF8! ex.resp}"
  IO.println s!"auth exchanges: {requests.length} requests on Spec.Srv, answer = Http.answer, {bad} failures"
  return bad

def interp : IO Nat := do
  let (sname, site) := sites.head!
  match (Net.Http.prog 2 site).check with
  | .error e => IO.println s!"FAIL auth http program does not check: {repr e}"; return 1
  | .ok _ => pure ()
  let mut bad := 0
  let ss := (sessions site).filter fun (n, _) => !n.endsWith "(7 pieces)"
  for (name, ins) in ss do
    if let some d := same site 1 ins then
      bad := bad + 1
      IO.println s!"FAIL auth net ({sname}) {name}: {d}"
  IO.println s!"auth net (interpreter, {sname}, 1 connection): {ss.length} sessions, Ember = Spec.Srv, {bad} failures"
  return bad

def hostC : IO Nat := do
  if !(← Tools.Cc.available) then
    IO.println "auth host C: no C compiler, skipped"
    return 0
  let mut bad := 0
  let mut k := 0
  for (si, (sname, site)) in sites.zipIdx.map (fun (x, i) => (i, x)) do
    let mut units := []
    for n in [1, 2] do
      match Tools.Cc.emit s!"auth{si}_{n}" (prog site n) with
      | .error e => IO.println s!"FAIL auth host C: emit {sname} n={n}: {e}"; return 1
      | .ok c => units := units ++ [(s!"auth{si}_{n}", c)]
    let exe ← match ← Tools.Cc.build { dir := s!".lake/ember-auth{si}", flags := #["-O2", "-fsanitize=undefined,address",
        "-fno-sanitize-recover=all"] } units with
      | .error e => IO.println s!"FAIL auth host C: build {sname}: {e}"; return 1
      | .ok exe => pure exe
    let tmp : System.FilePath := s!".lake/ember-auth{si}/inputs.trace"
    for (name, ins) in sessions site do
      for (n, idx) in [(1, 0), (2, 1)] do
        k := k + 1
        Tools.Cc.writeInputs tmp (Spec.Config.header {}) ins
        let (t, rc) ← Tools.Cc.run exe idx tmp
        let s := Tools.NetCheck.comparable (Srv.run (Srv.Http.app site) (srvCfg {} n) ins)
        let d := diff s (Tools.NetCheck.comparable t) { observable := false, context := 2 }
        if rc != 0 || !d.equal then
          bad := bad + 1
          IO.println s!"FAIL auth host C ({sname}) n={n} {name} (exit {rc}): {d.report}"
  IO.println s!"auth host C: {k} runs ({sites.length} sites, whole and in 7 pieces, 1 and 2 connections; -O2, UBSan/ASan), C = Spec.Srv, {bad} failures"
  return bad

/-! ## Recorded sessions: curl with tokens of the demo provider (HTTP and HTTPS) -/

/-- The traces in `dir`: `app` must give each (observable lines and drops). -/
def fixtures (what : String) (dir : System.FilePath) (app : Srv.App) : IO (Nat × Array (String × Array Input)) := do
  let mut bad := 0
  let mut out := #[]
  let files ← SpecTests.traceFiles dir
  for f in files do
    let t ← Trace.readFile f
    let r := Srv.run app (srvCfg (Spec.Config.ofHeader t.header)) t.inputs
    let d := diff t r { observable := true, drops := true }
    if !d.equal then
      bad := bad + 1
      IO.println s!"FAIL {what} fixture {f}\n{d.report}"
    out := out.push (f.toString, t.inputs)
  IO.println s!"{what} fixtures: {files.size} sessions recorded with curl, Spec.Srv = recorded, {bad} failures"
  return (bad, out)

/-- The sessions as recorded, re-chunked and with ticks. -/
def variants (fx : Array (String × Array Input)) (seed : Nat) : Array (String × Array Input) := Id.run do
  let mut out := #[]
  let mut rng := Rng.ofSeed (seed * 40503)
  for (name, ins) in fx do
    let s : Gen.Session := { kind := "https", inputs := ins }
    let ((c, t), rng') := (do return (← Gen.rechunk s, ← Gen.midTicks s) : RandM _).run rng
    rng := rng'
    out := out ++ #[(name, ins), (name ++ " re-chunked", c.inputs), (name ++ " ticks", t.inputs)]
  return out

/-- Ember (interpreter: the sessions as recorded, one connection; host C:
every variant, 1 and 2 connections) against `app`. -/
def emberRuns (what : String) (app : Srv.App) (mk : Nat → Prog) (streams : Array (String × Array Input)) : IO Nat := do
  let mut bad := 0
  let h := Spec.Config.header {}
  let verbose := (← IO.getEnv "EMBER_VERBOSE").isSome
  for (name, ins) in streams.filter (fun (n, _) => !n.endsWith " re-chunked" && !n.endsWith " ticks") do
    if verbose then
      IO.println s!"  {what} net: {name}"
      (← IO.getStdout).flush
    let s := Tools.NetCheck.comparable (Srv.run app (srvCfg {} 1) ins)
    let r := runMachine (Machine.init (mk 1) ins) { h with impl := "ember-interp" } (fuel := 4000000000)
    let d := diff s (Tools.NetCheck.comparable r.trace) { observable := false, context := 2 }
    if r.error.isSome || !d.equal then
      bad := bad + 1
      IO.println s!"FAIL {what} net {name}: {d.report}\n  {state r.machine}"
  IO.println s!"{what} net (interpreter): the recorded sessions, Ember = Spec.Srv, {bad} failures"
  if !(← Tools.Cc.available) then
    IO.println s!"{what} host C: no C compiler, skipped"
    return bad
  -- the unit names are C identifiers
  let unit := what.replace "-" "_"
  let mut units := []
  for n in [1, 2] do
    match Tools.Cc.emit s!"{unit}{n}" (mk n) with
    | .error e => IO.println s!"FAIL {what} host C: emit n={n}: {e}"; return bad + 1
    | .ok c => units := units ++ [(s!"{unit}{n}", c)]
  let exe ← match ← Tools.Cc.build { dir := s!".lake/ember-{what}", flags := #["-O2", "-fsanitize=undefined,address",
      "-fno-sanitize-recover=all"] } units with
    | .error e => IO.println s!"FAIL {what} host C: build: {e}"; return bad + 1
    | .ok exe => pure exe
  let tmp : System.FilePath := s!".lake/ember-{what}/inputs.trace"
  let mut k := 0
  let mut cbad := 0
  for (name, ins) in streams do
    for (n, idx) in [(1, 0), (2, 1)] do
      k := k + 1
      Tools.Cc.writeInputs tmp h ins
      let (t, rc) ← Tools.Cc.run exe idx tmp
      let s := Tools.NetCheck.comparable (Srv.run app (srvCfg {} n) ins)
      let d := diff s (Tools.NetCheck.comparable t) { observable := false, context := 2 }
      if rc != 0 || !d.equal then
        cbad := cbad + 1
        IO.println s!"FAIL {what} host C n={n} {name} (exit {rc}): {d.report}"
  IO.println s!"{what} host C: {k} runs (as recorded, re-chunked, ticks; 1 and 2 connections; -O2, UBSan/ASan), C = Spec.Srv, {cbad} failures"
  return bad + cbad

def recorded : IO Nat := do
  let httpApp := Srv.Http.app Srv.Http.demoAuth
  let (a, hfx) ← fixtures "http-auth" "Tests/Ember/http-auth" httpApp
  let b ← emberRuns "http-auth" httpApp (fun n => Tools.NetCheck.checked (Net.Http.prog n Srv.Http.demoAuth)) (variants hfx 11)
  let tlsApp := Srv.Tls.app Srv.Tls.demoAuth
  let (c, sfx) ← fixtures "https-auth" "Tests/Ember/https-auth" tlsApp
  let d ← emberRuns "https-auth" tlsApp (fun n => Tools.NetCheck.checked (Net.Tls.prog n Srv.Tls.demoAuth)) (variants sfx 12)
  return a + b + c + d

/-! ## The RNG's bytes in the handshake (plan M9.4) -/

/-- Eight reads of a register that holds `c`, as the target stores them. -/
def entropyOf (c : UInt32) : ByteArray :=
  ByteArray.mk ((List.replicate 8 [c.toUInt8, (c >>> 8).toUInt8, (c >>> 16).toUInt8, (c >>> 24).toUInt8]).flatten.toArray)

/-- 32 bytes that are not eight equal reads. -/
def entropyLive : ByteArray := ByteArray.mk ((List.range 32).map (·.toUInt8 * 37 + 5)).toArray

/-- With `entropy` the server's random and key share change; eight equal
reads of the RNG (a dead generator) end the handshake with
`internal_error` (decision 9).  The Ember program, reading the RNG
register, gives `Spec.Srv.Tls`'s trace: the interpreter with the register
set to a value, the host C (whose register reads 0) with zeros — both
eight equal reads, so both refused, as the Spec. -/
def rng : IO Nat := do
  let mut bad := 0
  let t ← Trace.readFile "Tests/Ember/https/curl-get.trace"
  let ins := t.inputs
  let c : UInt32 := 0x9e3779b9
  if Srv.Tls.stuck entropyLive || !Srv.Tls.stuck (entropyOf c) || !Srv.Tls.stuck (entropyOf 0) then
    IO.println "FAIL rng: stuck"; bad := bad + 1
  let live := { Srv.Tls.demo with entropy := some entropyLive }
  let dead := { Srv.Tls.demo with entropy := some (entropyOf c) }
  let plain := Tools.NetCheck.comparable (Srv.run (Srv.Tls.app Srv.Tls.demo) (srvCfg {} 1) ins)
  let mixed := Tools.NetCheck.comparable (Srv.run (Srv.Tls.app live) (srvCfg {} 1) ins)
  if (diff plain mixed { observable := false }).equal then
    IO.println "FAIL rng: the RNG's bytes change nothing"; bad := bad + 1
  -- a live generator gets a ServerHello, a dead one internal_error and nothing else
  let ch := TlsTests.clientHello TlsTests.goodShare
  let ok := HttpTests.exchange (Srv.Tls.app live) ch
  if ok.resp.size < 6 || ok.resp[0]! != 22 || ok.resp[5]! != 2 then
    IO.println s!"FAIL rng live: no ServerHello: {CryptoTests.toHex (ok.resp.extract 0 16)}"; bad := bad + 1
  let no := HttpTests.exchange (Srv.Tls.app dead) ch
  if no.resp.toList != (Srv.Tls.record 21 (Srv.Tls.b1 2 ++ Srv.Tls.b1 80)).toList || !no.fin then
    IO.println s!"FAIL rng dead: {CryptoTests.toHex no.resp} (fin {no.fin})"; bad := bad + 1
  let refused := Tools.NetCheck.comparable (Srv.run (Srv.Tls.app dead) (srvCfg {} 1) ins)
  let p1 := Tools.NetCheck.checked (Net.Tls.prog 1 dead)
  let m0 := Machine.init p1 ins
  let m0 := { m0 with world := { m0.world with mmio := m0.world.mmio.insert 0x600260B0 c } }
  let r := runMachine m0 { Spec.Config.header {} with impl := "ember-interp" } (fuel := 4000000000)
  let d := diff refused (Tools.NetCheck.comparable r.trace) { observable := false, context := 2 }
  if r.error.isSome || !d.equal then
    IO.println s!"FAIL rng interpreter: {d.report}"; bad := bad + 1
  if ← Tools.Cc.available then
    let z := { Srv.Tls.demo with entropy := some (ByteArray.mk (Array.replicate 32 0)) }
    match Tools.Cc.emit "rng1" (Tools.NetCheck.checked (Net.Tls.prog 1 z)) with
    | .error e => IO.println s!"FAIL rng host C: emit: {e}"; bad := bad + 1
    | .ok code =>
      match ← Tools.Cc.build { dir := ".lake/ember-rng", flags := #["-O2", "-fsanitize=undefined,address",
          "-fno-sanitize-recover=all"] } [("rng1", code)] with
      | .error e => IO.println s!"FAIL rng host C: build: {e}"; bad := bad + 1
      | .ok exe =>
        let tmp : System.FilePath := ".lake/ember-rng/inputs.trace"
        Tools.Cc.writeInputs tmp (Spec.Config.header {}) ins
        let (tc, rc) ← Tools.Cc.run exe 0 tmp
        let s := Tools.NetCheck.comparable (Srv.run (Srv.Tls.app z) (srvCfg {} 1) ins)
        let d2 := diff s (Tools.NetCheck.comparable tc) { observable := false, context := 2 }
        if rc != 0 || !d2.equal then
          IO.println s!"FAIL rng host C (exit {rc}): {d2.report}"; bad := bad + 1
  -- the host's entropy (plan M9.4): the system's, two runs differ, a ServerHello
  -- with it; given, none; a failing or stuck provider stops the host
  let a ← Tools.HostEntropy.get .os
  let b ← Tools.HostEntropy.get .os
  match a, b with
  | .ok (some x), .ok (some y) =>
    if x.size != 32 || x == y then
      IO.println "FAIL rng host: the system's bytes"; bad := bad + 1
    let hs := HttpTests.exchange (Srv.Tls.app { Srv.Tls.demo with entropy := some x }) ch
    if hs.resp.size < 6 || hs.resp[0]! != 22 || hs.resp[5]! != 2 then
      IO.println "FAIL rng host: no ServerHello with the system's bytes"; bad := bad + 1
  | _, _ => IO.println "FAIL rng host: no bytes from the system"; bad := bad + 1
  let hex := String.join ((List.range 32).map fun i => let s := Nat.toDigits 16 (i * 7 + 1); String.ofList (if s.length == 1 then '0' :: s else s))
  match ← Tools.HostEntropy.get (.given hex) with
  | .ok (some g) => if g.size != 32 || g[1]! != 8 then IO.println "FAIL rng host: --entropy"; bad := bad + 1
  | _ => IO.println "FAIL rng host: --entropy"; bad := bad + 1
  match ← Tools.HostEntropy.get .none with
  | .ok none => pure ()
  | _ => IO.println "FAIL rng host: --no-entropy"; bad := bad + 1
  let refused (r : Except String (Option ByteArray)) : Bool := match r with | .error _ => true | .ok _ => false
  if !refused (← Tools.HostEntropy.get (.given "zz")) || !refused (← Tools.HostEntropy.get .os (fun _ => throw (IO.userError "no getrandom"))) ||
     !refused (← Tools.HostEntropy.get .os (fun _ => pure (ByteArray.mk (Array.replicate 32 0)))) ||
     !refused (← Tools.HostEntropy.get .os (fun _ => pure (ByteArray.mk (Array.replicate 16 1)))) then
    IO.println "FAIL rng host: a bad source must stop the host"; bad := bad + 1
  IO.println s!"rng: the RNG's bytes change the handshake; eight equal reads refuse it; Ember reading the register = Spec.Srv.Tls (interpreter, host C); the host's entropy from the system (two runs differ, a failing or stuck source stops it), {bad} failures"
  return bad

def run : IO Nat := do
  let a ← answers
  let b ← interp
  let c ← hostC
  let d ← recorded
  let e ← rng
  return a + b + c + d + e

end Ember.Tests.AuthNetTests
