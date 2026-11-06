import Tests.Ember.AuthNetTests
import Tests.Ember.ControlTests

/-!
# Control requests and kept connections in Ember against the reference (plan M9.5)

A client keeps one connection and sends requests one after another, each
once the previous response is complete (or two in one segment), and ends
with its FIN.  The interpreter (one connection) and the host C (1 and 2
connections) must give `Spec.Srv`'s trace for the demo site with a control
route; so must they for the sessions recorded with curl (`Tests/Ember/http-ctl`,
`Tests/Ember/https-ctl`), which `Spec.Srv` must give as recorded.
-/

namespace Ember.Tests.ControlNetTests
open Ember Ember.Spec Ember.Trace Ember.Lang Ember.Tests.SrvTests Ember.Tests.HttpTests
open Ember.Tests.ControlTests (post bearer ctl)

/-- One kept connection: the requests in turn (each cut into `pieces`),
the responses ACKed as they come, until nothing more arrives; then our FIN. -/
def keepSession (A : Srv.App) (reqs : List ByteArray) (pieces : Nat := 1) : Array Input × ByteArray := Id.run do
  let mut s := Srv.State.init A {}
  let mut ins : Array Input := #[]
  let mut resp := ByteArray.empty
  let mut cseq : UInt32 := 1000
  let syn := Peer.slip (Peer.tcp peerPort cseq 0 Tcp.SYN (mss := some 536) (dport := A.port))
  let (s1, es) := Srv.step s syn
  s := s1
  ins := ins.push syn
  let some sa := (segsOf es).head? | return (ins, resp)
  cseq := cseq + 1
  let mut sack : UInt32 := sa.seq + 1
  let mss := (sa.mss.map (·.toNat)).getD 536
  for req in reqs do
    let k := max 1 pieces
    let step := min mss ((req.size + k - 1) / k)
    let mut off := 0
    let mut pending : List Tcp.Seg := []
    while off < req.size do
      let n := min step (req.size - off)
      let i := Peer.slip (Peer.tcp peerPort cseq sack (Tcp.ACK ||| Tcp.PSH) (Bytes.slice req off n) (dport := A.port))
      let (s2, es2) := Srv.step s i
      s := s2
      ins := ins.push i
      cseq := cseq + UInt32.ofNat n
      off := off + n
      pending := pending ++ segsOf es2
    let mut rounds := 0
    let mut quiet := 0
    while rounds < 200 && quiet < 2 do
      rounds := rounds + 1
      let mut got := false
      for sg in pending do
        if sg.seq == sack then
          if sg.data.size > 0 then
            resp := resp ++ sg.data
            sack := sack + UInt32.ofNat sg.data.size
            got := true
          if Tcp.has sg.flags Tcp.FIN then
            sack := sack + 1
            got := true
      quiet := if got then 0 else quiet + 1
      let i := if got then Peer.slip (Peer.tcp peerPort cseq sack Tcp.ACK (dport := A.port)) else Input.tick
      let (s2, es2) := Srv.step s i
      s := s2
      ins := ins.push i
      pending := segsOf es2
  let fin := Peer.slip (Peer.tcp peerPort cseq sack (Tcp.ACK ||| Tcp.FIN) (dport := A.port))
  ins := ins.push fin
  return (ins, resp)

def cget (path : String) (extra : String := "") (v : String := "1.1") : ByteArray :=
  ControlTests.str s!"GET {path} HTTP/{v}\r\n{bearer ctl}{extra}\r\n"

/-- The request lists, each sent on one kept connection. -/
def lists : List (String × List ByteArray) := [
  ("get, post, retry, conflict, next, close",
    [cget "/status", post "1" "takeoff", post "1" "takeoff", post "1" "land", post "2" "land",
     cget "/status" "Connection: close\r\n"]),
  ("two in one segment", [cget "/status" ++ cget "/hello.txt"]),
  ("a POST and a GET in one segment", [post "3" "hover" ++ cget "/status"]),
  ("411 closes", [cget "/status", ControlTests.str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\n\r\n", cget "/status"]),
  ("401 closes", [ControlTests.str "POST /cmd HTTP/1.1\r\nX-Ember-Seq: 1\r\nContent-Length: 2\r\n\r\ngo", cget "/status"]),
  ("HTTP/1.0 closes", [cget "/status" "" "1.0", cget "/status"]),
  ("405, 404 kept", [cget "/cmd", cget "/nowhere", post "1" "x"]),
  ("an empty body, then seq 2^32 - 1", [post "1" "", post "4294967295" "max"]),
  ("Transfer-Encoding", [post "1" "go" "Transfer-Encoding: chunked\r\n"]),
  ("leading zeros: Content-Length 02, X-Ember-Seq 01, then 1", [ControlTests.str s!"POST /cmd HTTP/1.1\r\n{bearer ctl}X-Ember-Seq: 1\r\nContent-Length: 02\r\n\r\ngo",
    post "01" "go"]),
  ("X-Ember-Seq 01 on a kept connection, then 1", [cget "/status", post "01" "go", post "1" "go"]),
  ("Connection: keep-alive, close closes", [cget "/status" "Connection: keep-alive, close\r\n", cget "/status"]),
  ("two Connection fields, the second close", [cget "/status" "Connection: keep-alive\r\nConnection: Close\r\n", cget "/status"]),
  ("Connection: closed and keep-alive;close are kept", [cget "/status" "Connection: closed\r\n", cget "/status" "Connection: keep-alive;close\r\n", cget "/status"]),
  ("POST with Connection: close, keep-alive", [post "1" "go" "Connection: close, keep-alive\r\n", cget "/status"]),
  ("HEAD kept", [ControlTests.str s!"HEAD /status HTTP/1.1\r\n{bearer ctl}\r\n", cget "/status"])]

def csite : Srv.Http.Site := Srv.Http.demoCtl
def capp : Srv.App := Srv.Http.app csite
def cmk (n : Nat) : Prog := Tools.NetCheck.checked (Net.Http.prog n csite)

def sessions : List (String × Array Input) :=
  lists.flatMap fun (name, reqs) =>
    [(name, (keepSession capp reqs).1), (name ++ " (7 pieces)", (keepSession capp reqs 7).1)]

def run : IO Nat := do
  let mut bad := 0
  -- what the client got on the first list: the answers in order
  let (_, r) := keepSession capp (lists.head!.2)
  let codes := ((String.fromUTF8! r).splitOn "HTTP/1.1 ").drop 1 |>.map (fun x => String.ofList (x.toList.take 3))
  if codes != ["200", "200", "200", "409", "200", "200"] then
    IO.println s!"FAIL control session: {codes}"; bad := bad + 1
  match (cmk 2).check with
  | .error e => IO.println s!"FAIL control program does not check: {repr e}"; return bad + 1
  | .ok _ => pure ()
  bad := bad + (← AuthNetTests.emberRuns "control" capp cmk (sessions.toArray))
  let (a, hfx) ← AuthNetTests.fixtures "http-ctl" "Tests/Ember/http-ctl" capp
  bad := bad + a + (← AuthNetTests.emberRuns "http-ctl" capp cmk (AuthNetTests.variants hfx 13))
  let tapp := Srv.Tls.app Srv.Tls.demoCtl
  let (b, sfx) ← AuthNetTests.fixtures "https-ctl" "Tests/Ember/https-ctl" tapp
  bad := bad + b + (← AuthNetTests.emberRuns "https-ctl" tapp (fun n => Tools.NetCheck.checked (Net.Tls.prog n Srv.Tls.demoCtl))
    (AuthNetTests.variants sfx 14))
  return bad

/-- `EMBER_M9_DUMP=DIR`: the HTTPS sessions of M9 (recorded with protected
routes, and with control requests; as recorded, re-chunked, with ticks)
with `Spec.Srv.Tls`'s traces on two connections, for the replay on the
ESP32-C3 images `stack-https-auth-test` (`DIR/auth`) and
`stack-https-ctl-test` (`DIR/ctl`). -/
def dump (dir : System.FilePath) : IO Unit := do
  for (sub, src, site) in [("auth", "Tests/Ember/https-auth", Srv.Tls.demoAuth), ("ctl", "Tests/Ember/https-ctl", Srv.Tls.demoCtl)] do
    let d := dir / sub
    IO.FS.createDirAll d
    let mut fx := #[]
    for f in ← SpecTests.traceFiles src do
      fx := fx.push (f.toString, (← Trace.readFile f).inputs)
    let mut i := 0
    for (name, ins) in AuthNetTests.variants fx 21 do
      let t := Srv.run (Srv.Tls.app site) (srvCfg {} 2) ins
      let lines := t.print.splitOn "\n"
      IO.FS.writeFile (d / s!"{sub}-{i}.trace")
        (lines.head! ++ s!"\n# {name}: Spec.Srv.Tls with the demo site of {sub}, 2 connections\n" ++ "\n".intercalate lines.tail!)
      i := i + 1
    IO.println s!"m9 {sub}: {i} sessions written to {d}"

end Ember.Tests.ControlNetTests
