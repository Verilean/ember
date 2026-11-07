import Ember.Spec.Srv.Stack
import Ember.Spec.Srv.Http
import Ember.Spec.Peer

/-!
# HTTP over `Ember.Spec.Srv` (plan M8.2)

A small TCP client drives the stack with the HTTP application: handshake,
the request (in one segment or cut in pieces), then an ACK for every
segment the server sends, until its FIN.  The bytes received must be the
response `Http.answer` gives, and the connection must be closed by the
server.  The inputs of each exchange are kept: they are the sessions the
Ember program is checked on.
-/

namespace Ember.Tests.HttpTests
open Ember Ember.Spec Ember.Trace

def peerPort : UInt16 := 40000

/-- The TCP segments the stack sent in some events. -/
def segsOf (es : List Event) : List Tcp.Seg :=
  es.filterMap (fun e => match e with | .tx b => some b | _ => none) |>.flatMap fun b =>
    (Slip.decodeAll b).filterMap fun f =>
      match Ipv4.validate f Peer.ip with
      | .ok (h, p) => match Tcp.parse h.src h.dst p with | .ok s => some s | .error _ => none
      | .error _ => none

structure Ex where
  inputs : Array Input := #[]
  resp   : ByteArray := .empty
  fin    : Bool := false
  rst    : Bool := false

/-- One exchange from the client port `peerPort`, from the server's state `s0`. -/
def exchangeFrom (A : Srv.App) (s0 : Srv.State A) (req : ByteArray) (pieces : Nat := 1)
    (peerPort : UInt16 := peerPort) : Ex × Srv.State A := Id.run do
  let mut s := s0
  let mut ex : Ex := {}
  let mut cseq : UInt32 := 1000
  let feed := fun (s : Srv.State A) (i : Input) => Srv.step s i
  -- handshake
  let syn := Peer.slip (Peer.tcp peerPort cseq 0 Tcp.SYN (mss := some 536) (dport := A.port))
  let (s1, es) := feed s syn
  s := s1
  ex := { ex with inputs := ex.inputs.push syn }
  let some sa := (segsOf es).head? | return (ex, s)
  cseq := cseq + 1
  let mut sack : UInt32 := sa.seq + 1
  -- the request
  let k := max 1 pieces
  -- no segment longer than the server's MSS (`sa.mss`, 256 on SLIP)
  let mss := (sa.mss.map (·.toNat)).getD 536
  let step := min mss ((req.size + k - 1) / k)
  let mut off := 0
  let mut pending : List Tcp.Seg := []
  if req.size == 0 then
    let a := Peer.slip (Peer.tcp peerPort cseq sack Tcp.ACK (dport := A.port))
    let (s2, es2) := feed s a
    s := s2
    ex := { ex with inputs := ex.inputs.push a }
    pending := pending ++ segsOf es2
  while off < req.size do
    let n := min step (req.size - off)
    let d := Bytes.slice req off n
    let i := Peer.slip (Peer.tcp peerPort cseq sack (Tcp.ACK ||| Tcp.PSH) d (dport := A.port))
    let (s2, es2) := feed s i
    s := s2
    ex := { ex with inputs := ex.inputs.push i }
    cseq := cseq + UInt32.ofNat n
    off := off + n
    pending := pending ++ segsOf es2
  -- the response: ACK what arrives in order, until the FIN
  let mut rounds := 0
  while rounds < 400 && !ex.fin && !ex.rst do
    rounds := rounds + 1
    let mut got := false
    for sg in pending do
      if Tcp.has sg.flags Tcp.RST then ex := { ex with rst := true }
      if sg.seq == sack then
        if sg.data.size > 0 then
          ex := { ex with resp := ex.resp ++ sg.data }
          sack := sack + UInt32.ofNat sg.data.size
          got := true
        if Tcp.has sg.flags Tcp.FIN then
          sack := sack + 1
          ex := { ex with fin := true }
          got := true
    let i := if got then Peer.slip (Peer.tcp peerPort cseq sack Tcp.ACK (dport := A.port)) else Input.tick
    let (s2, es2) := feed s i
    s := s2
    ex := { ex with inputs := ex.inputs.push i }
    pending := segsOf es2
  -- our FIN: the server's connection ends
  if ex.fin then
    let i := Peer.slip (Peer.tcp peerPort cseq sack (Tcp.ACK ||| Tcp.FIN) (dport := A.port))
    let (s2, _) := feed s i
    s := s2
    ex := { ex with inputs := ex.inputs.push i }
  return (ex, s)

/-- One exchange: the request cut into `pieces` segments. -/
def exchange (A : Srv.App) (req : ByteArray) (pieces : Nat := 1) (conns := 1) : Ex :=
  (exchangeFrom A (Srv.State.init A { conns }) req pieces).1

/-- Clients one after another, each from its own port, on one server. -/
def series (A : Srv.App) (reqs : List ByteArray) (conns := 1) : List Ex × Array Input := Id.run do
  let mut s := Srv.State.init A { conns }
  let mut out := []
  let mut ins := #[]
  let mut port : UInt16 := 41000
  for r in reqs do
    let (ex, s') := exchangeFrom A s r 1 port
    s := s'
    out := out ++ [ex]
    ins := ins ++ ex.inputs
    port := port + 1
  return (out, ins)

def str (s : String) : ByteArray := s.toUTF8

/-- Requests and what each must be answered with. -/
def cases : List (String × ByteArray) :=
  let get (p : String) := str s!"GET {p} HTTP/1.1\r\nHost: 10.0.0.1\r\nUser-Agent: curl/8\r\nAccept: */*\r\n\r\n"
  [("GET /", get "/"),
   ("GET /hello.txt", get "/hello.txt"),
   ("GET /big.txt", get "/big.txt"),
   ("GET /hello.txt?x=1", get "/hello.txt?x=1"),
   ("GET /missing", get "/missing"),
   ("HEAD /", str "HEAD / HTTP/1.1\r\nHost: x\r\n\r\n"),
   ("POST /", str "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\n\r\n"),
   ("HTTP/1.0", str "GET / HTTP/1.0\r\n\r\n"),
   ("garbage", str "hello there\r\n\r\n"),
   ("bad version", str "GET / HTTP/2.0\r\n\r\n"),
   ("version not a digit", str "GET / HTTP/1.A\r\n\r\n"),
   ("too long", str ("GET /" ++ String.mk (List.replicate 600 'a') ++ " HTTP/1.1\r\n\r\n")),
   -- a browser's header: longer than `reqMax`, its request line short
   ("long header", str ("GET /hello.txt HTTP/1.1\r\nHost: 10.0.0.1\r\n" ++
      String.join ((List.range 24).map fun i => s!"X-Header-{i}: {String.mk (List.replicate 50 'v')}\r\n") ++ "\r\n"))]

/-- Run every case whole and in pieces; the sessions, for the Ember checks. -/
def sessions : List (String × Array Input) :=
  cases.flatMap fun (n, r) =>
    [1, 3, 7].map fun k => (s!"{n} ×{k}", (exchange (Srv.Http.app Srv.Http.demo) r k).inputs)

def seriesReqs : List ByteArray :=
  [str "GET / HTTP/1.1\r\n\r\n", str "GET /hello.txt HTTP/1.1\r\n\r\n", str "HEAD /big.txt HTTP/1.1\r\n\r\n"]

def run : IO Nat := do
  let app := Srv.Http.app Srv.Http.demo
  let mut bad := 0
  let mut k := 0
  for (n, r) in cases do
    for pieces in [1, 3, 7] do
      k := k + 1
      let ex := exchange app r pieces
      -- the header ends somewhere; the request line must end within `reqMax` bytes
      let lineEnds := (Bytes.slice r 0 Srv.Http.demo.reqMax).toList.contains 13
      let want := if Srv.Http.headerEnds r && lineEnds then Srv.Http.answer Srv.Http.demo r
        else Srv.Http.errorText 400 "Bad Request" false
      if ex.resp.toList != want.toList || !ex.fin || ex.rst then
        bad := bad + 1
        IO.println s!"FAIL http {n} ×{pieces}: fin {ex.fin} rst {ex.rst}, got {ex.resp.size} bytes, want {want.size}\n{String.fromUTF8! (Bytes.slice ex.resp 0 (min 200 ex.resp.size))}"
  -- the status each request must get, independently of `Http.answer`
  let status : List (String × String) :=
    [("GET /", "200"), ("GET /hello.txt", "200"), ("GET /big.txt", "200"), ("GET /hello.txt?x=1", "200"),
     ("GET /missing", "404"), ("HEAD /", "200"), ("POST /", "501"), ("HTTP/1.0", "200"),
     ("garbage", "400"), ("bad version", "400"), ("version not a digit", "400"), ("too long", "400"), ("long header", "200")]
  for (n, code) in status do
    if let some (_, r) := cases.find? (·.1 == n) then
      let ex := exchange app r 1
      let line := String.fromUTF8! (Bytes.slice ex.resp 0 (min 12 ex.resp.size))
      if line != s!"HTTP/1.1 {code}" then
        bad := bad + 1
        IO.println s!"FAIL http status {n}: got '{line}', want HTTP/1.1 {code}"
    else
      bad := bad + 1
      IO.println s!"FAIL http status: no case {n}"
  -- three clients in a row on one connection: the one in TIME-WAIT is taken
  let (exs, _) := series app seriesReqs
  let okSeries := exs.length == 3 && (exs.zip seriesReqs).all fun (ex, r) =>
    ex.fin && !ex.rst && ex.resp.toList == (Srv.Http.answer Srv.Http.demo r).toList
  if !okSeries then
    bad := bad + 1
    IO.println s!"FAIL http series: {exs.map fun e => (e.fin, e.rst, e.resp.size)}"
  IO.println s!"http: {k} exchanges (13 requests × 1, 3, 7 pieces), response = Http.answer and the expected status, closed by the server, {bad} failures"
  return bad

end Ember.Tests.HttpTests
