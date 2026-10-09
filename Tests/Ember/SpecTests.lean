import LSpec
import Ember.Spec.Gen
import Ember.Trace.Diff
import Ember.Util.Pcap
import Tests.Ember.Fixtures
import Ember.Tools.GenRun

/-!
# M1 tests: `Ember.Spec`, traces, tools, corpus
-/

namespace Ember.Tests.SpecTests
open LSpec Ember Ember.Spec Ember.Trace

def bytes (l : List Nat) : ByteArray := Bytes.ofList (l.map UInt8.ofNat)

/-! ## M1.1 checksum -/

/-- RFC 1071 §3 example: 00 01 f2 03 f4 f5 f6 f7 sums to 0xddf2. -/
def rfc1071 := bytes [0x00, 0x01, 0xf2, 0x03, 0xf4, 0xf5, 0xf6, 0xf7]

/-- Incremental update equals recomputation, on random data. -/
def incrementalAgrees (seed : Nat) : Bool := Id.run do
  let mut r := Rng.ofSeed seed
  for _ in [0:500] do
    let ((d, i, v), r') := (do
      let n ← randRange 2 100
      let d ← randBytes (2 * n)
      let i ← randNat n
      let v ← randNat 65536
      return (d, 2 * i, v.toUInt16) : RandM _).run r
    r := r'
    let hc := Checksum.checksum d 0 d.size
    let d' := Bytes.set16 d i v
    let full := Checksum.checksum d' 0 d'.size
    let inc := Checksum.incremental hc (Bytes.get16 d i) v
    -- one's complement has two zeros; compare as sums
    if !(full == inc || (full == 0xFFFF && inc == 0) || (full == 0 && inc == 0xFFFF)) then return false
  return true

def checksumTests : TestSeq :=
  test "RFC 1071 sum" (Checksum.sum rfc1071 0 8 == 0xddf2) $
  test "RFC 1071 checksum" (Checksum.checksum rfc1071 0 8 == 0x220d) $
  test "odd length pads with zero" (Checksum.sum (bytes [0x12, 0x34, 0x56]) 0 3 == 0x6834) $
  test "RFC 1624 §4 example: HC'=0x0000 not 0xFFFF" (Checksum.incremental 0xDD2F 0x5555 0x3285 == 0x0000) $
  test "incremental = recompute (500 random)" (incrementalAgrees 1) $
  test "data with its checksum verifies" (
    let d := bytes [0x45, 0, 0, 0x54, 0, 0, 0, 0, 64, 1, 0, 0, 10, 0, 0, 1, 10, 0, 0, 2]
    let d := Bytes.set16 d 10 (Checksum.checksum d 0 20)
    Checksum.verifies (Checksum.sum d 0 20))

/-! ## M1.2 SLIP -/

def slipRoundTrip (seed : Nat) : Bool := Id.run do
  let mut r := Rng.ofSeed seed
  for _ in [0:500] do
    let (d, r') := (do
      let n ← randRange 1 mtu
      let mut d ← randBytes n
      -- make END/ESC frequent
      for _ in [0:(← randNat 8)] do
        let i ← randNat n
        d := Bytes.set d i (← randPick #[Slip.END, Slip.ESC])
      return d : RandM _).run r
    r := r'
    if (Slip.decodeAll (Slip.encode d)).map (·.toList) != [d.toList] then return false
  return true

def slipTests : TestSeq :=
  test "decode ∘ encode = id (500 random, END/ESC heavy)" (slipRoundTrip 2) $
  test "END and ESC escaped" ((Slip.encode (bytes [0xC0, 0xDB])).toList ==
    [0xC0, 0xDB, 0xDC, 0xDB, 0xDD, 0xC0]) $
  test "empty frames ignored" (Slip.decodeAll (bytes [0xC0, 0xC0, 0xC0]) == []) $
  test "oversize frame dropped" ((Slip.decodeAll (Slip.encode ⟨Array.replicate (mtu + 1) 1⟩)).length == 0)

/-! ## M1.3–M1.6 headers -/

def udpRoundTrip : Bool :=
  match Udp.parse 1 2 (Udp.emit 1 2 5 7 (bytes [1, 2, 3])) with
  | .ok d => d.sport == 5 && d.dport == 7 && d.data.toList == [1, 2, 3]
  | .error _ => false

def tcpRoundTrip : Bool :=
  let seg : Tcp.Seg := { sport := 7, dport := 9, seq := 5, ack := 6, flags := Tcp.SYN ||| Tcp.ACK,
                         wnd := 256, mss := some 256, data := bytes [9, 8] }
  match Tcp.parse 1 2 (Tcp.emit 1 2 seg) with
  | .ok s => s.seq == 5 && s.ack == 6 && s.flags == seg.flags && s.mss == some 256 && s.data.toList == [9, 8]
  | .error _ => false

def headerTests : TestSeq :=
  let p := Peer.ping 1 1 (Peer.pingPayload 56)
  test "IPv4 validate accepts a ping" ((Ipv4.validate p Peer.ours).toOption.isSome) $
  test "built header verifies" (Checksum.verifies (Checksum.sum (Ipv4.header 6 9 1 2 100) 0 20)) $
  test "DF on UDP/TCP, not ICMP" (Bytes.get (Ipv4.header 17 1 1 2 0) 6 == 0x40 &&
    Bytes.get (Ipv4.header 1 1 1 2 0) 6 == 0) $
  test "UDP emit/parse round trip" udpRoundTrip $
  test "TCP emit/parse round trip with MSS" tcpRoundTrip $
  test "options of every length skipped, MSS found" (
    Tcp.parseMss (Bytes.ofList ((List.replicate 20 0) ++ [1, 3, 3, 7, 4, 2, 8, 10, 0,0,0,0,0,0,0,0, 2, 4, 1, 0]
      |>.map UInt8.ofNat)) 40 == some 256) $
  test "back-off table" ((List.range 9).map rto == [3, 6, 12, 24, 48, 48, 48, 48, 48])

/-! ## M1.0 trace format and tools -/

def sampleTrace : Trace :=
  Spec.run {} #[Peer.slip (Peer.ping 1 1 (Peer.pingPayload 56)), .tick,
                Peer.slip (Peer.udp 4000 7 (Peer.str "x"))]

def roundTrip (t : Trace) : Bool :=
  match Trace.parse t.print with
  | .ok t' => t'.print == t.print && t'.header == t.header
  | .error _ => false

/-- Change one byte of the first `tx` line. -/
def oneByteOff (t : Trace) (off : Nat) : Trace := Id.run do
  let mut ls := t.lines
  for i in [0:ls.size] do
    if let .tx b := ls[i]!.ev then
      ls := ls.set! i { ls[i]! with ev := .tx (Bytes.set b off (Bytes.get b off ^^^ 1)) }
      break
  return { t with lines := ls }

/-- Give the first transmitted packet another IP identification (checksum fixed). -/
def otherIpId (t : Trace) : Trace := Id.run do
  let mut ls := t.lines
  for i in [0:ls.size] do
    if let .tx b := ls[i]!.ev then
      let p := (Slip.decodeAll b).head!
      let p := Peer.fixIpChecksum (Bytes.set16 p 4 0xBEEF)
      ls := ls.set! i { ls[i]! with ev := .tx (Slip.encode p) }
      break
  return { t with lines := ls }

def traceTests : TestSeq :=
  test "parse ∘ print = id" (roundTrip sampleTrace) $
  test "header keys round trip" (roundTrip { sampleTrace with header := { link := "eth", mtu := 576, dhcp := true, mask := ["ipv4.id"] } }) $
  test "equal traces agree" ((diff sampleTrace sampleTrace).equal) $
  test "one-byte difference found at its offset" (
    let r := diff sampleTrace (oneByteOff sampleTrace 9) { observable := true }
    !r.equal && (r.report.splitOn "first differing byte at offset 9").length == 2 &&
      (r.report.splitOn "ipv4.ttl").length == 2) $
  test "IP-id mask hides only the identification" (
    let t := otherIpId sampleTrace
    !(diff sampleTrace t { observable := true }).equal &&
    (diff sampleTrace t { observable := true, mask := ["ipv4.id"] }).equal &&
      !(diff sampleTrace (oneByteOff sampleTrace 9) { observable := true, mask := ["ipv4.id"] }).equal) $
  test "pcap: header + 4 records" (
    let p := Pcap.ofTrace sampleTrace
    p.size == 24 + (16 + 84) * 2 + (16 + 29) * 2 && Bytes.get p 20 == 101)

def unitTests : TestSeq :=
  group "M1.1 checksum" checksumTests ++ group "M1.2 SLIP" slipTests ++
  group "M1.3-6 headers" headerTests ++ group "M1.0 trace" traceTests

/-! ## Corpus, scenarios, generators (IO) -/

partial def traceFiles (d : System.FilePath) : IO (Array System.FilePath) := do
  if !(← d.pathExists) then return #[]
  let mut out := #[]
  for e in ← d.readDir do
    if ← e.path.isDir then out := out ++ (← traceFiles e.path)
    else if e.path.extension == some "trace" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

/-- Replay every fixture through the Spec; also checks parse ∘ print. -/
def corpus : IO Nat := do
  let mut bad := 0
  let files := (← traceFiles "Tests/Ember/corpus") ++ (← traceFiles "Tests/Ember/regress")
  for f in files do
    let t ← Trace.readFile f
    let r := Spec.run (Spec.Config.ofHeader t.header) t.inputs
    let d := diff t r { observable := true }
    if !d.equal then
      bad := bad + 1
      IO.println s!"FAIL corpus {f}\n{d.report}"
    if !roundTrip t then
      bad := bad + 1
      IO.println s!"FAIL parse ∘ print {f}"
  IO.println s!"corpus: {files.size} fixtures replayed, {bad} failures"
  return bad

def generated (count : Nat) : IO Nat := do
  let mut bad := 0
  for p in ["icmp", "udp", "tcp"] do
    let st ← Tools.GenRun.runProto p count 1
    IO.println s!"generated {p}: {st.sessions} sessions, {st.failures} failures"
    bad := bad + st.failures
  return bad

/-- M1.10: the corpus through the `ember-host` binary (when built). -/
def hostBinary : IO Nat := do
  let exe : System.FilePath := ".lake/build/bin/ember-host"
  if !(← exe.pathExists) then
    IO.println "ember-host: binary not built, skipped (lake build ember-host)"
    return 0
  let mut bad := 0
  let mut n := 0
  for f in ← traceFiles "Tests/Ember/corpus" do
    let t ← Trace.readFile f
    if t.header.link != "slip" || t.inputs.any (· == .tick) then continue
    let input := t.inputs.foldl (fun acc i => match i with | .rx b => acc ++ b | .tick => acc) .empty
    let child ← IO.Process.spawn { cmd := exe.toString, args := #["--tick-ms", "0"],
                                   stdin := .piped, stdout := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.write input
    stdin.flush
    let out ← IO.asTask child.stdout.readBinToEnd
    let _ ← (pure () : IO Unit)
    -- closing stdin ends the host
    let _ := stdin
    let r ← IO.ofExcept out.get
    discard <| child.wait
    let expect := (Spec.run (Spec.Config.ofHeader t.header) t.inputs).lines.foldl
      (fun acc l => match l.ev with | .tx b => acc ++ b | _ => acc) ByteArray.empty
    n := n + 1
    if r.toList != expect.toList then
      bad := bad + 1
      IO.println s!"FAIL ember-host {f}: {r.size} bytes vs {expect.size} in-process"
  IO.println s!"ember-host: {n} fixtures through the binary, {bad} failures"
  return bad

/-- Is a program on the PATH?  Tools-dependent tests skip without it. -/
def onPath (prog : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {prog}"] }
  return r.exitCode == 0

/-- M1.0: pcap of fixtures opens in tshark with valid checksums. -/
def pcapTshark : IO Nat := do
  if !(← onPath "tshark") then
    IO.println "tshark: not on PATH, skipped (nix-shell provides it)"
    return 0
  let mut bad := 0
  let files := #["Tests/Ember/corpus/tcp/linux-nc-echo.trace", "Tests/Ember/corpus/arp/linux-eth-ping.trace",
                 "Tests/Ember/corpus/udp/linux-udp-echo.trace"]
  for f in files do
    let t ← Trace.readFile f
    let tmp : System.FilePath := ".lake/ember-test.pcap"
    IO.FS.writeBinFile tmp (Pcap.ofTrace t)
    let r ← IO.Process.output { cmd := "tshark", args := #["-r", tmp.toString, "-T", "fields",
      "-o", "ip.check_checksum:TRUE", "-o", "tcp.check_checksum:TRUE", "-o", "udp.check_checksum:TRUE",
      "-e", "ip.checksum.status", "-e", "tcp.checksum.status", "-e", "udp.checksum.status"] }
    let rows := (r.stdout.splitOn "\n").filter (· ≠ "")
    let frames := t.lines.foldl (fun n l => match l.ev with
      | .rx b | .tx b => n + (Pretty.frames t.header.link b).length | _ => n) 0
    let allGood := rows.all fun row => (Str.words row).all (· == "1")
    if r.exitCode != 0 || rows.length != frames || !allGood then
      bad := bad + 1
      IO.println s!"FAIL tshark {f}: {rows.length} rows for {frames} frames\n{r.stdout}{r.stderr}"
  IO.println s!"tshark: {files.size} pcaps decoded, {bad} failures"
  return bad

def main : IO UInt32 := do
  let mut bad := 0
  bad := bad + (← pcapTshark)
  bad := bad + (← corpus)
  let sc ← Fixtures.runAll (write := false) (verbose := false)
  IO.println s!"scenarios: {Tests.Scenarios.all.length} checked, {sc} failures"
  bad := bad + sc
  bad := bad + (← generated 1000)
  bad := bad + (← hostBinary)
  return if bad == 0 then 0 else 1

end Ember.Tests.SpecTests
