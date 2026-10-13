import Ember.Z80.StackBound
import Ember.Z80.Check
import Ember.Lang.Examples
import Ember.Z80.Asm
import Ember.Net.Loop
import Ember.Net.Main
import Ember.Z80.IRInterp
import Ember.Z80.IRSem
import Ember.Z80.Codegen
import Ember.Z80.RtCheck
import Ember.Z80.Target
import Ember.Tools.NetCheck
import Ember.Tools.Fuzz
import Ember.Util.Rand

/-!
# `ember-z80` — the Z80 model as a tool (M4z, M6.1)

```
ember-z80 check [PROGRAMS] [--len N] [--seed S]     the CPU model against z88dk-ticks
ember-z80 replay IMAGE.ihx PATH... [--out DIR]      fixtures on the image: target trace = fixture
ember-z80 echo IMAGE.ihx [--bytes N] [--seed S]     byte-echo stress test (M4z.2)
ember-z80 slip IMAGE.ihx [--frames N] [--seed S]    SLIP loopback through the Ember SLIP code
ember-z80 ping IMAGE.ihx                            T-states per 56-byte ICMP echo
ember-z80 fuzz [COUNT] [--seed S] [--u64]           random programs: interpreter = SDCC's Z80 code
ember-z80 run IMAGE.ihx FIXTURE --itrace FILE [--trace-from STEP]
                                                    instruction trace with symbols (IMAGE.noi)
```

`IMAGE.ihx` is what `runtime/z80/Makefile` builds.
-/

namespace Ember.Tools.Z80
open Ember Ember.Trace Ember.Z80

def loadImage (path : String) : IO Machine := do
  match Machine.ofIhx (← IO.FS.readFile path) with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok m =>
    match Target.boot m with
    | .ok m => return m
    | .error e => throw (IO.userError s!"{path}: boot: {e}")

partial def traceFiles (d : System.FilePath) : IO (Array System.FilePath) := do
  if !(← d.isDir) then return #[d]
  let mut out := #[]
  for e in ← d.readDir do
    if ← e.path.isDir then out := out ++ (← traceFiles e.path)
    else if e.path.extension == some "trace" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

/-- Fixtures on a fresh machine each: number run, skipped, failed, and T-states. -/
def replayFiles (image : String) (paths : List String) (outDir : Option String) (verbose := false) :
    IO (Nat × Nat × Nat × Nat) := do
  let m0 ← loadImage image
  let mut ran := 0
  let mut skipped := 0
  let mut bad := 0
  let mut cycles := 0
  for p in paths do
    for f in ← traceFiles p do
      let t ← Trace.readFile f
      if !NetCheck.supported t.header then skipped := skipped + 1; continue
      let r := Target.replay m0 { t.header with impl := "z80", profile := "sdcc-z80" } t.inputs
      ran := ran + 1
      cycles := cycles + (r.machine.cpu.cycles - m0.cpu.cycles).toNat
      if let some d := outDir then
        IO.FS.createDirAll d
        let comps := f.components
        let name := "-".intercalate (comps.drop (comps.length - 2))
        IO.FS.writeFile (System.FilePath.mk d / name) r.trace.print
      let d := diff t r.trace { observable := true, drops := true }
      if r.error.isSome || !d.equal || r.machine.overruns != 0 then
        bad := bad + 1
        IO.println s!"FAIL {f}{match r.error with | some e => s!": {e}" | none => ""}"
        if r.machine.overruns != 0 then IO.println s!"  {r.machine.overruns} receive overruns"
        IO.println d.report
      else if verbose then IO.println s!"ok   {f}"
  return (ran, skipped, bad, cycles)

def slipEncode (p : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.empty.push 0xC0
  for c in p do
    if c == 0xC0 then o := (o.push 0xDB).push 0xDC
    else if c == 0xDB then o := (o.push 0xDB).push 0xDD
    else o := o.push c
  return o.push 0xC0

/-- M4z.2: random bytes in bursts — at line rate (640 T-states a byte),
slower, and at twice the line rate, which the main loop cannot follow, so
that the ring fills and RTS has to hold the sender — with the machine
sometimes left running between bursts instead of settling. -/
def echo (image : String) (n seed : Nat) : IO UInt32 := do
  let mut m ← loadImage image
  let mut rng := Rng.ofSeed seed
  let mut sent := ByteArray.empty
  let mut got := ByteArray.empty
  while sent.size < n do
    let ((len, gap, settleNow, run), r) := (do
      let len ← randPick #[1, 1, 2, 7, 64, 128, 129, 300, 700, 1500]
      let gap ← randPick #[320, 640, 640, 700, 1000, 5000]
      return (len, gap, ← randBool, ← randNat 20000) : RandM _).run rng
    rng := r
    let (chunk, r) := (randBytes (min len (n - sent.size))).run rng
    rng := r
    sent := sent ++ chunk
    m := { m.send chunk with rxGap := UInt64.ofNat gap }
    if settleNow then
      m := (m.runIdle).1
    else
      for _ in [0:run] do m := m.step
  let (m', done) := m.runIdle
  let (out, m'') := m'.takeTx
  got := got ++ out
  if !done || m''.dead then IO.println "FAIL echo: the machine did not come to rest"; return 1
  if got.toList != sent.toList then
    IO.println s!"FAIL echo: {got.size} bytes back of {sent.size}, first difference at {(List.range (min got.size sent.size)).find? (fun i => got[i]! != sent[i]!)}"
    return 1
  if m''.overruns != 0 then IO.println s!"FAIL echo: {m''.overruns} overruns"; return 1
  IO.println s!"echo: {sent.size} bytes back in order; {m''.interrupts} interrupts, 0 overruns, RTS raised {m''.holds} times, {m''.cpu.cycles} T-states"
  return 0

def slip (image : String) (frames seed : Nat) : IO UInt32 := do
  let mut m ← loadImage image
  let mut rng := Rng.ofSeed seed
  for k in [0:frames] do
    let (payload, r) := (do
      let n ← if ← randBool 30 then randPick #[1, 2, 20, 84, 295, 296] else randRange 1 296
      let mut b := ByteArray.empty
      for _ in [0:n] do
        b := b.push (← randPick #[0xC0, 0xDB, 0xDC, 0xDD, (← randNat 256).toUInt8, (← randNat 256).toUInt8])
      return b : RandM _).run rng
    rng := r
    let wire := slipEncode payload
    match Target.feed m (.rx wire) with
    | .error e => IO.println s!"FAIL slip frame {k}: {e}"; return 1
    | .ok (m', evs) =>
      m := m'
      if evs != [.tx wire] then
        IO.println s!"FAIL slip frame {k} ({payload.size} bytes): got {evs.map (·.kind)}"
        return 1
  match Target.feed m (.rx (slipEncode (ByteArray.mk (Array.replicate 297 0)))) with
  | .ok (m', [.drop "oversize-frame"]) => m := m'
  | .ok (_, evs) => IO.println s!"FAIL slip: oversize frame gave {evs.map (·.kind)}"; return 1
  | .error e => IO.println s!"FAIL slip: {e}"; return 1
  if m.overruns != 0 then IO.println s!"FAIL slip: {m.overruns} overruns"; return 1
  IO.println s!"slip: {frames} random frames echoed, oversize frame dropped; {m.interrupts} interrupts, RTS raised {m.holds} times"
  return 0

/-- A 56-byte echo request from 10.0.0.2 with the given sequence number. -/
def pingRequest (seq : Nat) : ByteArray := Id.run do
  let sum16 (b : ByteArray) : UInt16 := Id.run do
    let mut s : Nat := 0
    for i in [0:b.size / 2] do s := s + b[2 * i]!.toNat * 256 + b[2 * i + 1]!.toNat
    if b.size % 2 == 1 then s := s + b[b.size - 1]!.toNat * 256
    while s > 0xFFFF do s := s % 65536 + s / 65536
    return UInt16.ofNat (0xFFFF - s)
  let mut icmp := ByteArray.mk #[8, 0, 0, 0, 0x12, 0x34, UInt8.ofNat (seq / 256), UInt8.ofNat seq]
  for i in [0:56] do icmp := icmp.push (UInt8.ofNat i)
  let c := sum16 icmp
  icmp := (icmp.set! 2 (c >>> 8).toUInt8).set! 3 c.toUInt8
  let total := 20 + icmp.size
  let mut ip := ByteArray.mk #[0x45, 0, UInt8.ofNat (total / 256), UInt8.ofNat total, 0, UInt8.ofNat seq, 0, 0, 64, 1, 0, 0,
                               10, 0, 0, 2, 10, 0, 0, 1]
  let h := sum16 ip
  ip := (ip.set! 10 (h >>> 8).toUInt8).set! 11 h.toUInt8
  return ip ++ icmp

/-- T-states from the first byte of a ping to idle again (the receive
interrupts, the stack, the transmission), the wait for the bytes still on
the wire included: the median of eight. -/
def pingCycles (image : String) : IO Nat := do
  let mut m ← loadImage image
  let mut costs : Array Nat := #[]
  for k in [0:9] do
    let before := m.cpu.cycles
    match Target.feed m (.rx (slipEncode (pingRequest (k + 1)))) with
    | .ok (m', evs) =>
      if !evs.any (fun e => match e with | .tx _ => true | _ => false) && m'.tx.isEmpty then
        throw (IO.userError "ping not answered")
      m := m'
      if k > 0 then costs := costs.push (m.cpu.cycles - before).toNat
    | .error e => throw (IO.userError s!"ping: {e}")
  return (costs.qsort (· < ·))[costs.size / 2]!

/-- Symbols of a NoICE file (`DEF name 0xADDR`), sorted by address. -/
def readSymbols (path : System.FilePath) : IO (Array (Nat × String)) := do
  if !(← path.pathExists) then return #[]
  let mut out := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    match line.splitOn " " with
    | ["DEF", name, addr] =>
      if let some b := Bytes.ofHex ((addr.drop 2).toString) then
        if b.size == 2 then out := out.push (b[0]!.toNat * 256 + b[1]!.toNat, name)
    | _ => pure ()
  return out.qsort (fun a b => a.1 < b.1)

def symbolAt (syms : Array (Nat × String)) (pc : Nat) : String := Id.run do
  let mut best : Option (Nat × String) := none
  for (a, n) in syms do
    if a ≤ pc && !n.startsWith "s__" && !n.startsWith "l__" && !n.startsWith "." then best := some (a, n)
  match best with
  | some (a, n) => if a == pc then n else s!"{n}+{pc - a}"
  | none => ""

/-- Replay a fixture writing every instruction from input step `from` on. -/
def instrTrace (image fixture out : String) (fromStep : Nat) : IO UInt32 := do
  let syms ← readSymbols ((System.FilePath.mk image).withExtension "noi")
  let t ← Trace.readFile fixture
  let mut m ← loadImage image
  let h ← IO.FS.Handle.mk out .write
  let ins := t.inputs
  for i in [0:ins.size] do
    m := match ins[i]! with | .rx b => m.send b | .tick => m.tick
    if i ≥ fromStep then h.putStrLn s!"; step {i}"
    let mut n := 0
    while !(m.idle || m.dead) && n < 50000000 do
      if i ≥ fromStep && !m.cpu.halted then
        let c := m.cpu
        let bytes := " ".intercalate ((List.range 4).map fun k => Bytes.hex8 (c.rd (c.pc + UInt16.ofNat k)))
        h.putStrLn s!"{Check.hex4 c.pc.toNat} {bytes}  af={Check.hex4 c.af.toNat} bc={Check.hex4 c.bc.toNat} de={Check.hex4 c.de.toNat} hl={Check.hex4 c.hl.toNat} ix={Check.hex4 c.ix.toNat} sp={Check.hex4 c.sp.toNat} t={c.cycles}  {symbolAt syms c.pc.toNat}"
      m := m.step
      n := n + 1
    m := (m.takeTx).2
    m := (m.takeDbg).2
  h.flush
  IO.println s!"wrote {out}"
  return 0

/-! ## Any Ember program on the Z80 (M4z.1) -/

def sdccAvailable : IO Bool := do
  for (cmd, arg) in [("sdcc", "--version"), ("sdasz80", "-h")] do
    let ok ← try discard <| IO.Process.output { cmd, args := #[arg] }; pure true catch _ => pure false
    if !ok then return false
  return true

/-- SDCC flags, as `runtime/z80/Makefile`: warnings are errors. -/
def sdccFlags : Array String :=
  #["-mz80", "--std-c99", "--opt-code-size", "--Werror", "-Iruntime/common"]

/-- For generated programs: warnings are read from the output instead. -/
def sdccProgFlags : Array String := sdccFlags.filter (· != "--Werror")

/-- SDCC's "the optimiser changed the control flow" (110) or "unreachable
code" (126).  SDCC 4.6 says so when it has removed live code — a dead
local in an `if` in a loop deletes the rest of the function
(`docs/Ember-plan.md`, decision log) — so the Makefile makes these
errors.  Random programs are full of constant conditions and nearly all
draw one, so they run all the same, and a divergence of a flagged program
is counted apart. -/
def saysUnreachable (out : String) : Bool :=
  (out.splitOn "warning 110").length > 1 || (out.splitOn "warning 126").length > 1

def otherWarning (out : String) : Bool :=
  (out.splitOn "warning ").length - 1 >
    (out.splitOn "warning 110").length - 1 + ((out.splitOn "warning 126").length - 1) +
      ((out.splitOn "warning 346").length - 1)

/-- Build one harness image holding the programs (emitted for the
`sdcc-z80` profile, compiled concurrently).  Programs on which SDCC
stops with an internal error are left out and named in the result (third
component); the fourth names those it calls partly unreachable. -/
def buildHarness (dir : System.FilePath) (progs : List (String × Lang.Prog)) :
    IO (Except String (Machine × List String × List String × List String)) := do
  IO.FS.createDirAll dir
  let rel (n : String) := (dir / s!"{n}.rel").toString
  let mut units : Array (String × Task (Except IO.Error IO.Process.Output)) := #[]
  for (n, p) in progs do
    match C.emitC p { profile := .sdccZ80, namePrefix := n ++ "_", lines := false } with
    | .error e => return .error s!"emit {n}: {e}"
    | .ok c =>
      IO.FS.writeFile (dir / s!"{n}.c") c
      let args := sdccProgFlags ++ #["-c", (dir / s!"{n}.c").toString, "-o", rel n]
      let t ← IO.asTask (IO.Process.output { cmd := "sdcc", args })
      units := units.push (n, t)
  let mut good : List String := []
  let mut crashed : List String := []
  let mut refused : List String := []
  for (n, t) in units do
    match ← IO.wait t with
    | .ok r =>
      let out := r.stderr ++ r.stdout
      if (out.splitOn "Internal Error").length > 1 then crashed := crashed ++ [n]
      else if r.exitCode != 0 || otherWarning out then return .error s!"{n}: {out}"
      else
        good := good ++ [n]
        if saysUnreachable out then refused := refused ++ [n]
    | .error e => return .error (toString e)
  if good.isEmpty then return .error s!"sdcc: no program left (internal error: {crashed})"
  IO.FS.writeFile (dir / "glue.c") (C.glue (good.map (· ++ "_")))
  let fixed : List (String × Array String) :=
    [("sdcc", sdccFlags ++ #["-c", (dir / "glue.c").toString, "-o", rel "glue"]),
     ("sdcc", sdccFlags ++ #["-c", "runtime/z80/harness.c", "-o", rel "harness"]),
     ("sdcc", sdccFlags ++ #["-c", "runtime/z80/mmio.c", "-o", rel "mmio"]),
     ("sdasz80", #["-g", "-o", rel "crt0", "runtime/z80/crt0.s"])]
  let tasks ← fixed.mapM fun (cmd, args) => IO.asTask (IO.Process.output { cmd, args })
  for t in tasks do
    match ← IO.wait t with
    | .ok r => if r.exitCode != 0 then return .error s!"{r.stderr}{r.stdout}"
    | .error e => return .error (toString e)
  let ihx := dir / "harness.ihx"
  -- crt0 first: its data (the ring) must start the RAM
  let r ← IO.Process.output { cmd := "sdcc", args := #["-mz80", "--no-std-crt0", "--code-loc", "0x0100",
    "--data-loc", "0x8000", rel "crt0", rel "harness", rel "mmio", rel "glue"] ++ (good.map rel).toArray ++
    #["-o", ihx.toString] }
  if r.exitCode != 0 then return .error s!"link: {r.stderr}{r.stdout}"
  let text ← IO.FS.readFile ihx
  match Machine.ihxExtent text with
  | .error e => return .error e
  | .ok (_, top) =>
    if top > 0x8000 then return .error s!"image ends at {top}: it does not fit the 32 KB of ROM"
    return (Machine.ofIhx text).map (·, good, crashed, refused)

/-- Program `k` of a harness image on the inputs. -/
def runHarness (m : Machine) (k : Nat) (p : Lang.Prog) (ins : Array Input) : Except String Trace :=
  Target.runHarness m k { impl := "z80", profile := "sdcc-z80" } ins p.dropReasons.toArray p.notes.toArray 20000000

structure Outcome where
  ran : Nat := 0
  /-- Programs whose Z80 trace differs from the interpreter's. -/
  bad : Array String := #[]
  /-- Programs SDCC could not compile (internal compiler error). -/
  crashed : Array String := #[]
  /-- Diverging programs that SDCC called partly unreachable (110, 126). -/
  refused : Array String := #[]

/-- Programs with their inputs, in images of `per` programs. -/
def compareWithInterp (dir : System.FilePath) (cases : Array (String × Lang.Prog × Array Input)) (per : Nat := 8)
    (verbose := true) : IO Outcome := do
  let mut o : Outcome := {}
  let mut i := 0
  while i < cases.size do
    let group := cases.extract i (min cases.size (i + per))
    i := i + per
    -- several inputs for one program share its code
    let mut progs : List (String × Lang.Prog) := []
    for (n, p, _) in group do
      if !progs.any (·.1 == n) then progs := progs ++ [(n, p)]
    match ← buildHarness dir progs with
    | .error e =>
      if (e.splitOn "sdcc: no program left").length > 1 then
        o := { o with crashed := o.crashed ++ group.map (·.1) }
      else
        IO.println s!"FAIL building {progs.map (·.1)}:\n{e.take 3000}"
        o := { o with bad := o.bad ++ group.map (·.1) }
    | .ok (m, good, crashed, refused) =>
      o := { o with crashed := o.crashed ++ crashed.toArray }
      for (n, p, ins) in group do
        let some k := good.findIdx? (· == n) | continue
        o := { o with ran := o.ran + 1 }
        match Fuzz.interp p ins, runHarness m k p ins with
        | .ok it, .ok zt =>
          if !Fuzz.agree it zt && refused.contains n then
            o := { o with refused := o.refused.push n }
          else if !Fuzz.agree it zt then
            o := { o with bad := o.bad.push n }
            if verbose then
              IO.println s!"FAIL {n}: interpreter vs Z80\n{(diff it zt { observable := false }).report}"
        | .error e, _ => o := { o with bad := o.bad.push n }; IO.println s!"FAIL {n}: interpreter: {e}"
        | _, .error e =>
          if refused.contains n then o := { o with refused := o.refused.push n }
          else o := { o with bad := o.bad.push n }; IO.println s!"FAIL {n}: Z80: {e}"
  return o

/-- Does the program's Z80 trace differ from the interpreter's? -/
def diverges (dir : System.FilePath) (p : Lang.Prog) (ins : Array Input) : IO Bool := do
  let .ok it := Fuzz.interp p ins | return false
  match ← buildHarness dir [("p", p)] with
  | .error _ => return false
  | .ok (m, _, _, _) =>
    match runHarness m 0 p ins with
    | .ok zt => return !Fuzz.agree it zt
    | .error _ => return true

/-- `count` random programs (`Ember.Lang.Gen`), each on its random inputs;
a diverging one is shrunk and printed with its C.  Without `u64`
arithmetic unless `with64`: SDCC 4.6 miscompiles it (found by this
fuzzer; `docs/Ember-plan.md`, decision log). -/
def fuzz (count seed : Nat) (with64 := false) (verbose := false) : IO UInt32 := do
  unless ← sdccAvailable do
    IO.println "sdcc not installed (run inside nix-shell)"
    return 2
  let all := (Array.range count).map fun i =>
    let (p, ins) := if with64 then Lang.Gen.sample (seed + i) else Lang.Gen.sample (seed + i) #[.w8, .w16, .w32]
    (s!"p{seed + i}", p, ins)
  -- the generator's width list covers arithmetic; `u64` locals, casts and
  -- copies remain, and SDCC 4.6 miscompiles those too (a dead `u64` local
  -- in a loop can delete the rest of the function), so such programs are
  -- left out: only the declaration of the global `g64` may say `u64`
  let cases := if with64 then all else all.filter fun (_, p, _) => (p.pretty.splitOn "u64").length ≤ 2
  let o ← compareWithInterp ".lake/ember-z80-fuzz" cases 8 verbose
  for n in o.bad.toList.take 5 do
    if let some (_, p, ins) := cases.find? (·.1 == n) then
      let dir : System.FilePath := ".lake/ember-z80-fuzz/shrink"
      if ← diverges dir p ins then
        let small ← Lang.Gen.shrinkProg (diverges dir · ins) p
        IO.println s!"{n} shrunk from {Lang.Gen.progSize p} to {Lang.Gen.progSize small} statements:\n{small.pretty}"
        IO.println s!"inputs:\n{(Trace.ofSteps {} (ins.map (·, []))).print}"
        if verbose then
          if let .ok c := C.emitC small { profile := .sdccZ80, lines := false } then IO.println s!"C:\n{c}"
        if let .ok it := Fuzz.interp small ins then IO.println s!"interpreter:\n{it.print}"
        if let .ok (m, _, _, _) ← buildHarness dir [("p", small)] then
          if let .ok zt := runHarness m 0 small ins then IO.println s!"z80:\n{zt.print}"
  IO.println (s!"z80 fuzz: {o.ran} random programs{if with64 then "" else s!" ({all.size - cases.size} with u64 left out)"}: interpreter = SDCC's Z80 code on the model; " ++
    s!"{o.bad.size} failures {if o.bad.isEmpty then "" else toString o.bad}; " ++
    s!"{o.refused.size} more differ where SDCC warned of unreachable code (its bug) {if o.refused.isEmpty then "" else toString o.refused}; " ++
    s!"{o.crashed.size} not run (SDCC internal error)")
  return if o.bad.isEmpty then 0 else 1

/-- M6.2: every instruction form the assembler accepts, against
`z88dk-z80asm`. -/
def asmCheck : IO UInt32 := do
  let dir : System.FilePath := ".lake/ember-z80-asm"
  IO.FS.createDirAll dir
  let items := Asm.allForms
  let origin := 0x100
  let ours ← match Asm.assemble items origin with
    | .ok a => pure a
    | .error e => IO.println s!"FAIL assemble: {e}"; return 1
  IO.FS.writeFile (dir / "all.asm") (Asm.source items origin)
  let r ← try IO.Process.output { cmd := "z88dk-z80asm", args := #["-b", "-mz80", "all.asm"], cwd := dir }
    catch _ => IO.println "z88dk-z80asm not installed (run inside nix-shell)"; return 2
  if r.exitCode != 0 then
    IO.println s!"FAIL z88dk-z80asm rejects what Ember.Z80.Asm accepts:\n{(r.stderr ++ r.stdout).take 3000}"
    return 1
  let theirs ← IO.FS.readBinFile (dir / "all.bin")
  let n := items.filter (fun it => match it with | .ins _ => true | _ => false) |>.length
  let mut k := 0
  for it in items do
    let a := ours.addrs[k]! - origin
    let b := (if k + 1 < items.length then ours.addrs[k + 1]! else origin + ours.bytes.size) - origin
    let hex (x : ByteArray) := " ".intercalate ((x.extract a b).toList.map fun v => String.ofList (Nat.toDigits 16 v.toNat))
    if ours.bytes.extract a b != theirs.extract a b then
      IO.println s!"FAIL {it.text.trimAscii} at {a + origin}: Ember {hex ours.bytes}, z88dk-z80asm {hex theirs}"
      return 1
    k := k + 1
  if ours.bytes.size != theirs.size then
    IO.println s!"FAIL sizes differ: {ours.bytes.size} vs {theirs.size}"
    return 1
  IO.println s!"z80 assembler vs z88dk-z80asm: {n} instruction forms, {ours.bytes.size} bytes, identical"
  return 0

/-- Interpreter vs IR interpreter on one program. -/
def irDiverges (p : Lang.Prog) (ins : Array Input) : Bool :=
  -- as lowered, and with calls replaced by bodies (`IR.inlineCalls`)
  [false, true].any fun inline =>
    -- the IR interpreter, and the IR's total semantics (`IR.Sem`, what the proofs of M7 unfold)
    [IR.run p ins (inline := inline), IR.Sem.run p ins (inline := inline)].any fun r =>
      match Fuzz.interp p ins, r with
      | .ok a, .ok b => !Fuzz.agree a b
      | .ok _, .error _ => true
      | .error _, _ => false

/-- M6.3: random programs, Ember interpreter = IR interpreter (which also
runs the frame layout and its validator). -/
def irFuzz (count seed : Nat) : IO UInt32 := do
  let mut bad := 0
  for i in [0:count] do
    let (p, ins) := Lang.Gen.sample (seed + i)
    if irDiverges p ins then
      bad := bad + 1
      if bad ≤ 3 then
        let small ← Lang.Gen.shrinkProg (fun q => pure (irDiverges q ins)) p
        IO.println s!"FAIL p{seed + i}, shrunk to {Lang.Gen.progSize small} statements:\n{small.pretty}"
        IO.println s!"inputs:\n{(Trace.ofSteps {} (ins.map (·, []))).print}"
        if let .ok q := small.check then
          if let .ok ir := IR.lower q then IO.println ir.text
        if let .ok it := Fuzz.interp small ins then IO.println s!"interpreter:\n{it.print}"
        match IR.run small ins with
        | .ok t => IO.println s!"IR:\n{t.print}"
        | .error e => IO.println s!"IR: {e}"
  IO.println s!"z80 IR: {count} random programs: Ember interpreter = IR interpreter = IR semantics (IR.Sem); {bad} failures"
  return if bad == 0 then 0 else 1

/-- The stack (`Ember.Net`) on the IR interpreter: fixtures. -/
def irReplay (paths : List String) : IO UInt32 := do
  let mut ran := 0
  let mut bad := 0
  for p in paths do
    for f in ← traceFiles p do
      let t ← Trace.readFile f
      if !NetCheck.supported t.header then continue
      ran := ran + 1
      let mut ok := true
      for (what, r) in [("IR interpreter", IR.run Net.prog t.inputs { t.header with impl := "ir" }),
                        ("IR semantics", IR.Sem.run Net.prog t.inputs { t.header with impl := "irsem" })] do
        match r with
        | .error e => ok := false; IO.println s!"FAIL {f}: {what}: {e}"
        | .ok r =>
          let d := diff t r { observable := true, drops := true }
          if !d.equal then
            ok := false
            IO.println s!"FAIL {f}: {what}\n{d.report}"
      unless ok do bad := bad + 1
  IO.println s!"z80 IR replay: {ran - bad} of {ran} fixtures: the trace of the IR interpreter and of the IR semantics (IR.Sem) = fixture"
  return if bad == 0 then 0 else 1

/-- The IR of the stack, the examples and `count` random programs, with
and without inlining: to compare two versions of the lowering. -/
def irDump (count seed : Nat) : IO UInt32 := do
  let mut progs : List (String × Lang.Prog) :=
    [("net", Net.prog), ("sliploop", Net.Loop.prog), ("eth", Net.Eth.prog), ("dhcp", Net.Eth.progDhcp)] ++
      Lang.Examples.all
  for i in [0:count] do progs := progs ++ [(s!"p{seed + i}", (Lang.Gen.sample (seed + i)).1)]
  for (n, p) in progs do
    match p.check with
    | .error e => IO.println s!"== {n}: {e}"
    | .ok q =>
      for inline in [false, true] do
        match IR.lower q inline with
        | .error e => IO.println s!"== {n} inline={inline}: {e}"
        | .ok ir =>
          IO.println s!"== {n} inline={inline}"
          for f in ir.fns do
            IO.println s!"{f.text}  frame={f.frame} tmps={f.tmps} reg={repr f.regParam} inl={f.inlined} dead={f.dead}"
          for g in ir.globals do
            IO.println s!"  global {g.name} {g.size} {g.const} {(g.init.map (·.toList)).getD []}"
  return 0

/-! ## The own back end (plan M6) -/

/-- Compile with the own back end for the test harness. -/
def ownImage (p : Lang.Prog) (annotate := false) (passes := true) : Except String Codegen.Image := do
  let p ← match p.check with
    | .ok p => pure p
    | .error e => throw e.toString
  Codegen.build (← IR.lower p) Runtime.harness (annotate := annotate) (passes := passes)

def machineOf (img : Codegen.Image) : Machine :=
  { cpu := { (({} : Cpu).load img.origin img.bytes) with ramStart := 0x8000 } }

/-- A program through the own back end, on the model, with the harness. -/
def ownRun (p : Lang.Prog) (ins : Array Input) (budget : Nat := 20000000) (passes := true) :
    Except String Trace := do
  let img ← ownImage p (passes := passes)
  Target.runHarness (machineOf img) 0 { impl := "z80-own", profile := "z80" } ins
    p.dropReasons.toArray p.notes.toArray budget

def ownDiverges (p : Lang.Prog) (ins : Array Input) (passes := true) : Bool :=
  match Fuzz.interp p ins, ownRun p ins (passes := passes) with
  | .ok a, .ok b => !Fuzz.agree a b
  | .ok _, .error _ => true
  | .error _, _ => false

/-- Listing: the items of an image with their addresses. -/
def listing (img : Codegen.Image) : String := Id.run do
  let addrs := match Asm.assemble img.items with
    | .ok a => a.addrs
    | .error _ => #[]
  let mut out := ""
  let mut k := 0
  for it in img.items do
    match it with
    | .equ .. => pure ()
    | .comment _ => out := out ++ s!"\t\t{it.text}\n"
    | _ => out := out ++ s!"{String.ofList (Nat.toDigits 16 (addrs.getD k 0))}\t{it.text}\n"
    k := k + 1
  return out

/-- M6.5: random programs, Ember interpreter = own back end's code on the model. -/
def ownFuzz (count seed : Nat) (verbose : Bool) (passes := true) : IO UInt32 := do
  let mut bad := 0
  let mut bytes := 0
  for i in [0:count] do
    let (p, ins) := Lang.Gen.sample (seed + i)
    if let .ok img := ownImage p (passes := passes) then bytes := bytes + img.codeSize
    if ownDiverges p ins passes then
      bad := bad + 1
      if bad ≤ 2 then
        let small ← Lang.Gen.shrinkProg (fun q => pure (ownDiverges q ins passes)) p
        IO.println s!"FAIL p{seed + i}, shrunk to {Lang.Gen.progSize small} statements:\n{small.pretty}"
        IO.println s!"inputs:\n{(Trace.ofSteps {} (ins.map (·, []))).print}"
        if let .ok q := small.check then
          if let .ok ir := IR.lower q then IO.println ir.text
        if verbose then
          if let .ok img := ownImage small true passes then IO.println (listing img)
        if let .ok it := Fuzz.interp small ins then IO.println s!"interpreter:\n{it.print}"
        match ownRun small ins (passes := passes) with
        | .ok t => IO.println s!"z80:\n{t.print}"
        | .error e => IO.println s!"z80: {e}"
      else IO.println s!"FAIL p{seed + i}"
  IO.println s!"z80 own back end{if passes then "" else " (no passes on the assembly)"}: {count} random programs: Ember interpreter = generated code on the model; {bad} failures ({bytes / (max count 1)} bytes per image on average)"
  return if bad == 0 then 0 else 1

def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 (n % 256)
  String.ofList (((if d.length < 2 then ['0'] else []) ++ d).map Char.toUpper)

/-- Intel HEX, 16 bytes a record. -/
def toIhx (bytes : ByteArray) (origin : Nat) : String := Id.run do
  let mut out := ""
  let mut k := 0
  while k < bytes.size do
    let n := min 16 (bytes.size - k)
    let a := origin + k
    let mut sum := n + a / 256 + a % 256
    let mut line := s!":{hex2 n}{hex2 (a / 256)}{hex2 a}00"
    for j in [0:n] do
      line := line ++ hex2 bytes[k + j]!.toNat
      sum := sum + bytes[k + j]!.toNat
    out := out ++ line ++ hex2 (256 - sum % 256) ++ "\n"
    k := k + n
  return out ++ ":00000001FF\n"

/-- The stack or the SLIP loop for a board (`Runtime.board`), by the own
back end. -/
def ownBoardImage (name : String) (trace : Nat) (annotate := false) (passes := true) :
    Except String Codegen.Image := do
  let prog ← match name with
    | "net" => pure Net.prog
    | "sliploop" => pure Net.Loop.prog
    | "trapnote" => pure Lang.Examples.TrapNote.prog
    | n => throw s!"own-build: unknown program {n} (net, sliploop, trapnote)"
  let p ← match prog.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let (_, reserved) := Runtime.boardCells 0x8000
  Codegen.build (← IR.lower p) (Runtime.board trace p.dropReasons p.notes) (Runtime.boardHead 0x8000)
    (reserved := reserved) (annotate := annotate) (passes := passes)

/-- A board image of `Examples.TrapNote` on the model, through `Target`:
its notes, named `trap` and `trap counter`, come out as notes and stop
nothing; the byte `!` traps, and the line of the trap is a trap
(`Trace.isTrapNote`) — `trap (<where>)` when the image names the place
(`place`), `trap` otherwise.  The failures. -/
def trapNoteCheck (m : Machine) (place : Bool) : List String := Id.run do
  let bytes (l : List UInt8) : Input := .rx (ByteArray.mk l.toArray)
  let notes (evs : List Event) := evs.filterMap fun e => match e with | .note t => some t | _ => none
  let m0 ← match Target.boot m with
    | .ok m => pure m
    | .error e => return [s!"boot: {e}"]
  let mut bad : List String := []
  -- the notes of the program
  let want := ["trap 5", "trap counter 517", "trap 7", "trap counter 519"]
  match Target.feed m0 (bytes [5, 7]) with
  | .ok (_, evs) =>
    if notes evs != want || evs.length != want.length then bad := bad ++ [s!"notes: {notes evs}, expected {want}"]
  | .error e => bad := bad ++ [s!"the notes of the program stopped the image: {e}"]
  -- the trap: the line the image writes
  let (mt, done) := (m0.send (ByteArray.mk #[0x21])).runIdle
  match Target.collect mt with
  | .ok (_, evs) =>
    let ok := match notes evs with
      | [t] => isTrapNote t && (if place then t.startsWith "trap (" && t.length > 7 else t == "trap")
      | _ => false
    if !done || !ok || evs.length != 1 then
      bad := bad ++ [s!"trap: the image wrote {notes evs} ({if place then "with" else "without"} the place expected)"]
  | .error e => bad := bad ++ [s!"trap: {e}"]
  match Target.feed m0 (bytes [0x21]) with
  | .ok _ => bad := bad ++ ["the trap was not reported"]
  | .error _ => pure ()
  -- a replay: the notes, then the trap as the last line
  let r := Target.replay m0 { impl := "z80", profile := "z80" } #[bytes [5], bytes [0x21], bytes [7]]
  let got := r.trace.lines.toList.filterMap fun l => match l.ev with | .note t => some t | _ => none
  if r.error.isNone || !Cc.trapped r.trace || got.take 2 != ["trap 5", "trap counter 517"] || got.length != 3 then
    bad := bad ++ [s!"replay: notes {got}, error {r.error}"]
  let r := Target.replay m0 { impl := "z80", profile := "z80" } #[bytes [5], bytes [7]]
  if r.error.isSome || Cc.trapped r.trace then bad := bad ++ [s!"replay of notes alone: {r.error}"]
  return bad

def trapNote (image : String) (place : Bool) : IO UInt32 := do
  match Machine.ofIhx (← IO.FS.readFile image) with
  | .error e => IO.println s!"FAIL trap-note {image}: {e}"; return 1
  | .ok m =>
    let bad := trapNoteCheck m place
    for b in bad do IO.println s!"FAIL trap-note {image}: {b}"
    IO.println s!"z80 notes named `trap`, `trap counter` and a trap{if place then " with its place" else ""}, {image}: {bad.length} failures"
    return if bad.isEmpty then 0 else 1

/-- Bytes of code per function and runtime routine, largest first. -/
def ownSizes (img : Codegen.Image) : List (String × Nat) :=
  let syms := (img.labels.filter fun (n, a) =>
    a < img.codeSize && !(n.startsWith "l_") && !(n.startsWith "x_") &&
    -- inner labels of the runtime routines
    !(n.startsWith "rt_" && ((n.drop 3).toString.splitOn "_").length > 1 && !n.startsWith "rt_s_" &&
      !["rt_out_byte", "rt_out_end", "rt_mmio_read", "rt_mmio_write", "rt_mmio_addr", "rt_mmio_find",
        "rt_dbg_str", "rt_dbg_dec", "rt_dbg_dig", "rt_drop_names", "rt_note_names", "rt_acc_a", "rt_acc_hl"].contains n)).toArray.qsort
      (fun a b => a.2 < b.2)
  let sized := (List.range syms.size).map fun k =>
    (syms[k]!.1, (if k + 1 < syms.size then syms[k + 1]!.2 else img.codeSize) - syms[k]!.2)
  (sized.toArray.qsort (fun a b => a.2 > b.2)).toList

def ownBuild (name outDir : String) (trace : Nat) (passes := true) : IO UInt32 := do
  match ownBoardImage name trace (passes := passes) with
  | .error e => IO.println s!"FAIL own-build {name}: {e}"; return 1
  | .ok img =>
    IO.FS.createDirAll outDir
    let base := System.FilePath.mk outDir / s!"{name}-own{if passes then "" else "-plain"}"
    IO.FS.writeFile (base.withExtension "ihx") (toIhx img.bytes img.origin)
    -- the listing with the IR between the instructions
    if let .ok ann := ownBoardImage name trace true passes then IO.FS.writeFile (base.withExtension "lst") (listing ann)
    IO.FS.writeFile (base.withExtension "noi")
      (String.join (img.labels.map fun (n, a) => s!"DEF {n} 0x{hex2 (a / 256)}{hex2 a}\n"))
    IO.println s!"own back end: {name}: {img.codeSize} bytes of code and constants, {img.ramSize} bytes of RAM -> {base.withExtension "ihx"}"
    return 0

/-- T-states by function for one ping (the ninth of nine). -/
def profile (image : String) : IO UInt32 := do
  let syms := (← readSymbols ((System.FilePath.mk image).withExtension "noi")).filter fun (_, n) =>
    !(n.startsWith "l_") && !(n.startsWith "x_") && !(n.startsWith "s__") && !(n.startsWith "l__") &&
    !(n.startsWith ".") && !(n.startsWith "lit") && !(n.startsWith "g_") && !(n.startsWith "fr_")
  -- the symbol every address belongs to
  let mut owner : Array Nat := Array.replicate 65536 0
  let mut k := 0
  for pc in [0:65536] do
    while k + 1 < syms.size && syms[k + 1]!.1 ≤ pc do k := k + 1
    owner := owner.set! pc k
  let mut m ← loadImage image
  let mut cost : Array Nat := Array.replicate (syms.size + 1) 0
  let mut count : Array Nat := Array.replicate (syms.size + 1) 0
  let mut total := 0
  for round in [0:9] do
    m := m.send (slipEncode (pingRequest (round + 1)))
    let mut steps := 0
    while !(m.idle || m.dead) && steps < 50000000 do
      let pc := m.cpu.pc.toNat
      let before := m.cpu.cycles
      m := m.step
      steps := steps + 1
      if round == 8 then
        let d := (m.cpu.cycles - before).toNat
        let o := owner[pc]!
        cost := cost.modify o (· + d)
        total := total + d
        -- entries: an instruction at the symbol's own address
        if o < syms.size && syms[o]!.1 == pc then count := count.modify o (· + 1)
    m := (m.takeTx).2
    m := (m.takeDbg).2
  let rows := ((List.range syms.size).map fun i => (cost[i]!, count[i]!, syms[i]!.2)).filter (·.1 > 0)
  for (c, n, name) in (rows.toArray.qsort (fun a b => a.1 > b.1)).toList.take 40 do
    IO.println s!"  {c}\t{c * 100 / (max total 1)}%\t{n}x\t{name}"
  IO.println s!"profile: {total} T-states for one ping"
  return 0

/-- The deepest the stack gets over the fixtures (bytes below the top of
RAM), interrupts included. -/
def stackDepth (image : String) (paths : List String) : IO UInt32 := do
  let m0 ← loadImage image
  let mut deepest := 0
  let mut ran := 0
  for p in paths do
    for f in ← traceFiles p do
      let t ← Trace.readFile f
      if !NetCheck.supported t.header then continue
      ran := ran + 1
      let mut m := m0
      for i in t.inputs do
        m := match i with
          | .rx b => m.send b
          | .tick => m.tick
        let mut steps := 0
        while !(m.idle || m.dead) && steps < 50000000 do
          m := m.step
          steps := steps + 1
          let sp := m.cpu.sp.toNat
          if sp != 0 && 65536 - sp > deepest then deepest := 65536 - sp
        m := (m.takeTx).2
        m := (m.takeDbg).2
  IO.println s!"stack: {deepest} bytes at most over {ran} fixtures"
  return 0

structure Opts where
  pos : List String := []
  len : Nat := 1000
  seed : Nat := 1
  bytes : Nat := 10000
  frames : Nat := 300
  out : Option String := none
  itrace : Option String := none
  traceFrom : Nat := 0
  verbose : Bool := false
  u64 : Bool := false
  /-- `EMBER_TRACE` of an image built by the own back end. -/
  traceLevel : Nat := 2
  /-- The own back end without the passes on the assembly: the image the proofs speak of. -/
  plain : Bool := false

def parse : List String → Opts → Opts
  | [], o => o
  | "--len" :: n :: r, o => parse r { o with len := n.toNat?.getD o.len }
  | "--seed" :: n :: r, o => parse r { o with seed := n.toNat?.getD o.seed }
  | "--bytes" :: n :: r, o => parse r { o with bytes := n.toNat?.getD o.bytes }
  | "--frames" :: n :: r, o => parse r { o with frames := n.toNat?.getD o.frames }
  | "--out" :: d :: r, o => parse r { o with out := some d }
  | "--itrace" :: f :: r, o => parse r { o with itrace := some f }
  | "--trace-from" :: n :: r, o => parse r { o with traceFrom := n.toNat?.getD 0 }
  | "--verbose" :: r, o => parse r { o with verbose := true }
  | "--u64" :: r, o => parse r { o with u64 := true }
  | "--plain" :: r, o => parse r { o with plain := true }
  | "--trace" :: n :: r, o => parse r { o with traceLevel := n.toNat?.getD 2 }
  | a :: r, o => parse r { o with pos := o.pos ++ [a] }

def usage : String :=
  "the Z80 model:\n" ++
  "  ember-z80 check [PROGRAMS] [--len N] [--seed S]     the CPU model against z88dk-ticks\n" ++
  "  ember-z80 replay IMAGE.ihx PATH... [--out DIR] [--verbose]\n" ++
  "  ember-z80 echo IMAGE.ihx [--bytes N] [--seed S]\n" ++
  "  ember-z80 slip IMAGE.ihx [--frames N] [--seed S]\n" ++
  "  ember-z80 ping IMAGE.ihx                             T-states per ping\n" ++
  "  ember-z80 profile IMAGE.ihx                          the same, by function (needs IMAGE.noi)\n" ++
  "  ember-z80 stack IMAGE.ihx PATH...                    deepest stack over fixtures\n" ++
  "  ember-z80 run IMAGE.ihx FIXTURE --itrace FILE [--trace-from STEP]\n" ++
  "SDCC's code:\n" ++
  "  ember-z80 fuzz [COUNT] [--seed S] [--u64]            random programs: interpreter vs SDCC's code\n" ++
  "the own back end:\n" ++
  "  ember-z80 asm-check                                  the assembler against z88dk-z80asm\n" ++
  "  ember-z80 rt-check                                   the runtime routines against their specifications\n" ++
  "  ember-z80 ir-fuzz [COUNT] [--seed S]                 random programs: interpreter vs IR interpreter\n" ++
  "  ember-z80 ir-replay PATH...                          the stack on the IR interpreter\n" ++
  "  ember-z80 own-fuzz [COUNT] [--seed S] [--verbose]    random programs: interpreter vs generated code\n" ++
  "  ember-z80 own-build net|sliploop|trapnote [--trace 0|1|2] [--out DIR]    image, listing, symbols\n" ++
  "  ember-z80 own-size net|sliploop [--trace 0|1|2]      bytes per function\n" ++
  "  ember-z80 trap-note|trap-note-terse IMAGE.ihx                   the `trapnote` program: notes named like a trap, and a trap\n" ++
  "  --plain with own-fuzz, own-build, own-size: without the passes on the assembly (the image the proofs speak of)"

def main (args : List String) : IO UInt32 := do
  let o := parse args {}
  match o.pos with
  | "check" :: rest =>
    if !(← Check.ticksAvailable) then
      IO.println "z88dk-ticks not installed (run inside nix-shell)"
      return 2
    let count := (rest.head?.bind (·.toNat?)).getD 10
    let s ← Check.run count o.len o.seed
    IO.println s!"z80 model vs z88dk-ticks: {s.programs} programs, {s.instructions} instructions, {s.failures} failures"
    return if s.failures == 0 then 0 else 1
  | "replay" :: image :: paths =>
    let (ran, skipped, bad, cycles) ← replayFiles image paths o.out o.verbose
    IO.println s!"z80 replay: {ran - bad} of {ran} fixtures: target trace = fixture ({skipped} not for the SLIP build), {cycles} T-states"
    return if bad == 0 then 0 else 1
  | ["echo", image] => echo image o.bytes o.seed
  | ["slip", image] => slip image o.frames o.seed
  | ["ping", image] =>
    IO.println s!"ping: {← pingCycles image} T-states per 56-byte echo"
    return 0
  | ["asm-check"] => asmCheck
  | ["rt-check"] =>
    match RtCheck.run o.seed with
    | .error e => IO.println s!"FAIL rt-check: {e}"; return 1
    | .ok t =>
      if let some f := t.first then IO.println s!"FAIL {f}"
      IO.println s!"z80 runtime routines vs their specifications: {t.cases} cases, {t.bad} failures"
      return if t.bad == 0 then 0 else 1
  | ["trap-note", image] => trapNote image true
  | ["trap-note-terse", image] => trapNote image false
  | ["profile", image] => profile image
  | "stack" :: image :: paths => stackDepth image paths
  | ["own-build", name] => ownBuild name (o.out.getD ".lake/build/z80") o.traceLevel !o.plain
  | ["own-size", name] =>
    match ownBoardImage name o.traceLevel (passes := !o.plain) with
    | .error e => IO.println s!"FAIL {e}"; return 1
    | .ok img =>
      for (n, sz) in (ownSizes img).take 45 do IO.println s!"  {sz}\t{n}"
      let gl := (img.layout.globals.map (·.2)).filter (· ≥ 0x8000)
      let fr := img.layout.frames.map (·.2)
      let lo (xs : List Nat) := xs.foldl Nat.min 65536
      IO.println s!"RAM: runtime and ring {lo gl - 0x8000}, globals {lo fr - lo gl}, frames {img.layout.top - lo fr}"
      IO.println s!"own back end: {name}: {img.codeSize} bytes of code and constants, {img.ramSize} bytes of RAM"
      -- the stack: a static bound against the room above the static RAM
      let room := 65536 - img.layout.top
      match StackBound.ofItems img.items with
      | none => IO.println "FAIL stack bound: the analysis gave up"; return 1
      | some b =>
        IO.println s!"stack bound: {b.total} bytes at most ({b.main} from start-up on, {b.interrupt} for an interrupt); {room} bytes above the static RAM"
        return if b.total ≤ room then 0 else 1
  | "own-fuzz" :: rest => ownFuzz ((rest.head?.bind (·.toNat?)).getD 500) o.seed o.verbose !o.plain
  | "ir-replay" :: paths => irReplay paths
  | "ir-dump" :: rest => irDump ((rest.head?.bind (·.toNat?)).getD 400) o.seed
  | "ir-fuzz" :: rest => irFuzz ((rest.head?.bind (·.toNat?)).getD 1000) o.seed
  | "fuzz" :: rest => fuzz ((rest.head?.bind (·.toNat?)).getD 50) o.seed o.u64 o.verbose
  | ["run", image, fixture] =>
    match o.itrace with
    | some f => instrTrace image fixture f o.traceFrom
    | none => IO.eprintln usage; return 2
  | _ => IO.eprintln usage; return 2

end Ember.Tools.Z80
