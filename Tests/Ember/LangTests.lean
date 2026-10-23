import LSpec
import Ember.Lang.Examples
import Ember.Lang.Gen
import Ember.Lang.Pretty
import Ember.Spec.Checksum
import Ember.Spec.Slip
import Ember.Tools.Cc
import Ember.Tools.Emit
import Ember.Tools.Fuzz
import Ember.Tools.NetCheck
import Ember.Tools.Lockstep
import Ember.Lang.Sem
import Ember.C.Sem
import Ember.C.DropChecks
import Tests.Ember.LangPrograms

/-!
# M2 tests: `Ember.Lang` and `Ember.C`
-/

namespace Ember.Tests.LangTests
open LSpec Ember Ember.Lang Ember.Trace
open Ember.Tests.LangPrograms


/-! ## M2.2 type checker: one negative test per rule, errors carry spans -/

def checkErr (p : Prog) : Option Err :=
  match p.check with
  | .ok _ => none
  | .error e => some e

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def ruleTests : TestSeq := Bad.cases.foldr (init := .done) fun (rule, p, sub) acc =>
  let e := checkErr p
  test s!"rejects: {rule}" ((e.map fun e => contains e.msg sub).getD false) $
  test s!"error has a span: {rule}" ((e.map fun e => e.span.line > 0 && e.span.file.endsWith "LangPrograms.lean").getD false) acc

def positiveTests : TestSeq :=
  test "accepts: a function returning on every path" ((checkErr { globals := [], fns := [Bad.ok_fn, Bad.nop], entry := "nop" }).isNone) $
  test "accepts: the construct program" ((checkErr Examples.Constructs.prog).isNone) $
  test "accepts: every example" (Examples.all.all fun (_, p) => (checkErr p).isNone)

/-! ## M2.3 interpreter: every construct, a trap with its location -/

def constructsInputs : Array Input := #[.rx (Bytes.ofList [2]), .tick, .rx (Bytes.ofList [9])]

def constructsExpected : List String :=
  ["0      rx   02",
   "0      tx   fc 06 00 00 00 20 fd fe 20 02 00 01 02 9c 05 64 04 00 04",
   "1      tick", "1      note tick 42", "2      rx   09"]

def constructsRun : Option Result := (Examples.Constructs.prog.run constructsInputs).toOption

def fuelRunsOut : Bool :=
  let spin : Prog := { fns := [{ name := "main", body := [.loop 1000000 [.eff none .outByte [.lit 1 (some .w8)]]] }] }
  match spin.run #[.tick] (fuel := 1000) with
  | .ok r => (r.error.map fun e => contains e.msg "out of fuel").getD false
  | .error _ => false

def interpTests : TestSeq :=
  let r := constructsRun
  let lines := (r.map fun r => (r.trace.lines.toList.map Line.print)).getD []
  test "every construct: expected trace" (lines.take 5 == constructsExpected) $
  test "out-of-bounds read is an error naming the function and statement" (
    (r.bind (·.error)).any fun e => e.fn == "main" && e.path.length > 0 &&
      contains e.msg "index 9 out of bounds [0, 4)" && e.span.line > 0) $
  test "events before a trap are kept, the trap is the last line" (
    (r.map fun r => Tools.Cc.trapped r.trace).getD false) $
  test "fuel runs out" fuelRunsOut

/-! ## M2.4 surface syntax = hand-built AST -/

partial def strip : Stmt → Stmt
  | .at _ s => strip s
  | .ite c t e => .ite c (t.map strip) (e.map strip)
  | .forRange i w lo hi b => .forRange i w lo hi (b.map strip)
  | .loop n b => .loop n (b.map strip)
  | s => s

def handCsumAdd : Fn :=
  { name := "csum_add", params := [{ name := "acc", ty := .u16 }, { name := "w", ty := .u16 }], ret := some .u16,
    body := [.decl "s" .u16 (some (.bin .add (.var "acc") (.var "w"))),
             .ite (.bin .lt (.var "s") (.var "acc")) [.ret (some (.bin .add (.var "s") (.lit 1 none)))] [],
             .ret (some (.var "s"))] }

def handPush : Fn :=
  { name := "push", params := [{ name := "b", ty := .u8 }],
    body := [.decl "next" .u8 (some (.bin .band (.bin .add (.var "head") (.lit 1 none)) (.lit 15 none))),
             .ite (.bin .eq (.var "next") (.var "tail"))
               [.assign (.var "overruns") (.bin .add (.var "overruns") (.lit 1 none)), .ret none] [],
             .assign (.index (.var "ring") (.var "head")) (.var "b"),
             .assign (.var "head") (.var "next")] }

def handUpdate : Fn :=
  { name := "update", params := [{ name := "c", ty := .u32 }, { name := "b", ty := .u8 }], ret := some .u32,
    body := [.decl "x" .u32 (some (.bin .bxor (.var "c") (.cast .w32 (.var "b")))),
             .forRange "i" none (.lit 0 none) (.lit 8 none)
               [.ite (.bin .eq (.bin .band (.var "x") (.lit 1 none)) (.lit 1 none))
                 [.assign (.var "x") (.bin .bxor (.bin .shr (.var "x") (.lit 1 none)) (.lit 0xEDB88320 none))]
                 [.assign (.var "x") (.bin .shr (.var "x") (.lit 1 none))]],
             .ret (some (.var "x"))] }

def sameFn (a b : Fn) : Bool :=
  a.name == b.name && a.params == b.params && a.ret == b.ret && a.body.map strip == b.body.map strip

def carriesLine : Bool :=
  match Examples.Checksum.csum_add.body with
  | .at sp _ :: _ => sp.line > 0 && sp.file == "Ember/Lang/Examples.lean"
  | _ => false

def surfaceTests : TestSeq :=
  test "csum_add elaborates to the hand-built AST" (sameFn Examples.Checksum.csum_add handCsumAdd) $
  test "push elaborates to the hand-built AST" (sameFn Examples.Ring.push handPush) $
  test "update (for loop, casts, hex) elaborates to the hand-built AST" (sameFn Examples.Crc32.update handUpdate) $
  test "statements carry their Lean source line" carriesLine

/-! ## M2.5 profiles -/

def mulEmitted : Bool :=
  let p : Prog := { globals := [{ name := "a", ty := .u8 }], fns := [{ name := "main", body :=
    [.assign (.var "a") (.bin .mul (.var "a") (.var "a"))] }] }
  match C.emitC p { profile := .sdccZ80, lines := false } with
  | .ok c => contains c "g_a = ((uint8_t)(((unsigned)g_a) * ((unsigned)g_a)));"
  | .error _ => false

def profileTests : TestSeq :=
  test "u8 * u8 on sdcc-z80 is computed in unsigned (16-bit, no signed overflow)" (Profile.sdccZ80.opType .w8 == "unsigned") $
  test "u16 on sdcc-z80: unsigned" (Profile.sdccZ80.opType .w16 == "unsigned") $
  test "u32 on sdcc-z80: uint32_t" (Profile.sdccZ80.opType .w32 == "uint32_t") $
  test "u16 * u16 on host64: unsigned (32-bit)" (Profile.host64.opType .w16 == "unsigned") $
  test "u64 on rv32: uint64_t" (Profile.rv32.opType .w64 == "uint64_t") $
  test "u8 * u8 emitted with unsigned operands and a truncating cast" mulEmitted

/-- Each of the trapping regressions (the first two): the drop comes
before the trap in the interpreter. -/
def regressionsKeepOrder : Bool :=
  (Regress.progs.take 2).all fun (_, p, ins) =>
    match p.run ins with
    | .ok r =>
      let kinds := r.trace.lines.toList.map (·.ev.kind)
      r.error.isSome && kinds.contains "drop" && Tools.Cc.trapped r.trace
    | .error _ => false

def regressionTests : TestSeq :=
  test "fuzzer regressions: events before a trap are kept, in order" regressionsKeepOrder

def unitTests : TestSeq :=
  group "M2.2 checker (negative)" ruleTests ++ group "M2.2 checker (positive)" positiveTests ++
  group "M2.3 interpreter" interpTests ++ group "M2.4 surface syntax" surfaceTests ++
  group "M2.5 profiles" profileTests ++ group "M2.8 regressions" regressionTests

/-! ## IO suites -/

/-- M2.6 golden C for every registered program and profile. -/
def golden : IO Nat := do
  let mut bad := 0
  let mut n := 0
  for (name, p) in ← Tools.Emit.registry do
    for prof in Profile.all do
      n := n + 1
      let path := Tools.Emit.goldenPath name prof
      match Tools.Emit.emitFor p prof with
      | .error e => bad := bad + 1; IO.println s!"FAIL golden {name}: {e}"
      | .ok c =>
        if !(← path.pathExists) then bad := bad + 1; IO.println s!"FAIL golden {path}: missing (lake exe ember-emit --golden)"
        else if (← IO.FS.readFile path) != c then
          bad := bad + 1
          IO.println s!"FAIL golden {path}: emitted C changed (review, then lake exe ember-emit --golden)"
      if Tools.Emit.dropped.contains name then
        n := n + 1
        let path := Tools.Emit.droppedPath name prof
        match Tools.Emit.emitDroppedFor name p prof with
        | .error e => bad := bad + 1; IO.println s!"FAIL golden {name} (dropped): {e}"
        | .ok c =>
          if !(← path.pathExists) then bad := bad + 1; IO.println s!"FAIL golden {path}: missing (lake exe ember-emit --golden)"
          else if (← IO.FS.readFile path) != c then
            bad := bad + 1
            IO.println s!"FAIL golden {path}: emitted C changed (review, then lake exe ember-emit --golden)"
  IO.println s!"golden C: {n} files, {bad} failures"
  return bad

/-! M2.9 examples against Lean references, in the interpreter. -/

def crc32Ref (bs : List UInt8) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for b in bs do
    c := c ^^^ b.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1
  return ~~~ c

def txs (t : Trace) : List (List UInt8) :=
  t.lines.toList.filterMap fun l => match l.ev with | .tx b => some b.toList | _ => none

def drops (t : Trace) : Nat := t.lines.foldl (fun n l => match l.ev with | .drop _ => n + 1 | _ => n) 0

/-- Random rounds of bytes, each followed by a tick. -/
def rounds (seed : Nat) (n : Nat) (maxLen : Nat) : List (List UInt8) :=
  (((List.range n).mapM fun _ => do
    let k ← randRange 0 maxLen
    return (← randBytes k).toList) : RandM _).run' (Rng.ofSeed seed)

def roundInputs (rs : List (List UInt8)) : Array Input :=
  (rs.flatMap fun r => [Input.rx (Bytes.ofList r), .tick]).toArray

def runTrace (p : Prog) (ins : Array Input) : Option Trace :=
  (p.run ins (fuel := 100000000)).toOption.map (·.trace)

def referenceTests : IO Nat := do
  let mut bad := 0
  for seed in [0:100] do
    let rs := rounds seed 5 64
    -- checksum
    let want := rs.map fun r =>
      let c := Spec.Checksum.checksum (Bytes.ofList r) 0 r.length
      [(c >>> 8).toUInt8, c.toUInt8]
    if (runTrace Examples.Checksum.prog (roundInputs rs)).map txs != some want then
      bad := bad + 1; IO.println s!"FAIL checksum example vs Spec.Checksum, seed {seed}"
    -- CRC-32
    let want := rs.map fun r => let c := crc32Ref r; [c.toUInt8, (c >>> 8).toUInt8, (c >>> 16).toUInt8, (c >>> 24).toUInt8]
    if (runTrace Examples.Crc32.prog (roundInputs rs)).map txs != some want then
      bad := bad + 1; IO.println s!"FAIL crc32 example vs reference, seed {seed}"
    -- SLIP: random frames (some oversize) and noise
    let (stream, _) := (do
      let mut s := ByteArray.empty
      for _ in [0:(← randRange 1 6)] do
        let n ← randRange 0 320
        let mut d ← randBytes n
        for _ in [0:(← randNat 6)] do
          if n > 0 then d := Bytes.set d (← randNat n) (← randPick #[Spec.Slip.END, Spec.Slip.ESC])
        s := s ++ (if ← randBool 80 then Spec.Slip.encode d else d)
      return s : RandM _).run (Rng.ofSeed (seed + 7))
    let want := (Spec.Slip.decodeAll stream).map (·.toList)
    match runTrace Examples.Slip.prog #[.rx stream] with
    | some t => if txs t != want then bad := bad + 1; IO.println s!"FAIL slip example vs Spec.Slip, seed {seed}"
    | none => bad := bad + 1; IO.println s!"FAIL slip example did not run, seed {seed}"
    -- ring: model
    let ins := roundInputs (rounds (seed + 3) 6 24)
    let mut q : List UInt8 := []
    let mut over := 0
    let mut want : List (List UInt8) := []
    for i in ins do
      match i with
      | .rx b => for x in b.toList do
                   if q.length == 15 then over := (over + 1) % 256 else q := q ++ [x]
      | .tick => want := want ++ [q.take 4 ++ [UInt8.ofNat over]]; q := q.drop 4
    if (runTrace Examples.Ring.prog ins).map txs != some want then
      bad := bad + 1; IO.println s!"FAIL ring example vs model, seed {seed}"
  IO.println s!"examples vs references: 400 runs, {bad} failures"
  return bad

/-- M2.7 interpreter = host C for the examples and the construct program,
strict warnings, -O0 and -O2, UBSan + ASan. -/
def differential : IO Nat := do
  unless ← Tools.Cc.available do
    IO.println "differential C: no C compiler, skipped (nix-shell provides gcc)"
    return 0
  let regress : List (String × Prog × Array Input) := Regress.progs
  let progs : Array (String × Prog) := (Examples.all ++ regress.map (fun (r : String × Prog × Array Input) => (r.1, r.2.1))).toArray
  let mut units := []
  for (n, p) in progs.toList do
    match Tools.Cc.emit n p with
    | .ok c => units := units ++ [(n, c)]
    | .error e => IO.println s!"FAIL emit {n}: {e}"; return 1
  let mut bad := 0
  let mut runs := 0
  for opt in ["-O0", "-O2"] do
    let dir : System.FilePath := s!".lake/ember-cc/examples{opt}"
    match ← Tools.Cc.build { dir, flags := #[opt, "-fsanitize=undefined,address", "-fno-sanitize-recover=all"] } units with
    | .error e => IO.println s!"FAIL build {opt}:\n{e}"; return 1
    | .ok exe =>
      for k in [0:progs.size] do
        let (n, p) := progs[k]!
        for seed in [0:(if n == "constructs" || n.startsWith "regress" then 1 else 25)] do
          let ins := if n == "constructs" then constructsInputs
            else if let some (_, _, i) := regress.find? (fun (r : String × Prog × Array Input) => r.1 == n) then i
            else if n == "slip" then #[.rx ((randBytes 400).run' (Rng.ofSeed seed))]
            else roundInputs (rounds seed 4 40)
          let inp := dir / s!"in-{n}-{seed}.trace"
          Tools.Cc.writeInputs inp {} ins
          let (ct, _) ← Tools.Cc.run exe k inp
          runs := runs + 1
          match p.run ins with
          | .ok r =>
            if !Tools.Fuzz.agree r.trace ct then
              bad := bad + 1
              IO.println s!"FAIL interpreter vs C {n} {opt} seed {seed}\n{(diff r.trace ct { observable := false }).report}"
          | .error e => bad := bad + 1; IO.println s!"FAIL {n}: {e}"
  IO.println s!"interpreter = C: {runs} runs (examples and constructs, -O0/-O2, UBSan/ASan), {bad} failures"
  return bad

/-- SDCC diagnostics that report what its optimiser proved (a guard
`b == 0` that is always true, the branch it made unreachable) rather than
anything about the C: as with GCC's range warnings, no emitter can rule
them out in general, so they are the only ones disabled. -/
def sdccOptimiserNotes : Array String := #["--disable-warning", "110", "--disable-warning", "126"]

/-- The Z80 profile's C compiles with SDCC, warnings as errors. -/
def sdcc : IO Nat := do
  let ok ← try pure ((← IO.Process.output { cmd := "sdcc", args := #["--version"] }).exitCode == 0) catch _ => pure false
  unless ok do
    IO.println "sdcc: not installed, skipped (nix-shell provides it)"
    return 0
  let mut bad := 0
  let mut n := 0
  for (name, _) in ← Tools.Emit.registry do
    let f := Tools.Emit.goldenPath name .sdccZ80
    let r ← IO.Process.output { cmd := "sdcc", args := #["-mz80", "--std-c99", "--Werror"] ++ sdccOptimiserNotes ++
      #["-Iruntime/common", "-c", f.toString, "-o", s!".lake/ember-sdcc-{name}.rel"] }
    n := n + 1
    if r.exitCode != 0 then bad := bad + 1; IO.println s!"FAIL sdcc {f}:\n{r.stderr}{r.stdout}"
    if Tools.Emit.dropped.contains name then
      let f := Tools.Emit.droppedPath name .sdccZ80
      let r ← IO.Process.output { cmd := "sdcc", args := #["-mz80", "--std-c99", "--Werror"] ++ sdccOptimiserNotes ++
        #["-Iruntime/common", "-c", f.toString, "-o", s!".lake/ember-sdcc-{name}-dropped.rel"] }
      n := n + 1
      if r.exitCode != 0 then bad := bad + 1; IO.println s!"FAIL sdcc {f}:\n{r.stderr}{r.stdout}"
  IO.println s!"sdcc -mz80 --Werror: {n} programs, {bad} failures"
  return bad

def fuzz (count : Nat) : IO Nat := do
  unless ← Tools.Cc.available do
    IO.println "fuzz: no C compiler, skipped"
    return 0
  let rc ← Tools.Fuzz.main [toString count, "--quiet", "--seed", "1"]
  IO.println s!"fuzz: {count} random programs, -O0 and -O2 with UBSan/ASan: {if rc == 0 then "no divergence" else "DIVERGENCE"}"
  return if rc == 0 then 0 else 1

/-- M5.4: the total semantics (`Ember.Lang.Sem`, the one proofs unfold)
against the interpreter: random programs, the examples and regressions,
and the stack — all its builds — on the corpus. -/
def semantics (count : Nat) : IO Nat := do
  let mut bad := 0
  let mut runs := 0
  let check (name : String) (p : Prog) (ins : Array Input) : IO Nat := do
    match p.check with
    | .error e => IO.println s!"FAIL sem {name}: {e}"; return 1
    | .ok q =>
      let it := (runMachine (Machine.init q ins) { impl := "interp" }).trace
      let st := Sem.run q ins
      if Tools.Fuzz.agree it st then return 0
      IO.println s!"FAIL {name}: interpreter vs Sem\n{(diff it st { observable := false }).report}"
      return 1
  for i in [0:count] do
    let (p, ins) := Gen.sample (90000 + i)
    bad := bad + (← check s!"p{90000 + i}" p ins)
    runs := runs + 1
  for (n, p) in Examples.all do
    let ins := if n == "constructs" then constructsInputs
      else if n == "slip" then #[.rx ((randBytes 400).run' (Rng.ofSeed 3))]
      else roundInputs (rounds 3 4 40)
    bad := bad + (← check n p ins)
    runs := runs + 1
  for (n, p, ins) in (Regress.progs : List (String × Prog × Array Input)) do
    bad := bad + (← check n p ins)
    runs := runs + 1
  for (n, p) in Guard.progs do
    for ins in Guard.inputs do
      bad := bad + (← check n p ins)
      runs := runs + 1
  let mut fixtures := 0
  for d in ["Tests/Ember/corpus", "Tests/Ember/regress"] do
    for f in ← Tools.Lockstep.traceFiles d do
      let t ← Trace.readFile f
      if Tools.NetCheck.implemented t.header then
        bad := bad + (← check f.toString (Tools.NetCheck.progFor t.header) t.inputs)
        fixtures := fixtures + 1
  IO.println s!"semantics: {runs} runs of random programs and examples, the stack on {fixtures} fixtures: interpreter = Sem (the total semantics); {bad} failures"
  return bad

/-- M5.7: the emitted C under the C semantics of `Ember.C.Sem` against
`Ember.Lang.Sem`, for every profile: the same trace, and never
"undefined". -/
def csemantics (count : Nat) : IO Nat := do
  let mut bad := 0
  let mut runs := 0
  let check (name : String) (p : Prog) (ins : Array Input) : IO Nat := do
    match p.check with
    | .error e => IO.println s!"FAIL csem {name}: {e}"; return 1
    | .ok q =>
      let st := Sem.run q ins
      let mut bad := 0
      for prof in Profile.all do
        let o : C.Opts := { profile := prof }
        match C.compile q o with
        | .error e => IO.println s!"FAIL csem {name} ({prof.name}): {e}"; bad := bad + 1
        | .ok u =>
          let cp := C.Sem.CProg.ofUnit u prof o.entryName q.dropReasons q.notes
          let ct := C.Sem.run cp ins q.framed (fuel := 1000000)
          let undef := ct.lines.any fun l => match l.ev with
            | .note m => m.startsWith "undefined"
            | _ => false
          unless Tools.Fuzz.agree st ct && !undef do
            IO.println s!"FAIL {name} ({prof.name}): Sem vs C semantics\n{(diff st ct { observable := false }).report}"
            bad := bad + 1
      return bad
  for i in [0:count] do
    let (p, ins) := Gen.sample (95000 + i)
    bad := bad + (← check s!"p{95000 + i}" p ins)
    runs := runs + 1
  for (n, p) in Examples.all do
    let ins := if n == "constructs" then constructsInputs
      else if n == "slip" then #[.rx ((randBytes 400).run' (Rng.ofSeed 3))]
      else roundInputs (rounds 3 4 40)
    bad := bad + (← check n p ins)
    runs := runs + 1
  for (n, p, ins) in (Regress.progs : List (String × Prog × Array Input)) do
    bad := bad + (← check n p ins)
    runs := runs + 1
  for (n, p) in Guard.progs do
    for ins in Guard.inputs do
      bad := bad + (← check n p ins)
      runs := runs + 1
  let mut fixtures := 0
  for d in ["Tests/Ember/corpus", "Tests/Ember/regress"] do
    for f in ← Tools.Lockstep.traceFiles d do
      let t ← Trace.readFile f
      if Tools.NetCheck.implemented t.header then
        bad := bad + (← check f.toString (Tools.NetCheck.progFor t.header) t.inputs)
        fixtures := fixtures + 1
  -- self-test: a planted bug (the truncating cast of `+` dropped) must show
  let mut caught := 0
  let mut tried := 0
  for i in [0:1000] do
    if caught > 0 then break
    tried := tried + 1
    let (p, ins) := Gen.sample (1 + i)
    if let .ok q := p.check then
      let o : C.Opts := { profile := .host64, bugDropCast := true }
      if let .ok u := C.compile q o then
        let ct := C.Sem.run (C.Sem.CProg.ofUnit u .host64 o.entryName q.dropReasons q.notes) ins q.framed (fuel := 1000000)
        unless Tools.Fuzz.agree (Sem.run q ins) ct do caught := caught + 1
  if caught == 0 then
    IO.println "FAIL C semantics: the planted bug (dropped cast) was not noticed"
    bad := bad + 1
  IO.println s!"C semantics: planted bug noticed after {tried} random programs"
  IO.println s!"C semantics: {runs} runs of random programs and examples, the stack on {fixtures} fixtures, {Profile.all.length} profiles: Sem = the emitted C under Ember.C.Sem, nothing undefined; {bad} failures"
  return bad

/-- M5.9: the bounds checks taken out (`C.dropUnit`).  Of the SLIP build
(`Ember.Proof.CDrop.stack_c_dropped`): its C without checks, under the C
semantics, on every fixture of its configuration and every profile, has
the trace of `Ember.Lang.Sem` and nothing undefined, and the checks
taken out are all there were.  Where no proof says the run never traps
the checks stay: the tools refuse every other program, and on the
`Guard` programs (an index out of range for some input) the C with its
checks traps where the interpreter does, while without them the C
semantics has no meaning for the run (undefined) — which is why a check
goes only where a proof covers it. -/
def droppedTests : IO Nat := do
  let mut bad := 0
  let mut runs := 0
  let undefIn (t : Trace) : Bool := t.lines.any fun l => match l.ev with
    | .note m => m.startsWith "undefined"
    | _ => false
  -- the SLIP build: every check taken out, the same runs
  match Net.prog.check with
  | .error e => IO.println s!"FAIL dropped: {e}"; bad := bad + 1
  | .ok q =>
    for prof in Profile.all do
      let o : C.Opts := { profile := prof }
      match C.compile q o with
      | .error e => IO.println s!"FAIL dropped ({prof.name}): {e}"; bad := bad + 1
      | .ok u =>
        let d := C.dropUnit u
        unless C.checksUnit u > 0 && C.checksUnit d == 0 do
          IO.println s!"FAIL dropped ({prof.name}): {C.checksUnit u} checks, {C.checksUnit d} left"
          bad := bad + 1
        let cp := C.Sem.CProg.ofUnit d prof o.entryName q.dropReasons q.notes
        for dir in ["Tests/Ember/corpus", "Tests/Ember/regress"] do
          for f in ← Tools.Lockstep.traceFiles dir do
            let t ← Trace.readFile f
            if Tools.NetCheck.buildIndex t.header == some 0 then
              let ct := C.Sem.run cp t.inputs q.framed (fuel := 1000000)
              runs := runs + 1
              unless Tools.Fuzz.agree (Sem.run q t.inputs) ct && !undefIn ct do
                IO.println s!"FAIL dropped {f} ({prof.name}): Sem vs the C without checks"
                bad := bad + 1
  -- every other program keeps its checks
  for (name, p) in (← Tools.Emit.registry) ++ Tools.Emit.extra ++ Guard.progs do
    if !Tools.Emit.dropped.contains name then
      if let .ok _ := Tools.Emit.emitDroppedFor name p .host64 then
        IO.println s!"FAIL dropped: {name} emitted without checks"
        bad := bad + 1
  -- the Guard programs: the checks are what make the out-of-range runs traps
  let mut trapsKept := 0
  let mut undefWithout := 0
  for (name, p) in Guard.progs do
    match p.check with
    | .error e => IO.println s!"FAIL dropped {name}: {e}"; bad := bad + 1
    | .ok q =>
      let o : C.Opts := { profile := .host64 }
      match C.compile q o with
      | .error e => IO.println s!"FAIL dropped {name}: {e}"; bad := bad + 1
      | .ok u =>
        if C.checksUnit u == 0 then
          IO.println s!"FAIL dropped {name}: no check emitted"
          bad := bad + 1
        for ins in Guard.inputs do
          let st := Sem.run q ins
          let ct := C.Sem.run (C.Sem.CProg.ofUnit u .host64 o.entryName q.dropReasons q.notes) ins q.framed
            (fuel := 1000000)
          let dt := C.Sem.run (C.Sem.CProg.ofUnit (C.dropUnit u) .host64 o.entryName q.dropReasons q.notes) ins
            q.framed (fuel := 1000000)
          runs := runs + 1
          unless Tools.Fuzz.agree st ct && !undefIn ct do
            IO.println s!"FAIL dropped {name}: Sem vs the C with checks"
            bad := bad + 1
          if Tools.Cc.trapped st then
            trapsKept := trapsKept + 1
            if undefIn dt then undefWithout := undefWithout + 1
  -- out-of-range inputs exist, and each is undefined once its check is gone
  unless trapsKept > 0 && undefWithout == trapsKept do
    IO.println s!"FAIL dropped Guard: {trapsKept} trapping runs, {undefWithout} undefined without the checks"
    bad := bad + 1
  IO.println s!"bounds checks dropped (M5.9): the SLIP build without its checks on {runs} runs (fixtures × profiles, Guard) = Sem, nothing undefined; other programs refused; Guard: {trapsKept} trapping runs keep their trap, undefined without the check; {bad} failures"
  return bad

def main (fuzzCount : Nat := 1000) : IO UInt32 := do
  let mut bad := 0
  bad := bad + (← semantics fuzzCount)
  bad := bad + (← csemantics fuzzCount)
  bad := bad + (← golden)
  bad := bad + (← droppedTests)
  bad := bad + (← referenceTests)
  bad := bad + (← differential)
  bad := bad + (← sdcc)
  bad := bad + (← fuzz fuzzCount)
  return if bad == 0 then 0 else 1

end Ember.Tests.LangTests
