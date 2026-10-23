import LSpec
import Ember.Tools.Lockstep
import Ember.Spec.Checksum
import Ember.Spec.Tcp.Header

/-!
# M3 tests: `Ember.Net` against `Ember.Spec`
-/

namespace Ember.Tests.NetTests
open LSpec Ember Ember.Lang Ember.Trace Ember.Tools

/-! ## M3.2 function level, on random inputs -/

def machine : Machine := Machine.init NetCheck.netProg #[]

def withBuf (b : ByteArray) : Machine :=
  machine.setGlobal "buf" (.arr ((Array.range 296).map fun i => .int .w8 (Bytes.get b i).toUInt64))

def call (m : Machine) (f : String) (args : List Val) : Option Val :=
  match m.callFn f args with
  | .ok (v, _) => v
  | .error _ => none

def v16 (n : Nat) : Val := .int .w16 (UInt64.ofNat n)
def v32 (n : Nat) : Val := .int .w32 (UInt64.ofNat n)
def v8 (n : Nat) : Val := .int .w8 (UInt64.ofNat n)

/-- `csum`, `pseudo`, `csum_update`, `parse_mss` and `rto` against the Spec. -/
def functionLevel (n : Nat) (seed : Nat := 3) : IO Nat := do
  let mut bad := 0
  let mut rng := Rng.ofSeed seed
  for _ in [0:n] do
    let ((b, o, len, init, src, dst, w, hc), r) := (do
      let b ← randBytes 296
      let o ← randNat 100
      let len ← randNat (296 - o)
      return (b, o, len, (← randNat 65536), (← rand64).toUInt32, (← rand64).toUInt32,
              (← randNat 65536).toUInt16, (← randNat 65536).toUInt16) : RandM _).run rng
    rng := r
    let m := withBuf b
    if call m "csum" [v16 o, v16 len, v16 init] != some (v16 (Spec.Checksum.sum b o len init.toUInt16).toNat) then
      bad := bad + 1
    if call m "pseudo" [v32 src.toNat, v32 dst.toNat, v8 6, v16 len] !=
        some (v16 (Spec.Checksum.pseudo src dst 6 len).toNat) then bad := bad + 1
    if call m "csum_update" [v16 hc.toNat, v16 w.toNat, v16 (w ^^^ 0x0800).toNat] !=
        some (v16 (Spec.Checksum.incremental hc w (w ^^^ 0x0800)).toNat) then bad := bad + 1
    -- TCP options: the Spec's parseMss reads the segment at offset 0, the
    -- Ember one at buf[20]
    let off := 20 + 4 * (o % 11)
    let seg := b.extract 20 296
    let spec := Spec.Tcp.parseMss seg off
    match (m.callFn "parse_mss" [v16 off]) with
    | .ok (_, m') =>
      let has := NetCheck.field m' "sg" "has_mss" == 1
      let mss := NetCheck.field m' "sg" "mss"
      if (if has then some mss.toUInt16 else none) != spec then bad := bad + 1
    | .error _ => bad := bad + 1
  for k in [0:12] do
    if call machine "rto" [v8 k] != some (v8 (Spec.rto k)) then bad := bad + 1
  IO.println s!"function level (csum, pseudo, csum_update, parse_mss, rto): {n} random inputs, {bad} failures"
  return bad

/-- Corpus and generated sessions: Spec = interpreter (lockstep) = host C. -/
def stack (count : Nat) : IO Nat := do
  let args := ["Tests/Ember/corpus", "Tests/Ember/regress", "--gen", "all", toString count] ++
    (if ← Cc.available then ["--c"] else [])
  if !(← Cc.available) then IO.println "Ember stack C: no C compiler, interpreter only"
  let rc ← Lockstep.main args
  -- M5.9: the SLIP build's C without its bounds checks, under UBSan and ASan
  let rd ← if ← Cc.available then
      Lockstep.main ["Tests/Ember/corpus", "Tests/Ember/regress", "--gen", "slip", toString (count / 4), "--c", "--dropped"]
    else pure 0
  return if rc == 0 && rd == 0 then 0 else 1

def main (count : Nat := 1000) : IO UInt32 := do
  let mut bad := 0
  bad := bad + (← functionLevel 10000)
  bad := bad + (← stack count)
  return if bad == 0 then 0 else 1

end Ember.Tests.NetTests
