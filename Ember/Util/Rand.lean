/-!
# Ember.Util.Rand — a small deterministic PRNG (splitmix64)

Generators must be reproducible from a seed on every machine, so they do
not use `IO.rand`.
-/

namespace Ember

structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev RandM := StateM Rng

def rand64 : RandM UInt64 := modifyGet Rng.next

/-- Uniform in `[0, n)` (0 when `n = 0`). -/
def randNat (n : Nat) : RandM Nat := do
  if n == 0 then return 0
  return (← rand64).toNat % n

/-- Uniform in `[lo, hi]`. -/
def randRange (lo hi : Nat) : RandM Nat := do return lo + (← randNat (hi + 1 - lo))

def randBool (pct : Nat := 50) : RandM Bool := do return (← randNat 100) < pct

def randBytes (n : Nat) : RandM ByteArray := do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push (← randNat 256).toUInt8
  return b

def randPick (xs : Array α) [Inhabited α] : RandM α := do return xs[← randNat xs.size]!

def Rng.ofSeed (n : Nat) : Rng := ⟨UInt64.ofNat n * 0x2545F4914F6CDD1D + 1⟩

end Ember
