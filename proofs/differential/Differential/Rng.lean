/-!
# A seeded, reproducible random generator

SplitMix64 (Steele, Lea, Flood 2014): a 64-bit state advanced by a fixed odd constant, output
through a bijective mixer. The whole generator is pure; every test case is drawn from its own
generator seeded with `(seed, case index)`, so any single case can be regenerated without
generating the ones before it.
-/

namespace Differential

/-- SplitMix64 state. -/
structure Rng where
  state : UInt64

/-- The SplitMix64 output mixer. -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- One step: the next 64-bit output and the advanced state. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  (mix64 s, ⟨s⟩)

/-- The generator of case `index` of a run with seed `seed`. -/
def Rng.forCase (seed index : Nat) : Rng :=
  ⟨mix64 (mix64 (UInt64.ofNat seed) + UInt64.ofNat index)⟩

/-- Generators are state transformers over `Rng`. -/
abbrev Gen := StateM Rng

namespace Gen

/-- Uniform-ish natural number in `[0, n)` (`0` when `n = 0`). -/
def below (n : Nat) : Gen Nat := do
  let (x, g) := (← get).next
  set g
  return if n = 0 then 0 else x.toNat % n

/-- `true` with probability `num / den`. -/
def chance (num den : Nat) : Gen Bool := do
  return (← below den) < num

/-- A uniformly chosen element; `default` for the empty list. -/
def pick [Inhabited α] (l : List α) : Gen α := do
  return l[← below l.length]!

/-- A choice weighted by the given natural weights. -/
def weighted [Inhabited α] (l : List (Nat × α)) : Gen α := do
  let total := l.foldl (· + ·.1) 0
  let mut r ← below total
  for (w, x) in l do
    if r < w then return x
    r := r - w
  return default

/-- Between `lo` and `hi` (inclusive) draws of `g`. -/
def listOf (lo hi : Nat) (g : Gen α) : Gen (List α) := do
  let n := lo + (← below (hi + 1 - lo))
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← g)
  return out.toList

/-- A uniformly random permutation (Fisher-Yates). -/
def shuffle (l : List α) : Gen (List α) := do
  let mut a := l.toArray
  for i in [0:a.size] do
    let j := i + (← below (a.size - i))
    a := a.swapIfInBounds i j
  return a.toList

end Gen

end Differential
