import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime counts in arithmetic progressions

This module defines the inclusive prime-counting functions used in Maynard's
equation (1.3) and in the downstream `PrimeGapsLib` challenge surface.
-/

/-- The number of primes `p <= x` whose image in `ZMod q` is `a`. -/
noncomputable def Real.primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

/-- The number of primes at most the real cutoff `x`, coerced to `Real`. -/
noncomputable def pi (x : ℝ) : ℝ :=
  ⌊x⌋₊.primeCounting

namespace BombieriVinogradov

/-- The number of primes at most the real cutoff `x`, coerced to `Real`. -/
noncomputable def primeCounting (x : ℝ) : ℝ :=
  pi x

end BombieriVinogradov
