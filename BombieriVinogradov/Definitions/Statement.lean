import BombieriVinogradov.Definitions.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Bombieri-Vinogradov target

The target is Maynard's level-of-distribution formulation from equation (1.3),
with the quantifiers and endpoints used by `PrimeGapsLib` commit
`1faa7b14e82ddebc2772dfb9153922f01b106477`.
-/

namespace BombieriVinogradov

open Finset Nat Real

/-- The prime-counting discrepancy in the reduced residue class `a` modulo `q`. -/
noncomputable def primeDiscrepancy (x : Real) (q : Nat) (a : (ZMod q)ˣ) : Real :=
  |(Real.primeCountingZMod x q a : Real) - primeCounting x / q.totient|

/-- The maximum prime-counting discrepancy over reduced residue classes modulo `q`. -/
noncomputable def maxPrimeDiscrepancy (x : Real) (q : Nat) : Real :=
  ⨆ a : (ZMod q)ˣ, primeDiscrepancy x q a

/-- The averaged maximum discrepancy up to the modulus cutoff `floor(x^theta)`. -/
noncomputable def averagePrimeDiscrepancy (x theta : Real) : Real :=
  ∑ q ∈ Icc (1 : Nat) ⌊x ^ theta⌋₊, maxPrimeDiscrepancy x q

/--
The exact Bombieri-Vinogradov proposition targeted by this project.

It deliberately asserts every `theta < 1/2`, not the endpoint `theta = 1/2`,
and uses the unweighted prime count `pi(x; q, a)` rather than a Chebyshev sum.
-/
def Statement : Prop :=
  ∀ theta < (1 / 2 : Real), ∀ A ≥ (1 : Real), ∃ c > (0 : Real), ∀ x ≥ (3 : Real),
    averagePrimeDiscrepancy x theta ≤ c * x / x.log ^ A

end BombieriVinogradov
