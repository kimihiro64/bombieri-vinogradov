import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Principal-character level correction

These definitions isolate the finite Euler product relating the principal
Dirichlet L-function at level `N` to the Riemann zeta function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def principalLevelCorrectionFactor
    (p : Nat) (s : Complex) : Complex :=
  1 - (p : Complex) ^ (-s)

noncomputable def principalLevelCorrection
    (N : Nat) (s : Complex) : Complex :=
  ∏ p ∈ N.primeFactors, principalLevelCorrectionFactor p s

end BombieriVinogradov.SiegelWalfisz
