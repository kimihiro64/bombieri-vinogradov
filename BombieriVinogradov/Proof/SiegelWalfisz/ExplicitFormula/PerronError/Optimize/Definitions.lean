import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Optimized Perron line

This module defines the real part of the source contour after optimizing the
Perron truncation error.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The source choice `c = 1 + 1 / log x`. -/
def optimizedPerronLine (x : Nat) : Real :=
  1 + 1 / Real.log (x : Real)

end BombieriVinogradov.SiegelWalfisz
