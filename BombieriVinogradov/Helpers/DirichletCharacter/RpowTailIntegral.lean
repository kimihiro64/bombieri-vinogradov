import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact logarithm-free power tail integral

This module owns the elementary integral used in the character Abel-kernel
norm estimate.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BombieriVinogradov

/-- The tail integral of `t^(-sigma-1)` is `1/sigma` for positive `sigma`. -/
theorem integral_Ioi_rpow_neg_add_one {sigma : Real} (hsigma : 0 < sigma) :
    ∫ t : Real in Ioi 1, t ^ (-(sigma + 1)) = 1 / sigma := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have hDenominator : -(sigma + 1) + 1 = -sigma := by ring
  rw [hDenominator]
  field_simp [hsigma.ne']

end BombieriVinogradov
