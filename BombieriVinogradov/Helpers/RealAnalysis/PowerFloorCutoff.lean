import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Natural cutoffs of real powers

Exponents at most one give cutoffs below the original real endpoint.
Negative exponents and the resulting zero cutoff are included.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A power cutoff with exponent at most one is bounded by its endpoint. -/
theorem floor_rpow_le_self {X theta : Real} (hX : 1 <= X) (hTheta : theta <= 1) :
    (Nat.floor (X ^ theta) : Real) <= X := by
  calc
    (Nat.floor (X ^ theta) : Real) <= X ^ theta :=
      Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hX) theta)
    _ <= X ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hX hTheta
    _ = X := Real.rpow_one X

end BombieriVinogradov.RealAnalysis
