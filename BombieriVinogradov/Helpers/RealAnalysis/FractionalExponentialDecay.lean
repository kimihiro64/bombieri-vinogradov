import BombieriVinogradov.Helpers.RealAnalysis.CubicQuarticExponential
import BombieriVinogradov.Helpers.RealAnalysis.SixthRootPowers
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Fractional-power exponential decay at a fixed rate

Two-thirds-power damping absorbs any fixed square-root exponent
at a multiplicative cost depending only on the two coefficients.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_neg_twoThirds_le_exp_sqrt
    {a k L : Real} (ha : 0 <= a) (hk : 0 < k) (hL : 0 <= L) :
    Real.exp (-(k * L ^ (2 / 3 : Real))) <=
      Real.exp (a ^ 4 / k ^ 3) * Real.exp (-(a * Real.sqrt L)) := by
  have h := exp_neg_quartic_le_exp_cubic ha hk (Real.rpow_nonneg hL (1 / 6))
  simpa only [sixthRoot_fourth_eq_twoThirds hL, sixthRoot_cube_eq_sqrt hL] using h

end BombieriVinogradov.RealAnalysis
