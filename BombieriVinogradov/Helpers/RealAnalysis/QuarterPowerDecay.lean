import BombieriVinogradov.Helpers.RealAnalysis.QuadraticExponentialAbsorption
import BombieriVinogradov.Helpers.RealAnalysis.QuarterPowerFactorization
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential decay of the secondary source remainder

The exact quarter-power factorization reduces the complete real
source term to the proved quadratic exponential bound.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem quarterPower_log_le_secondary_decay
    {x a : Real} (hx : 3 <= x) (ha : a <= (1 / 2 : Real)) :
    x ^ (1 / 4 : Real) * Real.log x <=
      32 * (x * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxPos : 0 < x := by linarith
  have hGeometry := sqrtLog_height_bounds hx
  have hBound := sq_mul_exp_quadratic_le_thirty_two ha hGeometry.1
  calc
    x ^ (1 / 4 : Real) * Real.log x =
        (x * Real.exp (-(a * Real.sqrt (Real.log x)))) *
          ((Real.sqrt (Real.log x)) ^ 2 *
            Real.exp (-(3 / 4 : Real) * (Real.sqrt (Real.log x)) ^ 2 +
              a * Real.sqrt (Real.log x))) :=
      quarterPower_log_factorization hxPos hGeometry.2.1
    _ <= (x * Real.exp (-(a * Real.sqrt (Real.log x)))) * 32 :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = 32 * (x * Real.exp (-(a * Real.sqrt (Real.log x)))) := by ring

end BombieriVinogradov.RealAnalysis
