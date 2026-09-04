import BombieriVinogradov.Helpers.RealAnalysis.SqrtEndpointLog
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exponential-logarithmic decay above a square-root endpoint

An endpoint between sqrt(X) and X inherits a common X-scale estimate with
half the original exponential rate. No monotonicity of the product is assumed.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Above sqrt(X), replacing the endpoint by X costs only half the decay rate. -/
theorem mul_exp_neg_sqrt_log_le_of_sqrt_le {X y a : Real}
    (hX : 1 <= X) (hy : Real.sqrt X <= y) (hyX : y <= X) (ha : 0 <= a) :
    y * Real.exp (-(a * Real.sqrt (Real.log y))) <=
      X * Real.exp (-((a / 2) * Real.sqrt (Real.log X))) := by
  have hRoot := sqrt_log_le_two_mul_sqrt_log_of_sqrt_le hX hy
  have hRate := mul_le_mul_of_nonneg_left hRoot ha
  have hDecay : Real.exp (-(a * Real.sqrt (Real.log y))) <=
      Real.exp (-((a / 2) * Real.sqrt (Real.log X))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hXNonneg : 0 <= X := by linarith
  calc
    y * Real.exp (-(a * Real.sqrt (Real.log y))) <=
        X * Real.exp (-(a * Real.sqrt (Real.log y))) :=
      mul_le_mul_of_nonneg_right hyX (Real.exp_pos _).le
    _ <= X * Real.exp (-((a / 2) * Real.sqrt (Real.log X))) :=
      mul_le_mul_of_nonneg_left hDecay hXNonneg

end BombieriVinogradov.RealAnalysis
