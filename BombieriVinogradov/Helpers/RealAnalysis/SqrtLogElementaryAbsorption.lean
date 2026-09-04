import BombieriVinogradov.Helpers.RealAnalysis.QuadraticExponentialAbsorption
import BombieriVinogradov.Helpers.RealAnalysis.SqrtExponentialLogFactorization
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary square-root terms in an exponential-log scale

A half-quadratic exponential absorbs the logarithmic square with coefficient
thirty-two. The allowed linear rate is at most one quarter.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Absorb a square-root times a logarithmic square in the selected decay scale. -/
theorem sqrt_mul_sq_le_exponentialLog_scale {x t a : Real}
    (hx : 0 < x) (hSquare : t ^ 2 = Real.log x) (ht : 1 <= t)
    (ha : a <= (1 / 4 : Real)) :
    Real.sqrt x * t ^ 2 <= 32 * (x * Real.exp (-(a * t))) := by
  have hQuadratic :
      t ^ 2 * Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t) <= 32 := by
    have hRate : a + (1 / 4 : Real) <= (1 / 2 : Real) := by linarith
    have h := pow_mul_exp_quadratic_le_factorial_div_pow
      (r := (1 / 2 : Real)) (b := (1 / 4 : Real)) (a := a) (t := t)
      (by norm_num) (by norm_num) hRate ht 2
    convert h using 1
    norm_num
  have hFactor := sqrt_exponentialLog_scale_factorization (a := a) hx hSquare
  have hScale : 0 <= x * Real.exp (-(a * t)) := by positivity
  calc
    Real.sqrt x * t ^ 2 = ((x * Real.exp (-(a * t))) *
        Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t)) * t ^ 2 := by rw [hFactor]
    _ = (x * Real.exp (-(a * t))) *
        (t ^ 2 * Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t)) := by ring
    _ <= (x * Real.exp (-(a * t))) * 32 :=
      mul_le_mul_of_nonneg_left hQuadratic hScale
    _ = 32 * (x * Real.exp (-(a * t))) := by ring

/-- The elementary square-root logarithmic term has the same uniform decay scale. -/
theorem sqrt_mul_log_le_exponentialLog_scale {x a : Real}
    (hx : 0 < x) (hLog : 1 <= Real.log x) (ha : a <= (1 / 4 : Real)) :
    Real.sqrt x * Real.log x <=
      32 * (x * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hLogNonneg : 0 <= Real.log x := by linarith
  have hSquare := Real.sq_sqrt hLogNonneg
  have h := sqrt_mul_sq_le_exponentialLog_scale (a := a) hx hSquare
    (Real.one_le_sqrt.mpr hLog) ha
  rw [hSquare] at h
  exact h

end BombieriVinogradov.RealAnalysis
