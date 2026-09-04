import BombieriVinogradov.Helpers.RealAnalysis.ExponentialSquareGap
import BombieriVinogradov.Helpers.RealAnalysis.PolynomialDecayRate
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A quadratic logarithmic factor absorbed at a reciprocal gap

The zero-free denominator and the reciprocal-sum logarithm can both be
replaced by their linear cutoff scale before applying Taylor absorption.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_reciprocal_gap_mul_sq_le_exp
    {K x c D H t a : Real} (hK : 0 <= K) (hx : 0 <= x)
    (hc : 0 < c) (ha : 0 < a) (hRate : 2 * a <= c / 4)
    (ht : 0 < t) (hD : 0 < D) (hDUpper : D <= 4 * t)
    (hH : 0 <= H) (hHUpper : H <= 4 * t) :
    K * (x * Real.exp (-(c / D) * t ^ 2)) * H ^ 2 <=
      (32 * K / a ^ 2) * (x * Real.exp (-(a * t))) := by
  have hGap := exp_reciprocal_gap_sq_le_exp_linear hc ht hD hDUpper
  have hSquare : H ^ 2 <= 16 * t ^ 2 := by
    calc
      H ^ 2 <= (4 * t) ^ 2 := sq_le_sq' (by linarith) hHUpper
      _ = 16 * t ^ 2 := by ring
  have hPolynomial : t ^ 2 * Real.exp (-((c / 4) * t)) <=
      (2 / a ^ 2) * Real.exp (-(a * t)) := by
    simpa using (pow_mul_exp_neg_le_factorial_div_pow_mul_exp ha hRate ht.le 2)
  calc
    K * (x * Real.exp (-(c / D) * t ^ 2)) * H ^ 2 <=
        K * (x * Real.exp (-(c / D) * t ^ 2)) * (16 * t ^ 2) :=
      mul_le_mul_of_nonneg_left hSquare (by positivity)
    _ <= K * (x * Real.exp (-((c / 4) * t))) * (16 * t ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGap hx) hK)
        (by positivity)
    _ = (16 * K * x) * (t ^ 2 * Real.exp (-((c / 4) * t))) := by ring
    _ <= (16 * K * x) * ((2 / a ^ 2) * Real.exp (-(a * t))) :=
      mul_le_mul_of_nonneg_left hPolynomial (by positivity)
    _ = (32 * K / a ^ 2) * (x * Real.exp (-(a * t))) := by ring

end BombieriVinogradov.RealAnalysis
