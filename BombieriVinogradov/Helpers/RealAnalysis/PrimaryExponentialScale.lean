import BombieriVinogradov.Helpers.RealAnalysis.PolynomialDecayRate
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The primary source remainder at an exponential height

A logarithmic numerator at most twice t squared is absorbed using
degree-four Taylor decay. The coefficient is uniform for all a <= 1/2.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem div_exp_mul_sq_le_primary_decay
    {x t H a : Real} (hx : 0 <= x) (ht : 0 <= t)
    (hH : 0 <= H) (hUpper : H <= 2 * t ^ 2) (ha : a <= (1 / 2 : Real)) :
    x / Real.exp t * H ^ 2 <= 1536 * (x * Real.exp (-(a * t))) := by
  have hFourth : t ^ 4 * Real.exp (-t) <=
      384 * Real.exp (-((1 / 2 : Real) * t)) := by
    convert (pow_mul_exp_neg_le_factorial_div_pow_mul_exp
      (a := (1 / 2 : Real)) (b := (1 : Real))
      (by norm_num) (by norm_num) ht 4) using 1 <;> norm_num
  have hSquare : H ^ 2 <= 4 * t ^ 4 := by
    have hSq : 0 <= t ^ 2 := by positivity
    calc
      H ^ 2 <= (2 * t ^ 2) ^ 2 := sq_le_sq' (by linarith) hUpper
      _ = 4 * t ^ 4 := by ring
  have hDecay : Real.exp (-((1 / 2 : Real) * t)) <= Real.exp (-(a * t)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ha ht
    linarith
  have hPolynomial : t ^ 4 * Real.exp (-t) <= 384 * Real.exp (-(a * t)) :=
    hFourth.trans (mul_le_mul_of_nonneg_left hDecay (by norm_num))
  calc
    x / Real.exp t * H ^ 2 <= x / Real.exp t * (4 * t ^ 4) :=
      mul_le_mul_of_nonneg_left hSquare (by positivity)
    _ = (4 * x) * (t ^ 4 * Real.exp (-t)) := by
      rw [Real.exp_neg]
      field_simp
    _ <= (4 * x) * (384 * Real.exp (-(a * t))) :=
      mul_le_mul_of_nonneg_left hPolynomial (by positivity)
    _ = 1536 * (x * Real.exp (-(a * t))) := by ring

end BombieriVinogradov.RealAnalysis
