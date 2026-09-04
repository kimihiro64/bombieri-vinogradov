import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A reciprocal logarithmic gap at a square scale

A positive denominator at most four times t converts the square-scale
zero-free exponent into a uniform linear exponential decay exponent.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_reciprocal_gap_sq_le_exp_linear
    {c D t : Real} (hc : 0 < c) (ht : 0 < t)
    (hD : 0 < D) (hUpper : D <= 4 * t) :
    Real.exp (-(c / D) * t ^ 2) <= Real.exp (-((c / 4) * t)) := by
  have hRatio : c / (4 * t) <= c / D :=
    div_le_div_of_nonneg_left hc.le hD hUpper
  have hProduct := mul_le_mul_of_nonneg_right hRatio (show 0 <= t ^ 2 by positivity)
  have hCancel : c / (4 * t) * t ^ 2 = (c / 4) * t := by field_simp
  rw [hCancel] at hProduct
  apply Real.exp_le_exp.mpr
  linarith

end BombieriVinogradov.RealAnalysis
