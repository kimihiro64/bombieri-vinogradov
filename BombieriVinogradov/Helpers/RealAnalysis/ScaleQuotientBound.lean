import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Positive-scale normalization of a centered bound

A scaled absolute error can be divided by its positive scale without
changing the center or the comparison coefficient.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem abs_sub_div_le_of_abs_mul_sub_le {t p q B : Real}
    (ht : 0 < t) (h : abs (t * p - q) <= B) :
    abs (p - q / t) <= B / t := by
  have hId : t * (p - q / t) = t * p - q := by field_simp
  have hQuotient : t * (B / t) = B := by field_simp
  have hAbs : abs (t * p - q) = t * abs (p - q / t) := by
    rw [<- hId, abs_mul, abs_of_pos ht]
  have hScaled : t * abs (p - q / t) <= t * (B / t) := by
    rw [<- hAbs, hQuotient]
    exact h
  exact le_of_mul_le_mul_left hScaled ht

end BombieriVinogradov.RealAnalysis
