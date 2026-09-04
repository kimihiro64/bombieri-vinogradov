import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Absorbing a bilinear and a linear correction

Separate coefficient arithmetic from the analytic estimates supplying the
primary and secondary nonnegative error scales.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem bilinear_linear_correction_le_scale
    {a b k j P Q : Real} (hAB : a * b <= P) (hA : a <= P)
    (hP : 0 <= P) (hQ : 0 <= Q) (hk : 0 <= k) (hj : 0 <= j) :
    k * (a * b) + j * a + Q <= (k + j + 1) * (P + Q) := by
  have hFirst := mul_le_mul_of_nonneg_left hAB hk
  have hSecond := mul_le_mul_of_nonneg_left hA hj
  have hKQ := mul_nonneg hk hQ
  have hJQ := mul_nonneg hj hQ
  nlinarith

end BombieriVinogradov.RealAnalysis
