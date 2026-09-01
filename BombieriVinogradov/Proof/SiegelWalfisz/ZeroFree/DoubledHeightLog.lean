import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

/-!
# Logarithmic control after doubling a zero height

The squared-character term is evaluated at twice the original height. This
module absorbs that doubling into two copies of the original logarithm.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem log_double_height_le (t : Real) :
    Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have hArgumentPos : 0 < 2 * |t| + 2 := by positivity
  have hBasePos : 0 < |t| + 2 := by positivity
  have hArgumentLe : 2 * |t| + 2 ≤ (|t| + 2) ^ 2 := by
    nlinarith [sq_nonneg |t|]
  calc
    Real.log (|2 * t| + 2) = Real.log (2 * |t| + 2) := by
      rw [abs_mul]
      norm_num
    _ ≤ Real.log ((|t| + 2) ^ 2) :=
      Real.log_le_log hArgumentPos hArgumentLe
    _ = 2 * Real.log (|t| + 2) := by
      rw [Real.log_pow]
      norm_num

theorem log_square_point_height_le (sigma t : Real) :
    Real.log (|((sigma : Complex) + 2 * Complex.I * t).im| + 2) ≤
      2 * Real.log (|t| + 2) := by
  have hIm : ((sigma : Complex) + 2 * Complex.I * t).im = 2 * t := by
    simp [Complex.mul_im]
  rw [hIm]
  exact log_double_height_le t

end BombieriVinogradov.SiegelWalfisz
