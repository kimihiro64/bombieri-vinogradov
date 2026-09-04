import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic geometry above a square-root endpoint

An endpoint above the square root retains at least half the logarithmic size
and at least half the square-root logarithmic decay parameter.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Above the square-root endpoint, the logarithm loses at most a factor two. -/
theorem log_le_two_mul_log_of_sqrt_le {X y : Real}
    (hX : 1 <= X) (hy : Real.sqrt X <= y) :
    Real.log X <= 2 * Real.log y := by
  have hXPos : 0 < X := by linarith
  have hLog := Real.log_le_log (Real.sqrt_pos.mpr hXPos) hy
  rw [Real.log_sqrt hXPos.le] at hLog
  linarith

/-- The square-root logarithmic parameter also loses at most a factor two. -/
theorem sqrt_log_le_two_mul_sqrt_log_of_sqrt_le {X y : Real}
    (hX : 1 <= X) (hy : Real.sqrt X <= y) :
    Real.sqrt (Real.log X) <= 2 * Real.sqrt (Real.log y) := by
  have hLog := log_le_two_mul_log_of_sqrt_le hX hy
  have hLogX : 0 <= Real.log X := Real.log_nonneg hX
  have hLogY : 0 <= Real.log y := by linarith
  have hSquare := Real.sq_sqrt hLogY
  apply Real.sqrt_le_iff.mpr
  exact And.intro (by positivity) (by nlinarith)

end BombieriVinogradov.RealAnalysis
