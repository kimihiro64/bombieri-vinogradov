import BombieriVinogradov.Helpers.RealAnalysis.LogSqrtGrowth
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An explicit cutoff for logarithmic growth

At t at least sixteen times the squared coefficient, the logarithmic
factor two A log t is no larger than t.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem two_mul_mul_log_le_of_large
    {A t : Real} (hA : 0 <= A) (ht : 1 <= t) (hThreshold : 16 * A ^ 2 <= t) :
    (2 * A) * Real.log t <= t := by
  have htPos : 0 < t := by linarith
  have hSquare : (4 * A) ^ 2 <= t := by nlinarith only [hThreshold]
  have hFourA : 4 * A <= Real.sqrt t :=
    (Real.le_sqrt (by positivity) htPos.le).mpr hSquare
  have hLog := log_le_two_mul_sqrt htPos
  calc
    (2 * A) * Real.log t <= (2 * A) * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hLog (by positivity)
    _ = (4 * A) * Real.sqrt t := by ring
    _ <= Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_right hFourA (Real.sqrt_nonneg t)
    _ = t := Real.mul_self_sqrt htPos.le

end BombieriVinogradov.RealAnalysis
