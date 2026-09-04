import BombieriVinogradov.Helpers.RealAnalysis.LogarithmicCutoff
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An explicit power-versus-exponential cutoff

The logarithmic cutoff converts directly to a real-power comparison
by the exact logarithm of the square and exponential monotonicity.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sq_rpow_le_exp_of_large
    {A t : Real} (hA : 0 <= A) (ht : 1 <= t) (hThreshold : 16 * A ^ 2 <= t) :
    (t ^ 2) ^ A <= Real.exp t := by
  have htPos : 0 < t := by linarith
  have hSquarePos : 0 < t ^ 2 := by positivity
  have hLogSquare : Real.log (t ^ 2) = 2 * Real.log t := Real.log_pow t 2
  have hLogProduct : Real.log (t ^ 2) * A = (2 * A) * Real.log t := by
    rw [hLogSquare]
    ring
  calc
    (t ^ 2) ^ A = Real.exp (Real.log (t ^ 2) * A) :=
      Real.rpow_def_of_pos hSquarePos A
    _ = Real.exp ((2 * A) * Real.log t) := congrArg Real.exp hLogProduct
    _ <= Real.exp t := Real.exp_le_exp.mpr (two_mul_mul_log_le_of_large hA ht hThreshold)

end BombieriVinogradov.RealAnalysis
