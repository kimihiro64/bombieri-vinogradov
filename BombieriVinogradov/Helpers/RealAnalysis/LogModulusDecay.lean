import BombieriVinogradov.Helpers.RealAnalysis.ExponentialSquareGap
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Decay from an ambient logarithmic gap

The exponential modulus range converts c/log(N) times log(x)
into one uniform multiple of the square-root-log variable.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_neg_logModulus_gap_le_exp
    {c a : Real} (hc : 0 < c) (hRate : a <= c / 4) {N x : Nat}
    (hN : 3 <= N) (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    Real.exp (-(c / Real.log N) * Real.log x) <=
      Real.exp (-(a * Real.sqrt (Real.log x))) := by
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hNPos : (0 : Real) < (N : Real) := by linarith
  have hLogN : 0 < Real.log N := Real.log_pos (by linarith)
  let t : Real := Real.sqrt (Real.log x)
  have htOne : 1 <= t := (sqrtLog_height_bounds hxReal).1
  have htPos : 0 < t := by linarith
  have hSquare : t ^ 2 = Real.log x := (sqrtLog_height_bounds hxReal).2.1
  have hLogUpper : Real.log N <= t := by
    simpa only [Real.log_exp, t] using Real.log_le_log hNPos hMod
  have hGap := exp_reciprocal_gap_sq_le_exp_linear hc htPos hLogN
    (show Real.log N <= 4 * t by linarith)
  have hBase : Real.exp (-(c / Real.log N) * Real.log x) <=
      Real.exp (-((c / 4) * t)) := by
    simpa only [hSquare] using hGap
  exact hBase.trans (Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_right hRate htPos.le)))

end BombieriVinogradov.RealAnalysis
