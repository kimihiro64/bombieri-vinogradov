import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Admissibility of the square-root-logarithm height

For real arguments at least three, the proposed contour height lies
between two and the argument. Its squared exponent is exactly log(x).
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sqrtLog_height_bounds {x : Real} (hx : 3 <= x) :
    And (1 <= Real.sqrt (Real.log x))
      (And ((Real.sqrt (Real.log x)) ^ 2 = Real.log x)
        (And (2 <= Real.exp (Real.sqrt (Real.log x)))
          (Real.exp (Real.sqrt (Real.log x)) <= x))) := by
  have hxPos : 0 < x := by linarith
  have hLogThree : (1 : Real) <= Real.log 3 := by
    have h := Real.le_log_one_add_of_nonneg (x := (2 : Real)) (by norm_num)
    norm_num at h
    exact h
  have hLogOne : 1 <= Real.log x :=
    hLogThree.trans (Real.log_le_log (by norm_num) hx)
  have hLogNonneg : 0 <= Real.log x := zero_le_one.trans hLogOne
  have hRootOne : 1 <= Real.sqrt (Real.log x) := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hLogOne)
  have hSquare : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hLogNonneg
  have hRootLe : Real.sqrt (Real.log x) <= Real.log x := by
    have hMul := mul_le_mul_of_nonneg_left hRootOne
      (show 0 <= Real.sqrt (Real.log x) by linarith)
    nlinarith
  have hLower : 2 <= Real.exp (Real.sqrt (Real.log x)) := by
    have h := Real.add_one_le_exp (Real.sqrt (Real.log x))
    linarith
  have hUpper : Real.exp (Real.sqrt (Real.log x)) <= x := by
    calc
      Real.exp (Real.sqrt (Real.log x)) <= Real.exp (Real.log x) :=
        Real.exp_le_exp.mpr hRootLe
      _ = x := Real.exp_log hxPos
  exact And.intro hRootOne (And.intro hSquare (And.intro hLower hUpper))

end BombieriVinogradov.RealAnalysis
