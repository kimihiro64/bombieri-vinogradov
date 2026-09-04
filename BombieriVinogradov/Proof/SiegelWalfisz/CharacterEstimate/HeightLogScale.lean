import BombieriVinogradov.Helpers.RealAnalysis.ExponentialHeightLog
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Common logarithmic scale at the square-root-log height

The exponential modulus restriction and the rounded height bound control
both denominator logarithms and reciprocal-sum logarithms by one scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem sqrtLogHeight_log_scales {N x : Nat} (hN : 3 <= N) (hx : 3 <= x)
    (hModulus : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    And (Real.log N + Real.log (Real.exp (Real.sqrt (Real.log x)) + 2) <=
      4 * Real.sqrt (Real.log x))
      (Real.log N +
        Real.log (((Nat.ceil (Real.exp (Real.sqrt (Real.log x))) : Nat) : Real) + 2) <=
          4 * Real.sqrt (Real.log x)) := by
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hNPos : 0 < (N : Real) := by linarith
  have hRoot := (BombieriVinogradov.RealAnalysis.sqrtLog_height_bounds hxReal).1
  have hCeilLog := BombieriVinogradov.RealAnalysis.log_ceil_exp_add_two_le_three_mul hRoot
  have hModulusLog : Real.log N <= Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hNPos hModulus
    simpa only [Real.log_exp] using h
  have hRound := Nat.le_ceil (Real.exp (Real.sqrt (Real.log x)))
  have hHeightPos : 0 < Real.exp (Real.sqrt (Real.log x)) :=
    Real.exp_pos (Real.sqrt (Real.log x))
  have hHeightLog :
      Real.log (Real.exp (Real.sqrt (Real.log x)) + 2) <=
        Real.log (((Nat.ceil (Real.exp (Real.sqrt (Real.log x))) : Nat) : Real) + 2) := by
    apply Real.log_le_log (by linarith)
    linarith
  exact And.intro (by linarith) (by linarith)

end BombieriVinogradov.SiegelWalfisz
