import BombieriVinogradov.Helpers.RealAnalysis.PolynomialLogDecay
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Logarithmic finite Euler mass

The exponential modulus range bounds the two logarithms by a cube
in the square-root-log variable, which has a uniform decay coefficient.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem logarithmicEulerMass_le_exp
    {a : Real} (ha : a <= (1 / 2 : Real)) {N x : Nat}
    (hN : 3 <= N) (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    Real.log N * Real.log x / Real.log (2 : Real) <=
      (48 / Real.log (2 : Real)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hxPos : (0 : Real) < (x : Real) := by linarith
  have hNPos : (0 : Real) < (N : Real) := by linarith
  let t : Real := Real.sqrt (Real.log x)
  have htOne : 1 <= t := (sqrtLog_height_bounds hxReal).1
  have hSquare : t ^ 2 = Real.log x := (sqrtLog_height_bounds hxReal).2.1
  have hModulusLog : Real.log N <= t := by
    have hLog := Real.log_le_log hNPos hMod
    simpa only [Real.log_exp, t] using hLog
  have hLogNonneg : 0 <= Real.log x := Real.log_nonneg (by linarith)
  have hMass : Real.log N * Real.log x <= t ^ 3 := by
    calc
      Real.log N * Real.log x <= t * Real.log x :=
        mul_le_mul_of_nonneg_right hModulusLog hLogNonneg
      _ = t * t ^ 2 := congrArg (fun r : Real => t * r) hSquare.symm
      _ = t ^ 3 := by ring
  have hCube : t ^ 3 <= 48 * ((x : Real) * Real.exp (-(a * t))) := by
    convert (pow_le_exponentialLog_scale (a := a) (b := (1 / 2 : Real))
      hxPos hSquare htOne (by norm_num) (by linarith) 3) using 1
    norm_num
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  calc
    Real.log N * Real.log x / Real.log (2 : Real) <=
        (48 * ((x : Real) * Real.exp (-(a * t)))) / Real.log (2 : Real) :=
      div_le_div_of_nonneg_right (hMass.trans hCube) hLogTwo.le
    _ = (48 / Real.log (2 : Real)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
      dsimp [t]
      ring

end BombieriVinogradov.RealAnalysis
