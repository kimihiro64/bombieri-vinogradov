import BombieriVinogradov.Helpers.RealAnalysis.PrimaryExponentialScale
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The primary remainder for natural endpoints

The exponential modulus range bounds the product logarithm by twice
log(x), allowing the uniform degree-four absorption at the chosen height.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primaryRemainder_selectedHeight_le_exp
    {a : Real} (ha : a <= (1 / 2 : Real)) {N x : Nat}
    (hN : 3 <= N) (hx : 3 <= x)
    (hModulus : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    (x : Real) / Real.exp (Real.sqrt (Real.log x)) *
      Real.log ((N * x : Nat) : Real) ^ 2 <=
        1536 * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  let t : Real := Real.sqrt (Real.log x)
  let H : Real := Real.log ((N * x : Nat) : Real)
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hxPos : 0 < (x : Real) := by linarith
  have hNPos : 0 < (N : Real) := by linarith
  have hGeometry := BombieriVinogradov.RealAnalysis.sqrtLog_height_bounds hxReal
  have htOne : 1 <= t := hGeometry.1
  have htNonneg : 0 <= t := by linarith
  have hSquare : t ^ 2 = Real.log x := hGeometry.2.1
  have htLeSquare : t <= t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left htOne htNonneg
    nlinarith
  have hProduct : H = Real.log N + Real.log x := by
    dsimp [H]
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hNPos) (ne_of_gt hxPos)]
  have hModulusLog : Real.log N <= t := by
    have h := Real.log_le_log hNPos hModulus
    simpa only [Real.log_exp, t] using h
  have hLogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hLogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hH : 0 <= H := by
    rw [hProduct]
    linarith
  have hUpper : H <= 2 * t ^ 2 := by
    rw [hProduct]
    linarith
  have hBound := BombieriVinogradov.RealAnalysis.div_exp_mul_sq_le_primary_decay
    (Nat.cast_nonneg x) htNonneg hH hUpper ha
  simpa only [t, H] using hBound

end BombieriVinogradov.SiegelWalfisz
