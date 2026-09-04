import BombieriVinogradov.Helpers.RealAnalysis.PowerExponentialCutoff
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Inclusion of the large-height small-modulus range

The explicit cutoff ensures that the polylogarithmic modulus bound
is within the range of the uniform exceptional character estimate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem modulus_le_exp_sqrtLog_of_large
    {A : Real} (hA : 0 <= A) {N x : Nat} (hx : 3 <= x)
    (hMod : (N : Real) <= (Real.log x) ^ A)
    (hThreshold : 16 * A ^ 2 <= Real.sqrt (Real.log x)) :
    (N : Real) <= Real.exp (Real.sqrt (Real.log x)) := by
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hGeometry := BombieriVinogradov.RealAnalysis.sqrtLog_height_bounds hxReal
  have hCutoff := BombieriVinogradov.RealAnalysis.sq_rpow_le_exp_of_large
    hA hGeometry.1 hThreshold
  have hPower : (Real.log x) ^ A <= Real.exp (Real.sqrt (Real.log x)) := by
    simpa only [hGeometry.2.1] using hCutoff
  exact hMod.trans hPower

end BombieriVinogradov.SiegelWalfisz
