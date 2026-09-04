import BombieriVinogradov.Helpers.RealAnalysis.ExponentialQuadraticScale
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.HeightLogScale
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The retained-zero scale at the chosen contour height

The real-analytic scale estimate is specialized to the logarithmic
geometry of a natural endpoint and a modulus in the exponential range.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem selectedZeroSumScale_le_exp
    {K c a : Real} (hK : 0 <= K) (hc : 0 < c) (ha : 0 < a)
    (hRate : 2 * a <= c / 4) {N x : Nat} (hN : 3 <= N) (hx : 3 <= x)
    (hModulus : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    K * ((x : Real) * Real.exp
      (-(c / (Real.log N + Real.log (Real.exp (Real.sqrt (Real.log x)) + 2))) *
        Real.log x)) *
      (Real.log N +
        Real.log (((Nat.ceil (Real.exp (Real.sqrt (Real.log x))) : Nat) : Real) + 2)) ^ 2 <=
      (32 * K / a ^ 2) * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  let t : Real := Real.sqrt (Real.log x)
  let T : Real := Real.exp t
  let D : Real := Real.log N + Real.log (T + 2)
  let H : Real := Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)
  change K * ((x : Real) * Real.exp (-(c / D) * Real.log x)) * H ^ 2 <=
    (32 * K / a ^ 2) * ((x : Real) * Real.exp (-(a * t)))
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hGeometry := BombieriVinogradov.RealAnalysis.sqrtLog_height_bounds hxReal
  have htOne : 1 <= t := hGeometry.1
  have hSquare : t ^ 2 = Real.log x := hGeometry.2.1
  have hBounds : And (D <= 4 * t) (H <= 4 * t) := by
    simpa only [D, H, T, t] using sqrtLogHeight_log_scales hN hx hModulus
  have hLogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hTPos : 0 < T := Real.exp_pos t
  have hLogT : 0 <= Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hCeilNonneg : (0 : Real) <= ((Nat.ceil T : Nat) : Real) :=
    Nat.cast_nonneg (Nat.ceil T)
  have hLogCeil : 0 <= Real.log (((Nat.ceil T : Nat) : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hH : 0 <= H := by
    dsimp [H]
    linarith
  have hEstimate := BombieriVinogradov.RealAnalysis.exp_reciprocal_gap_mul_sq_le_exp
    hK (Nat.cast_nonneg x) hc ha hRate (show 0 < t by linarith)
      hD hBounds.1 hH hBounds.2
  calc
    K * ((x : Real) * Real.exp (-(c / D) * Real.log x)) * H ^ 2 =
        K * ((x : Real) * Real.exp (-(c / D) * t ^ 2)) * H ^ 2 := by rw [hSquare]
    _ <= (32 * K / a ^ 2) * ((x : Real) * Real.exp (-(a * t))) := hEstimate

end BombieriVinogradov.SiegelWalfisz
