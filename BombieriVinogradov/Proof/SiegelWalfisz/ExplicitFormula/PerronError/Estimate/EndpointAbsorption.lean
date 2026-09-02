import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.EndpointBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.HarmonicGrowth
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Absorbing the Perron endpoint

This module absorbs the exact singleton endpoint term into the same
`x * log (2 * x) ^ 2 / T` scale as the central harmonic ranges.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For `x > 2` and `c <= 3`, the endpoint is bounded by three copies of the
central logarithmic scale. -/
theorem endpointPerronBoundValue_le_logSquared
    {x : Nat} (hx : 2 < x) {c T : Real}
    (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) :
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
      3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hxPos
  have hLogOne := one_le_log_two_mul hx
  have hLogNonneg : 0 <= Real.log (2 * (x : Real)) := le_trans zero_le_one hLogOne
  have hLambdaLog : ArithmeticFunction.vonMangoldt x <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hxReal (by nlinarith [hxReal]))
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hDenom : T <= Real.pi * T := by
    nlinarith [hT, hPiOne]
  have hReciprocal : 1 / (Real.pi * T) <= 1 / T :=
    one_div_le_one_div_of_le hT hDenom
  have hFactor : c / (Real.pi * T) <= 3 / T := by
    calc
      c / (Real.pi * T) = c * (1 / (Real.pi * T)) := by ring
      _ <= c * (1 / T) := mul_le_mul_of_nonneg_left hReciprocal hc0
      _ <= 3 * (1 / T) := by
        exact mul_le_mul_of_nonneg_right hc3 (by positivity)
      _ = 3 / T := by ring
  have hFirst : ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
      Real.log (2 * (x : Real)) * (3 / T) := by
    exact mul_le_mul hLambdaLog hFactor (by positivity) hLogNonneg
  have hXL : (1 : Real) <= (x : Real) * Real.log (2 * (x : Real)) := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= (x : Real) * Real.log (2 * (x : Real)) :=
        mul_le_mul hxOne hLogOne zero_le_one hxReal.le
  calc
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
        Real.log (2 * (x : Real)) * (3 / T) := hFirst
    _ = (Real.log (2 * (x : Real)) * (3 / T)) * 1 := by ring
    _ <= (Real.log (2 * (x : Real)) * (3 / T)) *
        ((x : Real) * Real.log (2 * (x : Real))) :=
      mul_le_mul_of_nonneg_left hXL (mul_nonneg hLogNonneg (by positivity))
    _ = 3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by ring

end BombieriVinogradov.SiegelWalfisz
