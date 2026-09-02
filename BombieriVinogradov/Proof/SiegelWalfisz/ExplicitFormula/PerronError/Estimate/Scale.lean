import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.EndpointAbsorption
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.HarmonicGrowth
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.RangeSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeriesRange

/-!
# Source-scale Perron error estimate

This module assembles the far, central, and endpoint estimates under one
absolute constant at the published Perron-error scale.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One absolute constant controls the complete source majorant by the
`x ^ c / (T * (c - 1)) + x * log (2 * x) ^ 2 / T` scale. -/
theorem exists_tsum_sourcePerronErrorMajorantTerm_le_scale :
    Exists fun C : Real => And (0 < C) (forall x : Nat, 2 < x ->
      forall c T : Real, 1 < c -> c <= 3 -> 0 < T ->
        tsum (sourcePerronErrorMajorantTerm x c T) <=
          C * (((x : Real) ^ c / (T * (c - 1))) +
            ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T))) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div_le_three
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  have hSeries := hSpec.2
  refine Exists.intro (C0 + 51) (And.intro (by linarith) ?_)
  intro x hx c T hc1 hc3 hT
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hLogOne := one_le_log_two_mul hx
  have hLogNonneg : 0 <= Real.log (2 * (x : Real)) :=
    le_trans zero_le_one hLogOne
  have hRange := tsum_sourcePerronErrorMajorantTerm_le_ranges
    hxPos hc1 hc3 hT
  have hSeriesAt := hSeries c hc1 hc3
  have hcDenom : Ne (c - 1) 0 := ne_of_gt (sub_pos.mpr hc1)
  have hFar : ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c <=
      C0 * ((x : Real) ^ c / (T * (c - 1))) := by
    calc
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c <=
          ((x : Real) ^ c / T) * (C0 / (c - 1)) :=
        mul_le_mul_of_nonneg_left hSeriesAt (by positivity)
      _ = C0 * ((x : Real) ^ c / (T * (c - 1))) := by
        field_simp [ne_of_gt hT, hcDenom]
  have hHarmonic := harmonic_le_three_log_two_mul hxPos
  have hNear :
      2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real)) <=
      48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    calc
      2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) <=
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (3 * Real.log (2 * (x : Real)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hHarmonic (by positivity)) (by norm_num)
      _ = 48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
        ring
  have hEndpoint := endpointPerronBoundValue_le_logSquared hx
    (le_trans zero_lt_one.le hc1.le) hc3 hT
  have hCombined : tsum (sourcePerronErrorMajorantTerm x c T) <=
      C0 * ((x : Real) ^ c / (T * (c - 1))) +
        51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    calc
      tsum (sourcePerronErrorMajorantTerm x c T) <=
          ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
            2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
              (harmonic x : Real)) +
            ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := hRange
      _ <= C0 * ((x : Real) ^ c / (T * (c - 1))) +
            48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) +
            3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
        gcongr
      _ = C0 * ((x : Real) ^ c / (T * (c - 1))) +
          51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring
  have hFirstNonneg : 0 <= (x : Real) ^ c / (T * (c - 1)) := by
    positivity
  have hSecondNonneg :
      0 <= (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
    positivity
  calc
    tsum (sourcePerronErrorMajorantTerm x c T) <=
        C0 * ((x : Real) ^ c / (T * (c - 1))) +
          51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := hCombined
    _ <= (C0 + 51) * (((x : Real) ^ c / (T * (c - 1))) +
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := by
      nlinarith [mul_nonneg hC0.le hSecondNonneg,
        mul_nonneg (by norm_num : (0 : Real) <= 51) hFirstNonneg]

end BombieriVinogradov.SiegelWalfisz
