import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.NearSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.PointwiseAssembly
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceSummable

/-!
# Summed Perron range decomposition

This module sums the four pointwise range bounds, leaving the far L-series,
two harmonic factors, and the singleton endpoint contribution explicit.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The source majorant is bounded by its far L-series contribution, two
harmonic central ranges, and the exact endpoint term. -/
theorem tsum_sourcePerronErrorMajorantTerm_le_ranges
    {x : Nat} (hx : 0 < x) {c T : Real}
    (hc1 : 1 < c) (hc3 : c <= 3) (hT : 0 < T) :
    tsum (sourcePerronErrorMajorantTerm x c T) <=
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) +
        ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  have hSource := summable_sourcePerronErrorMajorantTerm hx hc1 hT
  have hFar := summable_farSourcePerronErrorTerm hx hc1 hT
  have hLower := summable_lowerNearPerronBound x T
  have hEndpoint := summable_endpointPerronBound x c T
  have hUpper := summable_upperNearPerronBound x T
  have hAll := ((hFar.add hLower).add hEndpoint).add hUpper
  have hDecomposition :
      tsum (sourcePerronErrorMajorantTerm x c T) <=
        tsum (farSourcePerronErrorTerm x c T) +
          tsum (lowerNearPerronBound x T) +
          tsum (endpointPerronBound x c T) +
          tsum (upperNearPerronBound x T) := by
    calc
      tsum (sourcePerronErrorMajorantTerm x c T) <=
          tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n +
              endpointPerronBound x c T n +
              upperNearPerronBound x T n) :=
        hSource.tsum_le_tsum
          (sourcePerronErrorMajorantTerm_le_decomposition hx
            (le_trans zero_lt_one.le hc1.le) hc3 hT) hAll
      _ = tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n +
              endpointPerronBound x c T n) +
            tsum (upperNearPerronBound x T) :=
        ((hFar.add hLower).add hEndpoint).tsum_add hUpper
      _ = (tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n) +
            tsum (endpointPerronBound x c T)) +
            tsum (upperNearPerronBound x T) := by
        rw [(hFar.add hLower).tsum_add hEndpoint]
      _ = ((tsum (farSourcePerronErrorTerm x c T) +
            tsum (lowerNearPerronBound x T)) +
            tsum (endpointPerronBound x c T)) +
            tsum (upperNearPerronBound x T) := by
        rw [hFar.tsum_add hLower]
  rw [tsum_lowerNearPerronBound_eq,
    tsum_endpointPerronBound_eq, tsum_upperNearPerronBound_eq] at hDecomposition
  calc
    tsum (sourcePerronErrorMajorantTerm x c T) <=
        tsum (farSourcePerronErrorTerm x c T) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) +
          ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) := hDecomposition
    _ <= ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) +
          ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) := by
      gcongr
      exact tsum_farSourcePerronErrorTerm_le hx hc1 hT
    _ = ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) +
        ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by ring

end BombieriVinogradov.SiegelWalfisz
