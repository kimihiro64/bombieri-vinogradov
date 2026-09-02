import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.UnitPerronTermBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Unit-point Perron source-sum bound

This module lifts the pointwise x equals one comparison through the infinite
source-majorant sum.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The full x equals one Perron source majorant is controlled by the standard
von Mangoldt L-series norm sum. -/
theorem tsum_sourcePerronErrorMajorantTerm_one_le_vonMangoldtSum
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    tsum (sourcePerronErrorMajorantTerm 1 c T) <=
      vonMangoldtLSeriesNormSum c := by
  have hSource := summable_sourcePerronErrorMajorantTerm
    (x := 1) (Nat.zero_lt_succ 0) hc hT
  have hLSeries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  unfold vonMangoldtLSeriesNormSum
  exact hSource.tsum_le_tsum
    (sourcePerronErrorMajorantTerm_one_le_vonMangoldtTerm c T)
    hLSeries.norm

end BombieriVinogradov.SiegelWalfisz
