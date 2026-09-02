import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.ErrorSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.HalfSumBridge

/-!
# Perron error bound for the character Chebyshev sum

This module assembles the exact finite-height Perron-series representation and
the source step series into the termwise error bound of Lemma 13.4.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The finite explicit-formula integral differs from the half-weighted
character Chebyshev sum by at most the convergent exact Perron majorant. -/
theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (scalarPerronErrorMajorantTerm chi x c T) := by
  have hErrorNorm := summable_norm_scalarPerronErrorTerm chi hx hc hT
  have hMajorant := summable_scalarPerronErrorMajorantTerm chi hx hc hT
  have hSeries := summable_scalarPerronSeriesTerm chi hx hc hT
  have hStep := summable_scalarPerronStepTerm (x := x) chi
  rw [explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm chi hx hc]
  rw [<- tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum chi hx]
  rw [<- hSeries.tsum_sub hStep]
  change norm (tsum (scalarPerronErrorTerm chi x c T)) <= _
  exact (norm_tsum_le_tsum_norm hErrorNorm).trans
    (hErrorNorm.tsum_le_tsum
      (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
        (lt_trans zero_lt_one hc) hT n)
      hMajorant)

end BombieriVinogradov.SiegelWalfisz
