import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Uniform von Mangoldt L-series bound

This module converts the audited zeta logarithmic-derivative estimate into the
uniform `1 / (c - 1)` bound required by the far-range Perron error.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

/-- There is one positive constant controlling the von Mangoldt norm series
uniformly for real `c` between one and two. -/
theorem exists_vonMangoldtLSeriesNormSum_le_div :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c < 2 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := ShiftZeroBound
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 1 <= C0 := hSpec.1
  have hBound : forall delta : Real, Membership.mem (Ioo 0 1) delta ->
      -(deriv riemannZeta (1 + (delta : Complex)) /
        riemannZeta (1 + (delta : Complex))).re <= 1 / delta + C0 :=
    hSpec.2
  refine Exists.intro (1 + C0) (And.intro (by linarith) ?_)
  intro c hcLower hcUpper
  have hDelta : Membership.mem (Ioo 0 1) (c - 1) := by
    exact And.intro (sub_pos.mpr hcLower) (by linarith)
  have hRaw := hBound (c - 1) hDelta
  have hPoint : (1 : Complex) + ((c - 1 : Real) : Complex) = (c : Complex) := by
    push_cast
    ring
  have hSeriesBound : vonMangoldtLSeriesNormSum c <=
      1 / (c - 1) + C0 := by
    rw [vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hcLower]
    rw [hPoint] at hRaw
    rw [neg_div, Complex.neg_re]
    exact hRaw
  have hC0Nonneg : 0 <= C0 := le_trans zero_le_one hC0
  have hDenom : Ne (c - 1) 0 := ne_of_gt hDelta.1
  have hMulDiv : C0 / (c - 1) * (c - 1) = C0 := by
    field_simp [hDenom]
  have hC0Div : C0 <= C0 / (c - 1) := by
    nlinarith [hDelta.1, hDelta.2, hC0Nonneg, hMulDiv]
  calc
    vonMangoldtLSeriesNormSum c <= 1 / (c - 1) + C0 := hSeriesBound
    _ <= 1 / (c - 1) + C0 / (c - 1) := add_le_add_right hC0Div _
    _ = (1 + C0) / (c - 1) := by ring

end BombieriVinogradov.SiegelWalfisz
