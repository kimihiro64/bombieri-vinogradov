import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeriesBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeriesMonotone

/-!
# Full source range for the von Mangoldt norm sum

This module extends the direct `1 < c < 2` zeta estimate through `c <= 3` by
monotonicity from the fixed point `c = 3 / 2`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One positive constant controls the von Mangoldt norm sum by `1 / (c - 1)`
through the full source interval `1 < c <= 3`. -/
theorem exists_vonMangoldtLSeriesNormSum_le_div_le_three :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c <= 3 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  have hNarrow := hSpec.2
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro c hc1 hc3
  have hDenomPos : 0 < c - 1 := sub_pos.mpr hc1
  by_cases hc2 : c < 2
  case pos =>
    have hRaw := hNarrow c hc1 hc2
    calc
      vonMangoldtLSeriesNormSum c <= C0 / (c - 1) := hRaw
      _ <= (4 * C0) / (c - 1) := by
        have hUnitNonneg : 0 <= 1 / (c - 1) := by positivity
        calc
          C0 / (c - 1) = C0 * (1 / (c - 1)) := by ring
          _ <= (4 * C0) * (1 / (c - 1)) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hC0]) hUnitNonneg
          _ = (4 * C0) / (c - 1) := by ring
  case neg =>
    have hcTwo : (2 : Real) <= c := le_of_not_gt hc2
    have hMono := vonMangoldtLSeriesNormSum_antitone
      (c := (3 / 2 : Real)) (d := c) (by norm_num) (by linarith)
    have hAt := hNarrow (3 / 2 : Real) (by norm_num) (by norm_num)
    have hFixed : vonMangoldtLSeriesNormSum c <= 2 * C0 := by
      calc
        vonMangoldtLSeriesNormSum c <=
            vonMangoldtLSeriesNormSum (3 / 2 : Real) := hMono
        _ <= C0 / ((3 / 2 : Real) - 1) := hAt
        _ = 2 * C0 := by ring
    have hDenomUpper : c - 1 <= 2 := by linarith
    have hReciprocal : (1 / 2 : Real) <= 1 / (c - 1) :=
      one_div_le_one_div_of_le hDenomPos hDenomUpper
    calc
      vonMangoldtLSeriesNormSum c <= 2 * C0 := hFixed
      _ = (4 * C0) * (1 / 2 : Real) := by ring
      _ <= (4 * C0) * (1 / (c - 1)) :=
        mul_le_mul_of_nonneg_left hReciprocal (by positivity)
      _ = (4 * C0) / (c - 1) := by ring

end BombieriVinogradov.SiegelWalfisz
