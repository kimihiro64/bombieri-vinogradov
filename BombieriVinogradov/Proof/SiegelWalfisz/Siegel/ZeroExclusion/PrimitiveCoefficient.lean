import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.DerivativeConstant

/-!
# Coefficient for primitive-character zero exclusion

This module packages the epsilon-dependent coefficient used simultaneously
for the Cauchy-radius condition and the derivative-loss estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def zeroExclusionRadiusAbsorptionConstant (epsilon : ℝ) : ℝ :=
  1 + (epsilon / 2)⁻¹

noncomputable def zeroExclusionDerivativeAbsorptionConstant (epsilon : ℝ) : ℝ :=
  1 + (epsilon / 4)⁻¹

noncomputable def primitiveZeroExclusionCoefficient (epsilon lowerBound : ℝ) : ℝ :=
  min
    (1 / (16 * zeroExclusionRadiusAbsorptionConstant epsilon))
    (lowerBound /
      (2 * characterLDerivativeBoundConstant *
        zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2))

theorem zeroExclusionRadiusAbsorptionConstant_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    0 < zeroExclusionRadiusAbsorptionConstant epsilon := by
  unfold zeroExclusionRadiusAbsorptionConstant
  positivity

theorem zeroExclusionDerivativeAbsorptionConstant_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    0 < zeroExclusionDerivativeAbsorptionConstant epsilon := by
  unfold zeroExclusionDerivativeAbsorptionConstant
  positivity

theorem primitiveZeroExclusionCoefficient_pos {epsilon lowerBound : ℝ}
    (hepsilon : 0 < epsilon) (hlowerBound : 0 < lowerBound) :
    0 < primitiveZeroExclusionCoefficient epsilon lowerBound := by
  unfold primitiveZeroExclusionCoefficient
  apply lt_min
  · exact one_div_pos.mpr (mul_pos (by norm_num)
      (zeroExclusionRadiusAbsorptionConstant_pos hepsilon))
  · exact div_pos hlowerBound
      (mul_pos
        (mul_pos (by norm_num) characterLDerivativeBoundConstant_pos)
        (pow_pos (zeroExclusionDerivativeAbsorptionConstant_pos hepsilon) 2))

theorem primitiveZeroExclusionCoefficient_le_radius {epsilon lowerBound : ℝ} :
    primitiveZeroExclusionCoefficient epsilon lowerBound ≤
      1 / (16 * zeroExclusionRadiusAbsorptionConstant epsilon) := by
  exact min_le_left _ _

theorem primitiveZeroExclusionCoefficient_le_derivative {epsilon lowerBound : ℝ} :
    primitiveZeroExclusionCoefficient epsilon lowerBound ≤
      lowerBound /
        (2 * characterLDerivativeBoundConstant *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2) := by
  exact min_le_right _ _

end BombieriVinogradov.SiegelWalfisz
