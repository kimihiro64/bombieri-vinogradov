import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PowerAbsorption
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PrimitiveCoefficient

/-!
# Derivative loss under the primitive zero-exclusion coefficient

This module proves that the selected interval width makes the uniform
derivative loss at most half of the Siegel lower bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem derivative_loss_at_primitiveZeroExclusionCoefficient
    {N : ℕ} [NeZero N] {epsilon lowerBound : ℝ}
    (hepsilon : 0 < epsilon) (hlowerBound : 0 < lowerBound) :
    characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 *
        (primitiveZeroExclusionCoefficient epsilon lowerBound *
          (N : ℝ) ^ (-epsilon)) ≤
      lowerBound / 2 * (N : ℝ) ^ (-epsilon / 2) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hcoefficientPos : 0 < primitiveZeroExclusionCoefficient epsilon lowerBound :=
    primitiveZeroExclusionCoefficient_pos hepsilon hlowerBound
  have hKPos : 0 < zeroExclusionDerivativeAbsorptionConstant epsilon :=
    zeroExclusionDerivativeAbsorptionConstant_pos hepsilon
  have habsorb :
      (1 + Real.log N) ^ 2 * (N : ℝ) ^ (-epsilon) ≤
        zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2 *
          (N : ℝ) ^ (-epsilon / 2) := by
    simpa [zeroExclusionDerivativeAbsorptionConstant] using
      (log_sq_mul_rpow_neg_le_half_power hNreal hepsilon)
  have hcoefficient :
      characterLDerivativeBoundConstant *
          primitiveZeroExclusionCoefficient epsilon lowerBound *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2 ≤
        lowerBound / 2 := by
    have hfactorPos :
        0 < characterLDerivativeBoundConstant *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2 :=
      mul_pos characterLDerivativeBoundConstant_pos (pow_pos hKPos 2)
    have hmul := mul_le_mul_of_nonneg_left
      (primitiveZeroExclusionCoefficient_le_derivative
        (epsilon := epsilon) (lowerBound := lowerBound)) hfactorPos.le
    calc
      characterLDerivativeBoundConstant *
          primitiveZeroExclusionCoefficient epsilon lowerBound *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2 =
        (characterLDerivativeBoundConstant *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2) *
            primitiveZeroExclusionCoefficient epsilon lowerBound := by ring
      _ ≤ (characterLDerivativeBoundConstant *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2) *
            (lowerBound /
              (2 * characterLDerivativeBoundConstant *
                zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2)) := hmul
      _ = lowerBound / 2 := by
        field_simp [characterLDerivativeBoundConstant_pos.ne', hKPos.ne']
  have hfactorNonneg :
      0 ≤ characterLDerivativeBoundConstant *
        primitiveZeroExclusionCoefficient epsilon lowerBound :=
    mul_nonneg characterLDerivativeBoundConstant_pos.le hcoefficientPos.le
  have hhalfPowerNonneg : 0 ≤ (N : ℝ) ^ (-epsilon / 2) :=
    Real.rpow_nonneg hNpos.le _
  calc
    characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 *
        (primitiveZeroExclusionCoefficient epsilon lowerBound *
          (N : ℝ) ^ (-epsilon)) =
      (characterLDerivativeBoundConstant *
        primitiveZeroExclusionCoefficient epsilon lowerBound) *
          ((1 + Real.log N) ^ 2 * (N : ℝ) ^ (-epsilon)) := by ring
    _ ≤ (characterLDerivativeBoundConstant *
        primitiveZeroExclusionCoefficient epsilon lowerBound) *
          (zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2 *
            (N : ℝ) ^ (-epsilon / 2)) :=
      mul_le_mul_of_nonneg_left habsorb hfactorNonneg
    _ = (characterLDerivativeBoundConstant *
          primitiveZeroExclusionCoefficient epsilon lowerBound *
          zeroExclusionDerivativeAbsorptionConstant epsilon ^ 2) *
        (N : ℝ) ^ (-epsilon / 2) := by ring
    _ ≤ lowerBound / 2 * (N : ℝ) ^ (-epsilon / 2) :=
      mul_le_mul_of_nonneg_right hcoefficient hhalfPowerNonneg

end BombieriVinogradov.SiegelWalfisz
