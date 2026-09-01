import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PowerAbsorption
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PrimitiveCoefficient
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.SphereGeometry

/-!
# Radius condition for primitive zero exclusion

This module proves that the selected epsilon-dependent coefficient places the
real interval inside the Cauchy radius used by the derivative estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitiveZeroExclusionCoefficient_mul_rpow_le_radius
    {N : ℕ} [NeZero N] {epsilon lowerBound : ℝ}
    (hepsilon : 0 < epsilon) :
    primitiveZeroExclusionCoefficient epsilon lowerBound *
        (N : ℝ) ^ (-epsilon) ≤ zeroExclusionRadius N := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hlogNonneg : 0 ≤ Real.log N := Real.log_nonneg hNreal
  have hlogPos : 0 < 1 + Real.log N := by linarith
  have hKPos : 0 < zeroExclusionRadiusAbsorptionConstant epsilon :=
    zeroExclusionRadiusAbsorptionConstant_pos hepsilon
  have habsorb :
      (1 + Real.log N) * (N : ℝ) ^ (-epsilon) ≤
        zeroExclusionRadiusAbsorptionConstant epsilon := by
    simpa [zeroExclusionRadiusAbsorptionConstant] using
      (log_mul_rpow_neg_le_constant hNreal hepsilon)
  have hpowerNonneg : 0 ≤ (N : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg hNpos.le _
  refine (mul_le_mul_of_nonneg_right
    primitiveZeroExclusionCoefficient_le_radius hpowerNonneg).trans ?_
  unfold zeroExclusionRadius
  rw [le_div_iff₀ (mul_pos (by norm_num) hlogPos)]
  calc
    (1 / (16 * zeroExclusionRadiusAbsorptionConstant epsilon) *
          (N : ℝ) ^ (-epsilon)) * (16 * (1 + Real.log N)) =
        ((1 + Real.log N) * (N : ℝ) ^ (-epsilon)) /
          zeroExclusionRadiusAbsorptionConstant epsilon := by
      field_simp
    _ ≤ zeroExclusionRadiusAbsorptionConstant epsilon /
          zeroExclusionRadiusAbsorptionConstant epsilon :=
      div_le_div_of_nonneg_right habsorb hKPos.le
    _ = 1 := div_self hKPos.ne'

end BombieriVinogradov.SiegelWalfisz
