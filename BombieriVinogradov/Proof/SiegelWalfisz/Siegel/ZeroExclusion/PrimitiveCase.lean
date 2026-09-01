import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.Main
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.DerivativeLoss
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.MeanValueLoss
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.RadiusCondition
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Zero exclusion for primitive quadratic characters

This module combines Siegel's lower bound at one with the uniform derivative
bound to exclude real zeros in an epsilon-dependent interval left of one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitiveQuadratic_zeroExclusionCoefficient :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 16 ∧
      ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N), 3 ≤ N ->
        DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
          ∀ t : ℝ, 1 - c * (N : ℝ) ^ (-epsilon) < t ->
            Ne (chi.LFunction t) 0 := by
  intro epsilon hepsilon
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨lowerBound, hlowerBoundPos, hlowerBound⟩ :=
    siegelLowerBound (epsilon / 2) hepsilonHalf
  let c := primitiveZeroExclusionCoefficient epsilon lowerBound
  have hcPos : 0 < c :=
    primitiveZeroExclusionCoefficient_pos hepsilon hlowerBoundPos
  have hKOne : 1 ≤ zeroExclusionRadiusAbsorptionConstant epsilon := by
    unfold zeroExclusionRadiusAbsorptionConstant
    have : 0 ≤ (epsilon / 2)⁻¹ := by positivity
    linarith
  have hKPos : 0 < zeroExclusionRadiusAbsorptionConstant epsilon :=
    zero_lt_one.trans_le hKOne
  have hcSmall : c ≤ 1 / 16 := by
    calc
      c ≤ 1 / (16 * zeroExclusionRadiusAbsorptionConstant epsilon) :=
        primitiveZeroExclusionCoefficient_le_radius
      _ ≤ 1 / 16 := by
        exact one_div_le_one_div_of_le (by norm_num)
          (by nlinarith : (16 : ℝ) ≤
            16 * zeroExclusionRadiusAbsorptionConstant epsilon)
  refine ⟨c, hcPos, hcSmall, ?_⟩
  intro N _ chi hN hchiPrimitive hchiSquare hchi t ht
  by_cases htOne : 1 ≤ t
  · exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi) (by simpa using htOne)
  have htUpper : t ≤ 1 := le_of_not_ge htOne
  have hwidth : 1 - t < c * (N : ℝ) ^ (-epsilon) := by
    linarith
  have hintervalWidth :
      c * (N : ℝ) ^ (-epsilon) ≤ zeroExclusionRadius N := by
    exact primitiveZeroExclusionCoefficient_mul_rpow_le_radius hepsilon
  have htLower : 1 - zeroExclusionRadius N ≤ t := by
    linarith
  have hmean := LFunction_re_lower_of_near_one chi hchi htLower htUpper
  have hlower :
      lowerBound * (N : ℝ) ^ (-epsilon / 2) ≤
        (chi.LFunction 1).re := by
    simpa only [neg_div] using
      (hlowerBound N chi hN hchiPrimitive hchiSquare hchi)
  have hlossBound := derivative_loss_at_primitiveZeroExclusionCoefficient
    (N := N) (epsilon := epsilon) (lowerBound := lowerBound)
    hepsilon hlowerBoundPos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlogPos : 0 < 1 + Real.log N := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    have hlogNonneg : 0 ≤ Real.log N := Real.log_nonneg hNreal
    linarith
  have hderivativeFactorPos :
      0 < characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 :=
    mul_pos characterLDerivativeBoundConstant_pos (pow_pos hlogPos 2)
  have hlossStrict :
      characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 * (1 - t) <
        characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 *
          (c * (N : ℝ) ^ (-epsilon)) :=
    mul_lt_mul_of_pos_left hwidth hderivativeFactorPos
  have hhalfPowerPos : 0 < (N : ℝ) ^ (-epsilon / 2) :=
    Real.rpow_pos_of_pos hNpos _
  have hrealPositive : 0 < (chi.LFunction t).re := by
    dsimp [c] at hintervalWidth hmean hlossBound hlossStrict ⊢
    nlinarith [mul_pos hlowerBoundPos hhalfPowerPos]
  intro hzero
  rw [hzero] at hrealPositive
  norm_num at hrealPositive

end BombieriVinogradov.SiegelWalfisz
