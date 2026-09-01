import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LogAbsorption

/-!
# Power absorption for zero exclusion

This module bounds the logarithmic factors in the zero-exclusion radius and
derivative loss by fixed constants times small powers.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem log_mul_rpow_neg_le_constant {x epsilon : ℝ}
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) :
    (1 + Real.log x) * x ^ (-epsilon) ≤
      1 + (epsilon / 2)⁻¹ := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hdelta : 0 < epsilon / 2 := by positivity
  have hlog := one_add_log_le_rpow_mul hx hdelta
  have hpowerNonneg : 0 ≤ x ^ (-epsilon) := Real.rpow_nonneg hxPos.le _
  have hproduct := mul_le_mul_of_nonneg_right hlog hpowerNonneg
  have hconstantNonneg : 0 ≤ 1 + (epsilon / 2)⁻¹ := by positivity
  calc
    (1 + Real.log x) * x ^ (-epsilon) ≤
        ((1 + (epsilon / 2)⁻¹) * x ^ (epsilon / 2)) * x ^ (-epsilon) := hproduct
    _ = (1 + (epsilon / 2)⁻¹) * x ^ (-epsilon / 2) := by
      rw [mul_assoc, ← Real.rpow_add hxPos]
      congr 2
      ring
    _ ≤ (1 + (epsilon / 2)⁻¹) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)) hconstantNonneg
    _ = 1 + (epsilon / 2)⁻¹ := mul_one _

theorem log_sq_mul_rpow_neg_le_half_power {x epsilon : ℝ}
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) :
    (1 + Real.log x) ^ 2 * x ^ (-epsilon) ≤
      (1 + (epsilon / 4)⁻¹) ^ 2 * x ^ (-epsilon / 2) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hdelta : 0 < epsilon / 4 := by positivity
  have hlog := one_add_log_le_rpow_mul hx hdelta
  have hlogNonneg : 0 ≤ 1 + Real.log x := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx
    linarith
  have hrightNonneg : 0 ≤ (1 + (epsilon / 4)⁻¹) * x ^ (epsilon / 4) := by
    positivity
  have hsquare :
      (1 + Real.log x) ^ 2 ≤
        ((1 + (epsilon / 4)⁻¹) * x ^ (epsilon / 4)) ^ 2 := by
    nlinarith [sq_nonneg ((1 + (epsilon / 4)⁻¹) * x ^ (epsilon / 4) -
      (1 + Real.log x))]
  have hpowerNonneg : 0 ≤ x ^ (-epsilon) := Real.rpow_nonneg hxPos.le _
  have hpowerIdentity :
      (x ^ (epsilon / 4)) ^ 2 * x ^ (-epsilon) = x ^ (-epsilon / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxPos.le,
      ← Real.rpow_add hxPos]
    congr 1
    ring
  calc
    (1 + Real.log x) ^ 2 * x ^ (-epsilon) ≤
        ((1 + (epsilon / 4)⁻¹) * x ^ (epsilon / 4)) ^ 2 * x ^ (-epsilon) :=
      mul_le_mul_of_nonneg_right hsquare hpowerNonneg
    _ = (1 + (epsilon / 4)⁻¹) ^ 2 * x ^ (-epsilon / 2) := by
      rw [mul_pow, mul_assoc, hpowerIdentity]

end BombieriVinogradov.SiegelWalfisz
