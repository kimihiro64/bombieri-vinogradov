import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.Main

/-!
# Constants for the large-level Siegel estimate

This module owns the fixed positive denominator and the resulting coefficient
after logarithm absorption. It contains no character-dependent argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLargeLevelDenominator
    (C : ℝ) (N : ℕ) (delta : ℝ) : ℝ :=
  C * characterLLogBoundConstant ^ 2 * (1 + Real.log N) * (1 + delta⁻¹)

theorem siegelLargeLevelDenominator_pos {C delta : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (hdelta : 0 < delta) :
    0 < siegelLargeLevelDenominator C N delta := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < 1 + Real.log N := by
    linarith [Real.log_nonneg hNreal]
  have hinverse : 0 < 1 + delta⁻¹ := by
    have : 0 < delta⁻¹ := inv_pos.mpr hdelta
    linarith
  unfold siegelLargeLevelDenominator
  exact mul_pos (mul_pos (mul_pos hC (pow_pos characterLLogBoundConstant_pos 2)) hlog)
    hinverse

noncomputable def siegelLargeLevelConstant
    (C epsilon s : ℝ) (N : ℕ) : ℝ :=
  ((1 - s) / siegelLargeLevelDenominator C N (epsilon / 2)) *
    (N : ℝ) ^ (-epsilon)

theorem siegelLargeLevelConstant_pos {C epsilon s : ℝ} {N : ℕ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hN : 0 < N) (hs : s < 1) :
    0 < siegelLargeLevelConstant C epsilon s N := by
  have hdenominator := siegelLargeLevelDenominator_pos hC hN
    (div_pos hepsilon zero_lt_two)
  unfold siegelLargeLevelConstant
  exact mul_pos (div_pos (sub_pos.mpr hs) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) (-epsilon))

end BombieriVinogradov.SiegelWalfisz
