import Mathlib.Analysis.PSeries

/-!
# Summed positive-index character-block tail

This module owns only the fixed scalar tail series, its summability, and its
nonnegativity.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def zeroExclusionTailConstant : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-15 / 8 : ℝ)

theorem zeroExclusionTail_summable :
    Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-15 / 8 : ℝ)) := by
  have hp : Summable (fun k : ℕ ↦ (k : ℝ) ^ (-15 / 8 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem zeroExclusionTailConstant_nonneg : 0 ≤ zeroExclusionTailConstant := by
  rw [zeroExclusionTailConstant]
  exact tsum_nonneg fun k ↦ Real.rpow_nonneg (by positivity) _

end BombieriVinogradov.SiegelWalfisz
