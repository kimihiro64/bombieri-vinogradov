import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailSeries

/-!
# Abstract comparison with the zero-exclusion tail

This module isolates the `tsum_le_tsum` step from all character and complex
analysis data.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_le_zeroExclusionTail {f : ℕ → ℝ} (hf : Summable f)
    {C : ℝ} (hpoint : ∀ k : ℕ,
      f k ≤ C * ((k + 1 : ℕ) : ℝ) ^ (-15 / 8 : ℝ)) :
    ∑' k : ℕ, f k ≤ C * zeroExclusionTailConstant := by
  rw [zeroExclusionTailConstant, ← tsum_mul_left]
  exact hf.tsum_le_tsum hpoint (zeroExclusionTail_summable.mul_left C)

end BombieriVinogradov.SiegelWalfisz
