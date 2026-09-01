import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailSeries

/-!
# Absolute constant in the near-one L-function bound

This module only packages the initial-block coefficient and the summed tail
into one positive constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLNearOneBoundConstant : ℝ :=
  2 * Real.exp (1 / 8 : ℝ) * (1 + zeroExclusionTailConstant)

theorem characterLNearOneBoundConstant_pos : 0 < characterLNearOneBoundConstant := by
  unfold characterLNearOneBoundConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (by linarith [zeroExclusionTailConstant_nonneg])

end BombieriVinogradov.SiegelWalfisz
