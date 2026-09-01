import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.ValueConstant

/-!
# Absolute constant in the near-one derivative bound

This module only packages the Cauchy-radius factor with the value-bound
constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLDerivativeBoundConstant : ℝ :=
  16 * characterLNearOneBoundConstant

theorem characterLDerivativeBoundConstant_pos :
    0 < characterLDerivativeBoundConstant := by
  unfold characterLDerivativeBoundConstant
  exact mul_pos (by norm_num) characterLNearOneBoundConstant_pos

end BombieriVinogradov.SiegelWalfisz
