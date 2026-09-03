import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Reciprocal bounds from an imaginary-part gap

This module converts a positive lower bound on the absolute imaginary part of
a complex number into the corresponding upper bound on its reciprocal norm.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_one_div_le_one_div_of_le_abs_im
    {a : Real} (ha : 0 < a) {rho : Complex}
    (hGap : a <= abs rho.im) :
    norm (1 / rho) <= 1 / a := by
  have hNorm : a <= norm rho :=
    hGap.trans (Complex.abs_im_le_norm rho)
  have hReciprocal : 1 / norm rho <= 1 / a :=
    one_div_le_one_div_of_le ha hNorm
  have hNormInverse : norm (1 / rho) = 1 / norm rho := by
    simpa only [one_div] using (norm_inv rho)
  rw [hNormInverse]
  exact hReciprocal

end BombieriVinogradov.ComplexAnalysis
