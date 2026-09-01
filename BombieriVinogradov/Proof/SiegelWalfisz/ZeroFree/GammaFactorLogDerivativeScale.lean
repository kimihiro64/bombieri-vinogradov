import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

/-!
# Imaginary scale of gamma-factor arguments

This module compares the logarithmic vertical scale after the half-arguments used by
the even and odd Dirichlet gamma factors.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem log_abs_im_div_two_add_two_le (s : Complex) :
    Real.log (|(s / 2).im| + 2) ≤ Real.log (|s.im| + 2) := by
  apply Real.log_le_log
  · positivity
  · rw [Complex.div_ofNat_im, abs_div]
    norm_num

theorem log_abs_im_add_one_div_two_add_two_le (s : Complex) :
    Real.log (|((s + 1) / 2).im| + 2) ≤ Real.log (|s.im| + 2) := by
  have hIm : ((s + 1) / 2).im = (s / 2).im := by
    simp
  rw [hIm]
  exact log_abs_im_div_two_add_two_le s

end BombieriVinogradov.SiegelWalfisz
