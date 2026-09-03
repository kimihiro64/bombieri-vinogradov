import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Reciprocal norm from a real-part gap
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_one_div_le_scale_div_of_re_gap
    {c L : Real} (hc : 0 < c) (hL : 0 < L)
    {rho : Complex} (hGap : c / L <= rho.re) :
    norm (1 / rho) <= L / c := by
  have hNormLower : c / L <= norm rho :=
    hGap.trans
      ((le_abs_self rho.re).trans (Complex.abs_re_le_norm rho))
  have hReciprocal : 1 / norm rho <= 1 / (c / L) :=
    one_div_le_one_div_of_le (div_pos hc hL) hNormLower
  have hNormOne : norm (1 : Complex) = 1 := by
    simpa using
      Complex.norm_of_nonneg (show 0 <= (1 : Real) by norm_num)
  calc
    norm (1 / rho) = 1 / norm rho := by
      rw [Complex.norm_div, hNormOne]
    _ <= 1 / (c / L) := hReciprocal
    _ = L / c := one_div_div c L

end BombieriVinogradov.ComplexAnalysis
