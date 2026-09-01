import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Variation of reciprocal powers at one

This module gives the sharp real-axis reciprocal estimate used in complete
Dirichlet-character blocks at `s = 1`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_one_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ ((-1 : ℝ) : ℂ) - (y : ℂ) ^ ((-1 : ℝ) : ℂ)‖ ≤
      (y - x) / x ^ 2 := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Complex.ofReal_cpow hx.le (-1), ← Complex.ofReal_cpow hy.le (-1),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg_one, Real.rpow_neg_one]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy hx).mpr hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp
  rw [hid, pow_two]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx hx)
    (mul_le_mul_of_nonneg_left hxy hx.le)

end BombieriVinogradov.SiegelWalfisz
