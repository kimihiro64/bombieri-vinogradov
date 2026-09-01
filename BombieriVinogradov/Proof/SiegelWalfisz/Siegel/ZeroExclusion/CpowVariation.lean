import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Reciprocal complex-power variation with a retained real exponent

This module proves the real mean-value bound needed for sharp complete-block
estimates near one, retaining the actual real part of the exponent.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le_re {s : ℂ} {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hre : 0 ≤ s.re) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (y - x) * x ^ (-s.re - 1) := by
  by_cases hsZero : s = 0
  · subst s
    norm_num
  have hs0 : Ne (-s) 0 := neg_ne_zero.mpr hsZero
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const
      (ne_of_gt (zero_lt_one.trans_le (hx.trans ht.1))) hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    have htpos : 0 < t := zero_lt_one.trans_le (hx.trans ht.1)
    have hpower : t ^ (-s.re - 1) ≤ x ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) ht.1 (by linarith)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul_of_nonneg_left hpower (norm_nonneg s)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
        (‖s‖ * x ^ (-s.re - 1)) * (y - x) := hmv
    _ = ‖s‖ * (y - x) * x ^ (-s.re - 1) := by ring

end BombieriVinogradov.SiegelWalfisz
