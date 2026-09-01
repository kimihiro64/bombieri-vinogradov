import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Uniform variation of reciprocal complex powers

This module owns the real mean-value estimate used to bound grouped Dirichlet
blocks on a fixed complex domain.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (15 / 4 : ℝ)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ (15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : t ^ (-s.re - 1) ≤ t ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : t ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by norm_num)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz
