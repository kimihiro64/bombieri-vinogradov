import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Logarithmic separation in the far Perron range

This module records the elementary lower bound for the logarithmic denominator
when the summation index is outside the interval from `x / 2` to `2 * x`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A rational lower bound for `log 2`. -/
theorem half_le_log_two : (1 / 2 : Real) <= Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
  norm_num at h
  exact le_trans (by norm_num : (1 / 2 : Real) <= 2 / 3) h

/-- Outside the central dyadic interval, the logarithmic Perron denominator is
bounded below by one half. -/
theorem half_le_abs_log_ratio_of_far
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    (hfar : n <= x / 2 \/ 2 * x <= n) :
    (1 / 2 : Real) <= abs (Real.log ((x : Real) / (n : Real))) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  rcases hfar with hLower | hUpper
  case inl =>
    have hTwice : 2 * n <= x := by omega
    have hTwiceReal : (2 : Real) * (n : Real) <= (x : Real) := by
      exact_mod_cast hTwice
    have hRatio : (2 : Real) <= (x : Real) / (n : Real) := by
      nlinarith [hnReal, hDivMul, hTwiceReal]
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) hRatio
    have hLogNonneg : 0 <= Real.log ((x : Real) / (n : Real)) :=
      (Real.log_nonneg (by norm_num : (1 : Real) <= 2)).trans hLog
    rw [abs_of_nonneg hLogNonneg]
    exact half_le_log_two.trans hLog
  case inr =>
    have hTwiceReal : (2 : Real) * (x : Real) <= (n : Real) := by
      exact_mod_cast hUpper
    have hRatio : (x : Real) / (n : Real) <= (1 / 2 : Real) := by
      nlinarith [hnReal, hRatioPos, hDivMul, hTwiceReal]
    have hLog := Real.log_le_log hRatioPos hRatio
    have hHalfLog : Real.log (1 / 2 : Real) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have hLogNonpos : Real.log ((x : Real) / (n : Real)) <= 0 := by
      rw [hHalfLog] at hLog
      nlinarith [half_le_log_two]
    rw [abs_of_nonpos hLogNonpos]
    rw [hHalfLog] at hLog
    nlinarith [half_le_log_two]

end BombieriVinogradov.SiegelWalfisz
