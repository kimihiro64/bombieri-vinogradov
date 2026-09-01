import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform control of the modulus power near one

This module proves that the factor `N^(1-re s)` stays uniformly bounded on
the narrow complex neighborhood used in the Cauchy derivative estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem modulus_rpow_one_sub_re_le {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re) :
    (N : ℝ) ^ (1 - s.re) ≤ Real.exp (1 / 8 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNreal
  have hdenominator : 0 < 8 * (1 + Real.log N) := by positivity
  by_cases hs : 1 ≤ s.re
  · have hexponent : 1 - s.re ≤ 0 := by linarith
    have hpower : (N : ℝ) ^ (1 - s.re) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hNreal hexponent
    exact hpower.trans (Real.one_le_exp (by norm_num))
  · have hgap : 1 - s.re ≤ 1 / (8 * (1 + Real.log N)) := by linarith
    have hlogRatio : Real.log N / (1 + Real.log N) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hproduct : (1 - s.re) * Real.log N ≤ 1 / 8 := by
      calc
        (1 - s.re) * Real.log N ≤
            (1 / (8 * (1 + Real.log N))) * Real.log N :=
          mul_le_mul_of_nonneg_right hgap hlog
        _ = (1 / 8) * (Real.log N / (1 + Real.log N)) := by
          field_simp
        _ ≤ 1 / 8 := mul_le_of_le_one_right (by norm_num) hlogRatio
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hproduct)

theorem submodulus_rpow_one_sub_re_le {j N : ℕ}
    (hj : 0 < j) (hjN : j ≤ N) {s : ℂ}
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re) :
    (j : ℝ) ^ (1 - s.re) ≤ Real.exp (1 / 8 : ℝ) := by
  have hN : 0 < N := hj.trans_le hjN
  have hjOne : (1 : ℝ) ≤ j := by exact_mod_cast hj
  by_cases hs : 1 ≤ s.re
  · exact (Real.rpow_le_one_of_one_le_of_nonpos hjOne (by linarith)).trans
      (Real.one_le_exp (by norm_num))
  · have hexponent : 0 ≤ 1 - s.re := by linarith
    have hjNreal : (j : ℝ) ≤ N := by exact_mod_cast hjN
    exact (Real.rpow_le_rpow (Nat.cast_nonneg j) hjNreal hexponent).trans
      (modulus_rpow_one_sub_re_le hN hre)

end BombieriVinogradov.SiegelWalfisz
