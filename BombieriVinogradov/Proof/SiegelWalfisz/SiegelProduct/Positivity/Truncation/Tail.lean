import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Truncation.Index
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Geometric decay at the logarithmic cutoff

This module proves that the selected cutoff makes the regular-series tail smaller than one half.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationTail_lt_half {A B Q : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpowpos : 0 < Q ^ K := pow_pos hQpos K
  have hXpos : 0 < X := mul_pos hBpos hQpowpos
  have hbase : Real.log (3 / 4 : ℝ) ≤ -1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hcutoff : 4 * Real.log X < (cutoff : ℝ) := by
    exact truncationIndex_lower hB hQ
  have hcutoff0 : 0 ≤ (cutoff : ℝ) := by positivity
  have hexponent : Real.log (3 / 4 : ℝ) * (cutoff : ℝ) < -Real.log X := by
    calc
      Real.log (3 / 4 : ℝ) * (cutoff : ℝ) ≤
          (-1 / 4 : ℝ) * (cutoff : ℝ) :=
        mul_le_mul_of_nonneg_right hbase hcutoff0
      _ < -Real.log X := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ cutoff < 1 / X := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have h := Real.exp_lt_exp.mpr hexponent
    rw [Real.exp_neg, Real.exp_log hXpos] at h
    simpa only [inv_eq_one_div] using h
  rcases hA.eq_or_lt with rfl | hApos
  · norm_num
  · have hpref : 0 < 4 * A * Q ^ K := mul_pos (mul_pos (by norm_num) hApos) hQpowpos
    calc
      4 * A * Q ^ K * (3 / 4 : ℝ) ^ cutoff <
          4 * A * Q ^ K * (1 / X) := mul_lt_mul_of_pos_left hpow hpref
      _ = 4 * A / B := by
        dsimp [X]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hBpos]
        nlinarith

end BombieriVinogradov.SiegelWalfisz
