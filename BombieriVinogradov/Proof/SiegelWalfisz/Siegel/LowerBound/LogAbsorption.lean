import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing logarithms into a small positive power

This module records the elementary logarithmic estimate used to absorb the
auxiliary `lcm` factor in the quantitative Siegel lower bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem one_add_log_le_rpow_mul {x delta : ℝ}
    (hx : 1 ≤ x) (hdelta : 0 < delta) :
    1 + Real.log x ≤ (1 + delta⁻¹) * x ^ delta := by
  have hpow : 1 ≤ x ^ delta := by
    simpa using Real.rpow_le_rpow zero_le_one hx hdelta.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) hdelta
  calc
    1 + Real.log x ≤ x ^ delta + x ^ delta / delta := add_le_add hpow hlog
    _ = (1 + delta⁻¹) * x ^ delta := by
      rw [div_eq_mul_inv]
      ring

theorem one_add_log_lcm_le_rpow_mul {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
  have hmul : 0 < N * M := Nat.mul_pos hN hM
  have hlcmNat : N.lcm M ≤ N * M :=
    Nat.le_of_dvd hmul (Nat.lcm_dvd_mul N M)
  have hlcm : (0 : ℝ) < N.lcm M := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hN.ne' hM.ne')
  have hlcmMul : (N.lcm M : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast hlcmNat
  have hproduct : (1 : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmul.ne'
  calc
    1 + Real.log (N.lcm M) ≤ 1 + Real.log (N * M : ℕ) := by
      simpa [add_comm] using add_le_add_left (Real.log_le_log hlcm hlcmMul) 1
    _ ≤ (1 + delta⁻¹) * (N * M : ℕ) ^ delta :=
      one_add_log_le_rpow_mul hproduct hdelta
    _ = (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
      norm_num

end BombieriVinogradov.SiegelWalfisz
