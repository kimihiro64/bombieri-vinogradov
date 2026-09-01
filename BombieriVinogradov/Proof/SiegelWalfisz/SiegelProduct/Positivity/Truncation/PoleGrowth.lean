import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Truncation.Index
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pole growth at the logarithmic cutoff

This module bounds `(1 + delta)^cutoff` by a fixed constant and modulus exponent.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationPoleGrowth {B Q delta : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    (1 + delta) ^ siegelTruncationIndex B Q K ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hXpos : 0 < X := mul_pos (zero_lt_one.trans_le hB) (pow_pos hQpos K)
  have hcutoff := truncationIndex_upper (K := K) hB hQ
  have hmul : (cutoff : ℝ) * delta ≤
      (4 * Real.log X + 2) * delta :=
    mul_le_mul_of_nonneg_right hcutoff.le hdelta0
  have hexponent : (cutoff : ℝ) * delta ≤ 4 * delta * Real.log X + 2 := by
    calc
      (cutoff : ℝ) * delta ≤ (4 * Real.log X + 2) * delta := hmul
      _ ≤ 4 * delta * Real.log X + 2 := by nlinarith
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa only [add_comm] using Real.add_one_le_exp delta
  have hbase0 : 0 ≤ 1 + delta := by linarith
  have hpow : (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := by
    exact pow_le_pow_left₀ hbase0 hbase cutoff
  calc
    (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := hpow
    _ = Real.exp ((cutoff : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * delta * Real.log X + 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * X ^ (4 * delta) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
      have harg : 4 * delta * Real.log X = Real.log X * (4 * delta) := by ring
      rw [harg]
      ring
    _ ≤ Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
      have hBrpow : B ^ (4 * delta) ≤ B := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hB (by nlinarith : 4 * delta ≤ 1)
      have hQrpow : (Q ^ K) ^ (4 * delta) = Q ^ ((4 * K : ℝ) * delta) := by
        calc
          (Q ^ K) ^ (4 * delta) = (Q ^ (4 * delta)) ^ K :=
            (Real.rpow_pow_comm hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * delta) * K) :=
            (Real.rpow_mul_natCast hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * K : ℝ) * delta) := by
            congr 1
            ring
      dsimp [X]
      rw [Real.mul_rpow hB0 (pow_nonneg hQ0 K), hQrpow]
      have hQnonneg : 0 ≤ Q ^ ((4 * K : ℝ) * delta) := Real.rpow_nonneg hQ0 _
      calc
        Real.exp 2 * (B ^ (4 * delta) * Q ^ ((4 * K : ℝ) * delta)) ≤
            Real.exp 2 * (B * Q ^ ((4 * K : ℝ) * delta)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBrpow hQnonneg) (Real.exp_nonneg 2)
        _ = Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by ring

end BombieriVinogradov.SiegelWalfisz
