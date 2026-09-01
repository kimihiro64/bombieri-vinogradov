import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic factors in positive-index character blocks

This module separates the modulus and block-index powers and weakens the
block exponent to a fixed summable exponent.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem modulus_block_rpow_factorization {N k : ℕ}
    (hN : 0 < N) (hk : 0 < k) (r : ℝ) :
    (N : ℝ) ^ 2 * (((k : ℝ) * (N : ℝ)) ^ (-r - 1)) =
      (N : ℝ) ^ (1 - r) * (k : ℝ) ^ (-r - 1) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.mul_rpow hkreal.le hNreal.le]
  calc
    (N : ℝ) ^ 2 * ((k : ℝ) ^ (-r - 1) * (N : ℝ) ^ (-r - 1)) =
        ((N : ℝ) ^ 2 * (N : ℝ) ^ (-r - 1)) * (k : ℝ) ^ (-r - 1) := by ring
    _ = (N : ℝ) ^ (1 - r) * (k : ℝ) ^ (-r - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hNreal]
      congr 2
      ring

theorem block_rpow_le_fixed {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr : 7 / 8 ≤ r) :
    (k : ℝ) ^ (-r - 1) ≤ (k : ℝ) ^ (-15 / 8 : ℝ) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact Real.rpow_le_rpow_of_exponent_le hkreal (by linarith)

end BombieriVinogradov.SiegelWalfisz
