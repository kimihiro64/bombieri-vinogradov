import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic truncation index

This module defines the natural cutoff and proves its exact lower and upper real bounds.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The source cutoff, rounded above and shifted once to retain a strict lower bound. -/
noncomputable def siegelTruncationIndex (B Q : ℝ) (K : ℕ) : ℕ :=
  ⌈4 * Real.log (B * Q ^ K)⌉₊ + 1

theorem truncationIndex_lower {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    4 * Real.log (B * Q ^ K) < siegelTruncationIndex B Q K := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  have hceil := Nat.le_ceil (4 * Real.log (B * Q ^ K))
  exact hceil.trans_lt (lt_add_one _)

theorem truncationIndex_upper {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    (siegelTruncationIndex B Q K : ℝ) <
      4 * Real.log (B * Q ^ K) + 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hlog]

end BombieriVinogradov.SiegelWalfisz
