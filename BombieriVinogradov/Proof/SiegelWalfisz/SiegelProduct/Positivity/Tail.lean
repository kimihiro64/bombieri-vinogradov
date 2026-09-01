import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric tail for the regular Siegel expansion

This module bounds a shifted complex power-series tail on the real source interval.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The regular coefficient tail beginning at `cutoff`, evaluated at a real displacement. -/
noncomputable def regularCoefficientTail
    (a : ℕ → ℂ) (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, a (cutoff + k) * (t : ℂ) ^ (cutoff + k)

/-- A `(2/3)^m` coefficient bound becomes a `(3/4)^cutoff` tail on `0 ≤ t ≤ 9/8`. -/
theorem norm_regularCoefficientTail_le
    (a : ℕ → ℂ) {A t : ℝ} (cutoff : ℕ)
    (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8)
    (ha : ∀ m, ‖a m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    ‖regularCoefficientTail a cutoff t‖ ≤
      4 * A * (3 / 4 : ℝ) ^ cutoff := by
  have hterm (k : ℕ) :
      ‖a (cutoff + k) * (t : ℂ) ^ (cutoff + k)‖ ≤
        A * (3 / 4 : ℝ) ^ (cutoff + k) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      ‖a (cutoff + k)‖ * t ^ (cutoff + k) ≤
          (A * (2 / 3 : ℝ) ^ (cutoff + k)) * t ^ (cutoff + k) :=
        mul_le_mul_of_nonneg_right (ha _) (pow_nonneg ht0 _)
      _ = A * ((2 / 3 : ℝ) * t) ^ (cutoff + k) := by
        rw [mul_assoc, mul_pow]
      _ ≤ A * (3 / 4 : ℝ) ^ (cutoff + k) := by
        gcongr
        nlinarith
  have hgeom : HasSum (fun k : ℕ => (3 / 4 : ℝ) ^ k) 4 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmajor : HasSum (fun k : ℕ => A * (3 / 4 : ℝ) ^ (cutoff + k))
      (4 * A * (3 / 4 : ℝ) ^ cutoff) := by
    have h := hgeom.mul_left (A * (3 / 4 : ℝ) ^ cutoff)
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  exact tsum_of_norm_bounded hmajor hterm

end BombieriVinogradov.SiegelWalfisz
