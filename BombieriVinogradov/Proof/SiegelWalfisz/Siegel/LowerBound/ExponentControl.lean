import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Choosing the near-one endpoint for a prescribed exponent

This module chooses the lower endpoint for seed selection and proves that the
residue exponent plus the logarithm-absorption exponent stays below epsilon.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) : ℝ :=
  max (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))

theorem seven_eighths_le_siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) :
    7 / 8 ≤ siegelLowerEndpoint epsilon D :=
  le_max_left _ _

theorem siegelLowerEndpoint_lt_one {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) : siegelLowerEndpoint epsilon D < 1 := by
  apply max_lt
  · norm_num
  · have hdenominator : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have : 0 < epsilon / (2 * ((D : ℝ) + 1)) := div_pos hepsilon hdenominator
    linarith

theorem siegel_exponent_control {epsilon s : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) (hs : siegelLowerEndpoint epsilon D ≤ s) :
    (D : ℝ) * (1 - s) + epsilon / 2 ≤ epsilon := by
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDplus : 0 < (D : ℝ) + 1 := by positivity
  have hrange : 1 - epsilon / (2 * ((D : ℝ) + 1)) ≤ s :=
    (le_max_right (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))).trans hs
  have hgap : 1 - s ≤ epsilon / (2 * ((D : ℝ) + 1)) := by linarith
  have hscaled : (D : ℝ) * (1 - s) ≤
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hgap hDnonneg
  have hratio : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
    (div_le_one hDplus).2 (by linarith)
  have habsorb : (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) ≤ epsilon / 2 := by
    calc
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) =
          (epsilon / 2) * ((D : ℝ) / ((D : ℝ) + 1)) := by
        field_simp
      _ ≤ epsilon / 2 :=
        mul_le_of_le_one_right (div_nonneg hepsilon.le zero_le_two) hratio
  linarith

end BombieriVinogradov.SiegelWalfisz
