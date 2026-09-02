import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.HarmonicGrowth
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Power
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Optimized Perron-error scale

This module absorbs the general two-term source estimate into a single
`x * log (2 * x) ^ 2 / T` term at the optimized line.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The general Perron-error scale is at most four copies of the optimized
logarithmic scale. -/
theorem optimizedPerronScale_le
    {x : Nat} (hx : 2 < x) {T : Real} (hT : 0 < T) :
    ((x : Real) ^ optimizedPerronLine x /
        (T * (optimizedPerronLine x - 1))) +
      ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) <=
    4 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hLogOne := one_le_log_natCast hx
  have hLogPos : 0 < Real.log (x : Real) := lt_of_lt_of_le zero_lt_one hLogOne
  have hLogTwoOne := one_le_log_two_mul hx
  have hLogTwoNonneg : 0 <= Real.log (2 * (x : Real)) :=
    le_trans zero_le_one hLogTwoOne
  have hLogMono : Real.log (x : Real) <=
      Real.log (2 * (x : Real)) := by
    apply Real.log_le_log hxReal
    nlinarith [hxReal]
  have hLogSquare : Real.log (x : Real) <=
      Real.log (2 * (x : Real)) ^ 2 := by
    calc
      Real.log (x : Real) <= Real.log (2 * (x : Real)) := hLogMono
      _ = Real.log (2 * (x : Real)) * 1 := by ring
      _ <= Real.log (2 * (x : Real)) *
          Real.log (2 * (x : Real)) :=
        mul_le_mul_of_nonneg_left hLogTwoOne hLogTwoNonneg
      _ = Real.log (2 * (x : Real)) ^ 2 := by ring
  have hPower := rpow_optimizedPerronLine_eq hx
  have hLineSub : optimizedPerronLine x - 1 =
      1 / Real.log (x : Real) := by
    unfold optimizedPerronLine
    ring
  have hFirstEq :
      (x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1)) =
        (x : Real) * Real.exp 1 * Real.log (x : Real) / T := by
    rw [hPower, hLineSub]
    field_simp [ne_of_gt hLogPos, ne_of_gt hT]
  have hExp : Real.exp 1 <= 3 := Real.exp_one_lt_three.le
  have hFirst :
      (x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1)) <=
        3 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    rw [hFirstEq]
    have hXTNonneg : 0 <= (x : Real) / T := by positivity
    calc
      (x : Real) * Real.exp 1 * Real.log (x : Real) / T =
          ((x : Real) / T) * (Real.exp 1 * Real.log (x : Real)) := by ring
      _ <= ((x : Real) / T) *
          (3 * Real.log (2 * (x : Real)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hExp hLogSquare hLogPos.le (by norm_num)) hXTNonneg
      _ = 3 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring
  linarith

end BombieriVinogradov.SiegelWalfisz
