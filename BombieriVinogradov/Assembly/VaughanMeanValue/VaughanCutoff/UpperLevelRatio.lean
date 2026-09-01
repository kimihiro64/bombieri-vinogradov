import Mathlib.Tactic

/-!
# Quotient normalization for the upper Vaughan level

This module owns the real ratio `x/q^2`, its elementary division and square-root
identities, and the power consequences of `x <= q^3`. Integer rounding and
analytic composition remain in separate outward modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def upperLevelRatio (x q : Real) : Real := x / q ^ 2

theorem upperLevelRatio_nonneg {x q : Real} (hx : 0 <= x) :
    0 <= upperLevelRatio x q := by
  exact div_nonneg hx (sq_nonneg q)

theorem upperLevelRatio_pos {x q : Real} (hx : 0 < x) (hq : 0 < q) :
    0 < upperLevelRatio x q := by
  exact div_pos hx (sq_pos_of_pos hq)

theorem one_le_upperLevelRatio {x q : Real}
    (hq : 0 < q) (hqSqX : q ^ 2 <= x) :
    1 <= upperLevelRatio x q := by
  rw [upperLevelRatio, le_div_iff₀ (sq_pos_of_pos hq)]
  simpa using hqSqX

theorem upperLevelRatio_le_self {x q : Real}
    (hx : 0 <= x) (hq : 1 <= q) :
    upperLevelRatio x q <= x := by
  have hqSqPos : 0 < q ^ 2 := sq_pos_of_pos (by linarith)
  have hqSqOne : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  rw [upperLevelRatio, div_le_iff₀ hqSqPos]
  exact le_mul_of_one_le_right hx hqSqOne

theorem upperLevelRatio_mul_sq {x q : Real} (hq : Ne q 0) :
    upperLevelRatio x q * q ^ 2 = x := by
  rw [upperLevelRatio]
  field_simp

theorem sqrt_upperLevelRatio {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) :
    Real.sqrt (upperLevelRatio x q) = Real.sqrt x / q := by
  rw [upperLevelRatio, Real.sqrt_div hx, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]

theorem upperLevelSixth_le_sqrt {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hxCube : x <= q ^ 3) :
    x ^ (1 / 6 : Real) <= Real.sqrt q := by
  have hpow := Real.rpow_le_rpow hx hxCube (by norm_num : (0 : Real) <= 1 / 6)
  calc
    x ^ (1 / 6 : Real) <= (q ^ 3) ^ (1 / 6 : Real) := hpow
    _ = (Real.rpow q (3 : Real)) ^ (1 / 6 : Real) := by
      congr 1
      exact (Real.rpow_natCast q 3).symm
    _ = Real.rpow q ((3 : Real) * (1 / 6 : Real)) := by
      exact (Real.rpow_mul hq (3 : Real) (1 / 6 : Real)).symm
    _ = Real.sqrt q := by
      norm_num
      exact (Real.sqrt_eq_rpow q).symm

theorem upperLevelTwoThird_le_sq {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hxCube : x <= q ^ 3) :
    x ^ (2 / 3 : Real) <= q ^ 2 := by
  have hpow := Real.rpow_le_rpow hx hxCube (by norm_num : (0 : Real) <= 2 / 3)
  calc
    x ^ (2 / 3 : Real) <= (q ^ 3) ^ (2 / 3 : Real) := hpow
    _ = (Real.rpow q (3 : Real)) ^ (2 / 3 : Real) := by
      congr 1
      exact (Real.rpow_natCast q 3).symm
    _ = Real.rpow q ((3 : Real) * (2 / 3 : Real)) := by
      exact (Real.rpow_mul hq (3 : Real) (2 / 3 : Real)).symm
    _ = q ^ 2 := by
      norm_num

end BombieriVinogradov.VaughanMeanValue
