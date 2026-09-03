import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Reciprocal vertical zero kernel

This module compares the real reciprocal kernel at real part two with the
standard quadratic weight in the vertical distance from a critical-strip zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

/-- A critical-strip point contributes at least one quarter of the standard
quadratic vertical-gap weight to the real reciprocal kernel at real part two. -/
theorem one_div_vertical_gap_sq_le_zeroKernel_re
    {T : Real} {rho : Complex}
    (hrhoLower : 0 < rho.re) (hrhoUpper : rho.re < 1) :
    1 / (4 * (1 + (T - rho.im) ^ 2)) <=
      (1 / (((2 : Real) : Complex) +
        (T : Complex) * Complex.I - rho)).re := by
  have haOne : 1 <= 2 - rho.re := by
    linarith
  have haTwo : 2 - rho.re <= 2 := by
    linarith
  have haPos : 0 < 2 - rho.re := lt_of_lt_of_le (by norm_num) haOne
  have hDenPos :
      0 < (2 - rho.re) ^ 2 + (T - rho.im) ^ 2 := by
    nlinarith [sq_nonneg (T - rho.im)]
  have hDenNonneg :
      0 <= (2 - rho.re) ^ 2 + (T - rho.im) ^ 2 := hDenPos.le
  have hDenUpper :
      (2 - rho.re) ^ 2 + (T - rho.im) ^ 2 <=
        4 * (1 + (T - rho.im) ^ 2) := by
    have hASq : (2 - rho.re) ^ 2 <= 4 := by
      nlinarith [mul_nonneg haPos.le (sub_nonneg.mpr haTwo)]
    nlinarith [sq_nonneg (T - rho.im)]
  have hOneDiv :
      (1 / (((2 : Real) : Complex) +
        (T : Complex) * Complex.I - rho) : Complex) =
        Inv.inv (((2 : Real) : Complex) +
          (T : Complex) * Complex.I - rho) := by
    rw [one_div]
  rw [hOneDiv, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, mul_zero, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.sub_im, Complex.add_im, zero_add]
  calc
    1 / (4 * (1 + (T - rho.im) ^ 2)) <=
        1 / ((2 - rho.re) * (2 - rho.re) +
          (T - rho.im) * (T - rho.im)) :=
      one_div_le_one_div_of_le (by simpa [pow_two] using hDenPos)
        (by simpa [pow_two] using hDenUpper)
    _ <= (2 - rho.re) /
        ((2 - rho.re) * (2 - rho.re) +
          (T - rho.im) * (T - rho.im)) :=
      div_le_div_of_nonneg_right haOne
        (by simpa [pow_two] using hDenNonneg)

end BombieriVinogradov.ComplexAnalysis
