import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reciprocal differences along a horizontal contour

This module proves the pointwise one-zero estimate used after subtracting
completed logarithmic derivatives at a strip point and at the reference
point with real part two. It contains no zero summation or character data.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_horizontal_reciprocal_difference_le
    {s rho : Complex} {T : Real}
    (hsIm : s.im = T)
    (hsLower : -(1 : Real) / 2 <= s.re)
    (hsUpper : s.re <= 2)
    (hFar : 1 <= abs (T - rho.im)) :
    norm (1 / (s - rho) -
      1 / (((2 : Real) : Complex) + (T : Complex) * Complex.I - rho)) <=
        6 * (1 / (1 + (T - rho.im) ^ 2)) := by
  let w : Complex :=
    ((2 : Real) : Complex) + (T : Complex) * Complex.I
  let d : Real := abs (T - rho.im)
  have hDOne : 1 <= d := by
    simpa [d] using hFar
  have hDPos : 0 < d := lt_of_lt_of_le (by norm_num) hDOne
  have hGapNe : Ne (T - rho.im) 0 := by
    intro hGapZero
    rw [hGapZero, abs_zero] at hFar
    norm_num at hFar
  have hwIm : w.im = T := by
    simp [w, Complex.mul_im]
  have hwRe : w.re = 2 := by
    simp [w, Complex.mul_re]
  have hsDenNe : Ne (s - rho) 0 := by
    intro hZero
    apply hGapNe
    have hImZero := congrArg Complex.im hZero
    simpa [Complex.sub_im, hsIm] using hImZero
  have hwDenNe : Ne (w - rho) 0 := by
    intro hZero
    apply hGapNe
    have hImZero := congrArg Complex.im hZero
    simpa [Complex.sub_im, hwIm] using hImZero
  have hIdentity :
      1 / (s - rho) - 1 / (w - rho) =
        (w - s) / ((s - rho) * (w - rho)) := by
    simp only [one_div]
    rw [inv_sub_inv hsDenNe hwDenNe]
    ring
  have hwSub : w - s = ((2 - s.re : Real) : Complex) := by
    exact Complex.ext (by simp [hwRe]) (by simp [hwIm, hsIm])
  have hNumerator : norm (w - s) <= (3 : Real) := by
    rw [hwSub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hsDenLower : d <= norm (s - rho) := by
    dsimp [d]
    calc
      abs (T - rho.im) = abs (s - rho).im := by
        rw [Complex.sub_im, hsIm]
      _ <= norm (s - rho) := Complex.abs_im_le_norm (s - rho)
  have hwDenLower : d <= norm (w - rho) := by
    dsimp [d]
    calc
      abs (T - rho.im) = abs (w - rho).im := by
        rw [Complex.sub_im, hwIm]
      _ <= norm (w - rho) := Complex.abs_im_le_norm (w - rho)
  have hDenLower :
      d * d <= norm (s - rho) * norm (w - rho) :=
    mul_le_mul hsDenLower hwDenLower (le_of_lt hDPos)
      (norm_nonneg (s - rho))
  have hRaw :
      norm ((w - s) / ((s - rho) * (w - rho))) <=
        3 / (d * d) := by
    rw [Complex.norm_div, Complex.norm_mul]
    calc
      norm (w - s) / (norm (s - rho) * norm (w - rho)) <=
          norm (w - s) / (d * d) :=
        div_le_div_of_nonneg_left (norm_nonneg (w - s))
          (mul_pos hDPos hDPos) hDenLower
      _ <= 3 / (d * d) :=
        div_le_div_of_nonneg_right hNumerator
          (mul_nonneg hDPos.le hDPos.le)
  have hWeightDen : 1 + d ^ 2 <= 2 * d ^ 2 := by
    nlinarith
  have hReciprocal :
      1 / (2 * d ^ 2) <= 1 / (1 + d ^ 2) :=
    one_div_le_one_div_of_le (by nlinarith [sq_nonneg d]) hWeightDen
  have hThree :
      3 / (d * d) = 6 * (1 / (2 * d ^ 2)) := by
    field_simp [ne_of_gt hDPos]
    ring
  have hWeight :
      3 / (d * d) <= 6 * (1 / (1 + d ^ 2)) := by
    rw [hThree]
    exact mul_le_mul_of_nonneg_left hReciprocal (by norm_num)
  rw [show
      (((2 : Real) : Complex) + (T : Complex) * Complex.I) = w by rfl]
  rw [hIdentity]
  simpa [d] using hRaw.trans hWeight

end BombieriVinogradov.ComplexAnalysis

