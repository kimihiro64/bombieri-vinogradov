import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Centered power-kernel bound on horizontal segments

This module isolates the elementary decay of the centered Perron kernel at
nonzero height throughout the explicit-formula contour strip.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_centered_cpow_kernel_horizontal_le
    (x : Nat) (hx : 2 < x) {s : Complex}
    (hsRe : s.re <= optimizedPerronLine x)
    (hsIm : 0 < abs s.im) :
    norm (((x : Complex) ^ s - 1) / s) <=
      4 * (x : Real) / abs s.im := by
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hxOne : 1 <= x :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hxPos)
  have hxReal : (1 : Real) <= (x : Real) := Nat.one_le_cast.mpr hxOne
  have hPower :
      norm ((x : Complex) ^ s) <= 3 * (x : Real) := by
    rw [Complex.norm_natCast_cpow_of_pos hxPos s]
    calc
      (x : Real) ^ s.re <=
          (x : Real) ^ optimizedPerronLine x :=
        Real.rpow_le_rpow_of_exponent_le hxReal hsRe
      _ = (x : Real) * Real.exp 1 :=
        rpow_optimizedPerronLine_eq hx
      _ <= (x : Real) * 3 :=
        mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Nat.cast_nonneg x)
      _ = 3 * (x : Real) := by ac_rfl
  have hNumerator :
      norm ((x : Complex) ^ s - 1) <= 4 * (x : Real) := by
    calc
      norm ((x : Complex) ^ s - 1) <=
          norm ((x : Complex) ^ s) + norm (1 : Complex) :=
        norm_sub_le _ _
      _ <= 3 * (x : Real) + 1 :=
        add_le_add hPower (by norm_num)
      _ <= 4 * (x : Real) := by linarith
  have hImNorm : abs s.im <= norm s := Complex.abs_im_le_norm s
  rw [norm_div]
  calc
    norm ((x : Complex) ^ s - 1) / norm s <=
        (4 * (x : Real)) / norm s :=
      div_le_div_of_nonneg_right hNumerator (norm_nonneg s)
    _ <= 4 * (x : Real) / abs s.im :=
      div_le_div_of_nonneg_left (by positivity) hsIm hImNorm

end BombieriVinogradov.SiegelWalfisz
