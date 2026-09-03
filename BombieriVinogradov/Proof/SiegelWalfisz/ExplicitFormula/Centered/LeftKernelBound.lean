import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Centered power-kernel bound on the left line

This module isolates the elementary decay supplied by the centered power
quotient on the vertical line with real part negative one half.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_centered_cpow_kernel_left_line_le
    (x : Nat) (hx : 1 <= x) {s : Complex}
    (hsRe : s.re = -(1 : Real) / 2) :
    norm (((x : Complex) ^ s - 1) / s) <=
      6 / (abs s.im + 1) := by
  have hxPos : 0 < x := Nat.zero_lt_of_lt hx
  have hxReal : (1 : Real) <= (x : Real) := Nat.one_le_cast.mpr hx
  have hPower :
      norm ((x : Complex) ^ s) <= 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hxPos s, hsRe]
    exact Real.rpow_le_one_of_one_le_of_nonpos hxReal (by norm_num)
  have hNumerator :
      norm ((x : Complex) ^ s - 1) <= 2 := by
    calc
      norm ((x : Complex) ^ s - 1) <=
          norm ((x : Complex) ^ s) + norm (1 : Complex) :=
        norm_sub_le _ _
      _ <= 1 + 1 := add_le_add hPower (by norm_num)
      _ = 2 := by norm_num
  have hReNorm : (1 : Real) / 2 <= norm s := by
    calc
      (1 : Real) / 2 = abs s.re := by rw [hsRe]; norm_num
      _ <= norm s := Complex.abs_re_le_norm s
  have hImNorm : abs s.im <= norm s := Complex.abs_im_le_norm s
  have hNormPos : 0 < norm s := by linarith
  have hScaleNorm : abs s.im + 1 <= 3 * norm s := by
    linarith
  have hThirdPos : 0 < (abs s.im + 1) / 3 := by positivity
  have hThirdLe : (abs s.im + 1) / 3 <= norm s := by
    linarith
  have hInv :
      1 / norm s <= 1 / ((abs s.im + 1) / 3) :=
    one_div_le_one_div_of_le hThirdPos hThirdLe
  rw [norm_div]
  calc
    norm ((x : Complex) ^ s - 1) / norm s <=
        2 / norm s :=
      div_le_div_of_nonneg_right hNumerator (norm_nonneg s)
    _ = 2 * (1 / norm s) := by ring
    _ <= 2 * (1 / ((abs s.im + 1) / 3)) :=
      mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ = 6 / (abs s.im + 1) := by
      field_simp
      norm_num

end BombieriVinogradov.SiegelWalfisz
