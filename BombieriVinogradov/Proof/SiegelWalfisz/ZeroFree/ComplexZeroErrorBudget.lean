import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform error budget for the complex zero argument

This module absorbs the principal constant and the two logarithmic-derivative
errors into one absolute multiple of `log N + log(|t| + 2)`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem complexZero_error_budget
    {C A B x y : Real} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : Real.log 3 ≤ x) (hy : 0 ≤ y) :
    3 * C + 4 * A * (x + y) + B * (x + 2 * y) ≤
      (3 * C / Real.log 3 + 4 * A + 2 * B) * (x + y) := by
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hxNonneg : 0 ≤ x := hLogThree.le.trans hx
  have hDivNonneg : 0 ≤ 3 * C / Real.log 3 :=
    div_nonneg (mul_nonneg (by norm_num) hC) hLogThree.le
  have hConstant : 3 * C ≤ (3 * C / Real.log 3) * x := by
    calc
      3 * C = (3 * C / Real.log 3) * Real.log 3 := by
        field_simp
      _ ≤ (3 * C / Real.log 3) * x :=
        mul_le_mul_of_nonneg_left hx hDivNonneg
  have hSquareTerm : B * (x + 2 * y) ≤ 2 * B * (x + y) := by
    nlinarith [mul_nonneg hB hxNonneg]
  nlinarith

end BombieriVinogradov.SiegelWalfisz
