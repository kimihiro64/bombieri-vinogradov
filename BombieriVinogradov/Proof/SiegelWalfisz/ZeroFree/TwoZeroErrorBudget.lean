import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Absorbing two-zero logarithmic-derivative errors

This pure real estimate absorbs the absolute and fixed-height terms from the
two-zero specialization of Lemma 11.3 into one coefficient of `log N`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem twoZero_error_budget {C A x : Real}
    (hC : 0 ≤ C) (hA : 0 < A) (hx : Real.log 3 ≤ x) :
    C + A * (x + Real.log 2) ≤
      (A + (C + A * Real.log 2) / Real.log 3) * x := by
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hConstant : 0 ≤ C + A * Real.log 2 := by positivity
  have hRatio : 0 ≤ (C + A * Real.log 2) / Real.log 3 :=
    div_nonneg hConstant hLogThree.le
  have hScaled := mul_le_mul_of_nonneg_left hx hRatio
  have hCancel :
      (C + A * Real.log 2) / Real.log 3 * Real.log 3 =
        C + A * Real.log 2 := by
    field_simp
  rw [hCancel] at hScaled
  nlinarith

end BombieriVinogradov.SiegelWalfisz
