import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Positive selected-height geometry
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem abs_eq_self_of_two_le_of_le
    {T Tprime : Real} (hT : 2 <= T) (hLower : T <= Tprime) :
    abs Tprime = Tprime := by
  exact abs_of_nonneg
    ((by norm_num : (0 : Real) <= 2).trans (hT.trans hLower))

theorem abs_neg_eq_self_of_two_le_of_le
    {T Tprime : Real} (hT : 2 <= T) (hLower : T <= Tprime) :
    abs (-Tprime) = Tprime := by
  rw [abs_neg]
  exact abs_eq_self_of_two_le_of_le hT hLower

theorem one_div_abs_le_one_div_of_two_le_of_le
    {T Tprime : Real} (hT : 2 <= T) (hLower : T <= Tprime) :
    1 / abs Tprime <= 1 / T := by
  rw [abs_eq_self_of_two_le_of_le hT hLower]
  exact one_div_le_one_div_of_le
    (lt_of_lt_of_le (by norm_num) hT) hLower

end BombieriVinogradov.RealAnalysis
