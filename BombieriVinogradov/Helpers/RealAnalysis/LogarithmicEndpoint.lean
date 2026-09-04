import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Logarithmic correction at a common real endpoint

Positive natural endpoints below the floor inherit the logarithmic
correction at the real cutoff. The correction is nonnegative above one.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem log_mul_log_nat_le_of_le_floor {N y : Nat} {X : Real}
    (hX : 0 <= X) (hy : 0 < y) (hyX : y <= Nat.floor X) :
    Real.log N * Real.log y / Real.log (2 : Real) <=
      Real.log N * Real.log X / Real.log (2 : Real) := by
  have hLog := Real.log_le_log (Nat.cast_pos.mpr hy)
    ((Nat.cast_le.mpr hyX).trans (Nat.floor_le hX))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLog (Real.log_natCast_nonneg N))
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le

theorem log_mul_log_div_log_two_nonneg (N : Nat) {X : Real} (hX : 1 <= X) :
    0 <= Real.log N * Real.log X / Real.log (2 : Real) :=
  div_nonneg (mul_nonneg (Real.log_natCast_nonneg N) (Real.log_nonneg hX))
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le

end BombieriVinogradov.RealAnalysis
