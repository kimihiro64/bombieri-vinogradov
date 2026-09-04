import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic

/-!
# Elementary logarithmic size below a square-root endpoint

For natural endpoints below the square root, the elementary y log y term
is at most sqrt(X) log(X). The zero endpoint is included.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- The elementary natural-endpoint size is uniform below the square-root cutoff. -/
theorem nat_mul_log_le_sqrt_mul_log {X : Real} {y : Nat}
    (hX : 1 <= X) (hy : (y : Real) <= Real.sqrt X) :
    (y : Real) * Real.log y <= Real.sqrt X * Real.log X := by
  by_cases hZero : y = 0
  case pos =>
    subst y
    simpa using mul_nonneg (Real.sqrt_nonneg X) (Real.log_nonneg hX)
  case neg =>
    have hyPos : 0 < (y : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hZero)
    have hyX : (y : Real) <= X := hy.trans (Real.sqrt_le_self_iff.mpr (Or.inr hX))
    have hLog : Real.log y <= Real.log X := Real.log_le_log hyPos hyX
    calc
      (y : Real) * Real.log y <= (y : Real) * Real.log X :=
        mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg y)
      _ <= Real.sqrt X * Real.log X :=
        mul_le_mul_of_nonneg_right hy (Real.log_nonneg hX)

end BombieriVinogradov.RealAnalysis
