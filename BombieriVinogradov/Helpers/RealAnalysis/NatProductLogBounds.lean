import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Logarithms of natural products

For a level at least three and an argument at least two, the product
logarithm is at least one and dominates either factor logarithm.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem natProductLog_bounds {N x : Nat} (hN : 3 <= N) (hx : 2 <= x) :
    And (1 <= Real.log ((N * x : Nat) : Real))
      (And (Real.log N <= Real.log ((N * x : Nat) : Real))
        (Real.log x <= Real.log ((N * x : Nat) : Real))) := by
  have hNPos : 0 < (N : Real) := Nat.cast_pos.mpr (by omega)
  have hxPos : 0 < (x : Real) := Nat.cast_pos.mpr (by omega)
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hNThree : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hLogNOne : 1 <= Real.log N :=
    hLogThree.trans (Real.log_le_log (by norm_num) hNThree)
  have hLogNNonneg := Real.log_natCast_nonneg N
  have hLogxNonneg := Real.log_natCast_nonneg x
  have hProduct : Real.log ((N * x : Nat) : Real) = Real.log N + Real.log x := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hNPos) (ne_of_gt hxPos)]
  rw [hProduct]
  exact And.intro (by linarith) (And.intro (by linarith) (by linarith))

end BombieriVinogradov.RealAnalysis
