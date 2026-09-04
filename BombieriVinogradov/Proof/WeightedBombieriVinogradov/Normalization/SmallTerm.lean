import BombieriVinogradov.Helpers.RealAnalysis.RpowDecayTransfer
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Normalized small-conductor contribution

The complete outer factors are retained at the common denominator scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The small-conductor term keeps its original uniform coefficient. -/
theorem normalized_small_term {X A C a : Real} {R : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hR : (R : Real) <= (Real.log X) ^ (A + 8))
    (hDecay : (Real.log X) ^ ((A + 8) + (A + 2)) *
      Real.exp (-(a * Real.sqrt (Real.log X))) <= 1) :
    C * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))) <=
      C * (X / (Real.log X) ^ (A + 2)) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogPos : 0 < Real.log X := by linarith
  exact mul_le_mul_of_nonneg_left
    (RealAnalysis.cutoff_mul_mul_le_div_of_decay
      (L := Real.log X) (X := X) (E := Real.exp (-(a * Real.sqrt (Real.log X))))
      (r := (R : Real)) (B := A + 8) (w := A + 2)
      hLogPos hXPos.le (Real.exp_pos _).le hR hDecay) hC

end BombieriVinogradov.WeightedBombieriVinogradov
