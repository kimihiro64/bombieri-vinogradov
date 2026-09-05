import BombieriVinogradov.Assembly.PrimeCountingConversion.Maximal
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Averaged prime discrepancy

The uniform class bound is summed over every positive modulus.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Summing the maximal conversion loses one prime-power error for each modulus. -/
theorem sum_maxPrimeDiscrepancy_le {X : Real} (Q : Nat) (hX : 3 <= X) :
    Finset.sum (Finset.Icc 1 Q) (maxPrimeDiscrepancy X) <=
      (WeightedBombieriVinogradov.averageWeightedDiscrepancy X Q +
        (Q : Real) * (4 * Real.sqrt X * Real.log X)) / Real.log (2 : Real) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (maxPrimeDiscrepancy X) <=
        Finset.sum (Finset.Icc 1 Q) (fun q =>
          (WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
            4 * Real.sqrt X * Real.log X) / Real.log (2 : Real)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxPrimeDiscrepancy_le hX (Finset.mem_Icc.mp hq).1
    _ = Finset.sum (Finset.Icc 1 Q) (fun q =>
        WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
          4 * Real.sqrt X * Real.log X) / Real.log (2 : Real) := by
      rw [Finset.sum_div]
    _ = (WeightedBombieriVinogradov.averageWeightedDiscrepancy X Q +
        (Q : Real) * (4 * Real.sqrt X * Real.log X)) /
          Real.log (2 : Real) := by
      unfold WeightedBombieriVinogradov.averageWeightedDiscrepancy
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul]

/-- The same bound at the exact public modulus cutoff. -/
theorem averagePrimeDiscrepancy_le {X theta : Real} (hX : 3 <= X) :
    averagePrimeDiscrepancy X theta <=
      (WeightedBombieriVinogradov.averageWeightedDiscrepancy X
          (Nat.floor (X ^ theta)) +
        (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X)) / Real.log (2 : Real) := by
  unfold averagePrimeDiscrepancy
  exact sum_maxPrimeDiscrepancy_le (Nat.floor (X ^ theta)) hX

end BombieriVinogradov.PrimeCountingConversion
