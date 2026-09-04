import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.EndpointMonotonicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Average Monotonicity

This focused module owns one bounded-endpoint responsibility.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Enlarge both the maximal endpoint and the outer modulus cutoff. -/
theorem averageWeightedDiscrepancy_mono {X M : Real} {Q N : Nat}
    (hFloor : Nat.floor X <= Nat.floor M) (hQN : Q <= N) :
    averageWeightedDiscrepancy X Q <= averageWeightedDiscrepancy M N := by
  unfold averageWeightedDiscrepancy
  have hEndpoint : Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy X) <=
      Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy M) := by
    apply Finset.sum_le_sum
    intro q hq
    exact maximalWeightedDiscrepancy_mono q hFloor
  have hCutoff : Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy M) <=
      Finset.sum (Finset.Icc 1 N) (maximalWeightedDiscrepancy M) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQN)
      (fun q hq hnot => maximalWeightedDiscrepancy_nonneg M q)
  exact hEndpoint.trans hCutoff

/-- The averaged maximal discrepancy itself is nonnegative. -/
theorem averageWeightedDiscrepancy_nonneg (X : Real) (Q : Nat) :
    0 <= averageWeightedDiscrepancy X Q := by
  unfold averageWeightedDiscrepancy
  exact Finset.sum_nonneg (fun q hq => maximalWeightedDiscrepancy_nonneg X q)

end BombieriVinogradov.WeightedBombieriVinogradov
