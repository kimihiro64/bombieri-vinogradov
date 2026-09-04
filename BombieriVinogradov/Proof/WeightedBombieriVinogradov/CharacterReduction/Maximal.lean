import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.CharacterReduction.MaximalPointwise
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.SetNotation

/-!
# Maximal discrepancy bounded by primitive conductor weights

Take both suprema in the endpoint-uniform primitive character reduction.
The finite endpoint type includes zero and the global centering is unchanged.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The primitive conductor bound is uniform over both maxima in the discrepancy. -/
theorem maximalWeightedDiscrepancy_le_primitive
    {X : Real} {N : Nat} [NeZero N] (hX : 2 <= X) :
    maximalWeightedDiscrepancy X N <=
      Finset.sum N.divisors (nonprincipalPrimitiveMaximalSum X) / (N.totient : Real) +
        Real.log N * Real.log X / Real.log (2 : Real) := by
  unfold maximalWeightedDiscrepancy
  exact ciSup_le (fun a => ciSup_le (fun y =>
    abs_psiProgression_sub_psiGlobal_div_totient_le_maximal_primitive
      a hX (Nat.le_of_lt_succ y.isLt)))

end BombieriVinogradov.WeightedBombieriVinogradov
