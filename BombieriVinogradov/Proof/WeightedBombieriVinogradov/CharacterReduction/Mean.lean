import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveMaximalNonneg
import BombieriVinogradov.Helpers.Nat.WeightedDivisorTotient
import BombieriVinogradov.Helpers.RealAnalysis.LogarithmicCorrectionSum
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.CharacterReduction.Maximal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Modulus-averaged primitive character reduction

Combine the maximal discrepancy bound, nonnegative conductor lifting and the
summed logarithmic Euler correction. The cutoff may be zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Reduce the averaged maximal weighted discrepancy to its primitive conductor mean. -/
theorem averageWeightedDiscrepancy_le_primitiveConductorMean
    (Q : Nat) {X : Real} (hX : 2 <= X) :
    averageWeightedDiscrepancy X Q <=
      (1 + Real.log Q) ^ 2 * primitiveConductorMean X Q +
        (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by
  have hX1 : 1 <= X := by linarith
  unfold averageWeightedDiscrepancy
  calc
    Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy X) <=
        Finset.sum (Finset.Icc 1 Q) (fun q =>
          Finset.sum q.divisors (nonprincipalPrimitiveMaximalSum X) / (q.totient : Real) +
            Real.log q * Real.log X / Real.log (2 : Real)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
      let : NeZero q := NeZero.mk (Nat.ne_of_gt hqPos)
      exact maximalWeightedDiscrepancy_le_primitive hX
    _ = Finset.sum (Finset.Icc 1 Q)
          (fun q => Finset.sum q.divisors (nonprincipalPrimitiveMaximalSum X) /
            (q.totient : Real)) +
        Finset.sum (Finset.Icc 1 Q)
          (fun q => Real.log q * Real.log X / Real.log (2 : Real)) :=
      Finset.sum_add_distrib
    _ <= (1 + Real.log Q) ^ 2 * primitiveConductorMean X Q +
        (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) :=
      add_le_add
        (sum_weighted_divisors_div_totient_le_log_sq Q
          (nonprincipalPrimitiveMaximalSum X) (nonprincipalPrimitiveMaximalSum_nonneg X))
        (RealAnalysis.sum_log_mul_log_div_log_two_le Q (X := X) hX1)

end BombieriVinogradov.WeightedBombieriVinogradov
