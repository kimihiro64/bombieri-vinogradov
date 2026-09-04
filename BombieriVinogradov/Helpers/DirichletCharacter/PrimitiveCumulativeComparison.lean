import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.PrimitiveConductorWeight
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.MaximalChebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Comparing nonprincipal cumulative means with Vaughan's mean

Removing the principal character can only decrease each nonnegative
conductor-weighted maximal character sum.
-/

set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Omitting the principal character decreases the full primitive conductor weight. -/
theorem nonprincipalPrimitiveConductorWeight_le_full (X : Real) (q : Nat) :
    nonprincipalPrimitiveConductorWeight X q <=
      (q : Real) / (q.totient : Real) *
        Finset.sum (LargeSieve.primitiveCharacters q)
          (fun chi => VaughanMeanValue.maximalPsiNorm X chi) := by
  have hErased :
      Finset.sum ((LargeSieve.primitiveCharacters q).erase 1)
          (fun chi => VaughanMeanValue.maximalPsiNorm X chi) <=
        Finset.sum (LargeSieve.primitiveCharacters q)
          (fun chi => VaughanMeanValue.maximalPsiNorm X chi) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset 1 (LargeSieve.primitiveCharacters q))
      (fun chi _ _ => VaughanMeanValue.maximalPsiNorm_nonneg X chi)
  unfold nonprincipalPrimitiveConductorWeight nonprincipalPrimitiveMaximalSum
  exact mul_le_mul_of_nonneg_left hErased
    (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q.totient))

/-- The nonprincipal cumulative weight is bounded by Vaughan's full primitive mean. -/
theorem sum_conductorWeight_le_primitivePsiMean (X : Real) (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun q => nonprincipalPrimitiveConductorWeight X q) <=
      VaughanMeanValue.primitivePsiMean X Q := by
  unfold VaughanMeanValue.primitivePsiMean
  exact Finset.sum_le_sum (fun q _ => nonprincipalPrimitiveConductorWeight_le_full X q)

end BombieriVinogradov.WeightedBombieriVinogradov
