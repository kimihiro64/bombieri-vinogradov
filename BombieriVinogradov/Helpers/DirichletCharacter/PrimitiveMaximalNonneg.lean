import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.DirichletCharacter.MaximalChebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Nonnegativity of primitive maximal character weights

The nonprincipal primitive weight and its reciprocal-totient mean are nonnegative.
No lower bound on the real cutoff or natural conductor is needed.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Every conductor contributes a nonnegative primitive maximal norm sum. -/
theorem nonprincipalPrimitiveMaximalSum_nonneg (X : Real) (q : Nat) :
    0 <= nonprincipalPrimitiveMaximalSum X q := by
  unfold nonprincipalPrimitiveMaximalSum
  exact Finset.sum_nonneg (fun chi _ => VaughanMeanValue.maximalPsiNorm_nonneg X chi)

/-- The reciprocal-totient primitive mean is nonnegative, including cutoff zero. -/
theorem primitiveConductorMean_nonneg (X : Real) (Q : Nat) :
    0 <= primitiveConductorMean X Q := by
  unfold primitiveConductorMean
  exact Finset.sum_nonneg (fun d _ =>
    div_nonneg (nonprincipalPrimitiveMaximalSum_nonneg X d) (Nat.cast_nonneg d.totient))

end BombieriVinogradov.WeightedBombieriVinogradov
