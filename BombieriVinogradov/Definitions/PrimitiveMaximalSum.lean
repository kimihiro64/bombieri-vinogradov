import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.VaughanMeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Primitive nonprincipal maximal character weights

The nonnegative weight at each conductor excludes the principal character.
Its mean retains the reciprocal totient, rather than Vaughan's conductor factor.
-/

set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Sum of maximal character norms over the nonprincipal primitive characters. -/
noncomputable def nonprincipalPrimitiveMaximalSum (X : Real) (q : Nat) : Real :=
  Finset.sum ((LargeSieve.primitiveCharacters q).erase 1)
    (fun chi => VaughanMeanValue.maximalPsiNorm X chi)

/-- The primitive nonprincipal maximal mean with reciprocal-totient weights. -/
noncomputable def primitiveConductorMean (X : Real) (Q : Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q)
    (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real))

end BombieriVinogradov.WeightedBombieriVinogradov
