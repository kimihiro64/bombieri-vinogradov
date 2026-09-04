import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

/-!
# Conductor-weighted nonprincipal primitive maxima

This is the cumulative Vaughan weight before reciprocal Abel summation.
The principal character is omitted, as required by the centered discrepancy.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The nonprincipal primitive maximal sum with Vaughan's conductor weight. -/
noncomputable def nonprincipalPrimitiveConductorWeight (X : Real) (q : Nat) : Real :=
  (q : Real) / (q.totient : Real) * nonprincipalPrimitiveMaximalSum X q

end BombieriVinogradov.WeightedBombieriVinogradov
