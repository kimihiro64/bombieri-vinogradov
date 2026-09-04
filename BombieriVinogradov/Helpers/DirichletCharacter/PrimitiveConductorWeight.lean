import BombieriVinogradov.Definitions.PrimitiveConductorWeight
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveMaximalNonneg
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Elementary facts about the primitive conductor weight

Nonnegativity holds also at zero; reciprocal cancellation is stated only
at positive conductors.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Vaughan's nonprincipal conductor weight is always nonnegative. -/
theorem nonprincipalPrimitiveConductorWeight_nonneg (X : Real) (q : Nat) :
    0 <= nonprincipalPrimitiveConductorWeight X q := by
  unfold nonprincipalPrimitiveConductorWeight
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q.totient))
    (nonprincipalPrimitiveMaximalSum_nonneg X q)

/-- At positive conductors the extra reciprocal removes exactly Vaughan's conductor factor. -/
theorem nonprincipalPrimitiveConductorWeight_div (X : Real) {q : Nat} (hq : 0 < q) :
    nonprincipalPrimitiveConductorWeight X q / (q : Real) =
      nonprincipalPrimitiveMaximalSum X q / (q.totient : Real) := by
  have hqReal : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hPhiReal : (0 : Real) < (q.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hqZero : Ne (q : Real) 0 := by positivity
  have hPhiZero : Ne (q.totient : Real) 0 := by positivity
  unfold nonprincipalPrimitiveConductorWeight
  field_simp

end BombieriVinogradov.WeightedBombieriVinogradov
