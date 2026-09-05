import BombieriVinogradov.Assembly.PrimeCountingConversion.Pointwise
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units

/-!
# Maximal prime discrepancy

The pointwise conversion is lifted over every reduced residue class.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The maximal public prime discrepancy obeys the same uniform pointwise bound. -/
theorem maxPrimeDiscrepancy_le {X : Real} {q : Nat}
    (hX : 3 <= X) (hq : 1 <= q) :
    maxPrimeDiscrepancy X q <=
      (WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
        4 * Real.sqrt X * Real.log X) / Real.log (2 : Real) := by
  unfold maxPrimeDiscrepancy
  apply ciSup_le
  intro a
  exact primeDiscrepancy_le a hX hq

end BombieriVinogradov.PrimeCountingConversion
