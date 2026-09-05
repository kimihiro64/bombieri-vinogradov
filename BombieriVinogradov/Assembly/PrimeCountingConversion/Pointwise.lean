import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimeCountBridge
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimeNatDiscrepancy
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.NormNum

/-!
# Public pointwise prime discrepancy

The finite natural-count estimate is transferred to the exact public real-cutoff
prime-counting definition.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The public prime discrepancy is bounded by the weighted maximum and prime powers. -/
theorem primeDiscrepancy_le {X : Real} {q : Nat}
    (a : Units (ZMod q)) (hX : 3 <= X) (hq : 1 <= q) :
    primeDiscrepancy X q a <=
      (WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
        4 * Real.sqrt X * Real.log X) / Real.log (2 : Real) := by
  have hXNonneg : 0 <= X := le_trans (by norm_num) hX
  have hBound := primeNatDiscrepancy_le a hX hq
  rw [primeProgressionNat_eq_primeCountingZMod hXNonneg q (a : ZMod q),
    primeGlobalNat_eq_primeCounting] at hBound
  simpa only [primeDiscrepancy, primeCounting, pi] using hBound

end BombieriVinogradov.PrimeCountingConversion
