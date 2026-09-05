import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Helpers.RealAnalysis.LogReciprocalAbelBound
import BombieriVinogradov.Proof.PrimeCountingConversion.CenteredCoefficientSums
import BombieriVinogradov.Proof.PrimeCountingConversion.CenteredPrimeLog
import BombieriVinogradov.Proof.PrimeCountingConversion.ThetaPrefixBound
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.NormNum

/-!
# Pointwise prime-counting conversion

Reciprocal-log Abel summation turns the uniform theta-prefix bound into the
corresponding centered unweighted prime-count bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The centered prime-count discrepancy is controlled pointwise by the weighted maximum. -/
theorem primeNatDiscrepancy_le {X : Real} {q : Nat}
    (a : Units (ZMod q)) (hX : 3 <= X) (hq : 1 <= q) :
    abs ((primeProgressionNat (Nat.floor X) q (a : ZMod q) : Real) -
      (primeGlobalNat (Nat.floor X) : Real) / (q.totient : Real)) <=
      (WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
        4 * Real.sqrt X * Real.log X) / Real.log (2 : Real) := by
  have hTwoThree : (2 : Real) <= 3 := by norm_num
  have hFloor : 2 <= Nat.floor X := Nat.le_floor (hTwoThree.trans hX)
  rw [Eq.symm (sum_centeredTheta_div_log (N := Nat.floor X)
    (q := q) (a : ZMod q))]
  exact RealAnalysis.abs_sum_Icc_div_log_le
    (fun n => centeredThetaCoefficient n q (a : ZMod q)) hFloor
    (centeredThetaCoefficient_one q (a : ZMod q)) (by
      intro k hk hkFloor
      exact abs_sum_centeredThetaCoefficient_le a hX hq hk hkFloor)

end BombieriVinogradov.PrimeCountingConversion
