import BombieriVinogradov.Assembly.PrimeCountingConversion.Average
import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.Main
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimePowerGlobal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bombieri-Vinogradov prime-counting assembly

The weighted theorem and the globally absorbed prime-power conversion error
are combined at the exact public cutoff and centering convention.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The centered weighted theorem implies the exact public prime-counting statement. -/
theorem weighted_to_prime_counting : Statement := by
  rw [statement_iff_average]
  intro theta hTheta A hA
  choose Cw hCw hWeighted using
    WeightedBombieriVinogradov.weighted_bombieri_vinogradov
      theta hTheta A hA
  choose Cp hCp hPrimePower using
    primePowerMeanError_global theta hTheta A hA
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  let C : Real := (Cw + Cp) / Real.log (2 : Real)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hC ?_)
  intro X hX
  have hWeightedX := hWeighted hX
  have hPrimePowerX := hPrimePower hX
  have hAverage :=
    averagePrimeDiscrepancy_le (theta := theta) hX
  have hNumerator :
      WeightedBombieriVinogradov.averageWeightedDiscrepancy X
          (Nat.floor (X ^ theta)) +
        (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X) <=
      (Cw + Cp) * (X / (Real.log X) ^ A) := by
    calc
      WeightedBombieriVinogradov.averageWeightedDiscrepancy X
            (Nat.floor (X ^ theta)) +
          (Nat.floor (X ^ theta) : Real) *
            (4 * Real.sqrt X * Real.log X) <=
        Cw * (X / (Real.log X) ^ A) +
          Cp * (X / (Real.log X) ^ A) :=
            add_le_add hWeightedX hPrimePowerX
      _ = (Cw + Cp) * (X / (Real.log X) ^ A) := by ring
  calc
    averagePrimeDiscrepancy X theta <=
        (WeightedBombieriVinogradov.averageWeightedDiscrepancy X
            (Nat.floor (X ^ theta)) +
          (Nat.floor (X ^ theta) : Real) *
            (4 * Real.sqrt X * Real.log X)) /
              Real.log (2 : Real) := hAverage
    _ <= ((Cw + Cp) * (X / (Real.log X) ^ A)) /
        Real.log (2 : Real) :=
      div_le_div_of_nonneg_right hNumerator hLogTwo.le
    _ = C * X / (Real.log X) ^ A := by
      dsimp [C]
      ring

end BombieriVinogradov.PrimeCountingConversion
