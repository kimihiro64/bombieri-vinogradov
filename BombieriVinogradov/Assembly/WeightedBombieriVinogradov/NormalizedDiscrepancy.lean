import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.NormalizedMean
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.CharacterReduction.Mean
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.CorrectionTerm
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.LiftingTerm
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered weighted discrepancy under explicit absorption hypotheses

The primitive mean, squared lifting cost and imprimitive correction are
combined without changing their centered Chebyshev convention.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The weighted discrepancy has a uniform coefficient after scalar normalization. -/
theorem weighted_discrepancy_normalized :
    exists a : Real, And (0 < a)
      (forall A : Real, 1 <= A -> exists C : Real, And (0 < C)
        (forall {X theta delta : Real}, Real.exp (4 : Real) <= X ->
          delta <= 1 / 6 -> theta + delta <= 1 / 2 ->
          (Real.log X) ^ (A + 8) <= X ^ delta ->
          (Real.log X) ^ ((A + 8) + (A + 2)) *
            Real.exp (-(a * Real.sqrt (Real.log X))) <= 1 ->
          forall Q : Nat, 1 <= Q -> (Q : Real) <= X -> (Q : Real) <= X ^ theta ->
            averageWeightedDiscrepancy X Q <= C * (X / (Real.log X) ^ A))) := by
  choose a Cv ha hCv hMean using primitive_conductor_mean_normalized
  refine Exists.intro a (And.intro ha ?_)
  intro A hA
  choose Cs hCs hPrimitive using hMean A hA
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by linarith)
  refine Exists.intro (4 * Cs + 288 * Cv + 1 / Real.log (2 : Real))
    (And.intro (by positivity) ?_)
  intro X theta delta hX hDelta hGap hSaving hDecay Q hQ hQX hPowerQ
  have hExp := Real.add_one_le_exp (4 : Real)
  have hXTwo : 2 <= X := by linarith
  have hPrimitiveBound := hPrimitive (X := X) (theta := theta) (delta := delta)
    hX hDelta hGap hSaving hDecay Q hQ hQX hPowerQ
  have hLifting := normalized_lifting_term (X := X) (A := A)
    (C := Cs + 72 * Cv) (M := primitiveConductorMean X Q) (Q := Q)
    hX (by positivity) hQ hQX hPrimitiveBound
  have hCorrection := normalized_correction_term (X := X) (A := A)
    (theta := theta) (delta := delta) (Q := Q)
    hX hQ hQX hPowerQ hSaving (by linarith)
  calc
    averageWeightedDiscrepancy X Q <=
        (1 + Real.log (Q : Real)) ^ 2 * primitiveConductorMean X Q +
          (Q : Real) * Real.log (Q : Real) * Real.log X / Real.log (2 : Real) :=
      averageWeightedDiscrepancy_le_primitiveConductorMean Q hXTwo
    _ <= 4 * (Cs + 72 * Cv) * (X / (Real.log X) ^ A) +
        (1 / Real.log (2 : Real)) * (X / (Real.log X) ^ A) :=
      add_le_add hLifting hCorrection
    _ = (4 * Cs + 288 * Cv + 1 / Real.log (2 : Real)) *
        (X / (Real.log X) ^ A) := by ring

end BombieriVinogradov.WeightedBombieriVinogradov
