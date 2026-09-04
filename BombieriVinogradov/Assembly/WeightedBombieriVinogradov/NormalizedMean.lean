import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.ConductorSplit
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.RealAnalysis.PolylogFloorCutoff
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.InverseTerm
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.MixedTerm
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.RootTerm
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.Normalization.SmallTerm
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Primitive conductor mean at the normalized logarithmic scale

The absolute decay rate and Vaughan coefficient remain outside the target
logarithmic exponent. All four contributions use the same denominator.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Normalize the primitive mean under the two explicit scalar absorption hypotheses. -/
theorem primitive_conductor_mean_normalized :
    exists a Cv : Real, And (0 < a) (And (0 < Cv)
      (forall A : Real, 1 <= A -> exists Cs : Real, And (0 < Cs)
        (forall {X theta delta : Real}, Real.exp (4 : Real) <= X ->
          delta <= 1 / 6 -> theta + delta <= 1 / 2 ->
          (Real.log X) ^ (A + 8) <= X ^ delta ->
          (Real.log X) ^ ((A + 8) + (A + 2)) *
            Real.exp (-(a * Real.sqrt (Real.log X))) <= 1 ->
          forall Q : Nat, 1 <= Q -> (Q : Real) <= X -> (Q : Real) <= X ^ theta ->
            primitiveConductorMean X Q <= (Cs + 72 * Cv) *
              (X / (Real.log X) ^ (A + 2))))) := by
  choose a Cv ha hCv hSplit using primitive_conductor_mean_split
  refine Exists.intro a (Exists.intro Cv (And.intro ha (And.intro hCv ?_)))
  intro A hA
  have hB : 0 < A + 8 := by linarith
  choose Cs hCs hBound using hSplit (A + 8) hB
  refine Exists.intro Cs (And.intro hCs ?_)
  intro X theta delta hX hDelta hGap hSaving hDecay Q hQ hQX hPowerQ
  let R : Nat := Nat.floor ((Real.log X) ^ (A + 8))
  have hCut := RealAnalysis.polylog_floor_cutoff_bounds (X := X) (B := A + 8)
    hX (by linarith)
  have hInitial := hBound (X := X) hX R Q hCut.1 hCut.2.1 hQ
  have hSmall := normalized_small_term (X := X) (A := A) (C := Cs) (a := a)
    (R := R) hX hCs.le hCut.2.1 hDecay
  have hInverse := normalized_inverse_term (X := X) (A := A) (C := Cv)
    (R := R) (Q := Q) hX hCv.le hQ hQX hCut.2.2
  have hMixed := normalized_mixed_term (X := X) (A := A) (C := Cv)
    (delta := delta) (Q := Q) hX hCv.le hQ hQX hSaving hDelta
  have hRoot := normalized_root_term (X := X) (A := A) (C := Cv)
    (theta := theta) (delta := delta) (Q := Q) hX hCv.le hQ hQX hPowerQ hSaving hGap
  calc
    primitiveConductorMean X Q <=
        Cs * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))) +
          (Cv * Real.log (X * (Q : Real)) ^ 3) *
            (2 * X / (R : Real) + X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) +
              2 * X ^ (1 / 2 : Real) * (Q : Real)) := hInitial
    _ = Cs * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))) +
        ((Cv * Real.log (X * (Q : Real)) ^ 3) * (2 * X / (R : Real)) +
          (Cv * Real.log (X * (Q : Real)) ^ 3) *
            (X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real))) +
          (Cv * Real.log (X * (Q : Real)) ^ 3) *
            (2 * X ^ (1 / 2 : Real) * (Q : Real))) := by ring
    _ <= Cs * (X / (Real.log X) ^ (A + 2)) +
        (32 * Cv * (X / (Real.log X) ^ (A + 2)) +
          24 * Cv * (X / (Real.log X) ^ (A + 2)) +
          16 * Cv * (X / (Real.log X) ^ (A + 2))) :=
      add_le_add hSmall (add_le_add (add_le_add hInverse hMixed) hRoot)
    _ = (Cs + 72 * Cv) * (X / (Real.log X) ^ (A + 2)) := by ring

end BombieriVinogradov.WeightedBombieriVinogradov
