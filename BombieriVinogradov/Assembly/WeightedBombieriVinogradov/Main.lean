import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.Eventual
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.AverageMonotonicity
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.BoundedRescaling
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered weighted Bombieri-Vinogradov at every endpoint

The eventual analytic estimate is joined to a single finite endpoint bound.
No numerical certificate is used for the bounded real interval.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The centered weighted Bombieri-Vinogradov estimate for every real endpoint at least three. -/
theorem weighted_bombieri_vinogradov
    (theta : Real) (hTheta : theta < 1 / 2) (A : Real) (hA : 1 <= A) :
    exists C : Real, And (0 < C) (forall {X : Real}, 3 <= X ->
      averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) <=
        C * (X / (Real.log X) ^ A)) := by
  choose Ce hCe hEventually using eventually_weighted_bombieri_vinogradov theta hTheta A hA
  choose M hTail using (Filter.eventually_atTop.mp hEventually)
  let T : Real := max 3 M
  let K : Real := averageWeightedDiscrepancy T (Nat.floor T)
  let Cb : Real := (K + 1) * (Real.log T) ^ A
  have hMT : M <= T := le_max_right 3 M
  have hThreeT : 3 <= T := le_max_left 3 M
  have hTPos : 0 < T := by linarith
  have hK : 0 <= K := averageWeightedDiscrepancy_nonneg T (Nat.floor T)
  have hLogTPos : 0 < Real.log T := Real.log_pos (by linarith)
  have hCb : 0 < Cb := by
    dsimp [Cb]
    positivity
  refine Exists.intro (Ce + Cb) (And.intro (by positivity) ?_)
  intro X hX
  have hXPos : 0 < X := by linarith
  have hXOne : 1 <= X := by linarith
  have hLogXPos : 0 < Real.log X := Real.log_pos (by linarith)
  have hScaleNonneg : 0 <= X / (Real.log X) ^ A :=
    div_nonneg hXPos.le (Real.rpow_nonneg hLogXPos.le A)
  by_cases hLarge : T <= X
  case pos =>
    have hEvent := hTail X (hMT.trans hLarge)
    calc
      averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) <=
          Ce * (X / (Real.log X) ^ A) := hEvent
      _ <= (Ce + Cb) * (X / (Real.log X) ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hScaleNonneg
  case neg =>
    have hXT : X <= T := (lt_of_not_ge hLarge).le
    have hFloor : Nat.floor X <= Nat.floor T := Nat.floor_mono hXT
    have hPowerEndpoint : X ^ theta <= X := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (x := X) (y := theta) (z := (1 : Real))
          hXOne (by linarith))
    have hCutoff : Nat.floor (X ^ theta) <= Nat.floor T :=
      Nat.floor_mono (hPowerEndpoint.trans hXT)
    have hMono : averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) <= K := by
      dsimp [K]
      exact averageWeightedDiscrepancy_mono hFloor hCutoff
    have hBound : K <= Cb * (X / (Real.log X) ^ A) := by
      dsimp [Cb]
      exact bounded_weighted_rescaling hX hXT hA hK
    calc
      averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) <=
          Cb * (X / (Real.log X) ^ A) := hMono.trans hBound
      _ <= (Ce + Cb) * (X / (Real.log X) ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hScaleNonneg

end BombieriVinogradov.WeightedBombieriVinogradov
