import BombieriVinogradov.Helpers.RealAnalysis.BoundedLogRescaling
import BombieriVinogradov.Helpers.RealAnalysis.PowerFloorCutoff
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimePowerEventual
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Global prime-power error absorption

The eventual estimate is extended to every endpoint at least three by a
symbolic bound on the remaining real interval.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The averaged prime-power error has arbitrary logarithmic decay for every endpoint. -/
theorem primePowerMeanError_global
    (theta : Real) (hTheta : theta < 1 / 2)
    (A : Real) (hA : 1 <= A) :
    exists C : Real, And (0 < C) (forall {X : Real}, 3 <= X ->
      (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X) <=
        C * (X / (Real.log X) ^ A)) := by
  have hEventually := eventually_primePowerMeanError theta hTheta A
  choose M hTail using Filter.eventually_atTop.mp hEventually
  let T : Real := max 3 M
  let K : Real := T * (4 * Real.sqrt T * Real.log T)
  let Cb : Real := (K + 1) * (Real.log T) ^ A
  have hMT : M <= T := le_max_right 3 M
  have hThreeT : 3 <= T := le_max_left 3 M
  have hTPos : 0 < T := by linarith
  have hLogTPos : 0 < Real.log T := Real.log_pos (by linarith)
  have hK : 0 <= K := by
    dsimp [K]
    positivity
  have hCb : 0 < Cb := by
    dsimp [Cb]
    positivity
  refine Exists.intro (4 + Cb) (And.intro (by positivity) ?_)
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
      (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X) <=
        4 * (X / (Real.log X) ^ A) := hEvent
      _ <= (4 + Cb) * (X / (Real.log X) ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hScaleNonneg
  case neg =>
    have hXT : X <= T := (lt_of_not_ge hLarge).le
    have hThetaOne : theta <= 1 := by linarith
    have hCutoffX : (Nat.floor (X ^ theta) : Real) <= X :=
      RealAnalysis.floor_rpow_le_self hXOne hThetaOne
    have hCutoffT : (Nat.floor (X ^ theta) : Real) <= T :=
      hCutoffX.trans hXT
    have hLogOrder : Real.log X <= Real.log T :=
      Real.log_le_log hXPos hXT
    have hFourSqrt : 4 * Real.sqrt X <= 4 * Real.sqrt T :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hXT) (by positivity)
    have hInner : 4 * Real.sqrt X * Real.log X <=
        4 * Real.sqrt T * Real.log T :=
      mul_le_mul hFourSqrt hLogOrder (Real.log_nonneg hXOne) (by positivity)
    have hBound : (Nat.floor (X ^ theta) : Real) *
        (4 * Real.sqrt X * Real.log X) <= K := by
      dsimp [K]
      exact mul_le_mul hCutoffT hInner (by positivity) (by linarith)
    have hRescale : K <= Cb * (X / (Real.log X) ^ A) := by
      simpa only [Cb] using
        (RealAnalysis.bounded_log_rescaling hX hXT hA hK)
    calc
      (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X) <=
        Cb * (X / (Real.log X) ^ A) := hBound.trans hRescale
      _ <= (4 + Cb) * (X / (Real.log X) ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hScaleNonneg

end BombieriVinogradov.PrimeCountingConversion
