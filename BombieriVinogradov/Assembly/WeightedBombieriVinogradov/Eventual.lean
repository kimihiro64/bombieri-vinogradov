import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.NormalizedDiscrepancy
import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Helpers.RealAnalysis.HalfPowerGap
import BombieriVinogradov.Helpers.RealAnalysis.LogarithmicAbsorption
import BombieriVinogradov.Helpers.RealAnalysis.PowerFloorCutoff
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogAbsorption
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Eventual centered weighted Bombieri-Vinogradov

Both growth hypotheses are supplied beyond a parameter-dependent threshold.
The empty modulus range is included when the power cutoff is zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The centered maximal weighted estimate holds eventually for every exponent below one-half. -/
theorem eventually_weighted_bombieri_vinogradov
    (theta : Real) (hTheta : theta < 1 / 2) (A : Real) (hA : 1 <= A) :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun X : Real =>
        averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) <=
          C * (X / (Real.log X) ^ A)) Filter.atTop) := by
  choose a ha hNormalized using weighted_discrepancy_normalized
  choose C hC hBound using hNormalized A hA
  choose delta hDeltaPos hDelta hGap using
    RealAnalysis.exists_bounded_half_power_gap hTheta
  refine Exists.intro C (And.intro hC ?_)
  have hSaving := RealAnalysis.eventually_log_rpow_le_rpow (A + 8) hDeltaPos
  have hDecay := RealAnalysis.eventually_log_rpow_mul_exp_sqrt_le_one
    ((A + 8) + (A + 2)) ha
  have hLarge := Filter.eventually_ge_atTop (Real.exp (4 : Real))
  refine (hSaving.and (hDecay.and hLarge)).mono ?_
  intro X h
  have hX : Real.exp (4 : Real) <= X := h.2.2
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogPos : 0 < Real.log X := by linarith
  let Q : Nat := Nat.floor (X ^ theta)
  change averageWeightedDiscrepancy X Q <= C * (X / (Real.log X) ^ A)
  by_cases hQ : Q = 0
  case pos =>
    have hEmpty : averageWeightedDiscrepancy X Q = 0 := by
      simp [averageWeightedDiscrepancy, hQ]
    rw [hEmpty]
    positivity
  case neg =>
    have hQOne : 1 <= Q := Nat.pos_of_ne_zero hQ
    have hQX : (Q : Real) <= X :=
      RealAnalysis.floor_rpow_le_self hXOne (by linarith)
    have hPowerQ : (Q : Real) <= X ^ theta :=
      Nat.floor_le (Real.rpow_nonneg hXPos.le theta)
    exact hBound (X := X) (theta := theta) (delta := delta)
      hX hDelta hGap h.1 h.2.1 Q hQOne hQX hPowerQ

end BombieriVinogradov.WeightedBombieriVinogradov
