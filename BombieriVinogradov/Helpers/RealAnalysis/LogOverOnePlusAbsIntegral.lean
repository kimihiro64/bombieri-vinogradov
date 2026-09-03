import BombieriVinogradov.Helpers.RealAnalysis.OneDivAbsIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmically weighted reciprocal absolute-value integral

This module bounds a symmetric reciprocal weight with a nondecreasing
logarithmic numerator by freezing the numerator at the interval endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem intervalIntegral_log_weight_div_abs_add_one_le
    (A C T : Real) (hC : 0 <= C) (hT : 0 <= T) :
    intervalIntegral
        (fun t : Real =>
          (A + C * Real.log (abs t + 2)) *
            (6 / (abs t + 1)))
        (-T) T MeasureTheory.volume <=
      12 * (A + C * Real.log (T + 2)) *
        Real.log (T + 1) := by
  let f : Real -> Real := fun t =>
    (A + C * Real.log (abs t + 2)) *
      (6 / (abs t + 1))
  let g : Real -> Real := fun t =>
    ((A + C * Real.log (T + 2)) * 6) *
      (1 / (abs t + 1))
  have hAbsOne : Continuous (fun t : Real => abs t + 1) :=
    continuous_abs.add continuous_const
  have hAbsTwo : Continuous (fun t : Real => abs t + 2) :=
    continuous_abs.add continuous_const
  have hReciprocal : Continuous (fun t : Real => 1 / (abs t + 1)) :=
    continuous_const.div hAbsOne (fun t => by positivity)
  have hSixReciprocal :
      Continuous (fun t : Real => 6 / (abs t + 1)) :=
    continuous_const.div hAbsOne (fun t => by positivity)
  have hLog : Continuous (fun t : Real => Real.log (abs t + 2)) :=
    hAbsTwo.log (fun t => by positivity)
  have hfContinuous : Continuous f := by
    dsimp [f]
    exact (continuous_const.add (continuous_const.mul hLog)).mul
      hSixReciprocal
  have hgContinuous : Continuous g := by
    dsimp [g]
    exact continuous_const.mul hReciprocal
  have hfIntegrable :
      IntervalIntegrable f MeasureTheory.volume (-T) T :=
    hfContinuous.intervalIntegrable _ _
  have hgIntegrable :
      IntervalIntegrable g MeasureTheory.volume (-T) T :=
    hgContinuous.intervalIntegrable _ _
  have hPointwise :
      forall t : Real, (Set.Icc (-T) T) t -> f t <= g t := by
    intro t ht
    have htAbs : abs t <= T := abs_le.mpr (And.intro ht.1 ht.2)
    have hLogBound :
        Real.log (abs t + 2) <= Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hWeight :
        A + C * Real.log (abs t + 2) <=
          A + C * Real.log (T + 2) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hLogBound hC) A
    have hKernelNonneg : 0 <= 6 / (abs t + 1) := by positivity
    dsimp [f, g]
    calc
      (A + C * Real.log (abs t + 2)) *
          (6 / (abs t + 1)) <=
        (A + C * Real.log (T + 2)) *
          (6 / (abs t + 1)) :=
        mul_le_mul_of_nonneg_right hWeight hKernelNonneg
      _ = ((A + C * Real.log (T + 2)) * 6) *
          (1 / (abs t + 1)) := by ring
  have hMono :
      intervalIntegral f (-T) T MeasureTheory.volume <=
        intervalIntegral g (-T) T MeasureTheory.volume :=
    intervalIntegral.integral_mono_on (by linarith)
      hfIntegrable hgIntegrable hPointwise
  calc
    intervalIntegral
        (fun t : Real =>
          (A + C * Real.log (abs t + 2)) *
            (6 / (abs t + 1)))
        (-T) T MeasureTheory.volume =
      intervalIntegral f (-T) T MeasureTheory.volume := by rfl
    _ <= intervalIntegral g (-T) T MeasureTheory.volume := hMono
    _ = ((A + C * Real.log (T + 2)) * 6) *
        intervalIntegral (fun t : Real => 1 / (abs t + 1))
          (-T) T MeasureTheory.volume := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul]
    _ = 12 * (A + C * Real.log (T + 2)) *
        Real.log (T + 1) := by
      rw [intervalIntegral_one_div_abs_add_one T hT]
      ring

end BombieriVinogradov.RealAnalysis
