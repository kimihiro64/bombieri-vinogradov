import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral of one over one plus absolute value

This module evaluates the elementary symmetric reciprocal-weight integral used
to turn vertical contour decay into a logarithmic loss.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem intervalIntegral_one_div_abs_add_one
    (T : Real) (hT : 0 <= T) :
    intervalIntegral (fun t : Real => 1 / (abs t + 1))
        (-T) T MeasureTheory.volume =
      2 * Real.log (T + 1) := by
  let f : Real -> Real := fun t => 1 / (abs t + 1)
  have hfContinuous : Continuous f := by
    dsimp [f]
    exact continuous_const.div (continuous_abs.add continuous_const)
      (fun t => by positivity)
  have hfNeg : IntervalIntegrable f MeasureTheory.volume (-T) 0 :=
    hfContinuous.intervalIntegrable _ _
  have hfPos : IntervalIntegrable f MeasureTheory.volume 0 T :=
    hfContinuous.intervalIntegrable _ _
  have hSplit :
      intervalIntegral f (-T) T MeasureTheory.volume =
        intervalIntegral f (-T) 0 MeasureTheory.volume +
          intervalIntegral f 0 T MeasureTheory.volume :=
    (intervalIntegral.integral_add_adjacent_intervals hfNeg hfPos).symm
  have hNegEq :
      intervalIntegral f (-T) 0 MeasureTheory.volume =
        intervalIntegral f 0 T MeasureTheory.volume := by
    have hComp :=
      intervalIntegral.integral_comp_neg
        (f := f) (a := 0) (b := T)
    simpa [f] using hComp.symm
  have hPos :
      intervalIntegral f 0 T MeasureTheory.volume =
        Real.log (T + 1) := by
    have hShift :=
      intervalIntegral.integral_comp_add_right
        (f := fun u : Real => u ^ (-1 : Int))
        (a := 0) (b := T) 1
    have hInv :=
      integral_inv_of_pos
        (a := (1 : Real)) (b := T + 1)
        (by norm_num) (by linarith)
    calc
      intervalIntegral f 0 T MeasureTheory.volume =
          intervalIntegral (fun t : Real => (t + 1) ^ (-1 : Int))
            0 T MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 <= t := by
          rw [Set.uIcc_of_le hT] at ht
          exact ht.1
        simp [abs_of_nonneg ht0]
      _ = intervalIntegral (fun u : Real => u ^ (-1 : Int))
            1 (T + 1) MeasureTheory.volume := by
        simpa only [zero_add] using hShift
      _ = Real.log ((T + 1) / 1) := by
        simpa only [zpow_neg_one] using hInv
      _ = Real.log (T + 1) := by simp
  rw [hSplit, hNegEq, hPos]
  ring

end BombieriVinogradov.RealAnalysis
