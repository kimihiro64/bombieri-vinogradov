import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Positivity

/-!
# Continuity of logarithmically weighted reciprocal decay

This module owns continuity and finite-interval integrability of the real
majorant used by later vertical-contour estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem continuous_log_weight_div_abs_add_one
    (A C : Real) :
    Continuous (fun t : Real =>
      (A + C * Real.log (abs t + 2)) *
        (6 / (abs t + 1))) := by
  have hAbsOne : Continuous (fun t : Real => abs t + 1) :=
    continuous_abs.add continuous_const
  have hAbsTwo : Continuous (fun t : Real => abs t + 2) :=
    continuous_abs.add continuous_const
  have hSixReciprocal :
      Continuous (fun t : Real => 6 / (abs t + 1)) :=
    continuous_const.div hAbsOne (fun t => by positivity)
  have hLog : Continuous (fun t : Real => Real.log (abs t + 2)) :=
    hAbsTwo.log (fun t => by positivity)
  exact (continuous_const.add (continuous_const.mul hLog)).mul
    hSixReciprocal

theorem intervalIntegrable_log_weight_div_abs_add_one
    (A C T : Real) :
    IntervalIntegrable
      (fun t : Real =>
        (A + C * Real.log (abs t + 2)) *
          (6 / (abs t + 1)))
      MeasureTheory.volume (-T) T :=
  (continuous_log_weight_div_abs_add_one A C).intervalIntegrable _ _

end BombieriVinogradov.RealAnalysis
