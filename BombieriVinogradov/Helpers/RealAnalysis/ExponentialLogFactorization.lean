import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Cancellation in the logarithmic exponential scale

The selected scale times its complementary exponential is exactly one.
This identity supports polynomial error bounds without a numerical cutoff.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exponentialLog_scale_cancellation
    {x t a : Real} (hx : 0 < x) (hSquare : t ^ 2 = Real.log x) :
    (x * Real.exp (-(a * t))) * Real.exp (-t ^ 2 + a * t) = 1 := by
  have hxExp : x = Real.exp (t ^ 2) := by rw [hSquare, Real.exp_log hx]
  have hCancel : t ^ 2 + (-(a * t)) + (-t ^ 2 + a * t) = 0 := by ring
  rw [hxExp, <- Real.exp_add, <- Real.exp_add, hCancel, Real.exp_zero]

end BombieriVinogradov.RealAnalysis
