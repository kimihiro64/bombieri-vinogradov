import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Square-root factorization in a logarithmic exponential scale

The complementary half-quadratic exponential turns the x-scale into its
positive square root. This exact identity supports the small-endpoint bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Exact half-quadratic cancellation against the logarithmic exponential scale. -/
theorem sqrt_exponentialLog_scale_factorization {x t a : Real}
    (hx : 0 < x) (hSquare : t ^ 2 = Real.log x) :
    (x * Real.exp (-(a * t))) *
        Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t) = Real.sqrt x := by
  have hxExp : x = Real.exp (t ^ 2) := by rw [hSquare, Real.exp_log hx]
  have hRoot : Real.exp (t ^ 2 / 2) = Real.sqrt x := by
    rw [hSquare, <- Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]
  have hCancel : t ^ 2 + (-(a * t)) + (-(1 / 2 : Real) * t ^ 2 + a * t) =
      t ^ 2 / 2 := by ring
  calc
    (x * Real.exp (-(a * t))) * Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t) =
        (Real.exp (t ^ 2) * Real.exp (-(a * t))) *
          Real.exp (-(1 / 2 : Real) * t ^ 2 + a * t) := by rw [hxExp]
    _ = Real.exp (t ^ 2 + (-(a * t)) +
        (-(1 / 2 : Real) * t ^ 2 + a * t)) := by
      rw [<- Real.exp_add, <- Real.exp_add]
    _ = Real.exp (t ^ 2 / 2) := by rw [hCancel]
    _ = Real.sqrt x := hRoot

end BombieriVinogradov.RealAnalysis
