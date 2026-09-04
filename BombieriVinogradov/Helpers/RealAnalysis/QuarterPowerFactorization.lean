import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exact quarter-power remainder factorization

At a square logarithmic scale, factor the secondary source term into
the target decay scale and one explicit quadratic exponential.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem quarterPower_log_factorization
    {x t a : Real} (hx : 0 < x) (hSquare : t ^ 2 = Real.log x) :
    x ^ (1 / 4 : Real) * Real.log x =
      (x * Real.exp (-(a * t))) *
        (t ^ 2 * Real.exp (-(3 / 4 : Real) * t ^ 2 + a * t)) := by
  have hxExp : Real.exp (t ^ 2) = x := by rw [hSquare, Real.exp_log hx]
  have hSplit : Real.exp (t ^ 2 / 4) =
      Real.exp (t ^ 2) * Real.exp (-(a * t)) *
        Real.exp (-(3 / 4 : Real) * t ^ 2 + a * t) := by
    rw [<- Real.exp_add, <- Real.exp_add]
    congr 1
    ring
  have hArg : t ^ 2 * (1 / 4 : Real) = t ^ 2 / 4 := by ring
  rw [Real.rpow_def_of_pos hx, <- hSquare, hArg, hSplit, hxExp]
  ring

end BombieriVinogradov.RealAnalysis
