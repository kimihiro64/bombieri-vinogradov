import BombieriVinogradov.Helpers.RealAnalysis.FloorHalfBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A positive floor-log conductor cutoff

The cutoff stays below the Siegel-Walfisz logarithmic range and retains
at least half its real size.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- The floor of a logarithmic power gives an admissible positive conductor cutoff. -/
theorem polylog_floor_cutoff_bounds {X B : Real}
    (hX : Real.exp (4 : Real) <= X) (hB : 1 <= B) :
    And (1 <= Nat.floor ((Real.log X) ^ B))
      (And ((Nat.floor ((Real.log X) ^ B) : Real) <= (Real.log X) ^ B)
        ((Real.log X) ^ B / 2 <= (Nat.floor ((Real.log X) ^ B) : Real))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogOne : 1 <= Real.log X := by linarith
  have hPower : Real.log X <= (Real.log X) ^ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLogOne hB
  have hTwo : 2 <= (Real.log X) ^ B := by linarith
  exact floor_half_bounds hTwo

end BombieriVinogradov.RealAnalysis
