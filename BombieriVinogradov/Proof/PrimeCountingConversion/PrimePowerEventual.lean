import BombieriVinogradov.Helpers.RealAnalysis.LogarithmicAbsorption
import BombieriVinogradov.Helpers.RealAnalysis.RpowSavingTransfer
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eventual prime-power error absorption

The positive gap below one-half absorbs the modulus cutoff, square root, and
one numerator logarithm into any requested logarithmic denominator.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The averaged prime-power conversion error has arbitrary logarithmic decay eventually. -/
theorem eventually_primePowerMeanError
    (theta : Real) (hTheta : theta < 1 / 2) (A : Real) :
    Filter.Eventually (fun X : Real =>
      (Nat.floor (X ^ theta) : Real) *
          (4 * Real.sqrt X * Real.log X) <=
        4 * (X / (Real.log X) ^ A)) Filter.atTop := by
  let delta : Real := 1 / 2 - theta
  have hDelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hSaving :=
    RealAnalysis.eventually_log_rpow_le_rpow (A + 1) hDelta
  have hLarge := Filter.eventually_ge_atTop (Real.exp (4 : Real))
  refine (hSaving.and hLarge).mono ?_
  intro X h
  have hX : Real.exp (4 : Real) <= X := h.2
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hXOne : 1 <= X :=
    (Real.one_le_exp (show (0 : Real) <= 4 by positivity)).trans hX
  have hLogFour : 4 <= Real.log X :=
    (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogOne : 1 <= Real.log X := by linarith
  have hCutoff : (Nat.floor (X ^ theta) : Real) <= X ^ theta :=
    Nat.floor_le (Real.rpow_nonneg hXPos.le theta)
  have hTransfer :
      X ^ (theta + 1 / 2) * (Real.log X) ^ (1 : Real) <=
        X / (Real.log X) ^ A :=
    RealAnalysis.rpow_mul_rpow_le_div_of_saving hXOne hLogOne h.1
      (by linarith) (by dsimp [delta]; linarith)
  calc
    (Nat.floor (X ^ theta) : Real) *
        (4 * Real.sqrt X * Real.log X) <=
      X ^ theta * (4 * Real.sqrt X * Real.log X) :=
        mul_le_mul_of_nonneg_right hCutoff (by positivity)
    _ = 4 * (X ^ (theta + 1 / 2) * (Real.log X) ^ (1 : Real)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hXPos theta (1 / 2),
        Real.rpow_one]
      ring
    _ <= 4 * (X / (Real.log X) ^ A) :=
      mul_le_mul_of_nonneg_left hTransfer (by positivity)

end BombieriVinogradov.PrimeCountingConversion
