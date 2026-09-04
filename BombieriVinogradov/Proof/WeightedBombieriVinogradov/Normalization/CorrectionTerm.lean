import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogRange
import BombieriVinogradov.Helpers.RealAnalysis.RpowSavingTransfer
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalized imprimitive correction

This module isolates one scalar step in the weighted mean argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The imprimitive correction retains its reciprocal-log-two coefficient. -/
theorem normalized_correction_term {X A theta delta : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X)
    (hPowerQ : (Q : Real) <= X ^ theta)
    (hSaving : (Real.log X) ^ (A + 8) <= X ^ delta) (hGap : theta + delta <= 1) :
    (Q : Real) * Real.log (Q : Real) * Real.log X / Real.log (2 : Real) <=
      (1 / Real.log (2 : Real)) * (X / (Real.log X) ^ A) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hLogPos : 0 < Real.log X := by linarith
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by linarith)
  have hPower := RealAnalysis.rpow_mul_pow_le_div_of_saving
    (X := X) (L := Real.log X) (b := A + 8) (t := theta)
    (delta := delta) (w := A) 2 hXOne hLogOne hSaving
    (show A + (2 : Real) <= A + 8 by linarith) hGap
  have hNumerator : (Q : Real) * Real.log (Q : Real) * Real.log X <=
      X ^ theta * (Real.log X) ^ 2 := by
    calc
      (Q : Real) * Real.log (Q : Real) * Real.log X <=
          (X ^ theta * Real.log X) * Real.log X :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hPowerQ hRange.2.2.1 hRange.2.1
            (Real.rpow_nonneg hXPos.le theta)) hLogPos.le
      _ = X ^ theta * (Real.log X) ^ 2 := by ring
  calc
    (Q : Real) * Real.log (Q : Real) * Real.log X / Real.log (2 : Real) <=
        (X ^ theta * (Real.log X) ^ 2) / Real.log (2 : Real) :=
      div_le_div_of_nonneg_right hNumerator hLogTwo.le
    _ <= (X / (Real.log X) ^ A) / Real.log (2 : Real) :=
      div_le_div_of_nonneg_right hPower hLogTwo.le
    _ = (1 / Real.log (2 : Real)) * (X / (Real.log X) ^ A) := by ring

end BombieriVinogradov.WeightedBombieriVinogradov
