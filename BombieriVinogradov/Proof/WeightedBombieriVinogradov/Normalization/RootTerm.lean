import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogEnvelope
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
# Normalized square-root contribution

The complete outer factors are retained at the common denominator scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The square-root Vaughan term retains coefficient sixteen. -/
theorem normalized_root_term {X A C theta delta : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X) (hPowerQ : (Q : Real) <= X ^ theta)
    (hSaving : (Real.log X) ^ (A + 8) <= X ^ delta)
    (hGap : theta + delta <= 1 / 2) :
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X ^ (1 / 2 : Real) * (Q : Real)) <=
      16 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hPower := RealAnalysis.rpow_mul_pow_le_div_of_saving
    (X := X) (L := Real.log X) (b := A + 8) (t := (1 / 2 : Real) + theta)
    (delta := delta) (w := A + 2) 3 hXOne hLogOne hSaving
    (show (A + 2) + (3 : Real) <= A + 8 by linarith) (by linarith)
  have hRoot : 2 * X ^ (1 / 2 : Real) * (Q : Real) <=
      2 * X ^ (1 / 2 : Real) * X ^ theta :=
    mul_le_mul_of_nonneg_left hPowerQ (by positivity)
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X ^ (1 / 2 : Real) * (Q : Real)) <=
        (C * (8 * (Real.log X) ^ 3)) * (2 * X ^ (1 / 2 : Real) * X ^ theta) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hRoot
        (by positivity) (by positivity)
    _ = 16 * C * (X ^ ((1 / 2 : Real) + theta) * (Real.log X) ^ 3) := by
      rw [Real.rpow_add hXPos (1 / 2) theta]
      ring
    _ <= 16 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
