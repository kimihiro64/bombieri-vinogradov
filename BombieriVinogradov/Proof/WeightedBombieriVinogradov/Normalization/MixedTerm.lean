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
# Normalized mixed-power contribution

The complete outer factors are retained at the common denominator scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The mixed-power Vaughan term retains coefficient twenty-four. -/
theorem normalized_mixed_term {X A C delta : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X)
    (hSaving : (Real.log X) ^ (A + 8) <= X ^ delta) (hDelta : delta <= 1 / 6) :
    (C * Real.log (X * (Q : Real)) ^ 3) *
        (X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real))) <=
      24 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hQLogNonneg : 0 <= Real.log (Q : Real) := hRange.2.1
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hPower := RealAnalysis.rpow_mul_pow_le_div_of_saving
    (X := X) (L := Real.log X) (b := A + 8) (t := (5 / 6 : Real))
    (delta := delta) (w := A + 2) 4 hXOne hLogOne hSaving
    (show (A + 2) + (4 : Real) <= A + 8 by linarith) (by linarith)
  have hLinear : X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) <=
      X ^ (5 / 6 : Real) * (3 * Real.log X) :=
    mul_le_mul_of_nonneg_left hEnvelope.2.2 (Real.rpow_nonneg hXPos.le (5 / 6))
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) *
        (X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real))) <=
      (C * (8 * (Real.log X) ^ 3)) * (X ^ (5 / 6 : Real) * (3 * Real.log X)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hLinear
        (by positivity) (by positivity)
    _ = 24 * C * (X ^ (5 / 6 : Real) * (Real.log X) ^ 4) := by ring
    _ <= 24 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
