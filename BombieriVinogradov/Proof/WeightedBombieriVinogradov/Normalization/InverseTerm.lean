import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogEnvelope
import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogRange
import BombieriVinogradov.Helpers.RealAnalysis.HalfCutoffReciprocal
import BombieriVinogradov.Helpers.RealAnalysis.RpowDenominatorScale
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalized inverse-cutoff contribution

The complete outer factors are retained at the common denominator scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The inverse-cutoff Vaughan term retains coefficient thirty-two. -/
theorem normalized_inverse_term {X A C : Real} {R Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X)
    (hR : (Real.log X) ^ (A + 8) / 2 <= (R : Real)) :
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X / (R : Real)) <=
      32 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hLogPos : 0 < Real.log X := by linarith
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hInverse := RealAnalysis.two_mul_div_le_of_half_le
    (T := (Real.log X) ^ (A + 8)) (r := (R : Real)) (X := X)
    (Real.rpow_pos_of_pos hLogPos (A + 8)) hR hXPos.le
  have hDenominator := RealAnalysis.pow_mul_div_le_div
    (L := Real.log X) (X := X) (v := A + 8) (w := A + 2) 3
    hLogOne hXPos.le (show (3 : Real) + (A + 2) <= A + 8 by linarith)
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X / (R : Real)) <=
        (C * (8 * (Real.log X) ^ 3)) * (4 * X / (Real.log X) ^ (A + 8)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hInverse
        (by positivity) (by positivity)
    _ = 32 * C * ((Real.log X) ^ 3 * (X / (Real.log X) ^ (A + 8))) := by ring
    _ <= 32 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hDenominator (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
