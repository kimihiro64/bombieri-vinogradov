import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogEnvelope
import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogRange
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
# Normalized logarithmic lifting

This module isolates one scalar step in the weighted mean argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Squared conductor lifting consumes exactly two powers of the denominator. -/
theorem normalized_lifting_term {X A C M : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C) (hQ : 1 <= Q)
    (hQX : (Q : Real) <= X) (hM : M <= C * (X / (Real.log X) ^ (A + 2))) :
    (1 + Real.log (Q : Real)) ^ 2 * M <= 4 * C * (X / (Real.log X) ^ A) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hLogPos : 0 < Real.log X := by linarith
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hEnvelope := (RealAnalysis.conductor_log_envelopes hX hQ hQX).2.1
  have hDenominator := RealAnalysis.pow_mul_div_le_div
    (L := Real.log X) (X := X) (v := A + 2) (w := A) 2
    hLogOne hXPos.le (show (2 : Real) + A <= A + 2 by linarith)
  calc
    (1 + Real.log (Q : Real)) ^ 2 * M <=
        (1 + Real.log (Q : Real)) ^ 2 * (C * (X / (Real.log X) ^ (A + 2))) :=
      mul_le_mul_of_nonneg_left hM (sq_nonneg _)
    _ <= (4 * (Real.log X) ^ 2) * (C * (X / (Real.log X) ^ (A + 2))) :=
      mul_le_mul_of_nonneg_right hEnvelope (by positivity)
    _ = 4 * C * ((Real.log X) ^ 2 * (X / (Real.log X) ^ (A + 2))) := by ring
    _ <= 4 * C * (X / (Real.log X) ^ A) :=
      mul_le_mul_of_nonneg_left hDenominator (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
