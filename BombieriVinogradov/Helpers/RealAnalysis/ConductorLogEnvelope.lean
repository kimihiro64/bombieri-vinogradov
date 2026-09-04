import BombieriVinogradov.Helpers.RealAnalysis.ConductorLogRange
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial envelopes for conductor logarithms

The mean-value, lifting and linear logarithmic factors are bounded with
explicit coefficients eight, four and three respectively.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Control every conductor logarithmic factor by the common endpoint logarithm. -/
theorem conductor_log_envelopes {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3)
      (And ((1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2)
        (2 + Real.log (Q : Real) <= 3 * Real.log X)) := by
  have hRange := conductor_log_range hX hQ hQX
  have hLogFour := hRange.1
  have hQNonneg := hRange.2.1
  have hQLe := hRange.2.2.1
  have hProductNonneg := hRange.2.2.2.1
  have hProductLe := hRange.2.2.2.2
  have hCube : Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3 := by
    calc
      Real.log (X * (Q : Real)) ^ 3 <= (2 * Real.log X) ^ 3 := by gcongr
      _ = 8 * (Real.log X) ^ 3 := by ring
  have hSquareRange : 1 + Real.log (Q : Real) <= 2 * Real.log X := by linarith
  have hSquareNonneg : 0 <= 1 + Real.log (Q : Real) := by linarith
  have hSquare : (1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2 := by
    calc
      (1 + Real.log (Q : Real)) ^ 2 <= (2 * Real.log X) ^ 2 := by gcongr
      _ = 4 * (Real.log X) ^ 2 := by ring
  exact And.intro hCube (And.intro hSquare (by linarith))

end BombieriVinogradov.RealAnalysis
