import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Logarithmic ranges below a real endpoint

The positive conductor logarithm is controlled by the endpoint logarithm,
and the product logarithm retains both factors.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Logarithmic sign and range bounds for a positive conductor below X. -/
theorem conductor_log_range {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (4 <= Real.log X)
      (And (0 <= Real.log (Q : Real))
        (And (Real.log (Q : Real) <= Real.log X)
          (And (0 <= Real.log (X * (Q : Real)))
            (Real.log (X * (Q : Real)) <= 2 * Real.log X)))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hQPos : (0 : Real) < (Q : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hQNonneg : 0 <= Real.log (Q : Real) := Real.log_natCast_nonneg Q
  have hQLe : Real.log (Q : Real) <= Real.log X := Real.log_le_log hQPos hQX
  have hProduct : Real.log (X * (Q : Real)) = Real.log X + Real.log (Q : Real) :=
    Real.log_mul (ne_of_gt hXPos) (ne_of_gt hQPos)
  have hProductNonneg : 0 <= Real.log (X * (Q : Real)) := by rw [hProduct]; linarith
  have hProductLe : Real.log (X * (Q : Real)) <= 2 * Real.log X := by rw [hProduct]; linarith
  exact And.intro hLogFour (And.intro hQNonneg
    (And.intro hQLe (And.intro hProductNonneg hProductLe)))

end BombieriVinogradov.RealAnalysis
