import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A bounded positive half-power gap

This module isolates one scalar step in the weighted mean argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A strict exponent below one-half supplies a positive gap capped by one-sixth. -/
theorem exists_bounded_half_power_gap {theta : Real} (hTheta : theta < 1 / 2) :
    exists delta : Real, And (0 < delta) (And (delta <= 1 / 6) (theta + delta <= 1 / 2)) := by
  have hPos : 0 < min (1 / 6 : Real) (1 / 2 - theta) :=
    lt_min (by linarith) (by linarith)
  have hCap := min_le_left (1 / 6 : Real) (1 / 2 - theta)
  have hGap := min_le_right (1 / 6 : Real) (1 / 2 - theta)
  exact Exists.intro (min (1 / 6 : Real) (1 / 2 - theta))
    (And.intro hPos (And.intro hCap (by linarith)))

end BombieriVinogradov.RealAnalysis
