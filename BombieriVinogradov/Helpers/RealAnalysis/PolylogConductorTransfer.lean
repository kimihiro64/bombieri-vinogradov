import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Conductor-power transfer after a square-root endpoint split

Once the original logarithm is at least four, losing a factor two in its base
is compensated by doubling any nonnegative logarithmic exponent.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Doubling the exponent compensates for a factor-two loss in a large base. -/
theorem rpow_le_rpow_twice_of_le_two_mul {L m B : Real}
    (hL : 4 <= L) (hm : L <= 2 * m) (hB : 0 <= B) :
    L ^ B <= m ^ (2 * B) := by
  have hLNonneg : 0 <= L := by linarith
  have hmNonneg : 0 <= m := by linarith
  have hmTwo : 2 <= m := by linarith
  have hProduct := mul_le_mul_of_nonneg_right hmTwo hmNonneg
  have hSquare : L <= m ^ 2 := by nlinarith
  calc
    L ^ B <= (m ^ 2) ^ B := Real.rpow_le_rpow hLNonneg hSquare hB
    _ = m ^ (2 * B) := by rw [Real.rpow_mul hmNonneg, Real.rpow_two]

end BombieriVinogradov.RealAnalysis
