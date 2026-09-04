import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic majorants against the reciprocal Abel kernel

The quadratic contribution is bounded before summing the positive kernel.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Divide a quadratic by the Abel denominator while preserving its coefficient scales. -/
theorem quadratic_div_reciprocal_kernel_le (a b c k : Real) (hc : 0 <= c) (hk : 0 < k) :
    (a + b * k + c * k ^ 2) / (k * (k + 1)) <=
      a / (k * (k + 1)) + b / (k + 1) + c := by
  have hkZero : Ne k 0 := by positivity
  have hkOne : Ne (k + 1) 0 := by positivity
  have hIdentity : (a + b * k + c * k ^ 2) / (k * (k + 1)) =
      a / (k * (k + 1)) + b / (k + 1) + c - c / (k + 1) := by
    field_simp
    ring
  have hRemainder : 0 <= c / (k + 1) := by positivity
  rw [hIdentity]
  linarith

end BombieriVinogradov.RealAnalysis
