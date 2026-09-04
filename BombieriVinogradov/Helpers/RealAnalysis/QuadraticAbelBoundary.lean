import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quadratic Abel boundary estimates

Only the constant term loses an inverse lower-cutoff factor at the boundary.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Bound a quadratic boundary term using any positive lower cutoff. -/
theorem quadratic_div_boundary_le (a b c q r : Real)
    (ha : 0 <= a) (hr : 0 < r) (hrq : r <= q) :
    (a + b * q + c * q ^ 2) / q <= a / r + b + c * q := by
  have hq : 0 < q := hr.trans_le hrq
  have hqZero : Ne q 0 := by positivity
  have hIdentity : (a + b * q + c * q ^ 2) / q = a / q + b + c * q := by
    field_simp
  have hConstant : a / q <= a / r := div_le_div_of_nonneg_left ha hr hrq
  rw [hIdentity]
  linarith

end BombieriVinogradov.RealAnalysis
