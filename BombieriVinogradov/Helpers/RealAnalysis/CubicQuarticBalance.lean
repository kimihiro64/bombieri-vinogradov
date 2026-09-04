import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A uniform cubic-versus-quartic bound

Splitting at the ratio of the positive coefficients controls the whole
nonnegative half-line without changing either exponent.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem cubic_sub_quartic_le
    {a k u : Real} (ha : 0 <= a) (hk : 0 < k) (hu : 0 <= u) :
    a * u ^ 3 - k * u ^ 4 <= a ^ 4 / k ^ 3 := by
  have hRightNonneg : 0 <= a ^ 4 / k ^ 3 := by positivity
  by_cases hCut : u <= a / k
  case pos =>
    have hCube : u ^ 3 <= (a / k) ^ 3 := by gcongr
    have hMain : a * u ^ 3 <= a * (a / k) ^ 3 :=
      mul_le_mul_of_nonneg_left hCube ha
    have hFourth : 0 <= k * u ^ 4 := by positivity
    calc
      a * u ^ 3 - k * u ^ 4 <= a * u ^ 3 := sub_le_self _ hFourth
      _ <= a * (a / k) ^ 3 := hMain
      _ = a ^ 4 / k ^ 3 := by ring
  case neg =>
    have hCutLt : a / k < u := lt_of_not_ge hCut
    have hScaled := mul_le_mul_of_nonneg_left hCutLt.le hk.le
    have hCancel : k * (a / k) = a := by field_simp
    rw [hCancel] at hScaled
    have hDifference : a - k * u <= 0 := by linarith
    have hProduct : (a - k * u) * u ^ 3 <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg hDifference (by positivity)
    calc
      a * u ^ 3 - k * u ^ 4 = (a - k * u) * u ^ 3 := by ring
      _ <= 0 := hProduct
      _ <= a ^ 4 / k ^ 3 := hRightNonneg

end BombieriVinogradov.RealAnalysis
