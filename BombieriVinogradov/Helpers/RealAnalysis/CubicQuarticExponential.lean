import BombieriVinogradov.Helpers.RealAnalysis.CubicQuarticBalance
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exponential absorption of quartic damping

The cubic-quartic balance yields a uniform multiplicative coefficient
while preserving the chosen cubic exponential rate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_neg_quartic_le_exp_cubic
    {a k u : Real} (ha : 0 <= a) (hk : 0 < k) (hu : 0 <= u) :
    Real.exp (-(k * u ^ 4)) <=
      Real.exp (a ^ 4 / k ^ 3) * Real.exp (-(a * u ^ 3)) := by
  have hBalance := cubic_sub_quartic_le ha hk hu
  have hExponent : -(k * u ^ 4) <= a ^ 4 / k ^ 3 + (-(a * u ^ 3)) := by
    linarith
  calc
    Real.exp (-(k * u ^ 4)) <= Real.exp (a ^ 4 / k ^ 3 + (-(a * u ^ 3))) :=
      Real.exp_le_exp.mpr hExponent
    _ = Real.exp (a ^ 4 / k ^ 3) * Real.exp (-(a * u ^ 3)) := Real.exp_add _ _

end BombieriVinogradov.RealAnalysis
