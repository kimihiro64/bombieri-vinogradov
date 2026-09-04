import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# A linear bound for a complex-power quotient

For a positive real base at least one and exponent with real part at
most one, the quotient is controlled by the base times the reciprocal.
The estimate includes a zero denominator through Lean's total division.
-/
set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_real_cpow_div_le_mul_norm_one_div
    {y : Real} (hy : 1 <= y) {s : Complex} (hs : s.re <= 1) :
    norm ((y : Complex) ^ s / s) <= y * norm ((1 : Complex) / s) := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hPower : norm ((y : Complex) ^ s) <= y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    exact Real.rpow_le_self_of_one_le hy hs
  calc
    norm ((y : Complex) ^ s / s) =
        norm ((y : Complex) ^ s) * norm ((1 : Complex) / s) := by
      rw [div_eq_mul_inv, norm_mul, one_div]
    _ <= y * norm ((1 : Complex) / s) :=
      mul_le_mul_of_nonneg_right hPower (by positivity)

end BombieriVinogradov.ComplexAnalysis
