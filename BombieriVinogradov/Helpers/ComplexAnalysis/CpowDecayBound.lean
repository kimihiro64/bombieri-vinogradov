import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex-power decay from a real-part gap

A gap below real part one contributes an explicit exponential factor.
The quotient estimate also includes zero through totalized division.
-/
set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_real_cpow_div_le_exp_gap_mul_reciprocal
    {y delta : Real} (hy : 1 <= y) {s : Complex} (hs : s.re <= 1 - delta) :
    norm ((y : Complex) ^ s / s) <=
      (y * Real.exp (-delta * Real.log y)) * norm ((1 : Complex) / s) := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hExponent : Real.log y * s.re <= Real.log y * (1 - delta) :=
    mul_le_mul_of_nonneg_left hs (Real.log_nonneg hy)
  have hPower : norm ((y : Complex) ^ s) <= y * Real.exp (-delta * Real.log y) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hyPos, Real.rpow_def_of_pos hyPos]
    calc
      Real.exp (Real.log y * s.re) <= Real.exp (Real.log y * (1 - delta)) :=
        Real.exp_le_exp.mpr hExponent
      _ = y * Real.exp (-delta * Real.log y) := by
        have hIdentity : Real.log y * (1 - delta) =
            Real.log y + (-delta * Real.log y) := by ring
        rw [hIdentity, Real.exp_add, Real.exp_log hyPos]
  calc
    norm ((y : Complex) ^ s / s) =
        norm ((y : Complex) ^ s) * norm ((1 : Complex) / s) := by
      rw [div_eq_mul_inv, norm_mul, one_div]
    _ <= (y * Real.exp (-delta * Real.log y)) * norm ((1 : Complex) / s) :=
      mul_le_mul_of_nonneg_right hPower (by positivity)

end BombieriVinogradov.ComplexAnalysis
