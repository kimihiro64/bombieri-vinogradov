import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The logarithm of an exponential height cutoff

Rounding the positive height upward and shifting it by two costs at most
three times the exponent when the exponent is at least one.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem log_ceil_exp_add_two_le_three_mul {t : Real} (ht : 1 <= t) :
    Real.log (((Nat.ceil (Real.exp t) : Nat) : Real) + 2) <= 3 * t := by
  have hExpPos : 0 < Real.exp t := Real.exp_pos t
  have hExpOne : 1 <= Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have hCeil : ((Nat.ceil (Real.exp t) : Nat) : Real) < Real.exp t + 1 :=
    Nat.ceil_lt_add_one hExpPos.le
  have hArg : ((Nat.ceil (Real.exp t) : Nat) : Real) + 2 <= 4 * Real.exp t := by
    linarith
  have hArgPos : 0 < ((Nat.ceil (Real.exp t) : Nat) : Real) + 2 := by
    have h : (0 : Real) <= ((Nat.ceil (Real.exp t) : Nat) : Real) :=
      Nat.cast_nonneg (Nat.ceil (Real.exp t))
    linarith
  have hLogTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : Real)) (by norm_num)
    norm_num at h
    exact h
  have hLogFour : Real.log (4 : Real) = Real.log (2 : Real) + Real.log (2 : Real) := by
    calc
      Real.log (4 : Real) = Real.log ((2 : Real) * 2) := by norm_num
      _ = Real.log (2 : Real) + Real.log (2 : Real) :=
        Real.log_mul (by norm_num) (by norm_num)
  have hLogProduct : Real.log ((4 : Real) * Real.exp t) = Real.log 4 + t := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hExpPos), Real.log_exp]
  have hLog := Real.log_le_log hArgPos hArg
  rw [hLogProduct, hLogFour] at hLog
  linarith

end BombieriVinogradov.RealAnalysis
