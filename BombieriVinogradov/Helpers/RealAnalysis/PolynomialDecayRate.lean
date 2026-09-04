import BombieriVinogradov.Helpers.RealAnalysis.PolynomialExponentialAbsorption
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial absorption while preserving exponential decay

When the original rate is at least twice a positive target rate, one
Taylor bound absorbs any natural power without losing the target rate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem pow_mul_exp_neg_le_factorial_div_pow_mul_exp
    {a b t : Real} (ha : 0 < a) (hRate : 2 * a <= b)
    (ht : 0 <= t) (n : Nat) :
    t ^ n * Real.exp (-(b * t)) <=
      ((Nat.factorial n : Real) / a ^ n) * Real.exp (-(a * t)) := by
  have hTaylor := pow_mul_exp_neg_mul_le_factorial_div_pow ha ht n
  have hSplit : Real.exp (-(b * t)) =
      Real.exp (-(a * t)) * Real.exp (-((b - a) * t)) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  have hDecay : Real.exp (-((b - a) * t)) <= Real.exp (-(a * t)) := by
    apply Real.exp_le_exp.mpr
    have hMul := mul_le_mul_of_nonneg_right hRate ht
    linarith
  calc
    t ^ n * Real.exp (-(b * t)) =
        (t ^ n * Real.exp (-(a * t))) * Real.exp (-((b - a) * t)) := by
      rw [hSplit]
      ring
    _ <= ((Nat.factorial n : Real) / a ^ n) * Real.exp (-((b - a) * t)) :=
      mul_le_mul_of_nonneg_right hTaylor (Real.exp_pos _).le
    _ <= ((Nat.factorial n : Real) / a ^ n) * Real.exp (-(a * t)) :=
      mul_le_mul_of_nonneg_left hDecay (by positivity)

end BombieriVinogradov.RealAnalysis
