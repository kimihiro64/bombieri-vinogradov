import BombieriVinogradov.Helpers.RealAnalysis.PolynomialExponentialAbsorption
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Polynomial absorption against a quadratic exponential

For t at least one, a nonnegative quadratic coefficient supplies a
linear decay gap. The factorial bound works for every natural degree.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem pow_mul_exp_quadratic_le_factorial_div_pow
    {r b a t : Real} (hr : 0 <= r) (hb : 0 < b)
    (hRate : a + b <= r) (ht : 1 <= t) (n : Nat) :
    t ^ n * Real.exp (-r * t ^ 2 + a * t) <=
      (Nat.factorial n : Real) / b ^ n := by
  have htNonneg : 0 <= t := by linarith
  have hSquare : t <= t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ht htNonneg
    nlinarith
  have hR := mul_le_mul_of_nonneg_left hSquare hr
  have hAB := mul_le_mul_of_nonneg_right hRate htNonneg
  have hDecay : Real.exp (-r * t ^ 2 + a * t) <= Real.exp (-(b * t)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hTaylor := pow_mul_exp_neg_mul_le_factorial_div_pow hb htNonneg n
  exact (mul_le_mul_of_nonneg_left hDecay (show 0 <= t ^ n by positivity)).trans hTaylor

theorem sq_mul_exp_quadratic_le_thirty_two
    {a t : Real} (ha : a <= (1 / 2 : Real)) (ht : 1 <= t) :
    t ^ 2 * Real.exp (-(3 / 4 : Real) * t ^ 2 + a * t) <= 32 := by
  convert (pow_mul_exp_quadratic_le_factorial_div_pow
    (r := (3 / 4 : Real)) (b := (1 / 4 : Real)) (a := a) (t := t)
    (by norm_num) (by norm_num) (by linarith) ht 2) using 1
  norm_num

end BombieriVinogradov.RealAnalysis
