import BombieriVinogradov.Helpers.RealAnalysis.ExponentialLogFactorization
import BombieriVinogradov.Helpers.RealAnalysis.QuadraticExponentialAbsorption
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial absorption into a square-logarithmic scale

The exact cancellation identity and the quadratic exponential bound
absorb every natural power into x times the selected exponential decay.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem pow_le_exponentialLog_scale
    {x t a b : Real} (hx : 0 < x) (hSquare : t ^ 2 = Real.log x)
    (ht : 1 <= t) (hb : 0 < b) (hRate : a + b <= 1) (n : Nat) :
    t ^ n <= ((Nat.factorial n : Real) / b ^ n) *
      (x * Real.exp (-(a * t))) := by
  have hQuadratic : t ^ n * Real.exp (-t ^ 2 + a * t) <=
      (Nat.factorial n : Real) / b ^ n := by
    simpa using (pow_mul_exp_quadratic_le_factorial_div_pow
      (r := (1 : Real)) (by norm_num) hb hRate ht n)
  have hCancel := exponentialLog_scale_cancellation (a := a) hx hSquare
  calc
    t ^ n = t ^ n * 1 := by ring
    _ = t ^ n * ((x * Real.exp (-(a * t))) *
        Real.exp (-t ^ 2 + a * t)) := by rw [hCancel]
    _ = (x * Real.exp (-(a * t))) *
        (t ^ n * Real.exp (-t ^ 2 + a * t)) := by ring
    _ <= (x * Real.exp (-(a * t))) *
        ((Nat.factorial n : Real) / b ^ n) :=
      mul_le_mul_of_nonneg_left hQuadratic (by positivity)
    _ = ((Nat.factorial n : Real) / b ^ n) *
        (x * Real.exp (-(a * t))) := by ring

end BombieriVinogradov.RealAnalysis
