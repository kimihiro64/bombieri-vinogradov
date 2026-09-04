import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial absorption into exponential decay

A single nonnegative Taylor term gives explicit uniform bounds for every
natural degree, including degree zero and the endpoint zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem pow_mul_exp_neg_le_factorial {u : Real} (hu : 0 <= u) (n : Nat) :
    u ^ n * Real.exp (-u) <= (Nat.factorial n : Real) := by
  have hFactorial : 0 < (Nat.factorial n : Real) :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hFactorialNe : Ne (Nat.factorial n : Real) 0 := ne_of_gt hFactorial
  have hExpNe : Ne (Real.exp u) 0 := ne_of_gt (Real.exp_pos u)
  have hTaylor := Real.pow_div_factorial_le_exp u hu n
  have hBound := mul_le_mul_of_nonneg_right hTaylor
    (show 0 <= (Nat.factorial n : Real) * Real.exp (-u) by positivity)
  calc
    u ^ n * Real.exp (-u) =
        (u ^ n / (Nat.factorial n : Real)) *
          ((Nat.factorial n : Real) * Real.exp (-u)) := by field_simp
    _ <= Real.exp u * ((Nat.factorial n : Real) * Real.exp (-u)) := hBound
    _ = (Nat.factorial n : Real) := by
      rw [Real.exp_neg]
      field_simp

theorem pow_mul_exp_neg_mul_le_factorial_div_pow
    {a t : Real} (ha : 0 < a) (ht : 0 <= t) (n : Nat) :
    t ^ n * Real.exp (-(a * t)) <= (Nat.factorial n : Real) / a ^ n := by
  have hPower : 0 < a ^ n := pow_pos ha n
  have hPowerNe : Ne (a ^ n) 0 := ne_of_gt hPower
  have hScaled := pow_mul_exp_neg_le_factorial (show 0 <= a * t by positivity) n
  have hBound := mul_le_mul_of_nonneg_right hScaled
    (show 0 <= 1 / a ^ n by positivity)
  calc
    t ^ n * Real.exp (-(a * t)) =
        ((a * t) ^ n * Real.exp (-(a * t))) * (1 / a ^ n) := by
      rw [mul_pow]
      field_simp
    _ <= (Nat.factorial n : Real) * (1 / a ^ n) := hBound
    _ = (Nat.factorial n : Real) / a ^ n := by ring

end BombieriVinogradov.RealAnalysis
