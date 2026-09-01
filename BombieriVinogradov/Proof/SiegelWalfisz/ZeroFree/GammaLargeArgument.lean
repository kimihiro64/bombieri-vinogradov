import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Real Gamma bound for large arguments

This module bounds `Gamma x` for `x >= 2` by rounding upward to a natural
argument and applying the elementary factorial bound `n! <= n^n`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem realGamma_le_rpow_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ (x + 1) ^ (x + 1) := by
  let n : ℕ := Nat.ceil x
  have hxNonneg : 0 ≤ x := zero_le_two.trans hx
  have hxn : x ≤ (n : ℝ) := by
    exact Nat.le_ceil x
  have hnUpper : (n : ℝ) ≤ x + 1 := by
    exact (Nat.ceil_lt_add_one hxNonneg).le
  have hnTwo : 2 ≤ n := by
    exact_mod_cast hx.trans hxn
  have hgammaMonotone : Real.Gamma x ≤ Real.Gamma n :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hx)
      (Set.mem_Ici.mpr (by exact_mod_cast hnTwo)) hxn
  have hgammaNat : Real.Gamma n = ((n - 1).factorial : ℝ) := by
    have hnOne : 1 ≤ n := one_le_two.trans hnTwo
    have hnSplit : n - 1 + 1 = n := Nat.sub_add_cancel hnOne
    rw [← hnSplit]
    simpa using Real.Gamma_nat_eq_factorial (n - 1)
  have hfactorialNat : (n - 1).factorial ≤ n ^ n := by
    exact (Nat.factorial_le (Nat.sub_le n 1)).trans
      (Nat.factorial_le_pow n)
  have hfactorial : ((n - 1).factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfactorialNat
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  have hnLePower : (n : ℝ) ^ n ≤ (x + 1) ^ (x + 1) := by
    rw [← Real.rpow_natCast]
    calc
      (n : ℝ) ^ (n : ℝ) ≤ (x + 1) ^ (n : ℝ) :=
        Real.rpow_le_rpow hnNonneg hnUpper hnNonneg
      _ ≤ (x + 1) ^ (x + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hnUpper
  exact hgammaMonotone.trans_eq hgammaNat |>.trans hfactorial |>.trans hnLePower

end BombieriVinogradov.SiegelWalfisz
