import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Logarithmic mass of the prime divisors

The product of the distinct prime divisors of a positive integer divides the
integer, so their logarithms sum to at most the logarithm of that integer.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_log_primeFactors_le_log (N : Nat) [NeZero N] :
    ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
  have hProductPos : 0 < ∏ p ∈ N.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hProductLe : (∏ p ∈ N.primeFactors, p) ≤ N :=
    Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)
  have hLogProduct :
      Real.log (∏ p ∈ N.primeFactors, (p : Real)) =
        ∑ p ∈ N.primeFactors, Real.log p := by
    exact Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
  calc
    ∑ p ∈ N.primeFactors, Real.log p =
        Real.log (∏ p ∈ N.primeFactors, (p : Real)) := hLogProduct.symm
    _ = Real.log ((∏ p ∈ N.primeFactors, p : Nat) : Real) := by
      rw [Nat.cast_prod]
    _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hProductPos) (by
      exact_mod_cast hProductLe)

end BombieriVinogradov.SiegelWalfisz
