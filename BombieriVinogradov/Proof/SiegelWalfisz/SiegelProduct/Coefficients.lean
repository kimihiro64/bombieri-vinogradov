import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.PrimePowers

/-!
# Global positivity for the Siegel product

This module lifts prime-power positivity to every coefficient by multiplicative factorization.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

/-- Every Dirichlet coefficient of the four-factor product in Siegel's theorem is nonnegative. -/
theorem siegelProductCoefficients_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelProductCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(siegelProductCoefficients_isMultiplicative χ ψ).multiplicative_factorization
      _ hn] using!
      Finset.prod_nonneg fun p hp ↦
        siegelProductCoefficients_primePower_nonneg χ ψ hχ hψ
          (Nat.prime_of_mem_primeFactors hp)

/-- The coefficient at one is exactly one. -/
theorem siegelProductCoefficients_one {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ 1 = 1 :=
  (siegelProductCoefficients_isMultiplicative χ ψ).map_one

end BombieriVinogradov.SiegelWalfisz
