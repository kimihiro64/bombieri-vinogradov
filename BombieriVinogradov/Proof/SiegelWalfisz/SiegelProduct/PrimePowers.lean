import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.LocalPairs
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Values

/-!
# Prime-power positivity for the Siegel product

This module assembles the local character-value cases into coefficient positivity at one prime power.
-/

set_option autoImplicit false

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_primePower_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) {p r : ℕ} (hp : p.Prime) :
    0 ≤ siegelProductCoefficients χ ψ (p ^ r) := by
  rcases quadraticValue_cases χ hχ p with hχp | hχp | hχp
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, zero_mul]
      exact localPairCoefficient_zero_zero_nonneg (r - i)
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, one_mul]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) (r - i)
  · rw [siegelProductCoefficients_grouped,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower χ hp, hχp]
      exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) i
    · rw [character_right_mul_pair_primePower χ ψ hp, hχp]
      rcases quadraticValue_cases ψ hψ p with hψp | hψp | hψp
      · rw [hψp]
        norm_num
        exact localPairCoefficient_zero_zero_nonneg (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_right_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)

end BombieriVinogradov.SiegelWalfisz
