import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Four-factor Siegel-product coefficients

This module owns the arithmetic convolution, its multiplicativity, and exact prime-power evaluation.
-/

set_option autoImplicit false

open ArithmeticFunction

namespace BombieriVinogradov.SiegelWalfisz

theorem arithmeticFunction_mul_apply_primePower (f g : ArithmeticFunction ℂ)
    {p r : ℕ} (hp : p.Prime) :
    (f * g) (p ^ r) = ∑ i ∈ Finset.range (r + 1), f (p ^ i) * g (p ^ (r - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

/-- The arithmetic function attached to the pointwise product of two characters. -/
noncomputable def characterPairArithmetic {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * ψ n

theorem toArithmeticFunction_apply_of_ne_zero (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

theorem characterPairArithmetic_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (characterPairArithmetic χ ψ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ ↦ ?_⟩
  · simp [characterPairArithmetic, toArithmeticFunction]
  · simp [characterPairArithmetic, toArithmeticFunction, hm, hn, map_mul]
    ring

theorem arithmeticZeta_primePower {p i : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) = 1 := by
  simp [hp.ne_zero]

theorem characterArithmetic_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p i : ℕ} (hp : p.Prime) :
    toArithmeticFunction (χ ·) (p ^ i) = (χ p) ^ i := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow,
    map_pow]

theorem characterPairArithmetic_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p i : ℕ} (hp : p.Prime) :
    characterPairArithmetic χ ψ (p ^ i) = (χ p * ψ p) ^ i := by
  have hpPow : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [characterPairArithmetic, toArithmeticFunction_apply_of_ne_zero _ hpPow]
  simp only [Nat.cast_pow, map_pow, mul_pow]

/-- Dirichlet coefficients of the four-factor product used in Siegel's theorem. -/
noncomputable def siegelProductCoefficients {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    characterPairArithmetic χ ψ

theorem siegelProductCoefficients_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (siegelProductCoefficients χ ψ).IsMultiplicative := by
  exact (((isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction).mul
    ψ.isMultiplicative_toArithmeticFunction).mul (characterPairArithmetic_isMultiplicative χ ψ))

theorem siegelProductCoefficients_grouped {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·)) *
        (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients, mul_assoc]

theorem siegelProductCoefficients_grouped_swap {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (ψ ·)) *
        (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients]
  ring

theorem siegelProductCoefficients_outer_expand {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    siegelProductCoefficients χ ψ n =
      ∑ d ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.zeta * toArithmeticFunction (χ ·) *
          toArithmeticFunction (ψ ·)) d.1 * characterPairArithmetic χ ψ d.2 := by
  rw [siegelProductCoefficients, ArithmeticFunction.mul_apply]

end BombieriVinogradov.SiegelWalfisz
