import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Convolution

/-!
# Local pairs of geometric Euler factors

This module proves the finite geometric-series identities and positivity facts used at one prime.
-/

set_option autoImplicit false

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

/-- The coefficient of degree `r` in the product of two geometric series. -/
noncomputable def localPairCoefficient (a b : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), a ^ i * b ^ (r - i)

theorem arithmeticFunction_mul_apply_primePower_eq_localPair
    (f g : ArithmeticFunction ℂ) (a b : ℂ) {p r : ℕ} (hp : p.Prime)
    (hf : ∀ i : ℕ, f (p ^ i) = a ^ i) (hg : ∀ i : ℕ, g (p ^ i) = b ^ i) :
    (f * g) (p ^ r) = localPairCoefficient a b r := by
  rw [arithmeticFunction_mul_apply_primePower f g hp, localPairCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

theorem localPairCoefficient_comm (a b : ℂ) (r : ℕ) :
    localPairCoefficient a b r = localPairCoefficient b a r := by
  simpa [localPairCoefficient] using (Commute.all a b).geom_sum₂_comm (r + 1)

theorem localPairCoefficient_one_left_eq_geom (b : ℂ) (r : ℕ) :
    localPairCoefficient 1 b r = ∑ i ∈ Finset.range (r + 1), b ^ i := by
  calc
    localPairCoefficient 1 b r = localPairCoefficient b 1 r :=
      localPairCoefficient_comm 1 b r
    _ = ∑ i ∈ Finset.range (r + 1), b ^ i := by
      simp [localPairCoefficient]

theorem localPairCoefficient_one_left_nonneg (b : ℂ)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (r : ℕ) :
    0 ≤ localPairCoefficient 1 b r := by
  rw [localPairCoefficient_one_left_eq_geom]
  rcases hb with rfl | rfl | rfl
  · simp [zero_geom_sum]
  · simp only [one_geom_sum]
    exact_mod_cast Nat.zero_le (r + 1)
  · rw [neg_one_geom_sum]
    split_ifs <;> simp

theorem localPairCoefficient_one_right_nonneg (a : ℂ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (r : ℕ) :
    0 ≤ localPairCoefficient a 1 r := by
  rw [localPairCoefficient_comm]
  exact localPairCoefficient_one_left_nonneg a ha r

theorem localPairCoefficient_zero_zero_nonneg (r : ℕ) :
    0 ≤ localPairCoefficient 0 0 r := by
  cases r with
  | zero => simp [localPairCoefficient]
  | succ r =>
      rw [localPairCoefficient]
      apply Finset.sum_nonneg
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · simp [zero_pow hi0]

theorem zeta_mul_character_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p r : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·))
        (p ^ r) = localPairCoefficient 1 (χ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ by simpa using arithmeticZeta_primePower hp)
    (fun _ ↦ characterArithmetic_primePower χ hp)

theorem character_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (χ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower χ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

theorem character_right_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (ψ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower ψ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

end BombieriVinogradov.SiegelWalfisz
